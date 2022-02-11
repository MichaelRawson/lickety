use crate::nf::NormalForm;
use crate::syntax;
use anyhow::{anyhow, bail, Context};
use fnv::{FnvHashMap, FnvHashSet};
use std::borrow::Cow;
use std::rc::Rc;
use std::{env, fs, path};
use tptp::cnf::*;
use tptp::common::*;
use tptp::fof::*;
use tptp::top::*;
use tptp::{cnf, common, fof, TPTPIterator};

fn read_path_with_parent(parent: &path::Path, path: &path::Path) -> anyhow::Result<Vec<u8>> {
    fs::read(parent.join(path))
        .map_err(anyhow::Error::from)
        .with_context(|| {
            format!(
                "reading '{}' in directory '{}'...",
                path.display(),
                parent.display()
            )
        })
}

fn read_path_no_parent(path: &path::Path) -> anyhow::Result<Vec<u8>> {
    let directory = env::var("TPTP_DIR")
        .map(path::PathBuf::from)
        .or_else(|_| env::current_dir())?;
    read_path_with_parent(&directory, path)
}

fn read_path(parent: Option<&path::Path>, path: &path::Path) -> anyhow::Result<Vec<u8>> {
    if let Some(parent) = parent {
        read_path_with_parent(parent, path)
            .or_else(|_| read_path_no_parent(path))
            .context("failed relative include, falling back...")
    } else {
        read_path_no_parent(path)
    }
}

#[derive(PartialEq, Eq, Hash)]
struct SymbolEntry<'a> {
    arity: usize,
    sort: syntax::Sort,
    name: Cow<'a, str>,
}

#[derive(Default)]
struct Loader {
    nf: NormalForm,
    equality: Option<syntax::SymbolRef>,
    fresh_variable: usize,
    fresh_symbol: usize,
    lower: FnvHashMap<SymbolEntry<'static>, syntax::SymbolRef>,
    quoted: FnvHashMap<SymbolEntry<'static>, syntax::SymbolRef>,
    number: FnvHashMap<String, syntax::SymbolRef>,
    distinct: FnvHashMap<String, syntax::SymbolRef>,
}

impl Loader {
    fn get_equality_symbol(&mut self) -> syntax::SymbolRef {
        *self.equality.get_or_insert_with(|| {
            syntax::SymbolRef::new(syntax::Symbol {
                number: 1,
                arity: 2,
                sort: syntax::Sort::Boolean,
                name: syntax::Name::Equality,
            })
        })
    }

    fn defined_term(&mut self, term: common::DefinedTerm, sort: syntax::Sort) -> syntax::FofTerm {
        let (lookup, borrowed) = match term {
            common::DefinedTerm::Number(ref number) => {
                let borrowed = match number {
                    Number::Integer(n) => n.0,
                    Number::Rational(r) => r.0,
                    Number::Real(r) => r.0,
                };
                (&mut self.number, borrowed)
            }
            common::DefinedTerm::Distinct(ref distinct) => (&mut self.distinct, distinct.0),
        };
        let symbol = if let Some(symbol) = lookup.get(borrowed) {
            *symbol
        } else {
            let number = self.fresh_symbol;
            self.fresh_symbol += 1;
            let name = match term {
                common::DefinedTerm::Number(_) => syntax::Name::Number(borrowed.to_owned()),
                common::DefinedTerm::Distinct(_) => syntax::Name::Distinct(borrowed.to_owned()),
            };
            let symbol = syntax::SymbolRef::new(syntax::Symbol {
                number,
                arity: 0,
                sort,
                name,
            });
            lookup.insert(borrowed.to_owned(), symbol);
            symbol
        };
        syntax::FofTerm::Function(symbol, vec![])
    }

    fn fof_plain_term<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        term: PlainTerm<'a>,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::FofTerm> {
        let (sym, args) = match term {
            PlainTerm::Constant(c) => (c.0 .0, vec![]),
            PlainTerm::Function(f, args) => (f.0, args.0),
        };
        let arity = args.len();
        let (lookup, borrowed) = match sym {
            AtomicWord::Lower(ref w) => (&mut self.lower, w.0),
            AtomicWord::SingleQuoted(ref q) => (&mut self.quoted, q.0),
        };
        let name = Cow::Borrowed(borrowed);
        let entry = SymbolEntry { arity, sort, name };
        let symbol = if let Some(symbol) = lookup.get(&entry) {
            *symbol
        } else {
            let number = self.fresh_symbol;
            self.fresh_symbol += 1;
            let string = borrowed.to_string();
            let name = Cow::Owned(string.clone());
            let entry = SymbolEntry { arity, sort, name };
            let name = match sym {
                AtomicWord::Lower(_) => syntax::Name::Atom(string),
                AtomicWord::SingleQuoted(_) => syntax::Name::Quoted(string),
            };
            let symbol = syntax::SymbolRef::new(syntax::Symbol {
                number,
                arity,
                sort,
                name,
            });
            lookup.insert(entry, symbol);
            symbol
        };
        let args = args
            .into_iter()
            .map(|t| self.fof_term(bound, free, t, syntax::Sort::Individual))
            .collect::<anyhow::Result<_>>()?;
        Ok(syntax::FofTerm::Function(symbol, args))
    }

    fn fof_defined_term(
        &mut self,
        term: fof::DefinedTerm,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::FofTerm> {
        match term {
            fof::DefinedTerm::Defined(defined) => Ok(self.defined_term(defined, sort)),
            fof::DefinedTerm::Atomic(atomic) => {
                Err(anyhow!("unsupported defined term: {}", atomic))
            }
        }
    }

    fn fof_function_term<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        term: FunctionTerm<'a>,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::FofTerm> {
        match term {
            FunctionTerm::Plain(term) => self.fof_plain_term(bound, free, term, sort),
            FunctionTerm::Defined(def) => self.fof_defined_term(def, sort),
            FunctionTerm::System(system) => Err(anyhow!("unsupported system term: {}", system)),
        }
    }

    fn fof_term<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        term: Term<'a>,
        sort: syntax::Sort,
    ) -> anyhow::Result<syntax::FofTerm> {
        Ok(match term {
            Term::Function(term) => self.fof_function_term(bound, free, *term, sort)?,
            Term::Variable(x) => {
                let name = x.0 .0;
                let var =
                    if let Some((_, var)) = bound.iter().rev().find(|(bound, _)| *bound == name) {
                        *var
                    } else if let Some((_, var)) = free.iter().find(|(free, _)| *free == name) {
                        *var
                    } else {
                        let var = self.fresh_variable;
                        free.push((name, var));
                        self.fresh_variable += 1;
                        var
                    };
                syntax::FofTerm::Variable(var)
            }
        })
    }

    fn fof_defined_plain_formula(
        &mut self,
        atom: DefinedPlainFormula,
    ) -> anyhow::Result<syntax::FofAtomic> {
        match atom.0 {
            DefinedPlainTerm::Constant(c) => match c.0 .0 .0 .0 .0 {
                "true" => Ok(syntax::FofAtomic::Boolean(true)),
                "false" => Ok(syntax::FofAtomic::Boolean(false)),
                _ => Err(anyhow!("unsupported defined formula: {}", c)),
            },
            f @ DefinedPlainTerm::Function(_, _) => {
                Err(anyhow!("unsupported defined formula: {}", f))
            }
        }
    }

    fn fof_defined_atomic_formula<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        atom: DefinedAtomicFormula<'a>,
    ) -> anyhow::Result<syntax::FofAtomic> {
        Ok(match atom {
            DefinedAtomicFormula::Plain(plain) => self.fof_defined_plain_formula(plain)?,
            DefinedAtomicFormula::Infix(infix) => {
                syntax::FofAtomic::Predicate(syntax::FofTerm::Function(
                    self.get_equality_symbol(),
                    vec![
                        self.fof_term(bound, free, *infix.left, syntax::Sort::Individual)?,
                        self.fof_term(bound, free, *infix.right, syntax::Sort::Individual)?,
                    ],
                ))
            }
        })
    }

    fn fof_atomic_formula<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        atom: AtomicFormula<'a>,
    ) -> anyhow::Result<syntax::FofAtomic> {
        match atom {
            AtomicFormula::Plain(plain) => Ok(syntax::FofAtomic::Predicate(self.fof_plain_term(
                bound,
                free,
                plain.0,
                syntax::Sort::Boolean,
            )?)),
            AtomicFormula::Defined(defined) => {
                Ok(self.fof_defined_atomic_formula(bound, free, defined)?)
            }
            AtomicFormula::System(system) => Err(anyhow!("unsupported system formula: {}", system)),
        }
    }

    fn fof_infix_unary<'a>(
        &mut self,
        bound: &[(&str, usize)],
        free: &mut Vec<(&'a str, usize)>,
        infix: InfixUnary<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        Ok(syntax::Fof::Not(Box::new(syntax::Fof::Atom(
            syntax::FofAtomic::Predicate(syntax::FofTerm::Function(
                self.get_equality_symbol(),
                vec![
                    self.fof_term(bound, free, *infix.left, syntax::Sort::Individual)?,
                    self.fof_term(bound, free, *infix.right, syntax::Sort::Individual)?,
                ],
            )),
        ))))
    }

    fn fof_unit_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: UnitFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        match fof {
            UnitFormula::Unitary(f) => self.fof_unitary_formula(bound, free, f),
            UnitFormula::Unary(f) => self.fof_unary_formula(bound, free, f),
        }
    }

    fn fof_binary_assoc<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: BinaryAssoc<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        Ok(match fof {
            BinaryAssoc::And(fs) => syntax::Fof::And(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(bound, free, f))
                    .collect::<anyhow::Result<_>>()?,
            ),
            BinaryAssoc::Or(fs) => syntax::Fof::Or(
                fs.0.into_iter()
                    .map(|f| self.fof_unit_formula(bound, free, f))
                    .collect::<anyhow::Result<_>>()?,
            ),
        })
    }

    fn fof_binary_nonassoc<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: BinaryNonassoc<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        let left = self.fof_unit_formula(bound, free, *fof.left)?;
        let right = self.fof_unit_formula(bound, free, *fof.right)?;
        use NonassocConnective as NC;
        Ok(match fof.op {
            NC::LRImplies => syntax::Fof::Or(vec![syntax::Fof::Not(Box::new(left)), right]),
            NC::RLImplies => syntax::Fof::Or(vec![left, syntax::Fof::Not(Box::new(right))]),
            NC::Equivalent => syntax::Fof::Equivalent(Box::new(left), Box::new(right)),
            NC::NotEquivalent => syntax::Fof::Not(Box::new(syntax::Fof::Equivalent(
                Box::new(left),
                Box::new(right),
            ))),
            NC::NotAnd => syntax::Fof::Not(Box::new(syntax::Fof::And(vec![left, right]))),
            NC::NotOr => syntax::Fof::Not(Box::new(syntax::Fof::Or(vec![left, right]))),
        })
    }

    fn fof_binary_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: BinaryFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        match fof {
            BinaryFormula::Assoc(f) => self.fof_binary_assoc(bound, free, f),
            BinaryFormula::Nonassoc(f) => self.fof_binary_nonassoc(bound, free, f),
        }
    }

    fn fof_quantified_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: QuantifiedFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        let num_bound = fof.bound.0.len();
        for x in fof.bound.0.into_iter() {
            let name = x.0 .0;
            let var = self.fresh_variable;
            self.fresh_variable += 1;
            bound.push((name, var));
        }
        let mut f = self.fof_unit_formula(bound, free, *fof.formula)?;
        for _ in 0..num_bound {
            let (_, var) = bound.pop().expect("bound this earlier");
            f = match fof.quantifier {
                Quantifier::Forall => syntax::Fof::Forall(var, Box::new(f)),
                Quantifier::Exists => syntax::Fof::Exists(var, Box::new(f)),
            };
        }
        Ok(f)
    }

    fn fof_unitary_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: UnitaryFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        Ok(match fof {
            UnitaryFormula::Quantified(f) => self.fof_quantified_formula(bound, free, f)?,
            UnitaryFormula::Atomic(f) => {
                syntax::Fof::Atom(self.fof_atomic_formula(bound, free, *f)?)
            }
            UnitaryFormula::Parenthesised(f) => self.fof_logic_formula(bound, free, *f)?,
        })
    }

    fn fof_unary_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: UnaryFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        Ok(match fof {
            UnaryFormula::Unary(_, f) => {
                syntax::Fof::Not(Box::new(self.fof_unit_formula(bound, free, *f)?))
            }
            UnaryFormula::InfixUnary(f) => self.fof_infix_unary(bound, free, f)?,
        })
    }

    fn fof_logic_formula<'a>(
        &mut self,
        bound: &mut Vec<(&'a str, usize)>,
        free: &mut Vec<(&'a str, usize)>,
        fof: LogicFormula<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        match fof {
            LogicFormula::Binary(f) => self.fof_binary_formula(bound, free, f),
            LogicFormula::Unary(f) => self.fof_unary_formula(bound, free, f),
            LogicFormula::Unitary(f) => self.fof_unitary_formula(bound, free, f),
        }
    }

    fn fof_formula(&mut self, fof: fof::Formula) -> anyhow::Result<syntax::Fof> {
        let mut bound = vec![];
        let mut free = vec![];
        let mut formula = self.fof_logic_formula(&mut bound, &mut free, fof.0)?;
        while let Some((_, free)) = free.pop() {
            formula = syntax::Fof::Forall(free, Box::new(formula));
        }
        Ok(formula)
    }

    fn literal<'a>(
        &mut self,
        free: &mut Vec<(&'a str, usize)>,
        lit: Literal<'a>,
    ) -> anyhow::Result<syntax::Fof> {
        Ok(match lit {
            Literal::Atomic(atomic) => {
                syntax::Fof::Atom(self.fof_atomic_formula(&[], free, atomic)?)
            }
            Literal::NegatedAtomic(atomic) => syntax::Fof::Not(Box::new(syntax::Fof::Atom(
                self.fof_atomic_formula(&[], free, atomic)?,
            ))),
            Literal::Infix(infix) => self.fof_infix_unary(&[], free, infix)?,
        })
    }

    fn cnf_formula(&mut self, cnf: cnf::Formula) -> anyhow::Result<syntax::Fof> {
        let disjunction = match cnf {
            cnf::Formula::Disjunction(d) => d,
            cnf::Formula::Parenthesised(d) => d,
        };
        let mut free = vec![];
        let mut formula = syntax::Fof::Or(
            disjunction
                .0
                .into_iter()
                .map(|lit| self.literal(&mut free, lit))
                .collect::<anyhow::Result<_>>()?,
        );
        while let Some((_, free)) = free.pop() {
            formula = syntax::Fof::Forall(free, Box::new(formula));
        }
        Ok(formula)
    }

    fn annotated<D: Dialect>(
        &mut self,
        selection: Option<&FnvHashSet<Name>>,
        path: Rc<str>,
        annotated: Annotated<D>,
    ) -> anyhow::Result<()> {
        if selection
            .map(|selection| !selection.contains(&annotated.name))
            .unwrap_or_default()
        {
            return Ok(());
        }

        let role = (annotated.role.0).0;
        let negate = role == "conjecture";
        let is_goal = negate || role == "negated_conjecture";
        let source = syntax::Source::Axiom {
            path,
            name: annotated.name.to_string().into(),
        };
        let info = syntax::Info { source, is_goal };

        let mut formula = annotated.formula.load(self)?;
        self.fresh_variable = 0;
        if negate {
            formula = syntax::Fof::Not(Box::new(formula));
        }
        self.nf.process_fof(&mut self.fresh_symbol, formula, info);
        Ok(())
    }

    fn load(
        &mut self,
        parent: Option<&path::Path>,
        selection: Option<FnvHashSet<Name>>,
        path: &path::Path,
    ) -> anyhow::Result<()> {
        let display_path: Rc<str> = format!("'{}'", path.display()).into();
        let bytes = read_path(parent, path)?;
        let mut statements = TPTPIterator::<()>::new(&bytes);
        while let Some(statement) = statements.next() {
            let statement = statement.map_err(|_| {
                let start = bytes.as_ptr();
                let remaining = statements.remaining.as_ptr();
                let offset = unsafe { remaining.offset_from(start) } as usize;
                let line = bytes[0..offset].iter().filter(|b| **b == b'\n').count() + 1;
                anyhow!(
                    "syntax error in {}, detected at or after line {}",
                    display_path,
                    line
                )
            })?;
            match statement {
                TPTPInput::Annotated(annotated) => match *annotated {
                    AnnotatedFormula::Tfx(_) => {
                        bail!("typed first-order form not yet supported");
                    }
                    AnnotatedFormula::Fof(fof) => {
                        self.annotated(selection.as_ref(), display_path.clone(), fof.0)?;
                    }
                    AnnotatedFormula::Cnf(cnf) => {
                        self.annotated(selection.as_ref(), display_path.clone(), cnf.0)?;
                    }
                },
                TPTPInput::Include(include) => {
                    let Include {
                        file_name,
                        selection,
                    } = *include;
                    let included = path::Path::new((file_name.0).0);
                    let selection: Option<FnvHashSet<_>> =
                        selection.0.map(|list| list.0.into_iter().collect());
                    self.load(path.parent(), selection, included)
                        .with_context(|| format!("included '{}'", included.display(),))?;
                }
            }
        }
        Ok(())
    }

    fn finish(self) -> syntax::Matrix {
        self.nf.finish()
    }
}

trait Dialect {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Fof>;
}

impl Dialect for fof::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Fof> {
        loader.fof_formula(self)
    }
}

impl Dialect for cnf::Formula<'_> {
    fn load(self, loader: &mut Loader) -> anyhow::Result<syntax::Fof> {
        loader.cnf_formula(self)
    }
}

pub(crate) fn load(path: &path::Path) -> anyhow::Result<syntax::Matrix> {
    let mut loader = Loader {
        fresh_symbol: 2,
        ..Default::default()
    };
    loader
        .load(None, None, path)
        .with_context(|| format!("loading from '{}'...", path.display()))?;
    Ok(loader.finish())
}
