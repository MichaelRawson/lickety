use crate::builder::Builder;
use crate::syntax::*;
use crate::util::VarSet;

#[derive(Default)]
pub(crate) struct NormalForm {
    builder: Builder,
    variables: VarSet,
    fresh_skolem: usize,
}

impl NormalForm {
    fn nnf(&mut self, polarity: bool, formula: &Fof) -> Nnf {
        match (polarity, formula) {
            (_, Fof::Atom(FofAtomic::Boolean(b))) => {
                if *b == polarity {
                    Nnf::And(vec![])
                } else {
                    Nnf::Or(vec![])
                }
            }
            (_, Fof::Atom(FofAtomic::Predicate(atom))) => Nnf::Literal(NnfLiteral {
                polarity,
                atom: atom.clone(),
            }),
            (_, Fof::Not(f)) => self.nnf(!polarity, f),
            (true, Fof::And(fs)) | (false, Fof::Or(fs)) => {
                Nnf::And(fs.iter().map(|f| self.nnf(polarity, f)).collect())
            }
            (true, Fof::Or(fs)) | (false, Fof::And(fs)) => {
                Nnf::Or(fs.iter().map(|f| self.nnf(polarity, f)).collect())
            }
            (_, Fof::Equivalent(l, r)) => {
                let pl = self.nnf(polarity, l);
                let nl = self.nnf(!polarity, l);
                let pr = self.nnf(polarity, r);
                let nr = self.nnf(!polarity, r);
                if polarity {
                    Nnf::And(vec![Nnf::Or(vec![nl, pr]), Nnf::Or(vec![nr, pl])])
                } else {
                    Nnf::Or(vec![Nnf::And(vec![nl, pr]), Nnf::And(vec![nr, pl])])
                }
            }
            (true, Fof::Forall(x, f)) | (false, Fof::Exists(x, f)) => {
                Nnf::Forall(*x, Box::new(self.nnf(polarity, f)))
            }
            (true, Fof::Exists(x, f)) | (false, Fof::Forall(x, f)) => {
                Nnf::Exists(*x, Box::new(self.nnf(polarity, f)))
            }
        }
    }

    fn skolemise(&mut self, fresh_symbol: &mut usize, x: usize, nnf: &mut Nnf) {
        self.variables.clear();
        nnf.free_variables(&mut self.variables);
        self.variables.remove(x);
        let args: Vec<FofTerm> = self.variables.members().map(FofTerm::Variable).collect();
        let arity = args.len();

        let number = *fresh_symbol;
        *fresh_symbol += 1;
        let name = Name::Skolem(self.fresh_skolem);
        self.fresh_skolem += 1;
        let symbol = SymbolRef::new(Symbol {
            number,
            arity,
            name,
        });
        let term = FofTerm::Function(symbol, args);
        nnf.substitute(x, &term);
    }

    fn cnf(&mut self, fresh_symbol: &mut usize, nnf: Nnf) -> Vec<Vec<NnfLiteral>> {
        let clauses = match nnf {
            Nnf::Literal(l) => vec![vec![l]],
            Nnf::And(fs) => fs
                .into_iter()
                .flat_map(|f| self.cnf(fresh_symbol, f))
                .collect(),
            Nnf::Or(fs) => {
                let mut result = vec![vec![]];
                for f in fs {
                    let cnf = self.cnf(fresh_symbol, f);
                    for c in std::mem::take(&mut result) {
                        for d in &cnf {
                            let mut clause = vec![];
                            clause.extend(c.iter().cloned());
                            clause.extend(d.iter().cloned());
                            result.push(clause);
                        }
                    }
                }
                result
            }
            Nnf::Exists(x, mut f) => {
                self.skolemise(fresh_symbol, x, &mut f);
                self.cnf(fresh_symbol, *f)
            }
            Nnf::Forall(_, f) => self.cnf(fresh_symbol, *f),
        };
        let mut result = vec![];
        'clauses: for mut clause in clauses {
            clause.sort_unstable();
            clause.dedup();
            let mut literals = clause.iter();
            while let Some(literal) = literals.next() {
                let (f, ts) = if let FofTerm::Function(f, ts) = &literal.atom {
                    (f, ts)
                } else {
                    unreachable!()
                };
                // todo abstract
                if let (Name::Equality, [s, t]) = (&f.symbol.name, ts.as_slice()) {
                    if s == t {
                        continue 'clauses;
                    }
                }
                if literals
                    .clone()
                    .any(|other| other.polarity != literal.polarity && other.atom == literal.atom)
                {
                    continue 'clauses;
                }
            }
            result.push(clause);
        }
        result
    }

    fn process_nnf(&mut self, fresh_symbol: &mut usize, nnf: Nnf, info: Info) {
        for clause in self.cnf(fresh_symbol, nnf) {
            self.builder.process_clause(clause, info.clone());
        }
    }

    pub(crate) fn process_fof(&mut self, fresh_symbol: &mut usize, formula: Fof, info: Info) {
        let nnf = self.nnf(true, &formula);
        self.process_nnf(fresh_symbol, nnf, info);
    }

    pub(crate) fn finish(self) -> Matrix {
        self.builder.finish()
    }
}
