use crate::splitter::Splitter;
use crate::syntax::*;
use fnv::FnvHashSet;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct Builder {
    matrix: Matrix,
    splitter: Splitter,
    equality: Option<SymbolRef>,
    congruence_symbols: FnvHashSet<SymbolRef>,
}

fn build_term(out: &mut FlatBuf, term: &FofTerm) {
    match term {
        FofTerm::Variable(x) => {
            out.push(FlatCell::Variable(*x));
        }
        FofTerm::Function(f, ts) => {
            let index = out.flat().len();
            out.push(FlatCell::Symbol(*f, 0));
            for t in ts {
                build_term(out, t);
            }
            out.set_jump(index);
        }
    }
}

fn build_literal(literal: &NnfLiteral) -> Literal {
    let polarity = literal.polarity;
    let mut atom = FlatBuf::default();
    build_term(&mut atom, &literal.atom);
    let atom = Rc::new(atom);
    Literal { polarity, atom }
}

impl Builder {
    fn insert_clause(&mut self, clause: Clause, info: Info) {
        let clause_index = self.matrix.clauses.len();
        for (split_index, split) in clause.splits.iter().enumerate() {
            for (literal_index, literal) in split.literals.iter().enumerate() {
                let location = Location {
                    clause: clause_index,
                    split: split_index,
                    literal: literal_index,
                };
                self.matrix.predicates[literal.polarity as usize]
                    .get_or_insert_with(literal.index_key(), Vec::new)
                    .push(location);
            }
        }
        self.matrix.clauses.push((clause, info));
    }

    fn process_equality_clause(&mut self, variables: usize, clause: Vec<NnfLiteral>) {
        let literals = clause
            .into_iter()
            .map(|literal| build_literal(&literal))
            .collect::<Vec<_>>();
        let splits = self.splitter.split(literals, variables);
        let clause = Clause { splits };
        let info = Info {
            source: Source::Equality,
            is_goal: false,
        };
        self.insert_clause(clause, info);
    }

    fn add_equality_axioms(&mut self, equality: SymbolRef) {
        let x0 = FofTerm::Variable(0);
        let x1 = FofTerm::Variable(1);
        let x2 = FofTerm::Variable(2);
        self.process_equality_clause(
            1,
            vec![NnfLiteral {
                polarity: true,
                atom: FofTerm::Function(equality, vec![x0.clone(), x0.clone()]),
            }],
        );
        self.process_equality_clause(
            2,
            vec![
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality, vec![x0.clone(), x1.clone()]),
                },
                NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(equality, vec![x1.clone(), x0.clone()]),
                },
            ],
        );
        self.process_equality_clause(
            3,
            vec![
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality, vec![x0.clone(), x1.clone()]),
                },
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality, vec![x1.clone(), x2.clone()]),
                },
                NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(equality, vec![x0.clone(), x2.clone()]),
                },
            ],
        );

        let mut vars = vec![x0, x1, x2];
        let mut symbols = self.congruence_symbols.drain().collect::<Vec<_>>();
        symbols.sort_unstable();
        for sref in symbols {
            let arity = sref.symbol.arity;
            while vars.len() < 2 * arity {
                vars.push(FofTerm::Variable(vars.len()));
            }
            let mut literals = vec![];
            let mut left = vec![];
            let mut right = vec![];
            for i in 0..arity {
                literals.push(NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(
                        equality,
                        vec![vars[2 * i].clone(), vars[2 * i + 1].clone()],
                    ),
                });
                left.push(vars[2 * i].clone());
                right.push(vars[2 * i + 1].clone());
            }
            if sref.symbol.sort.is_boolean() {
                literals.push(NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(sref, left),
                });
                literals.push(NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(sref, right),
                });
            } else {
                literals.push(NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(
                        equality,
                        vec![
                            FofTerm::Function(sref, left),
                            FofTerm::Function(sref, right),
                        ],
                    ),
                })
            }
            self.process_equality_clause(2 * arity, literals);
        }
    }

    pub(crate) fn process_clause(&mut self, clause: Vec<NnfLiteral>, info: Info) {
        let literals = clause
            .into_iter()
            .map(|literal| build_literal(&literal))
            .collect::<Vec<_>>();
        let variables = literals
            .iter()
            .flat_map(|literal| literal.variables())
            .max()
            .map(|n| n + 1)
            .unwrap_or_default();
        let splits = self.splitter.split(literals, variables);

        let symbols = splits
            .iter()
            .flat_map(|split| &split.literals)
            .flat_map(|literal| literal.symbols());
        for sref in symbols {
            if sref.symbol.is_equality() {
                self.equality = Some(sref)
            } else if sref.symbol.arity > 0 {
                self.congruence_symbols.insert(sref);
            }
        }

        let index = self.matrix.clauses.len();
        if info.is_goal {
            self.matrix.goal_clauses.push(index);
        }

        let clause = Clause { splits };
        self.insert_clause(clause, info);
    }

    pub(crate) fn finish(mut self) -> Matrix {
        if let Some(equality) = std::mem::take(&mut self.equality) {
            self.add_equality_axioms(equality);
        }
        self.matrix
    }
}
