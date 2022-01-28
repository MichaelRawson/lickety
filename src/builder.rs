use crate::splitter::Splitter;
use crate::syntax::*;
use crate::util::Renaming;
use fnv::FnvHashMap;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct Builder {
    matrix: Matrix,
    splitter: Splitter,
    rename: Renaming,
    equality: Option<Rc<Symbol>>,
    congruence_symbols: FnvHashMap<*const Symbol, Rc<Symbol>>,
}

impl Builder {
    fn build_term(&mut self, out: &mut FlatVec, term: &FofTerm) {
        match term {
            FofTerm::Variable(x) => {
                out.push(Flat::Variable(*x));
            }
            FofTerm::Function(f, ts) => {
                let index = out.as_slice().len();
                out.push(Flat::Symbol(f.clone(), 0));
                for t in ts {
                    self.build_term(out, t);
                }
                out.set_jump(index);
            }
        }
    }

    fn build_literal(&mut self, literal: &NnfLiteral) -> Literal {
        let polarity = literal.polarity;
        let mut atom = FlatVec::default();
        self.build_term(&mut atom, &literal.atom);
        Literal { polarity, atom }
    }

    pub(crate) fn process_clause(&mut self, clause: Vec<NnfLiteral>, info: Info) {
        let literals = clause
            .into_iter()
            .map(|literal| self.build_literal(&literal))
            .collect::<Vec<_>>();
        let variables = literals
            .iter()
            .map(|lit| lit.variable_limit())
            .max()
            .unwrap_or_default();
        let mut splits = self.splitter.split(literals, variables);
        for split in &mut splits {
            split.normalise(&mut self.rename);
        }
        let splits = splits.into_iter().map(Rc::new).collect();

        let index = self.matrix.clauses.len();
        if info.is_goal {
            self.matrix.goal_clauses.push(index);
        }

        let clause = Clause { splits };
        for symbol in clause.symbols() {
            if symbol.is_equality() {
                if self.equality.is_none() {
                    self.equality = Some(symbol.clone())
                }
            } else if symbol.arity > 0 {
                self.congruence_symbols
                    .entry(Rc::as_ptr(symbol))
                    .or_insert_with(|| symbol.clone());
            }
        }

        self.matrix.clauses.push((clause, info));
    }

    fn insert_equality_clause(&mut self, clause: Vec<NnfLiteral>, variables: usize) {
        let literals = clause
            .into_iter()
            .map(|literal| self.build_literal(&literal))
            .collect::<Vec<_>>();
        let split = Rc::new(Split {
            literals,
            variables,
        });
        let splits = vec![split];
        let clause = Clause { splits };
        let info = Info {
            source: Source::Equality,
            is_goal: false,
        };
        self.matrix.clauses.push((clause, info));
    }

    fn add_equality_axioms(&mut self, equality: Rc<Symbol>) {
        let x0 = FofTerm::Variable(0);
        let x1 = FofTerm::Variable(1);
        let x2 = FofTerm::Variable(2);
        self.insert_equality_clause(
            vec![NnfLiteral {
                polarity: true,
                atom: FofTerm::Function(equality.clone(), vec![x0.clone(), x0.clone()]),
            }],
            1,
        );
        self.insert_equality_clause(
            vec![
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality.clone(), vec![x0.clone(), x1.clone()]),
                },
                NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(equality.clone(), vec![x1.clone(), x0.clone()]),
                },
            ],
            2,
        );
        self.insert_equality_clause(
            vec![
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality.clone(), vec![x0.clone(), x1.clone()]),
                },
                NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(equality.clone(), vec![x1.clone(), x2.clone()]),
                },
                NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(equality.clone(), vec![x0.clone(), x2.clone()]),
                },
            ],
            3,
        );

        let mut vars = vec![x0, x1, x2];
        let mut symbols = std::mem::take(&mut self.congruence_symbols)
            .into_values()
            .collect::<Vec<_>>();
        symbols.sort_unstable();
        for symbol in symbols {
            let arity = symbol.arity;
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
                        equality.clone(),
                        vec![vars[2 * i].clone(), vars[2 * i + 1].clone()],
                    ),
                });
                left.push(vars[2 * i].clone());
                right.push(vars[2 * i + 1].clone());
            }
            if symbol.is_predicate() {
                literals.push(NnfLiteral {
                    polarity: false,
                    atom: FofTerm::Function(symbol.clone(), left),
                });
                literals.push(NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(symbol, right),
                });
            } else {
                literals.push(NnfLiteral {
                    polarity: true,
                    atom: FofTerm::Function(
                        equality.clone(),
                        vec![
                            FofTerm::Function(symbol.clone(), left),
                            FofTerm::Function(symbol, right),
                        ],
                    ),
                })
            }
            self.insert_equality_clause(literals, 2 * arity);
        }
    }

    pub(crate) fn finish(mut self) -> Matrix {
        if let Some(equality) = std::mem::take(&mut self.equality) {
            self.add_equality_axioms(equality);
        }
        self.matrix
    }
}
