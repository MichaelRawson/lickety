use crate::splitter::Splitter;
use crate::syntax::*;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct Builder {
    matrix: Matrix,
    splitter: Splitter,
}

fn build_term(out: &mut FlatVec, term: &FofTerm) {
    match term {
        FofTerm::Variable(x) => {
            out.push(Flat::Variable(*x));
        }
        FofTerm::Function(f, ts) => {
            let index = out.as_slice().len();
            out.push(Flat::Symbol(*f, 0));
            for t in ts {
                build_term(out, t);
            }
            out.set_jump(index);
        }
    }
}

fn build_literal(literal: &NnfLiteral) -> Literal {
    let polarity = literal.polarity;
    let mut atom = FlatVec::default();
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
                if let Some((left, right)) = literal.as_equation() {
                    if literal.polarity {
                        self.matrix
                            .equations
                            .get_or_insert_with(left.index_key(), Vec::new)
                            .push(EqualityLocation {
                                location,
                                l2r: true,
                            });
                        self.matrix
                            .equations
                            .get_or_insert_with(right.index_key(), Vec::new)
                            .push(EqualityLocation {
                                location,
                                l2r: false,
                            });
                    }
                } else {
                    self.matrix.predicates[literal.polarity as usize]
                        .get_or_insert_with(literal.index_key(), Vec::new)
                        .push(location);
                }
                for subterm_index in literal.subterm_indices() {
                    self.matrix
                        .subterms
                        .get_or_insert_with(
                            literal.atom.as_slice().at_index(subterm_index).index_key(),
                            Vec::new,
                        )
                        .push(SubtermLocation {
                            location,
                            index: subterm_index,
                        });
                }
            }
        }
        self.matrix.clauses.push((clause, info));
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

        let index = self.matrix.clauses.len();
        if info.is_goal {
            self.matrix.goal_clauses.push(index);
        }

        let clause = Clause { splits };
        self.insert_clause(clause, info);
    }

    pub(crate) fn finish(self) -> Matrix {
        self.matrix
    }
}
