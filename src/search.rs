use crate::splitter::Splitter;
use crate::syntax::*;
use crate::unify::Unifier;
use crate::util::Stack;
use std::rc::Rc;

const HARD_LITERAL_LIMIT: usize = 100;
const HARD_WEIGHT_LIMIT: usize = 100;

struct Search<'matrix> {
    matrix: &'matrix Matrix,
    splitter: Splitter,
}

impl<'matrix> Search<'matrix> {
    fn new(matrix: &'matrix Matrix) -> Self {
        let splitter = Splitter::default();
        Self { matrix, splitter }
    }

    fn go(&mut self) -> bool {
        for limit in 0.. {
            if self.start(limit) {
                return true;
            }
        }
        false
    }

    fn start(&mut self, limit: usize) -> bool {
        for index in &self.matrix.goal_clauses {
            let (clause, _) = &self.matrix.clauses[*index];
            let path = Stack::Nil;
            if clause
                .splits
                .iter()
                .all(|split| self.prove(limit, &path, split))
            {
                return true;
            }
        }
        false
    }

    fn prove<'a>(
        &mut self,
        limit: usize,
        path: &'a Stack<'a, Rc<Split>>,
        goal: &Rc<Split>,
    ) -> bool {
        if limit < goal.literals.len()
            || goal.weight() > HARD_WEIGHT_LIMIT
            || goal.literals.len() > HARD_LITERAL_LIMIT
            || goal.is_tautology()
            || path.iter().any(|split| split.hash == goal.hash)
        {
            return false;
        }

        //println!("{}", goal.hash);
        let goal_literal = goal.literals.last().expect("no goal literal");

        // factoring
        for literal in goal.literals.iter().rev().skip(1) {
            if literal.polarity != goal_literal.polarity {
                continue;
            }
            if !FlatSlice::might_unify(literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                continue;
            }
            let mut unifier = Unifier::new(goal.variables);
            if !unifier.unify(literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                continue;
            }

            let literals = goal
                .literals
                .iter()
                .rev()
                .skip(1)
                .map(|literal| Literal {
                    polarity: literal.polarity,
                    atom: unifier.apply(literal.atom.as_slice()),
                })
                .collect();
            let path = Stack::Cons(goal.clone(), path);
            if self
                .splitter
                .split(literals, goal.variables)
                .all(|split| self.prove(limit - 1, &path, &split))
            {
                return true;
            }
        }

        // ancestor resolution
        for split in path.iter() {
            for (index, literal) in split.literals.iter().enumerate() {
                if literal.polarity == goal_literal.polarity {
                    continue;
                }
                if !FlatSlice::might_unify(literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                    continue;
                }

                let mut literal = literal.clone();
                literal.offset(goal.variables);
                let variables = goal.variables + split.variables;
                let mut unifier = Unifier::new(variables);
                if !unifier.unify(literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                    continue;
                }

                let literals = goal
                    .literals
                    .iter()
                    .rev()
                    .skip(1)
                    .cloned()
                    .chain(
                        split
                            .literals
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != index)
                            .map(|(_, l)| {
                                let mut l = l.clone();
                                l.offset(goal.variables);
                                l
                            }),
                    )
                    .map(|literal| Literal {
                        polarity: literal.polarity,
                        atom: unifier.apply(literal.atom.as_slice()),
                    })
                    .collect();
                let path = Stack::Cons(goal.clone(), path);
                if self
                    .splitter
                    .split(literals, variables)
                    .all(|split| self.prove(limit - 1, &path, &split))
                {
                    return true;
                }
            }
        }

        // input resolution
        for location in self.matrix.index[!goal_literal.polarity as usize]
            .query(goal_literal.index_key(), true, true)
            .flatten()
        {
            let (clause, _) = &self.matrix.clauses[location.clause];
            let split = &clause.splits[location.split];
            let literal = &split.literals[location.literal];

            let mut literal = literal.clone();
            literal.offset(goal.variables);
            let variables = goal.variables + split.variables;
            let mut unifier = Unifier::new(variables);
            if !unifier.unify(literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                continue;
            }

            let literals = goal
                .literals
                .iter()
                .rev()
                .skip(1)
                .cloned()
                .chain(
                    split
                        .literals
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != location.literal)
                        .map(|(_, l)| {
                            let mut l = l.clone();
                            l.offset(goal.variables);
                            l
                        }),
                )
                .map(|literal| Literal {
                    polarity: literal.polarity,
                    atom: unifier.apply(literal.atom.as_slice()),
                })
                .collect();

            let path = Stack::Cons(goal.clone(), path);
            if self
                .splitter
                .split(literals, variables)
                .all(|split| self.prove(limit - 1, &path, &split))
                && clause
                    .splits
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != location.split)
                    .map(|(_, l)| l)
                    .all(|split| self.prove(limit - 1, &path, split))
            {
                return true;
            }
        }

        false
    }
}

pub(crate) fn go(matrix: &Matrix) -> bool {
    let mut search = Search::new(matrix);
    search.go()
}
