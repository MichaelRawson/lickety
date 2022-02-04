use crate::sat::{SATLiteral, Solver};
use crate::splitter::Splitter;
use crate::syntax::*;
use crate::unify::Unifier;
use crate::util::Stack;

const HARD_LITERAL_LIMIT: usize = 100;
const HARD_WEIGHT_LIMIT: usize = 100;

struct Search<'matrix> {
    matrix: &'matrix Matrix,
    splitter: Splitter,
    solver: Solver,
}

impl<'matrix> Search<'matrix> {
    fn new(matrix: &'matrix Matrix) -> Self {
        let splitter = Splitter::default();
        let mut solver = Solver::default();
        for (clause, _) in &matrix.clauses {
            solver.assert_input_clause(clause);
        }
        Self {
            matrix,
            splitter,
            solver,
        }
    }

    fn go(&mut self) -> bool {
        for limit in 0.. {
            if self.solver.unsat() {
                return true;
            }
            if self.start(limit) {
                return true;
            }
        }
        false
    }

    fn start(&mut self, limit: usize) -> bool {
        'clauses: for index in &self.matrix.goal_clauses {
            let (clause, _) = &self.matrix.clauses[*index];
            let path = Stack::Nil;
            for split in &clause.splits {
                let sat = self.solver.split(split);
                if !self.prove(limit, &path, split, sat) {
                    continue 'clauses;
                }
            }
            return true;
        }
        false
    }

    fn prove<'a>(
        &mut self,
        limit: usize,
        path: &'a Stack<'a, &'a Split>,
        goal: &Split,
        sat: SATLiteral,
    ) -> bool {
        if limit < goal.literals.len()
            || goal.weight() > HARD_WEIGHT_LIMIT
            || goal.literals.len() > HARD_LITERAL_LIMIT
            || goal.is_tautology()
            || path.iter().any(|split| *split == goal)
        {
            return false;
        }

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

            let literals = goal.literals.iter().rev().skip(1).map(|literal| Literal {
                polarity: literal.polarity,
                atom: unifier.apply(literal.atom.as_slice()),
            });
            let path = Stack::Cons(goal, path);
            let splits = self.splitter.split(literals);
            let mut deduction = vec![-sat];

            let mut success = true;
            for split in splits {
                let sat = self.solver.split(&split);
                self.solver.ground_split(&split, sat);
                deduction.push(sat);
                if success && !self.prove(limit - 1, &path, &split, sat) {
                    success = false;
                }
            }
            self.solver.assert(deduction);
            if success {
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
                let mut unifier = Unifier::new(goal.variables + split.variables);
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
                    });
                let path = Stack::Cons(goal, path);
                let splits = self.splitter.split(literals);
                let mut success = true;
                let mut deduction = vec![-sat, -self.solver.split(split)];
                for split in splits {
                    let sat = self.solver.split(&split);
                    self.solver.ground_split(&split, sat);
                    deduction.push(sat);
                    let sat = self.solver.split(&split);
                    if success && !self.prove(limit - 1, &path, &split, sat) {
                        success = false;
                    }
                }
                self.solver.assert(deduction);
                if success {
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
            let mut unifier = Unifier::new(goal.variables + split.variables);
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
                });

            let path = Stack::Cons(goal, path);
            let mut success = true;
            let mut deduction = vec![-sat, -self.solver.split(split)];
            for split in self.splitter.split(literals) {
                let sat = self.solver.split(&split);
                self.solver.ground_split(&split, sat);
                deduction.push(sat);
                if success && !self.prove(limit - 1, &path, &split, sat) {
                    success = false;
                }
            }
            self.solver.assert(deduction);
            for other in &clause.splits {
                if std::ptr::eq(other, split) {
                    continue;
                }
                let sat = self.solver.split(other);
                self.solver.ground_split(split, sat);
                if success && !self.prove(limit - 1, &path, other, sat) {
                    success = false;
                }
            }
            if success {
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
