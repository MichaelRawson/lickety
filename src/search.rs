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
        let mut limit = 1;
        loop {
            if self.solver.unsat() {
                return true;
            }
            self.start(limit);
            if !self.solver.new_clauses {
                limit += 1;
            } else if limit > 1 {
                limit -= 1
            }
            self.solver.new_clauses = false;
        }
    }

    fn start(&mut self, limit: usize) {
        for index in &self.matrix.goal_clauses {
            let (clause, _) = &self.matrix.clauses[*index];
            let path = Stack::Nil;
            for split in &clause.splits {
                self.prove(limit, &path, split);
            }
        }
    }

    fn prove<'a>(
        &mut self,
        limit: usize,
        path: &'a Stack<'a, (&'a Split, SATLiteral)>,
        goal: &Split,
    ) {
        if self.solver.unsat() {
            return;
        }
        if limit < goal.literals.len()
            || goal.weight() > HARD_WEIGHT_LIMIT
            || goal.literals.len() > HARD_LITERAL_LIMIT
            || goal.is_tautology()
            || path.iter().any(|(split, _)| *split == goal)
        {
            return;
        }
        let sat = self.solver.split(goal);
        if !self.solver.value(sat) {
            return;
        }
        if path.iter().any(|(_, sat)| !self.solver.value(*sat)) {
            return;
        }

        for goal_literal in &goal.literals {
            let sat_literal = self.solver.literal(goal_literal);
            if !self.solver.value(sat_literal) {
                continue;
            }

            // factoring
            for literal in goal
                .literals
                .iter()
                .filter(|literal| !std::ptr::eq(goal_literal, *literal))
            {
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
                    .filter(|other| !std::ptr::eq(goal_literal, *other))
                    .map(|literal| Literal {
                        polarity: literal.polarity,
                        atom: unifier.apply(literal.atom.as_slice()),
                    });

                let splits = self.splitter.split(literals);
                let mut deduction = vec![-sat];
                for split in &splits {
                    let sat = self.solver.split(split);
                    self.solver.ground_split(split, sat);
                    deduction.push(sat);
                }
                self.solver.assert(deduction);

                let path = Stack::Cons((goal, sat), path);
                for split in splits {
                    self.prove(limit - 1, &path, &split);
                }
            }

            // ancestor resolution
            for (split, psat) in path.iter() {
                for literal in &split.literals {
                    if literal.polarity == goal_literal.polarity {
                        continue;
                    }
                    if !FlatSlice::might_unify(
                        literal.atom.as_slice(),
                        goal_literal.atom.as_slice(),
                    ) {
                        continue;
                    }

                    let mut offset_literal = literal.clone();
                    offset_literal.offset(goal.variables);
                    let mut unifier = Unifier::new(goal.variables + split.variables);
                    if !unifier.unify(offset_literal.atom.as_slice(), goal_literal.atom.as_slice())
                    {
                        continue;
                    }

                    let literals = goal
                        .literals
                        .iter()
                        .filter(|literal| !std::ptr::eq(goal_literal, *literal))
                        .cloned()
                        .chain(
                            split
                                .literals
                                .iter()
                                .filter(|other| !std::ptr::eq(*other, literal))
                                .map(|l| {
                                    let mut l = l.clone();
                                    l.offset(goal.variables);
                                    l
                                }),
                        )
                        .map(|literal| Literal {
                            polarity: literal.polarity,
                            atom: unifier.apply(literal.atom.as_slice()),
                        });

                    let splits = self.splitter.split(literals);
                    let mut deduction = vec![-psat, -sat];
                    for split in &splits {
                        let sat = self.solver.split(split);
                        self.solver.ground_split(split, sat);
                        deduction.push(sat);
                    }
                    self.solver.assert(deduction);

                    let path = Stack::Cons((goal, sat), path);
                    for split in splits {
                        self.prove(limit - 1, &path, &split);
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

                let mut offset_literal = literal.clone();
                offset_literal.offset(goal.variables);
                let mut unifier = Unifier::new(goal.variables + split.variables);
                if !unifier.unify(offset_literal.atom.as_slice(), goal_literal.atom.as_slice()) {
                    continue;
                }

                let literals = goal
                    .literals
                    .iter()
                    .filter(|literal| !std::ptr::eq(goal_literal, *literal))
                    .cloned()
                    .chain(
                        split
                            .literals
                            .iter()
                            .filter(|other| !std::ptr::eq(*other, literal))
                            .map(|l| {
                                let mut l = l.clone();
                                l.offset(goal.variables);
                                l
                            }),
                    )
                    .map(|literal| Literal {
                        polarity: literal.polarity,
                        atom: unifier.apply(literal.atom.as_slice()),
                    });

                let splits = self.splitter.split(literals);
                let mut deduction = vec![-sat, -self.solver.split(split)];
                for split in &splits {
                    let sat = self.solver.split(split);
                    self.solver.ground_split(split, sat);
                    deduction.push(sat);
                }
                self.solver.assert(deduction);

                let path = Stack::Cons((goal, sat), path);
                for split in splits {
                    self.prove(limit - 1, &path, &split);
                }
                for other in &clause.splits {
                    if !std::ptr::eq(other, split) {
                        self.prove(limit - 1, &path, split);
                    }
                }
            }
        }
    }
}

pub(crate) fn go(matrix: &Matrix) -> bool {
    let mut search = Search::new(matrix);
    search.go()
}
