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
            limit += 1;
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

    fn factor(
        &mut self,
        goal: &Split,
        goal_label: SATLiteral,
        goal_index: usize,
        factor_index: usize,
    ) -> Option<Vec<Split>> {
        let goal_literal = &goal.literals[goal_index];
        let factor_literal = &goal.literals[factor_index];
        // todo move to self
        let mut unifier = Unifier::new(goal.variables);
        if !unifier.unify(goal_literal, factor_literal, 0) {
            return None;
        }

        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply(literal, 0))
            .collect();

        let splits = self.splitter.split(literals, goal.variables);
        let mut deduction = vec![-goal_label];
        for split in &splits {
            let split_label = self.solver.split(split);
            self.solver.ground_split(split, split_label);
            deduction.push(split_label);
        }
        self.solver.assert(deduction);

        Some(splits)
    }

    fn resolve(
        &mut self,
        goal: &Split,
        goal_label: SATLiteral,
        goal_index: usize,
        split: &Split,
        split_label: Option<SATLiteral>,
        split_index: usize,
    ) -> Option<Vec<Split>> {
        let goal_literal = &goal.literals[goal_index];
        let split_literal = &split.literals[split_index];
        let mut unifier = Unifier::new(goal.variables + split.variables);
        if !unifier.unify(goal_literal, split_literal, goal.variables) {
            return None;
        }

        let split_label = split_label.unwrap_or_else(|| self.solver.split(split));
        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply(literal, 0))
            .chain(
                split
                    .literals
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != split_index)
                    .map(|(_, literal)| unifier.apply(literal, goal.variables)),
            )
            .collect();

        let splits = self
            .splitter
            .split(literals, goal.variables + split.variables);
        let mut deduction = vec![-goal_label, -split_label];
        for split in &splits {
            let split_label = self.solver.split(split);
            self.solver.ground_split(split, split_label);
            deduction.push(split_label);
        }
        self.solver.assert(deduction);

        Some(splits)
    }

    fn prove<'a>(
        &mut self,
        limit: usize,
        path: &'a Stack<'a, (&'a Split, SATLiteral)>,
        goal: &Split,
    ) {
        if self.solver.unsat()
            || limit < goal.literals.len()
            || goal.weight() > HARD_WEIGHT_LIMIT
            || goal.literals.len() > HARD_LITERAL_LIMIT
            || goal.is_tautology()
            || path.iter().any(|(split, _)| *split == goal)
        {
            return;
        }
        let goal_label = self.solver.split(goal);
        if !self.solver.value(goal_label)
            || path.iter().any(|(_, label)| !self.solver.value(*label))
        {
            return;
        }

        for (goal_index, goal_literal) in goal.literals.iter().enumerate() {
            let goal_literal_label = self.solver.literal(goal_literal);
            if !self.solver.value(goal_literal_label) {
                continue;
            }

            // factoring
            for factor_index in goal_index + 1..goal.literals.len() {
                let factor_literal = &goal.literals[factor_index];
                if factor_literal.polarity != goal_literal.polarity {
                    continue;
                }
                if !FlatSlice::might_unify(
                    factor_literal.atom.as_slice(),
                    goal_literal.atom.as_slice(),
                ) {
                    continue;
                }

                let splits =
                    if let Some(splits) = self.factor(goal, goal_label, goal_index, factor_index) {
                        splits
                    } else {
                        continue;
                    };

                let path = Stack::Cons((goal, goal_label), path);
                for split in splits {
                    self.prove(limit - 1, &path, &split);
                }
            }

            // ancestor resolution
            for (split, split_label) in path.iter() {
                for (split_index, split_literal) in split.literals.iter().enumerate() {
                    if split_literal.polarity == goal_literal.polarity {
                        continue;
                    }
                    if !FlatSlice::might_unify(
                        split_literal.atom.as_slice(),
                        goal_literal.atom.as_slice(),
                    ) {
                        continue;
                    }

                    let splits = if let Some(splits) = self.resolve(
                        goal,
                        goal_label,
                        goal_index,
                        split,
                        Some(*split_label),
                        split_index,
                    ) {
                        splits
                    } else {
                        continue;
                    };
                    let path = Stack::Cons((goal, goal_label), path);
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
                let clause = &self.matrix.clauses[location.clause].0;
                let split = &clause.splits[location.split];
                let split_index = location.literal;

                let splits = if let Some(splits) =
                    self.resolve(goal, goal_label, goal_index, split, None, split_index)
                {
                    splits
                } else {
                    continue;
                };

                let path = Stack::Cons((goal, goal_label), path);
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
