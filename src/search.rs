use crate::digest::Digest;
use crate::sat::{SATLiteral, Solver};
use crate::splitter::Splitter;
use crate::syntax::*;
use crate::unify::Unifier;
use crate::util::Stack;
use fnv::FnvHashMap;

struct PathEntry<'a> {
    split: &'a Split,
    label: SATLiteral,
}

type Path<'a> = &'a Stack<'a, PathEntry<'a>>;

struct Search<'matrix> {
    matrix: &'matrix Matrix,
    unifier: Unifier<'static>,
    splitter: Splitter,
    solver: Solver,
}

impl<'matrix> Search<'matrix> {
    fn new(matrix: &'matrix Matrix) -> Self {
        let unifier = Unifier::default();
        let splitter = Splitter::default();
        let solver = Solver::default();
        Self {
            matrix,
            unifier,
            splitter,
            solver,
        }
    }

    fn go(&mut self) -> bool {
        let mut limit = 1;
        for (clause, _) in &self.matrix.clauses {
            self.solver.axiom(clause);
        }
        while self.solver.solve(None) && !self.start(limit) {
            limit += 1;
        }
        true
    }

    fn start(&mut self, limit: usize) -> bool {
        let mut cache = FnvHashMap::default();
        for index in &self.matrix.goal_clauses {
            let (clause, _) = &self.matrix.clauses[*index];
            let path = Stack::empty();
            if self.prove_all(&mut cache, limit, &path, &clause.splits) {
                return true;
            }
        }
        false
    }

    fn factor(
        &mut self,
        cache: &mut FnvHashMap<(bool, Digest), bool>,
        limit: usize,
        path: Path,
        goal: &Split,
        goal_label: SATLiteral,
        factor_index: usize,
    ) -> bool {
        let goal_literal = &goal.literals[0];
        let factor_literal = &goal.literals[factor_index];
        if factor_literal.polarity != goal_literal.polarity
            || !Flat::might_unify(factor_literal.atom.flat(), goal_literal.atom.flat())
        {
            return false;
        }

        let unifier = self.unifier.recycle(goal.variables);
        if !unifier.unify_literal(goal_literal, factor_literal, 0) {
            return false;
        }

        let literals = goal.literals[1..]
            .iter()
            .map(|literal| unifier.apply_literal(literal, 0))
            .collect();

        let splits = self.splitter.split(literals, goal.variables);
        let splits = if let Some(splits) = splits {
            splits
        } else {
            return false;
        };
        self.solver.unary_deduction(goal_label, &splits);
        self.prove_all(cache, limit, path, splits.iter())
    }

    fn resolve(
        &mut self,
        cache: &mut FnvHashMap<(bool, Digest), bool>,
        limit: usize,
        path: Path,
        goal: &Split,
        goal_label: SATLiteral,
        split: &Split,
        split_label: Option<SATLiteral>,
        split_index: usize,
    ) -> bool {
        let goal_literal = &goal.literals[0];
        let split_literal = &split.literals[split_index];

        let variables = goal.variables + split.variables;
        let unifier = self.unifier.recycle(variables);
        if !unifier.unify_literal(goal_literal, split_literal, goal.variables) {
            return false;
        }

        let literals = goal.literals[1..]
            .iter()
            .map(|literal| unifier.apply_literal(literal, 0))
            .chain(
                split
                    .literals
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != split_index)
                    .map(|(_, literal)| unifier.apply_literal(literal, goal.variables)),
            );

        let splits = self.splitter.split(literals.collect(), variables);
        let splits = if let Some(splits) = splits {
            splits
        } else {
            return false;
        };
        let split_label = split_label.unwrap_or_else(|| self.solver.label(split));
        self.solver
            .binary_deduction(goal_label, split_label, &splits);
        self.prove_all(cache, limit, path, splits.iter())
    }

    fn prove_all<'a, I: IntoIterator<Item = &'a Split>>(
        &mut self,
        cache: &mut FnvHashMap<(bool, Digest), bool>,
        limit: usize,
        path: Path,
        splits: I,
    ) -> bool {
        for split in splits {
            let result = *cache
                .entry((split.polarity, split.digest))
                .or_insert_with(|| self.prove(limit - 1, path, split));
            if !result {
                return false;
            }
        }
        true
    }

    fn prove(&mut self, limit: usize, path: Path, goal: &Split) -> bool {
        if goal.literals.len() >= limit {
            return false;
        }

        let goal_label = self.solver.label(goal);
        if self.solver.forced_false(goal_label) {
            return true;
        }
        if path.into_iter().any(|entry| entry.label == goal_label) {
            return false;
        }

        let goal_literal = &goal.literals[0];
        let entry = PathEntry {
            split: goal,
            label: goal_label,
        };
        let path = path.push(entry);
        let mut cache = FnvHashMap::default();

        // factoring
        for factor_index in 1..goal.literals.len() {
            if self.factor(&mut cache, limit, &path, goal, goal_label, factor_index) {
                return true;
            }
        }

        // ancestor resolution
        for entry in path.into_iter().skip(1) {
            let split = entry.split;
            let split_label = Some(entry.label);
            let split_index = 0;
            let split_literal = &split.literals[split_index];
            if split_literal.polarity != goal_literal.polarity
                && Flat::might_unify(split_literal.atom.flat(), goal_literal.atom.flat())
                && self.resolve(
                    &mut cache,
                    limit,
                    &path,
                    goal,
                    goal_label,
                    split,
                    split_label,
                    split_index,
                )
            {
                return true;
            }
        }

        // input resolution
        for location in self.matrix.predicates[!goal_literal.polarity as usize]
            .query(goal_literal.index_key(), true, true)
            .flatten()
        {
            let clause = &self.matrix.clauses[location.clause].0;
            let split = &clause.splits[location.split];
            let split_index = location.literal;

            if self.resolve(
                &mut cache,
                limit,
                &path,
                goal,
                goal_label,
                split,
                None,
                split_index,
            ) && self.prove_all(
                &mut cache,
                limit,
                &path,
                clause
                    .splits
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != location.split)
                    .map(|(_, split)| split),
            ) {
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
