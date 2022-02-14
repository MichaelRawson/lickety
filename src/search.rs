use crate::digest::Digest;
use crate::splitter::Splitter;
use crate::syntax::*;
use crate::unify::Unifier;
use crate::util::Stack;
use fnv::FnvHashMap;

struct PathEntry<'a> {
    split: &'a Split,
}

type Path<'a> = &'a Stack<'a, PathEntry<'a>>;

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
        let mut limit = 1;
        while !self.start(limit) {
            limit += 1;
        }
        true
    }

    #[must_use]
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

    #[must_use]
    fn factor(
        &mut self,
        cache: &mut FnvHashMap<(bool, Digest), bool>,
        limit: usize,
        path: Path,
        goal: &Split,
        goal_index: usize,
        factor_index: usize,
    ) -> bool {
        let goal_literal = &goal.literals[goal_index];
        let factor_literal = &goal.literals[factor_index];
        if factor_literal.polarity != goal_literal.polarity
            || !Flat::might_unify(factor_literal.atom.flat(), goal_literal.atom.flat())
        {
            return false;
        }

        let mut unifier = Unifier::new(goal.variables);
        if !unifier.unify_literal(goal_literal, factor_literal, 0) {
            return false;
        }

        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply_literal(literal, 0))
            .collect();

        let splits = self.splitter.split(literals, goal.variables);
        self.prove_all(cache, limit, path, splits.iter())
    }

    #[must_use]
    fn resolve(
        &mut self,
        cache: &mut FnvHashMap<(bool, Digest), bool>,
        limit: usize,
        path: Path,
        goal: &Split,
        goal_index: usize,
        split: &Split,
        split_index: usize,
    ) -> bool {
        let goal_literal = &goal.literals[goal_index];
        let split_literal = &split.literals[split_index];

        let variables = goal.variables + split.variables;
        let mut unifier = Unifier::new(variables);
        if !unifier.unify_literal(goal_literal, split_literal, goal.variables) {
            return false;
        }

        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply_literal(literal, 0))
            .chain(
                split
                    .literals
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != split_index)
                    .map(|(_, literal)| unifier.apply_literal(literal, goal.variables)),
            );

        let splits = self.splitter.split(literals.collect(), variables);
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

    #[must_use]
    fn prove(&mut self, limit: usize, path: Path, goal: &Split) -> bool {
        if goal.literals.len() >= limit
            || goal.is_tautology()
            || path.into_iter().any(|entry| {
                entry.split.polarity == goal.polarity && entry.split.digest == goal.digest
            })
        {
            return false;
        }

        let entry = PathEntry { split: goal };
        let path = path.push(entry);
        let mut cache = FnvHashMap::default();

        for (goal_index, goal_literal) in goal.literals.iter().enumerate() {
            // factoring
            for factor_index in 0..goal_index {
                if self.factor(&mut cache, limit, &path, goal, goal_index, factor_index) {
                    return true;
                }
            }

            // ancestor resolution
            for entry in path.into_iter().skip(1) {
                let split = entry.split;
                for (split_index, split_literal) in split.literals.iter().enumerate() {
                    if split_literal.polarity != goal_literal.polarity
                        && Flat::might_unify(split_literal.atom.flat(), goal_literal.atom.flat())
                        && self.resolve(
                            &mut cache,
                            limit,
                            &path,
                            goal,
                            goal_index,
                            split,
                            split_index,
                        )
                    {
                        return true;
                    }
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
                    goal_index,
                    split,
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
        }

        false
    }
}

pub(crate) fn go(matrix: &Matrix) -> bool {
    let mut search = Search::new(matrix);
    search.go()
}
