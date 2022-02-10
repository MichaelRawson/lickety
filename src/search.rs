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

    fn reflexivity(
        &mut self,
        goal: &Split,
        goal_label: SATLiteral,
        goal_index: usize,
    ) -> Option<Vec<Split>> {
        let goal_literal = &goal.literals[goal_index];
        if goal_literal.polarity {
            return None;
        }
        let (left, right) = goal_literal.as_equation()?;
        if !FlatSlice::might_unify(left, right) {
            return None;
        }

        let mut unifier = Unifier::new(goal.variables);
        if !unifier.unify_term(left, right, 0) {
            return None;
        }

        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply_literal(literal, 0))
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

    fn factor(
        &mut self,
        goal: &Split,
        goal_label: SATLiteral,
        goal_index: usize,
        factor_index: usize,
    ) -> Option<Vec<Split>> {
        let goal_literal = &goal.literals[goal_index];
        let factor_literal = &goal.literals[factor_index];
        if factor_literal.polarity != goal_literal.polarity {
            return None;
        }
        if !FlatSlice::might_unify(factor_literal.atom.as_slice(), goal_literal.atom.as_slice()) {
            return None;
        }

        let mut unifier = Unifier::new(goal.variables);
        if !unifier.unify_literal(goal_literal, factor_literal, 0) {
            return None;
        }

        let literals = goal
            .literals
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != goal_index)
            .map(|(_, literal)| unifier.apply_literal(literal, 0))
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

    fn instantiate(
        &mut self,
        split: &Split,
        split_label: SATLiteral,
        unifier: &Unifier,
        offset: usize,
        variables: usize,
    ) -> Vec<Literal> {
        let literals = split
            .literals
            .iter()
            .map(|literal| unifier.apply_literal(literal, offset))
            .collect::<Vec<_>>();
        let splits = self.splitter.split(literals.clone(), variables);
        let mut deduction = vec![-split_label];
        for split in &splits {
            let label = self.solver.split(split);
            deduction.push(label);
            self.solver.ground_split(split, label);
        }
        self.solver.assert(deduction);
        literals
    }

    #[allow(clippy::too_many_arguments)]
    fn resolve(
        &mut self,
        precheck: bool,
        goal: &Split,
        goal_label: SATLiteral,
        goal_index: usize,
        split: &Split,
        split_label: SATLiteral,
        split_index: usize,
    ) -> Option<Vec<Split>> {
        let goal_literal = &goal.literals[goal_index];
        let split_literal = &split.literals[split_index];
        if precheck {
            if split_literal.polarity == goal_literal.polarity {
                return None;
            }
            if !FlatSlice::might_unify(split_literal.atom.as_slice(), goal_literal.atom.as_slice())
            {
                return None;
            }
        }

        let variables = goal.variables + split.variables;
        let mut unifier = Unifier::new(variables);
        if !unifier.unify_literal(goal_literal, split_literal, goal.variables) {
            return None;
        }

        let mut goal_literals = self.instantiate(goal, goal_label, &unifier, 0, variables);
        goal_literals.swap_remove(goal_index);

        let mut split_literals =
            self.instantiate(split, split_label, &unifier, goal.variables, variables);
        split_literals.swap_remove(split_index);

        let mut literals = goal_literals;
        literals.extend(split_literals);
        let splits = self.splitter.split(literals, variables);
        let mut deduction = vec![-goal_label, -split_label];
        for split in &splits {
            let split_label = self.solver.split(split);
            self.solver.ground_split(split, split_label);
            deduction.push(split_label);
        }
        self.solver.assert(deduction);

        Some(splits)
    }

    #[allow(clippy::too_many_arguments)]
    fn paramodulate(
        &mut self,
        precheck: bool,
        l2r: bool,
        from: &Split,
        from_label: SATLiteral,
        from_index: usize,
        into: &Split,
        into_label: SATLiteral,
        into_index: usize,
        subterm_index: usize,
    ) -> Option<Vec<Split>> {
        let from_literal = &from.literals[from_index];
        if precheck && !from_literal.polarity {
            return None;
        }
        let (mut left, mut right) = from_literal.as_equation()?;
        if !l2r {
            std::mem::swap(&mut left, &mut right);
        }

        let into_literal = &into.literals[into_index];
        let subterm = into_literal.atom.as_slice().at_index(subterm_index);

        if precheck && !FlatSlice::might_unify(left, subterm) {
            return None;
        }
        let variables = into.variables + from.variables;
        let mut unifier = Unifier::new(variables);
        if !unifier.unify_term(subterm, left, into.variables) {
            return None;
        }
        let right = unifier.apply_term(right, into.variables);

        let mut into_literals = self.instantiate(into, into_label, &unifier, 0, variables);
        let rewritten = into_literal.substitute(subterm_index, right);
        let rewritten = unifier.apply_literal(&rewritten, 0);
        into_literals[into_index] = rewritten;

        let mut from_literals =
            self.instantiate(from, from_label, &unifier, into.variables, variables);
        from_literals.swap_remove(from_index);

        let mut literals = into_literals;
        literals.extend(from_literals);
        let splits = self.splitter.split(literals, variables);
        let mut deduction = vec![-from_label, -into_label];
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
        {
            return;
        }
        let goal_label = self.solver.split(goal);
        if goal.is_tautology() {
            self.solver.assert(vec![goal_label]);
            return;
        }
        if !self.solver.value(goal_label)
            || path
                .iter()
                .any(|(_, label)| *label == goal_label || !self.solver.value(*label))
        {
            return;
        }

        for (goal_index, goal_literal) in goal.literals.iter().enumerate() {
            let goal_literal_label = self.solver.literal(goal_literal);
            if !self.solver.value(goal_literal_label) {
                continue;
            }

            // reflexivity
            if let Some(splits) = self.reflexivity(goal, goal_label, goal_index) {
                let path = Stack::Cons((goal, goal_label), path);
                for split in splits {
                    self.prove(limit - 1, &path, &split);
                }
            }

            // factoring
            for factor_index in goal_index + 1..goal.literals.len() {
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
                for split_index in 0..split.literals.len() {
                    let splits = if let Some(splits) = self.resolve(
                        true,
                        goal,
                        goal_label,
                        goal_index,
                        split,
                        *split_label,
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

            // paramodulation from ancestors into goal
            for subterm_index in goal_literal.subterm_indices() {
                for (split, split_label) in path.iter() {
                    for split_index in 0..split.literals.len() {
                        for l2r in [true, false] {
                            if let Some(splits) = self.paramodulate(
                                true,
                                l2r,
                                split,
                                *split_label,
                                split_index,
                                goal,
                                goal_label,
                                goal_index,
                                subterm_index,
                            ) {
                                let path = Stack::Cons((goal, goal_label), path);
                                for split in splits {
                                    self.prove(limit - 1, &path, &split);
                                }
                            }
                        }
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
                let split_label = self.solver.split(split);
                if !self.solver.value(split_label) {
                    continue;
                }

                let splits = if let Some(splits) = self.resolve(
                    false,
                    goal,
                    goal_label,
                    goal_index,
                    split,
                    split_label,
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
                for other in &clause.splits {
                    if !std::ptr::eq(other, split) {
                        self.prove(limit - 1, &path, split);
                    }
                }
            }

            // paramodulation from input into goal
            for subterm_index in goal_literal.subterm_indices() {
                for location in self
                    .matrix
                    .equations
                    .query(
                        goal_literal
                            .atom
                            .as_slice()
                            .at_index(subterm_index)
                            .index_key(),
                        true,
                        true,
                    )
                    .flatten()
                {
                    let l2r = location.l2r;
                    let location = location.location;
                    let clause = &self.matrix.clauses[location.clause].0;
                    let split = &clause.splits[location.split];
                    let split_index = location.literal;
                    let split_label = self.solver.split(split);
                    if !self.solver.value(split_label) {
                        continue;
                    }

                    if let Some(splits) = self.paramodulate(
                        false,
                        l2r,
                        split,
                        split_label,
                        split_index,
                        goal,
                        goal_label,
                        goal_index,
                        subterm_index,
                    ) {
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

            if !goal_literal.polarity || !goal_literal.is_equation() {
                continue;
            }

            // paramodulation from goal into ancestors
            for (split, split_label) in path.iter() {
                for (split_index, split_literal) in split.literals.iter().enumerate() {
                    for subterm_index in split_literal.subterm_indices() {
                        for l2r in [true, false] {
                            if let Some(splits) = self.paramodulate(
                                true,
                                l2r,
                                goal,
                                goal_label,
                                goal_index,
                                split,
                                *split_label,
                                split_index,
                                subterm_index,
                            ) {
                                let path = Stack::Cons((goal, goal_label), path);
                                for split in splits {
                                    self.prove(limit - 1, &path, &split);
                                }
                            }
                        }
                    }
                }
            }

            // paramodulation from goal into input
            for l2r in [true, false] {
                let (mut left, mut right) = goal_literal.as_equation().unwrap();
                if !l2r {
                    std::mem::swap(&mut left, &mut right);
                }
                for location in self
                    .matrix
                    .subterms
                    .query(left.index_key(), true, true)
                    .flatten()
                {
                    let subterm_index = location.index;
                    let location = location.location;
                    let clause = &self.matrix.clauses[location.clause].0;
                    let split = &clause.splits[location.split];
                    let split_index = location.literal;
                    let split_label = self.solver.split(split);
                    if !self.solver.value(split_label) {
                        continue;
                    }

                    if let Some(splits) = self.paramodulate(
                        false,
                        l2r,
                        goal,
                        goal_label,
                        goal_index,
                        split,
                        split_label,
                        split_index,
                        subterm_index,
                    ) {
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
    }
}

pub(crate) fn go(matrix: &Matrix) -> bool {
    let mut search = Search::new(matrix);
    search.go()
}
