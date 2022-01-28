use crate::splitter::Splitter;
use crate::syntax::*;
use crate::unify::Unifier;
use crate::util::{Renaming, Stack};
use std::rc::Rc;

const HARD_LITERAL_LIMIT: usize = 100;
const HARD_WEIGHT_LIMIT: usize = 100;

struct Search<'matrix> {
    matrix: &'matrix Matrix,
}

impl<'matrix> Search<'matrix> {
    fn new(matrix: &'matrix Matrix) -> Self {
        Self { matrix }
    }

    fn go(&mut self) {
        for limit in 0.. {
            if self.start(limit) {
                println!("proved");
                break;
            }
        }
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
            || path.iter().any(|split| split == goal)
        {
            return false;
        }

        //println!("{}", goal);
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
                .split(literals, goal.variables)
                .iter()
                .all(|split| self.prove(limit - 1, &path, split))
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
                    .split(literals, variables)
                    .iter()
                    .all(|split| self.prove(limit - 1, &path, split))
                {
                    return true;
                }
            }
        }

        // input resolution
        for (clause, _) in self.matrix.clauses.iter() {
            for (split_index, split) in clause.splits.iter().enumerate() {
                for (literal_index, literal) in split.literals.iter().enumerate() {
                    if literal.polarity == goal_literal.polarity {
                        continue;
                    }
                    if !FlatSlice::might_unify(
                        literal.atom.as_slice(),
                        goal_literal.atom.as_slice(),
                    ) {
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
                                .filter(|(i, _)| *i != literal_index)
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
                        .split(literals, variables)
                        .iter()
                        .all(|split| self.prove(limit - 1, &path, split))
                        && clause
                            .splits
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != split_index)
                            .map(|(_, l)| l)
                            .all(|split| self.prove(limit - 1, &path, split))
                    {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn split(&mut self, literals: Vec<Literal>, variables: usize) -> Vec<Rc<Split>> {
        let mut splitter = Splitter::default();
        let mut splits = splitter.split(literals, variables);
        let mut renaming = Renaming::default();
        for split in &mut splits {
            split.normalise(&mut renaming);
        }
        splits.into_iter().map(Rc::new).collect()
    }

    /*
    fn possible_rules(&self, matrix: &Matrix) -> Vec<Rule> {
        let mut result = vec![];

        let goal = self.path.last().expect("no goal");
        let goal_literal = goal.literals.last().expect("no goal literal");

        result
    }

    fn compute_splits(&self, matrix: &Matrix, rule: Rule) -> Vec<Arc<Split>> {
        match rule {
            Rule::InputResolution {
                clause,
                split,
                literal,
            } => {
                let goal = self.path.last().expect("no goal");
                let clause = &matrix.clauses[clause].0;
                let mut clause = clause.splits.clone();
                let goal_literal = goal.literals.last().expect("no goal literal");
                let mut split = clause.remove(split);
                let split = Arc::make_mut(&mut split);
                split.offset(goal.variables);
                let literal = split.literals.remove(literal);

                let variables = goal.variables + split.variables;
                let mut unifier = Unifier::new(variables);
                unifier.unify_fast(literal.atom.as_slice(), goal_literal.atom.as_slice());
                let literals = goal.literals[..goal.literals.len() - 1]
                    .iter()
                    .chain(split.literals.iter())
                    .map(|literal| Literal {
                        polarity: literal.polarity,
                        atom: unifier.apply(literal.atom.as_slice()),
                    })
                    .collect();
                let mut splitter = Splitter::default();
                let mut splits = splitter.split(literals, variables);
                let mut renaming = Renaming::default();
                for split in &mut splits {
                    split.normalise(&mut renaming);
                }
                clause.extend(splits.into_iter().map(Arc::new));
                clause
            }
        }
    }
    */
}

pub(crate) fn go(matrix: &Matrix) {
    let mut search = Search::new(matrix);
    search.go();
}
