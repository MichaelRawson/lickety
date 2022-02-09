use crate::syntax::*;
use crate::util::{Renaming, VarSet};
use std::cmp::Ordering;

#[derive(Default)]
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn clear(&mut self) {
        self.parent.clear();
    }

    fn singleton(&mut self) -> usize {
        let new = self.parent.len();
        self.parent.push(new);
        new
    }

    fn root(&mut self, start: usize) -> usize {
        let mut node = start;
        while self.parent[node] != node {
            node = self.parent[node];
        }
        self.parent[start] = node;
        node
    }

    fn merge(&mut self, left: usize, right: usize) -> usize {
        self.parent[right] = left;
        left
    }
}

fn symbol_comparison(left: &Literal, right: &Literal) -> Ordering {
    left.polarity
        .cmp(&right.polarity)
        .then_with(|| left.index_key().cmp(right.index_key()))
}

fn variable_comparison(
    left_renaming: &Renaming,
    left: &Literal,
    right_renaming: &Renaming,
    right: &Literal,
) -> Ordering {
    let left = left.variables().map(|x| left_renaming.try_rename(x));
    let right = right.variables().map(|x| right_renaming.try_rename(x));
    left.cmp(right)
}

#[derive(Default)]
struct Normaliser {
    renaming: Renaming,
    left_renaming: Renaming,
    right_renaming: Renaming,
}

impl Normaliser {
    fn compare_variants(
        &mut self,
        literals: &[Literal],
        start: usize,
        left_index: usize,
        right_index: usize,
    ) -> Ordering {
        self.left_renaming.clone_from(&self.renaming);
        for x in literals[left_index].variables() {
            self.left_renaming.rename(x);
        }
        self.right_renaming.clone_from(&self.renaming);
        for x in literals[right_index].variables() {
            self.right_renaming.rename(x);
        }
        let left_literals = (start..literals.len())
            .filter(|i| *i != left_index)
            .map(|i| &literals[i]);
        let right_literals = (start..literals.len())
            .filter(|i| *i != right_index)
            .map(|i| &literals[i]);
        for (left, right) in left_literals.zip(right_literals) {
            let result =
                variable_comparison(&self.left_renaming, left, &self.right_renaming, right);
            if result.is_ne() {
                return result;
            }
        }
        Ordering::Equal
    }

    fn normalise(&mut self, mut literals: Vec<Literal>) -> Split {
        literals.sort_unstable_by(symbol_comparison);
        literals.dedup();

        let mut current = 0;
        while current < literals.len() {
            let mut symbols = current + 1;
            while symbols != literals.len()
                && symbol_comparison(&literals[current], &literals[symbols]).is_eq()
            {
                symbols += 1;
            }
            while current < symbols {
                literals[current..symbols].sort_unstable_by(|left, right| {
                    variable_comparison(&self.renaming, left, &self.renaming, right)
                });

                let mut vars = current + 1;
                while vars < symbols
                    && variable_comparison(
                        &self.renaming,
                        &literals[current],
                        &self.renaming,
                        &literals[vars],
                    )
                    .is_eq()
                {
                    vars += 1;
                }
                let minimum = (current..vars)
                    .into_iter()
                    .min_by(|l, r| self.compare_variants(&literals, current, *l, *r))
                    .unwrap();
                literals.swap(current, minimum);

                literals[current].rename(&mut self.renaming);
                current += 1;
            }
        }

        literals.dedup();
        let variables = self.renaming.len();
        self.renaming.clear();

        Split {
            variables,
            literals,
        }
    }
}

#[derive(Default)]
pub(crate) struct Splitter {
    first_occurs: Vec<usize>,
    uf: UnionFind,
    variables: VarSet,
    splits: Vec<Vec<Literal>>,
    normaliser: Normaliser,
}

impl Splitter {
    pub(crate) fn split(&mut self, literals: Vec<Literal>, variables: usize) -> Vec<Split> {
        if literals.is_empty() {
            return vec![];
        } else if variables == 0 {
            return literals
                .into_iter()
                .map(|literal| Split {
                    variables: 0,
                    literals: vec![literal],
                })
                .collect();
        } else if literals.len() == 1 {
            return vec![self.normaliser.normalise(literals)];
        }

        self.first_occurs.resize(variables, usize::MAX);
        for literal in &literals {
            let mut root = self.uf.singleton();

            self.variables.extend(literal.variables());
            for x in self.variables.members() {
                let occurs = self.first_occurs[x];
                if occurs != usize::MAX {
                    let other = self.uf.root(occurs);
                    root = self.uf.merge(other, root);
                } else {
                    self.first_occurs[x] = root;
                }
            }
            self.variables.clear();
        }

        for (index, literal) in literals.into_iter().enumerate() {
            let root = self.uf.root(index);
            while root >= self.splits.len() {
                self.splits.push(vec![]);
            }
            self.splits[root].push(literal);
        }

        self.first_occurs.clear();
        self.uf.clear();

        self.splits
            .drain(..)
            .filter(|split| !split.is_empty())
            .map(|split| self.normaliser.normalise(split))
            .collect()
    }
}
