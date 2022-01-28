use crate::syntax::*;
use crate::util::VarSet;

#[derive(Default)]
pub(crate) struct Splitter {
    first_occurrence: Vec<usize>,
    parent: Vec<usize>,
    variables: VarSet,
}

impl Splitter {
    fn root(&self, mut index: usize) -> usize {
        while self.parent[index] != index {
            index = self.parent[index];
        }
        index
    }

    pub(crate) fn split(&mut self, literals: Vec<Literal>, variables: usize) -> Vec<Split> {
        if literals.is_empty() {
            return vec![];
        } else if literals.len() == 1 {
            return vec![Split {
                literals,
                variables,
            }];
        } else if variables == 0 {
            return literals
                .into_iter()
                .map(|literal| Split {
                    literals: vec![literal],
                    variables: 0,
                })
                .collect();
        }

        self.first_occurrence.resize(variables, usize::MAX);

        for (index, literal) in literals.iter().enumerate() {
            self.parent.push(index);
            self.variables.extend(literal.variables());
            for x in self.variables.members() {
                let first_occurrence = self.first_occurrence[x];
                if first_occurrence < index {
                    let left = self.root(first_occurrence);
                    let right = self.root(index);
                    self.parent[right] = left;
                } else {
                    self.first_occurrence[x] = index;
                }
            }
            self.variables.clear();
        }

        let mut splits = vec![];
        for _ in 0..self.parent.len() {
            splits.push(Split {
                literals: vec![],
                variables,
            });
        }
        for (index, literal) in literals.into_iter().enumerate() {
            let root = self.root(index);
            splits[root].literals.push(literal);
        }
        splits.retain(|split| !split.literals.is_empty());

        self.first_occurrence.clear();
        self.parent.clear();

        splits
    }
}
