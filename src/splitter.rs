use crate::syntax::*;
use crate::util::VarSet;
use std::rc::Rc;

#[derive(Default)]
pub(crate) struct Splitter {
    first_occurrence: Vec<usize>,
    parent: Vec<usize>,
    variables: VarSet,
    splits: Vec<Vec<Literal>>
}

impl Splitter {
    fn root(&self, mut index: usize) -> usize {
        while self.parent[index] != index {
            index = self.parent[index];
        }
        index
    }

    pub(crate) fn split(&mut self, literals: Vec<Literal>, variables: usize) -> Vec<Rc<Split>> {
        if literals.is_empty() {
            return vec![];
        } else if literals.len() == 1 {
            return vec![Split::from_literals(literals)];
        } else if variables == 0 {
            return literals
                .into_iter()
                .map(|literal| {
                    Rc::new(Split {
                        variables: 0,
                        literals: vec![literal],
                    })
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

        self.splits.resize_with(self.parent.len(), Default::default);
        for (index, literal) in literals.into_iter().enumerate() {
            let root = self.root(index);
            self.splits[root].push(literal);
        }
        self.splits.retain(|split| !split.is_empty());

        self.first_occurrence.clear();
        self.parent.clear();

        self.splits.drain(..).map(Split::from_literals).collect()
    }
}
