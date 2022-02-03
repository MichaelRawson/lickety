use crate::syntax::*;
use crate::util::VarSet;
use std::rc::Rc;

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

    pub(crate) fn split(
        &mut self,
        literals: Vec<Literal>,
        variables: usize,
    ) -> impl Iterator<Item = Rc<Split>> {
        let splits = if literals.is_empty() {
            vec![]
        } else if literals.len() == 1 {
            vec![literals]
        } else if variables == 0 {
            literals.into_iter().map(|literal| vec![literal]).collect()
        } else {
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

            let mut splits = vec![vec![]; self.parent.len()];
            for (index, literal) in literals.into_iter().enumerate() {
                let root = self.root(index);
                splits[root].push(literal);
            }
            splits.retain(|split| !split.is_empty());

            self.first_occurrence.clear();
            self.parent.clear();

            splits
        };

        splits.into_iter().map(Split::from_literals)
    }
}
