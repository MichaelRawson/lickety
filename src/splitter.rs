use crate::syntax::*;
use crate::util::VarSet;

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

#[derive(Default)]
pub(crate) struct Splitter {
    first_occurs: Vec<usize>,
    uf: UnionFind,
    variables: VarSet,
    literals: Vec<Literal>,
    splits: Vec<Vec<Literal>>,
}

impl Splitter {
    pub(crate) fn split<I: IntoIterator<Item = Literal>>(&mut self, literals: I) -> Vec<Split> {
        for literal in literals {
            let mut root = self.uf.singleton();

            self.variables.extend(literal.variables());
            while self.variables.len() > self.first_occurs.len() {
                self.first_occurs.push(usize::MAX);
            }
            for x in self.variables.members() {
                let occurs = self.first_occurs[x];
                if occurs != usize::MAX {
                    let other = self.uf.root(occurs);
                    root = self.uf.merge(other, root);
                } else {
                    self.first_occurs[x] = root;
                }
            }
            self.literals.push(literal);
            self.variables.clear();
        }

        for (index, literal) in self.literals.drain(..).enumerate() {
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
            .map(Split::from_literals)
            .collect()
    }
}
