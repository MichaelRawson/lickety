#[derive(Default)]
pub(crate) struct Renaming(Vec<usize>);

impl Renaming {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn rename(&mut self, x: usize) -> usize {
        self.0.iter().position(|y| x == *y).unwrap_or_else(|| {
            let index = self.0.len();
            self.0.push(x);
            index
        })
    }
}

#[derive(Default, Debug)]
pub(crate) struct VarSet(Vec<bool>);

impl VarSet {
    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn insert(&mut self, x: usize) {
        if x >= self.0.len() {
            self.0.resize(x + 1, false);
        }
        self.0[x] = true;
    }

    pub(crate) fn remove(&mut self, x: usize) {
        if x >= self.0.len() {
            return;
        }
        self.0[x] = false;
    }

    pub(crate) fn members(&self) -> impl Iterator<Item = usize> + DoubleEndedIterator + '_ {
        self.0
            .iter()
            .enumerate()
            .filter(|(_, set)| **set)
            .map(|(index, _)| index)
    }
}

impl Extend<usize> for VarSet {
    fn extend<I: IntoIterator<Item = usize>>(&mut self, items: I) {
        for x in items {
            self.insert(x);
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum Stack<'a, T> {
    Nil,
    Cons(T, &'a Self),
}

impl<'a, T> Stack<'a, T> {
    pub(crate) fn iter(&'a self) -> StackIterator<'a, T> {
        StackIterator(self)
    }
}

pub(crate) struct StackIterator<'a, T>(&'a Stack<'a, T>);

impl<'a, T> Iterator for StackIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            Stack::Nil => None,
            Stack::Cons(t, next) => {
                self.0 = *next;
                Some(t)
            }
        }
    }
}
