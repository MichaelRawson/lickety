use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::{Rng, SeedableRng};

#[derive(Default, Debug)]
pub(crate) struct Renaming(Vec<usize>);

impl Renaming {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn clone_from(&mut self, other: &Self) {
        self.0.clear();
        self.0.extend(&other.0);
    }

    pub(crate) fn try_rename(&self, x: usize) -> Option<usize> {
        self.0.iter().position(|y| x == *y)
    }

    pub(crate) fn rename(&mut self, x: usize) -> usize {
        self.try_rename(x).unwrap_or_else(|| {
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
    pub(crate) fn empty() -> Self {
        Self::Nil
    }

    pub(crate) fn push(&'a self, top: T) -> Self {
        Self::Cons(top, self)
    }
}

impl<'a, T> IntoIterator for &'a Stack<'a, T> {
    type Item = &'a T;
    type IntoIter = StackIterator<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
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

pub(crate) struct DefaultRng(SmallRng);

impl Default for DefaultRng {
    fn default() -> Self {
        Self(SmallRng::seed_from_u64(0))
    }
}

impl DefaultRng {
    pub(crate) fn index(&mut self, max: usize) -> usize {
        self.0.gen_range(0..max)
    }

    pub(crate) fn choose<'a, T>(&mut self, slice: &'a [T]) -> Option<&'a T> {
        slice.choose(&mut self.0)
    }
}
