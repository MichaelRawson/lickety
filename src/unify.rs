use crate::syntax::*;
use std::rc::Rc;

fn offset_flat(flat: FlatCell, offset: usize) -> FlatCell {
    match flat {
        FlatCell::Variable(x) => FlatCell::Variable(x + offset),
        f => f,
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Offset<'a> {
    flat: Flat<'a>,
    offset: usize,
}

impl<'a> Offset<'a> {
    pub(crate) fn new(flat: Flat<'a>, offset: usize) -> Self {
        Self { flat, offset }
    }

    pub(crate) fn is_empty(self) -> bool {
        self.flat.is_empty()
    }

    pub(crate) fn head(self) -> FlatCell {
        offset_flat(self.flat.head(), self.offset)
    }

    pub(crate) fn tail(self) -> Self {
        Self {
            flat: self.flat.tail(),
            offset: self.offset,
        }
    }

    pub(crate) fn next(self) -> Self {
        Self {
            flat: self.flat.next(),
            offset: self.offset,
        }
    }

    pub(crate) fn args(self) -> impl Iterator<Item = Offset<'a>> {
        let offset = self.offset;
        self.flat.args().map(move |flat| Self { flat, offset })
    }

    pub(crate) fn iter(self) -> impl Iterator<Item = FlatCell> + 'a {
        let offset = self.offset;
        self.flat
            .into_iter()
            .map(move |flat| offset_flat(flat, offset))
    }

    pub(crate) fn trim_to_next(self) -> Self {
        Self {
            flat: self.flat.trim_to_next(),
            offset: self.offset,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct Unifier<'a> {
    bindings: Vec<Option<Offset<'a>>>,
}

impl Unifier<'static> {
    pub(crate) fn recycle<'a>(&mut self, variables: usize) -> &mut Unifier<'a> {
        self.bindings.clear();
        self.bindings.resize(variables, None);
        unsafe { std::mem::transmute(self) }
    }
}

impl<'a> Unifier<'a> {
    fn occurs(&self, x: usize, offset: Offset<'a>) -> bool {
        for flat in offset.iter() {
            if let FlatCell::Variable(y) = flat {
                if x == y {
                    return true;
                }
                if let Some(bound) = self.bindings[y] {
                    if self.occurs(x, bound) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn apply_rec(&self, out: &mut FlatBuf, offset: Offset<'a>) {
        match offset.head() {
            FlatCell::Variable(x) => {
                if let Some(bound) = self.bindings[x] {
                    self.apply_rec(out, bound);
                } else {
                    out.push(FlatCell::Variable(x));
                }
            }
            FlatCell::Symbol(f, _) => {
                let start = out.flat().len();
                out.push(FlatCell::Symbol(f, 0));
                for arg in offset.args() {
                    self.apply_rec(out, arg);
                }
                out.set_jump(start);
            }
        }
    }

    fn unify_offset(&mut self, mut left: Offset<'a>, mut right: Offset<'a>) -> bool {
        while !left.is_empty() && !right.is_empty() {
            match (left.head(), right.head()) {
                (FlatCell::Variable(x), _) => {
                    if let Some(bound) = self.bindings[x] {
                        if !self.unify_offset(bound, right) {
                            return false;
                        }
                    } else {
                        let mut term = right.trim_to_next();
                        while let FlatCell::Variable(y) = term.head() {
                            if let Some(bound) = self.bindings[y] {
                                term = bound;
                            } else {
                                break;
                            }
                        }
                        if let FlatCell::Variable(y) = term.head() {
                            if x != y {
                                self.bindings[x] = Some(term);
                            }
                        } else {
                            if self.occurs(x, term) {
                                return false;
                            }
                            self.bindings[x] = Some(term);
                        }
                    }
                    left = left.tail();
                    right = right.next();
                }
                (_, FlatCell::Variable(_)) => {
                    std::mem::swap(&mut left, &mut right);
                }
                (FlatCell::Symbol(f, _), FlatCell::Symbol(g, _)) => {
                    if f != g {
                        return false;
                    }
                    left = left.tail();
                    right = right.tail();
                }
            }
        }
        true
    }

    pub(crate) fn unify_term(&mut self, left: Flat<'a>, right: Flat<'a>, offset: usize) -> bool {
        self.unify_offset(Offset::new(left, 0), Offset::new(right, offset))
    }

    pub(crate) fn unify_literal(
        &mut self,
        left: &'a Literal,
        right: &'a Literal,
        offset: usize,
    ) -> bool {
        self.unify_term(left.atom.flat(), right.atom.flat(), offset)
    }

    pub(crate) fn apply_term(&self, flat: Flat<'a>, offset: usize) -> FlatBuf {
        let mut atom = FlatBuf::default();
        self.apply_rec(&mut atom, Offset::new(flat, offset));
        atom
    }

    pub(crate) fn apply_literal(&self, literal: &Literal, offset: usize) -> Literal {
        let polarity = literal.polarity;
        let atom = Rc::new(self.apply_term(literal.atom.flat(), offset));
        Literal { polarity, atom }
    }
}
