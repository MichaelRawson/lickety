use crate::syntax::*;
use std::rc::Rc;

#[derive(Debug, Default)]
pub(crate) struct Unifier<'a> {
    bindings: Vec<Option<Offset<'a>>>,
}

impl<'a> Unifier<'a> {
    fn occurs(&self, x: usize, offset: Offset<'a>) -> bool {
        for flat in offset.iter() {
            if let Flat::Variable(y) = flat {
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

    fn apply_rec(&self, out: &mut FlatVec, offset: Offset<'a>) {
        match offset.head() {
            Flat::Variable(x) => {
                if let Some(bound) = self.bindings[x] {
                    self.apply_rec(out, bound);
                } else {
                    out.push(Flat::Variable(x));
                }
            }
            Flat::Symbol(f, _) => {
                let start = out.as_slice().len();
                out.push(Flat::Symbol(f, 0));
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
                (Flat::Variable(x), _) => {
                    if let Some(bound) = self.bindings[x] {
                        if !self.unify_offset(bound, right) {
                            return false;
                        }
                    } else {
                        let mut term = right.trim_to_next();
                        while let Flat::Variable(y) = term.head() {
                            if let Some(bound) = self.bindings[y] {
                                term = bound;
                            } else {
                                break;
                            }
                        }
                        if let Flat::Variable(y) = term.head() {
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
                (_, Flat::Variable(_)) => {
                    std::mem::swap(&mut left, &mut right);
                }
                (Flat::Symbol(f, _), Flat::Symbol(g, _)) => {
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

    pub(crate) fn new(variables: usize) -> Self {
        Self {
            bindings: vec![None; variables],
        }
    }

    pub(crate) fn unify(&mut self, left: &'a Literal, right: &'a Literal, offset: usize) -> bool {
        self.unify_offset(
            Offset::new(left.atom.as_slice(), 0),
            Offset::new(right.atom.as_slice(), offset),
        )
    }

    pub(crate) fn apply(&self, literal: &Literal, offset: usize) -> Literal {
        let polarity = literal.polarity;
        let mut atom = FlatVec::default();
        self.apply_rec(&mut atom, Offset::new(literal.atom.as_slice(), offset));
        let atom = Rc::new(atom);
        Literal { polarity, atom }
    }
}
