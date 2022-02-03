use crate::syntax::*;

#[derive(Debug, Default)]
pub(crate) struct Unifier<'a>(Vec<Option<FlatSlice<'a>>>);

impl<'a> Unifier<'a> {
    fn occurs(&self, x: usize, term: FlatSlice<'a>) -> bool {
        for flat in term {
            if let Flat::Variable(y) = flat {
                if x == *y {
                    return true;
                }
                if let Some(bound) = self.0[*y] {
                    if self.occurs(x, bound) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn apply_rec(&self, out: &mut FlatVec, term: FlatSlice) {
        match term.head() {
            Flat::Variable(x) => {
                if let Some(bound) = self.0[x] {
                    self.apply_rec(out, bound);
                } else {
                    out.push(Flat::Variable(x));
                }
            }
            Flat::Symbol(f, _) => {
                let start = out.as_slice().len();
                out.push(Flat::Symbol(f, 0));
                for arg in term.args() {
                    self.apply_rec(out, arg);
                }
                out.set_jump(start);
            }
        }
    }

    pub(crate) fn new(variables: usize) -> Self {
        Self(vec![None; variables])
    }

    pub(crate) fn unify(&mut self, mut left: FlatSlice<'a>, mut right: FlatSlice<'a>) -> bool {
        while !left.is_empty() && !right.is_empty() {
            match (left.head(), right.head()) {
                (Flat::Variable(x), _) => {
                    if let Some(bound) = self.0[x] {
                        if !self.unify(bound, right) {
                            return false;
                        }
                    } else {
                        let mut term = right.trim_to_next();
                        while let Flat::Variable(y) = term.head() {
                            if let Some(bound) = self.0[y] {
                                term = bound;
                            } else {
                                break;
                            }
                        }
                        if let Flat::Variable(y) = term.head() {
                            if x != y {
                                self.0[x] = Some(term);
                            }
                        } else {
                            if self.occurs(x, term) {
                                return false;
                            }
                            self.0[x] = Some(term);
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

    pub(crate) fn apply(&self, term: FlatSlice) -> FlatVec {
        let mut out = FlatVec::default();
        self.apply_rec(&mut out, term);
        out
    }
}
