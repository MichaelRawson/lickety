use crate::digest::Digest;
use crate::syntax::*;
use fnv::{FnvHashMap, FnvHashSet};
use std::os::raw::c_int;

const PICOSAT_UNSATISFIABLE: c_int = 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SATLiteral(c_int);

impl std::ops::Not for SATLiteral {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(-self.0)
    }
}

#[repr(C)]
struct PicoSAT {
    _unused: [u8; 0],
}

#[link(name = "picosat")]
extern "C" {
    fn picosat_init() -> *mut PicoSAT;
    fn picosat_reset(pico: *mut PicoSAT);
    fn picosat_add(pico: *mut PicoSAT, literal: c_int) -> c_int;
    fn picosat_sat(pico: *mut PicoSAT, limit: c_int) -> c_int;
    fn picosat_deref_toplevel(pico: *mut PicoSAT, literal: c_int) -> c_int;
}

struct Cdcl {
    pico: *mut PicoSAT,
    cache: FnvHashSet<Digest>,
}

impl Default for Cdcl {
    fn default() -> Self {
        let pico = unsafe { picosat_init() };
        Self {
            pico,
            cache: FnvHashSet::default(),
        }
    }
}

impl Drop for Cdcl {
    fn drop(&mut self) {
        unsafe { picosat_reset(self.pico) }
    }
}

impl Cdcl {
    fn assert(&mut self, clause: &mut Vec<SATLiteral>) {
        clause.sort_unstable();
        clause.dedup();
        for literal in clause.iter() {
            if clause.contains(&!*literal) {
                clause.clear();
                return;
            }
        }

        let mut digest = Digest::default();
        for literal in clause.iter() {
            digest.update(literal.0 as isize);
        }
        if self.cache.insert(digest) {
            for literal in clause.iter() {
                unsafe { picosat_add(self.pico, literal.0) };
            }
            unsafe { picosat_add(self.pico, 0) };
        }
        clause.clear();
    }

    fn forced_false(&self, literal: SATLiteral) -> bool {
        let result = unsafe { picosat_deref_toplevel(self.pico, literal.0) };
        result == -1
    }

    fn solve(&mut self, limit: Option<usize>) -> bool {
        let limit = limit.map(|l| l as c_int).unwrap_or(-1);
        let result = unsafe { picosat_sat(self.pico, limit) };
        result != PICOSAT_UNSATISFIABLE
    }
}

#[derive(Default)]
pub(crate) struct Solver {
    cdcl: Cdcl,
    map: FnvHashMap<Digest, SATLiteral>,
    fresh: c_int,
    deduction: Vec<SATLiteral>,
    grounding: Vec<SATLiteral>,
}

impl Solver {
    fn atom(&mut self, polarity: bool, digest: Digest) -> (bool, SATLiteral) {
        let mut new = false;
        let mut label = *self.map.entry(digest).or_insert_with(|| {
            new = true;
            self.fresh += 1;
            SATLiteral(self.fresh as c_int)
        });
        if !polarity {
            label = !label;
        }
        (new, label)
    }

    pub(crate) fn literal_zero_vars(&mut self, literal: &Literal) -> SATLiteral {
        let digest = literal.atom.digest_zero_vars();
        let (_, label) = self.atom(literal.polarity, digest);
        label
    }

    fn ground(&mut self, split: &Split, label: SATLiteral) {
        self.grounding.push(!label);
        for literal in &split.literals {
            let literal = self.literal_zero_vars(literal);
            self.grounding.push(literal);
        }
        self.cdcl.assert(&mut self.grounding);
    }

    pub(crate) fn label(&mut self, split: &Split) -> SATLiteral {
        let (new, label) = self.atom(split.polarity, split.digest);
        if new && split.variables > 0 {
            self.ground(split, label);
        }
        label
    }

    pub(crate) fn forced_false(&self, label: SATLiteral) -> bool {
        self.cdcl.forced_false(label)
    }

    pub(crate) fn axiom(&mut self, clause: &Clause) {
        for split in &clause.splits {
            let label = self.label(split);
            self.deduction.push(label);
        }
        self.cdcl.assert(&mut self.deduction)
    }

    pub(crate) fn unary_deduction(&mut self, premise: SATLiteral, conclusions: &[Split]) {
        self.deduction.push(!premise);
        for conclusion in conclusions {
            let label = self.label(conclusion);
            self.deduction.push(label);
        }
        self.cdcl.assert(&mut self.deduction);
    }

    pub(crate) fn binary_deduction(
        &mut self,
        premise1: SATLiteral,
        premise2: SATLiteral,
        conclusions: &[Split],
    ) {
        self.deduction.push(!premise1);
        self.deduction.push(!premise2);
        for conclusion in conclusions {
            let label = self.label(conclusion);
            self.deduction.push(label);
        }
        self.cdcl.assert(&mut self.deduction);
    }

    pub(crate) fn solve(&mut self, limit: Option<usize>) -> bool {
        self.cdcl.solve(limit)
    }
}
