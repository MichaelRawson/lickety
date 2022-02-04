use crate::digest::{Digest, DigestMap, DigestSet};
use crate::syntax::*;
use fnv::FnvHashSet;
use std::os::raw::c_int;

const PICOSAT_UNSATISFIABLE: c_int = 20;

pub(crate) type SATLiteral = c_int;

#[repr(C)]
struct PicoSAT {
    _unused: [u8; 0],
}

#[link(name = "picosat")]
extern "C" {
    fn picosat_init() -> *mut PicoSAT;
    fn picosat_add(sat: *mut PicoSAT, lit: SATLiteral) -> c_int;
    fn picosat_sat(sat: *mut PicoSAT, limit: c_int) -> c_int;
    //fn picosat_deref(sat: *mut PicoSAT, lit: Lit) -> Lit;
    //fn picosat_deref_toplevel(sat: *mut PicoSAT, lit: Lit) -> Lit;
}

struct Cdcl(*mut PicoSAT);

impl Default for Cdcl {
    fn default() -> Self {
        let sat = unsafe { picosat_init() };
        Self(sat)
    }
}

impl Cdcl {
    fn assert(&mut self, clause: &[SATLiteral]) {
        for lit in clause {
            unsafe { picosat_add(self.0, *lit) };
        }
        unsafe { picosat_add(self.0, 0) };
        //println!("{:?}", clause);
    }

    fn unsat(&mut self) -> bool {
        let result = unsafe { picosat_sat(self.0, -1) };
        result == PICOSAT_UNSATISFIABLE
    }
}

#[derive(Default)]
pub(crate) struct Solver {
    cdcl: Cdcl,
    fresh: SATLiteral,
    atoms: DigestMap<SATLiteral>,
    splits: DigestMap<SATLiteral>,
    cache: DigestSet,
    grounded: FnvHashSet<SATLiteral>,
}

impl Solver {
    fn atom(&mut self, atom: FlatSlice) -> SATLiteral {
        let fresh = &mut self.fresh;
        *self.atoms.entry(atom.hash_grounded()).or_insert_with(|| {
            *fresh += 1;
            *fresh
        })
    }

    fn literal(&mut self, literal: &Literal) -> SATLiteral {
        let mut lit = self.atom(literal.atom.as_slice());
        if !literal.polarity {
            lit = -lit;
        }
        lit
    }

    fn proper_split(&mut self, split: &Split) -> SATLiteral {
        let fresh = &mut self.fresh;
        *self
            .splits
            .entry(split.hash_nonground())
            .or_insert_with(|| {
                *fresh += 1;
                *fresh
            })
    }

    pub(crate) fn assert(&mut self, mut clause: Vec<SATLiteral>) {
        clause.sort_unstable();
        clause.dedup();
        let mut digest = Digest::default();
        for literal in &clause {
            digest.update(*literal as u128);
        }
        if self.cache.insert(digest) {
            self.cdcl.assert(&clause);
        }
    }

    pub(crate) fn split(&mut self, split: &Split) -> SATLiteral {
        if split.variables == 0 {
            self.literal(&split.literals[0])
        } else {
            self.proper_split(split)
        }
    }

    pub(crate) fn ground_split(&mut self, split: &Split, lit: SATLiteral) {
        if split.variables == 0 || !self.grounded.insert(lit) {
            return;
        }

        let mut sat_clause = vec![-lit];
        for literal in &split.literals {
            sat_clause.push(self.literal(literal));
        }
        self.assert(sat_clause);
    }

    pub(crate) fn assert_input_clause(&mut self, clause: &Clause) {
        let mut sat_clause = vec![];
        for split in &clause.splits {
            let lit = self.split(split);
            self.ground_split(split, lit);
            sat_clause.push(lit);
        }
        self.assert(sat_clause);
    }

    pub(crate) fn unsat(&mut self) -> bool {
        self.cdcl.unsat()
    }
}
