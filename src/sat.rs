use crate::digest::{Digest, DigestMap, DigestSet};
use crate::syntax::*;
use crate::util::DefaultRng;
use fnv::FnvHashSet;
use std::os::raw::c_int;

const SLS_ITERATIONS: usize = 1000;
const PICOSAT_UNSATISFIABLE: c_int = 20;

pub(crate) type SATLiteral = c_int;

#[repr(C)]
struct PicoSAT {
    _unused: [u8; 0],
}

#[link(name = "picosat")]
extern "C" {
    fn picosat_init() -> *mut PicoSAT;
    fn picosat_add(sat: *mut PicoSAT, literal: c_int) -> c_int;
    fn picosat_sat(sat: *mut PicoSAT, limit: c_int) -> c_int;
    fn picosat_deref(sat: *mut PicoSAT, literal: c_int) -> c_int;
    fn picosat_deref_toplevel(sat: *mut PicoSAT, literal: c_int) -> c_int;
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
        for literal in clause {
            unsafe { picosat_add(self.0, *literal) };
        }
        unsafe { picosat_add(self.0, 0) };
        //println!("{:?}", clause);
    }

    fn forced(&self, literal: SATLiteral) -> bool {
        let result = unsafe { picosat_deref_toplevel(self.0, literal) };
        result != 0
    }

    fn value(&self, literal: SATLiteral) -> bool {
        let result = unsafe { picosat_deref(self.0, literal) };
        result == 1
    }

    fn solve(&mut self) -> bool {
        let result = unsafe { picosat_sat(self.0, -1) };
        result != PICOSAT_UNSATISFIABLE
    }
}

struct Watch {
    clause: usize,
    rest: Option<Box<Watch>>,
}

struct Assignment(Vec<bool>);

impl Default for Assignment {
    fn default() -> Self {
        Self(vec![false])
    }
}

impl Assignment {
    fn extend(&mut self) {
        self.0.push(false);
    }

    fn flip(&mut self, index: usize) {
        self.0[index] = !self.0[index];
    }

    fn value(&mut self, literal: SATLiteral) -> bool {
        let polarity = literal > 0;
        let atom = literal.abs();
        self.0[atom as usize] == polarity
    }
}

struct Sls {
    cdcl: Cdcl,
    rng: DefaultRng,
    fresh: SATLiteral,
    clauses: Vec<Vec<SATLiteral>>,
    assignment: Assignment,
    forced: Vec<bool>,
    watch: Vec<Option<Box<Watch>>>,
    unsatisfied: Vec<usize>,
    candidate_literals: Vec<usize>,
    unsat: bool,
}

impl Default for Sls {
    fn default() -> Self {
        Self {
            cdcl: Cdcl::default(),
            rng: DefaultRng::default(),
            fresh: 1,
            clauses: vec![],
            assignment: Assignment::default(),
            forced: vec![false],
            watch: vec![None],
            unsatisfied: vec![],
            candidate_literals: vec![],
            unsat: false,
        }
    }
}

impl Sls {
    fn fresh(&mut self) -> SATLiteral {
        let fresh = self.fresh;
        self.fresh += 1;
        self.assignment.extend();
        self.forced.push(false);
        self.watch.push(None);
        fresh
    }

    fn flip(&mut self, index: usize) {
        self.assignment.flip(index);
        let mut watch = std::mem::take(&mut self.watch[index]);
        while let Some(boxed) = watch {
            let Watch { clause, rest } = *boxed;
            if !self.satisfy(clause) {
                self.unsatisfied.push(clause);
            }
            watch = rest;
        }
    }

    fn satisfy(&mut self, clause: usize) -> bool {
        if let Some(literal) = self.clauses[clause]
            .iter()
            .find(|literal| self.assignment.value(**literal))
            .copied()
        {
            let index = literal.abs() as usize;
            let rest = std::mem::take(&mut self.watch[index]);
            let watch = Box::new(Watch { clause, rest });
            self.watch[index] = Some(watch);
            true
        } else {
            false
        }
    }

    fn choose_unsatisfied(&mut self) -> Option<usize> {
        while !self.unsatisfied.is_empty() {
            let index = self.rng.index(self.unsatisfied.len());
            let unsatisfied = self.unsatisfied.swap_remove(index);
            if !self.satisfy(unsatisfied) {
                return Some(unsatisfied);
            }
        }
        None
    }

    fn choose_flip(&mut self, unsatisfied: usize) -> Option<usize> {
        self.candidate_literals.extend(
            self.clauses[unsatisfied]
                .iter()
                .map(|lit| lit.abs() as usize)
                .filter(|index| !self.forced[*index]),
        );
        let result = self.rng.choose(&self.candidate_literals).copied();
        self.candidate_literals.clear();
        result
    }

    fn solve(&mut self) {
        for _ in 0..SLS_ITERATIONS {
            let unsatisfied = if let Some(unsatisfied) = self.choose_unsatisfied() {
                unsatisfied
            } else {
                //println!("sls");
                return;
            };
            if let Some(index) = self.choose_flip(unsatisfied) {
                self.flip(index);
                assert!(self.satisfy(unsatisfied));
            } else {
                self.unsatisfied.push(unsatisfied);
                break;
            }
        }

        if self.unsatisfied.is_empty() {}
        if !self.cdcl.solve() {
            self.unsat = true;
            return;
        }
        //println!("cdcl");

        for literal in 1..self.fresh {
            let index = literal.abs() as usize;
            self.forced[index] = self.cdcl.forced(literal);
            if self.cdcl.value(literal) != self.assignment.value(literal) {
                self.flip(index);
            }
        }
        while let Some(unsatisfied) = self.unsatisfied.pop() {
            assert!(self.satisfy(unsatisfied));
        }
    }

    fn assert(&mut self, clause: Vec<SATLiteral>) {
        if self.unsat {
            return;
        }

        if clause.len() == 1 {
            let literal = clause[0];
            let index = literal.abs() as usize;
            self.forced[index] = true;
            if !self.value(literal) {
                self.flip(index);
            }
        }

        self.cdcl.assert(&clause);
        let index = self.clauses.len();
        self.clauses.push(clause);
        if !self.satisfy(index) {
            self.unsatisfied.push(index);
        }

        self.solve();
    }

    fn value(&mut self, literal: SATLiteral) -> bool {
        self.assignment.value(literal)
    }
}

#[derive(Default)]
pub(crate) struct Solver {
    pub(crate) new_clauses: bool,
    sls: Sls,
    atoms: DigestMap<SATLiteral>,
    splits: DigestMap<SATLiteral>,
    cache: DigestSet,
    grounded: FnvHashSet<SATLiteral>,
}

impl Solver {
    fn atom(&mut self, atom: FlatSlice) -> SATLiteral {
        let sls = &mut self.sls;
        *self
            .atoms
            .entry(atom.hash_grounded())
            .or_insert_with(|| sls.fresh())
    }

    fn literal(&mut self, literal: &Literal) -> SATLiteral {
        let mut sat = self.atom(literal.atom.as_slice());
        if !literal.polarity {
            sat = -sat;
        }
        sat
    }

    fn proper_split(&mut self, split: &Split) -> SATLiteral {
        let sls = &mut self.sls;
        let lit = *self
            .splits
            .entry(split.hash_nonground())
            .or_insert_with(|| sls.fresh());
        lit
    }

    pub(crate) fn assert(&mut self, mut clause: Vec<SATLiteral>) {
        clause.sort_unstable();
        clause.dedup();
        let mut digest = Digest::default();
        for literal in &clause {
            digest.update(*literal as isize);
        }
        if self.cache.insert(digest) {
            self.sls.assert(clause);
            self.new_clauses = true;
        }
    }

    pub(crate) fn split(&mut self, split: &Split) -> SATLiteral {
        if split.variables == 0 {
            self.literal(&split.literals[0])
        } else {
            self.proper_split(split)
        }
    }

    pub(crate) fn ground_split(&mut self, split: &Split, sat: SATLiteral) {
        if split.variables == 0 || !self.grounded.insert(sat) {
            return;
        }

        let mut sat_clause = vec![-sat];
        for literal in &split.literals {
            sat_clause.push(self.literal(literal));
        }
        self.assert(sat_clause);
    }

    pub(crate) fn assert_input_clause(&mut self, clause: &Clause) {
        let mut sat_clause = vec![];
        for split in &clause.splits {
            let sat = self.split(split);
            self.ground_split(split, sat);
            sat_clause.push(sat);
        }
        self.assert(sat_clause);
    }

    pub(crate) fn value(&mut self, sat: SATLiteral) -> bool {
        self.sls.value(sat)
    }

    pub(crate) fn unsat(&mut self) -> bool {
        self.sls.unsat
    }
}
