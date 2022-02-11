use crate::digest::Digest;
use crate::util::{Renaming, VarSet};
use discrimination_tree::DiscriminationTree;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Sort {
    Individual,
    Boolean,
}

impl Sort {
    pub(crate) fn is_boolean(self) -> bool {
        matches!(self, Self::Boolean)
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub(crate) enum Name {
    Equality,
    Atom(String),
    Quoted(String),
    Number(String),
    Distinct(String),
    Skolem(usize),
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Equality => write!(f, "sPE"),
            Self::Atom(s) | Self::Number(s) => write!(f, "{}", s),
            Self::Quoted(quoted) => write!(f, "'{}'", quoted),
            Self::Distinct(distinct) => write!(f, "\"{}\"", distinct),
            Self::Skolem(n) => write!(f, "sK{}", n),
        }
    }
}

#[derive(Debug)]
pub(crate) struct Symbol {
    pub(crate) number: usize,
    pub(crate) arity: usize,
    pub(crate) sort: Sort,
    pub(crate) name: Name,
}

impl Symbol {
    pub(crate) fn is_equality(&self) -> bool {
        matches!(self.name, Name::Equality)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.name.fmt(fmt)
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.number == other.number
    }
}

impl Eq for Symbol {}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.number.cmp(&other.number))
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.number.cmp(&other.number)
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.number.hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord)]
pub(crate) struct SymbolRef {
    pub(crate) symbol: &'static Symbol,
}

impl SymbolRef {
    pub(crate) fn new(symbol: Symbol) -> Self {
        Self {
            symbol: Box::leak(Box::new(symbol)),
        }
    }
}

impl fmt::Display for SymbolRef {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.symbol.fmt(fmt)
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.symbol as *const Symbol, other.symbol as *const Symbol)
    }
}

impl Eq for SymbolRef {}

impl Hash for SymbolRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

impl discrimination_tree::Symbol for SymbolRef {
    fn arity(&self) -> usize {
        self.symbol.arity
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FofTerm {
    Variable(usize),
    Function(SymbolRef, Vec<FofTerm>),
}

impl FofTerm {
    fn variables<V: Extend<usize>>(&self, variables: &mut V) {
        match self {
            Self::Variable(x) => {
                variables.extend(std::iter::once(*x));
            }
            Self::Function(_, ts) => {
                for t in ts {
                    t.variables(variables);
                }
            }
        }
    }

    fn substitute(&mut self, substitute: usize, term: &Self) {
        match self {
            Self::Variable(x) => {
                if *x == substitute {
                    *self = term.clone();
                }
            }
            Self::Function(_, ts) => {
                for t in ts {
                    t.substitute(substitute, term);
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum FofAtomic {
    Boolean(bool),
    Predicate(FofTerm),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NnfLiteral {
    pub(crate) polarity: bool,
    pub(crate) atom: FofTerm,
}

impl NnfLiteral {
    fn substitute(&mut self, substitute: usize, term: &FofTerm) {
        self.atom.substitute(substitute, term);
    }

    pub(crate) fn variables<V: Extend<usize>>(&self, variables: &mut V) {
        self.atom.variables(variables);
    }
}

#[derive(Debug)]
pub(crate) enum Fof {
    Atom(FofAtomic),
    Not(Box<Fof>),
    And(Vec<Fof>),
    Or(Vec<Fof>),
    Equivalent(Box<Fof>, Box<Fof>),
    Forall(usize, Box<Fof>),
    Exists(usize, Box<Fof>),
}

#[derive(Debug)]
pub(crate) enum Nnf {
    Literal(NnfLiteral),
    And(Vec<Nnf>),
    Or(Vec<Nnf>),
    Forall(usize, Box<Nnf>),
    Exists(usize, Box<Nnf>),
}

impl Nnf {
    pub(crate) fn free_variables(&self, variables: &mut VarSet) {
        match self {
            Self::Literal(literal) => {
                literal.variables(variables);
            }
            Self::And(fs) | Self::Or(fs) => {
                for f in fs {
                    f.free_variables(variables);
                }
            }
            Self::Forall(x, f) | Self::Exists(x, f) => {
                f.free_variables(variables);
                variables.remove(*x);
            }
        }
    }

    pub(crate) fn substitute(&mut self, substitute: usize, term: &FofTerm) {
        match self {
            Self::Literal(l) => {
                l.substitute(substitute, term);
            }
            Self::And(fs) | Self::Or(fs) => {
                for f in fs {
                    f.substitute(substitute, term);
                }
            }
            Self::Forall(_, f) | Self::Exists(_, f) => {
                f.substitute(substitute, term);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Source {
    Equality,
    Axiom { path: Rc<str>, name: Rc<str> },
}

impl fmt::Display for Source {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Equality => write!(fmt, "theory(equality)"),
            Self::Axiom { path, name } => {
                write!(fmt, "file({}, {})", path, name)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Info {
    pub(crate) is_goal: bool,
    pub(crate) source: Source,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Flat {
    Variable(usize),
    Symbol(SymbolRef, usize),
}

impl Flat {
    fn jump(self) -> usize {
        match self {
            Self::Variable(_) => 1,
            Self::Symbol(_, jump) => jump,
        }
    }

    fn variable(self) -> Option<usize> {
        if let Self::Variable(x) = self {
            Some(x)
        } else {
            None
        }
    }

    fn symbol(self) -> Option<SymbolRef> {
        if let Self::Symbol(f, _) = self {
            Some(f)
        } else {
            None
        }
    }

    fn offset(self, offset: usize) -> Self {
        match self {
            Self::Variable(x) => Self::Variable(x + offset),
            f => f,
        }
    }

    fn hash_nonground(self, digest: &mut Digest) {
        match self {
            Flat::Variable(x) => {
                let code = -(x as isize);
                digest.update(code);
            }
            Flat::Symbol(f, _) => {
                let code = f.symbol.number as isize;
                digest.update(code);
            }
        }
    }

    fn hash_grounded(self, digest: &mut Digest) {
        match self {
            Flat::Variable(_) => {
                digest.update(0);
            }
            Flat::Symbol(f, _) => {
                let code = f.symbol.number as isize;
                digest.update(code);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FlatSlice<'a>(&'a [Flat]);

impl<'a> FlatSlice<'a> {
    fn variables(self) -> impl Iterator<Item = usize> + 'a {
        self.0.iter().copied().filter_map(Flat::variable)
    }

    fn symbols(self) -> impl Iterator<Item = SymbolRef> + 'a {
        self.0.iter().copied().filter_map(Flat::symbol)
    }

    pub(crate) fn index_key(self) -> impl Iterator<Item = Option<SymbolRef>> + 'a {
        self.0.iter().copied().map(Flat::symbol)
    }

    fn as_equation(self) -> Option<(Self, Self)> {
        let f = if let Flat::Symbol(f, _) = self.0[0] {
            f
        } else {
            return None;
        };
        if !f.symbol.is_equality() {
            return None;
        }
        let args = &self.0[1..];
        let jump = args[0].jump();
        let left = Self(&args[..jump]);
        let right = Self(&args[jump..]);
        Some((left, right))
    }

    fn hash_nonground(self, digest: &mut Digest) {
        for flat in self.0 {
            flat.hash_nonground(digest);
        }
    }

    pub(crate) fn hash_grounded(self) -> Digest {
        let mut digest = Digest::default();
        for flat in self.0 {
            flat.hash_grounded(&mut digest);
        }
        digest
    }

    pub(crate) fn args(self) -> impl Iterator<Item = FlatSlice<'a>> {
        let arity = match self.0[0] {
            Flat::Symbol(f, _) => f.symbol.arity,
            _ => unreachable!(),
        };
        let mut index = 1;
        (0..arity).into_iter().map(move |_| {
            let jump = self.0[index].jump();
            let arg = FlatSlice(&self.0[index..index + jump]);
            index += jump;
            arg
        })
    }

    pub(crate) fn is_empty(self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn len(self) -> usize {
        self.0.len()
    }

    pub(crate) fn head(self) -> Flat {
        self.0[0]
    }

    pub(crate) fn tail(self) -> Self {
        Self(&self.0[1..])
    }

    pub(crate) fn next(self) -> Self {
        Self(&self.0[self.head().jump()..])
    }

    pub(crate) fn trim_to_next(self) -> Self {
        Self(&self.0[..self.head().jump()])
    }

    pub(crate) fn might_unify(mut left: Self, mut right: Self) -> bool {
        while !left.is_empty() && !right.is_empty() {
            if let (Flat::Symbol(f, _), Flat::Symbol(g, _)) = (left.head(), right.head()) {
                if f != g {
                    return false;
                }
                left = left.tail();
                right = right.tail();
            } else {
                left = left.next();
                right = right.next();
            }
        }
        true
    }
}

impl<'a> IntoIterator for FlatSlice<'a> {
    type Item = &'a Flat;
    type IntoIter = std::slice::Iter<'a, Flat>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> fmt::Display for FlatSlice<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.head() {
            Flat::Variable(x) => write!(fmt, "X{}", x),
            Flat::Symbol(f, _) => {
                f.symbol.fmt(fmt)?;
                if f.symbol.arity > 0 {
                    write!(fmt, "(")?;
                    let mut term = self.tail();
                    for i in 0..f.symbol.arity {
                        if i > 0 {
                            write!(fmt, ",")?;
                        }
                        term.fmt(fmt)?;
                        term = term.next();
                    }
                    write!(fmt, ")")?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Offset<'a> {
    flat: FlatSlice<'a>,
    offset: usize,
}

impl<'a> Offset<'a> {
    pub(crate) fn new(flat: FlatSlice<'a>, offset: usize) -> Self {
        Self { flat, offset }
    }

    pub(crate) fn is_empty(self) -> bool {
        self.flat.is_empty()
    }

    pub(crate) fn head(self) -> Flat {
        self.flat.head().offset(self.offset)
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

    pub(crate) fn iter(self) -> impl Iterator<Item = Flat> + 'a {
        let offset = self.offset;
        self.flat
            .0
            .iter()
            .copied()
            .map(move |flat| flat.offset(offset))
    }

    pub(crate) fn trim_to_next(self) -> Self {
        Self {
            flat: self.flat.trim_to_next(),
            offset: self.offset,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FlatVec(Vec<Flat>);

impl FlatVec {
    fn rename(&mut self, renaming: &mut Renaming) {
        for mut flat in &mut self.0 {
            if let Flat::Variable(x) = &mut flat {
                *x = renaming.rename(*x);
            }
        }
    }

    pub(crate) fn as_slice(&self) -> FlatSlice {
        FlatSlice(&self.0)
    }

    pub(crate) fn push(&mut self, flat: Flat) {
        self.0.push(flat);
    }

    pub(crate) fn set_jump(&mut self, index: usize) {
        let end = self.0.len();
        let computed = end - index;
        match &mut self.0[index] {
            Flat::Variable(_) => {}
            Flat::Symbol(_, jump) => {
                *jump = computed;
            }
        }
    }
}

impl fmt::Display for FlatVec {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.as_slice().fmt(fmt)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Literal {
    pub(crate) polarity: bool,
    pub(crate) atom: Rc<FlatVec>,
}

impl Literal {
    pub(crate) fn variables(&self) -> impl Iterator<Item = usize> + '_ {
        self.atom.as_slice().variables()
    }

    pub(crate) fn symbols(&self) -> impl Iterator<Item = SymbolRef> + '_ {
        self.atom.as_slice().symbols()
    }

    pub(crate) fn index_key(&self) -> impl Iterator<Item = Option<SymbolRef>> + '_ {
        self.atom.as_slice().index_key()
    }

    pub(crate) fn weight(&self) -> usize {
        self.atom.as_slice().len()
    }

    pub(crate) fn rename(&mut self, renaming: &mut Renaming) {
        Rc::make_mut(&mut self.atom).rename(renaming);
    }

    fn hash_nonground(&self, digest: &mut Digest) {
        digest.update(self.polarity as isize);
        self.atom.as_slice().hash_nonground(digest);
    }

    pub(crate) fn as_equation(&self) -> Option<(FlatSlice, FlatSlice)> {
        self.atom.as_slice().as_equation()
    }

    fn is_equational_tautology(&self) -> bool {
        if !self.polarity {
            return false;
        }
        self.as_equation()
            .map(|(left, right)| left == right)
            .unwrap_or_default()
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if !self.polarity {
            write!(fmt, "~")?;
        }
        self.atom.fmt(fmt)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Split {
    pub(crate) variables: usize,
    pub(crate) literals: Vec<Literal>,
}

impl Split {
    pub(crate) fn weight(&self) -> usize {
        self.literals.iter().map(Literal::weight).sum()
    }

    pub(crate) fn is_tautology(&self) -> bool {
        let mut literals = self.literals.iter();
        while let Some(literal) = literals.next() {
            if literal.is_equational_tautology() {
                return true;
            }
            for other in literals.clone() {
                if literal.polarity != other.polarity && literal.atom == other.atom {
                    return true;
                }
            }
        }
        false
    }

    pub(crate) fn hash_nonground(&self) -> Digest {
        let mut digest = Digest::default();
        for literal in &self.literals {
            literal.hash_nonground(&mut digest);
        }
        digest
    }
}

impl fmt::Display for Split {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if self.variables > 0 {
            write!(fmt, "![")?;
            for i in 0..self.variables {
                if i > 0 {
                    write!(fmt, ",")?;
                }
                write!(fmt, "X{}", i)?;
            }
            write!(fmt, "]: ")?;
        }
        write!(fmt, "(")?;
        let mut print_sep = false;
        for literal in &self.literals {
            if print_sep {
                write!(fmt, " | ")?;
            }
            literal.fmt(fmt)?;
            print_sep = true;
        }
        write!(fmt, ")")
    }
}

#[derive(Debug)]
pub(crate) struct Clause {
    pub(crate) splits: Vec<Split>,
}

impl fmt::Display for Clause {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if self.splits.is_empty() {
            write!(fmt, "$false")
        } else {
            let mut print_sep = false;
            for split in &self.splits {
                if print_sep {
                    write!(fmt, " | ")?;
                }
                split.fmt(fmt)?;
                print_sep = true;
            }
            Ok(())
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Location {
    pub(crate) clause: usize,
    pub(crate) split: usize,
    pub(crate) literal: usize,
}

#[derive(Debug, Default)]
pub(crate) struct Matrix {
    pub(crate) clauses: Vec<(Clause, Info)>,
    pub(crate) goal_clauses: Vec<usize>,
    pub(crate) predicates: [DiscriminationTree<SymbolRef, Vec<Location>>; 2],
}

impl fmt::Display for Matrix {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for (index, (clause, info)) in self.clauses.iter().enumerate() {
            let role = if info.is_goal {
                "negated_conjecture"
            } else {
                "axiom"
            };
            write!(
                fmt,
                "fof({}, {}, {}, [{}]).",
                index, role, clause, info.source
            )?;
            if index + 1 != self.clauses.len() {
                writeln!(fmt)?;
            }
        }
        Ok(())
    }
}
