use crate::util::*;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Sort {
    Individual,
    Boolean,
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
    pub(crate) fn is_predicate(&self) -> bool {
        matches!(self.sort, Sort::Boolean)
    }

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

#[derive(Clone, Debug, PartialOrd, Ord)]
pub(crate) enum FofTerm {
    Variable(usize),
    Function(Rc<Symbol>, Vec<FofTerm>),
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

impl PartialEq for FofTerm {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Variable(x), Self::Variable(y)) => x == y,
            (Self::Function(f, ss), Self::Function(g, ts)) => Rc::ptr_eq(f, g) && ss.iter().eq(ts),
            _ => false,
        }
    }
}

impl Eq for FofTerm {}

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

#[derive(Clone, Debug, PartialOrd, Ord)]
pub(crate) enum Flat {
    Variable(usize),
    Symbol(Rc<Symbol>, usize),
}

impl Flat {
    fn jump(&self) -> usize {
        match self {
            Self::Variable(_) => 1,
            Self::Symbol(_, jump) => *jump,
        }
    }
}

impl PartialEq for Flat {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Variable(x), Self::Variable(y)) => x == y,
            (Self::Symbol(f, _), Self::Symbol(g, _)) => Rc::ptr_eq(f, g),
            _ => false,
        }
    }
}

impl Eq for Flat {}

impl Hash for Flat {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        std::mem::discriminant(self).hash(hasher);
        match self {
            Self::Variable(x) => {
                x.hash(hasher);
            }
            Self::Symbol(f, _) => {
                std::ptr::hash::<Symbol, H>(&**f, hasher);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FlatSlice<'a>(&'a [Flat]);

impl<'a> FlatSlice<'a> {
    fn variables(self) -> impl Iterator<Item = usize> + 'a {
        self.0.iter().filter_map(|flat| {
            if let Flat::Variable(x) = flat {
                Some(*x)
            } else {
                None
            }
        })
    }

    fn symbols(self) -> impl Iterator<Item = &'a Rc<Symbol>> {
        self.0.iter().filter_map(|flat| {
            if let Flat::Symbol(f, _) = flat {
                Some(f)
            } else {
                None
            }
        })
    }

    fn variable_limit(self) -> usize {
        self.variables().max().map(|n| n + 1).unwrap_or_default()
    }

    fn as_equation(self) -> Option<(&'a [Flat], &'a [Flat])> {
        let f = if let Flat::Symbol(f, _) = &self.0[0] {
            f
        } else {
            return None;
        };
        if !f.is_equality() {
            return None;
        }
        let args = &self.0[1..];
        let jump = args[0].jump();
        let left = &args[..jump];
        let right = &args[jump..];
        Some((left, right))
    }

    pub(crate) fn args(self) -> impl Iterator<Item = FlatSlice<'a>> {
        let arity = match &self.0[0] {
            Flat::Symbol(f, _) => f.arity,
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

    pub(crate) fn head(self) -> &'a Flat {
        &self.0[0]
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
                if !Rc::ptr_eq(f, g) {
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
                f.fmt(fmt)?;
                if f.arity > 0 {
                    write!(fmt, "(")?;
                    let mut term = self.tail();
                    for i in 0..f.arity {
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

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FlatVec(Vec<Flat>);

impl FlatVec {
    fn offset(&mut self, by: usize) {
        for mut flat in &mut self.0 {
            if let Flat::Variable(x) = &mut flat {
                *x += by;
            }
        }
    }

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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Literal {
    pub(crate) polarity: bool,
    pub(crate) atom: FlatVec,
}

impl Literal {
    pub(crate) fn symbols(&self) -> impl Iterator<Item = &Rc<Symbol>> {
        self.atom.as_slice().symbols()
    }

    pub(crate) fn variables(&self) -> impl Iterator<Item = usize> + '_ {
        self.atom.as_slice().variables()
    }

    pub(crate) fn variable_limit(&self) -> usize {
        self.atom.as_slice().variable_limit()
    }

    pub(crate) fn weight(&self) -> usize {
        self.atom.as_slice().len()
    }

    fn rename(&mut self, renaming: &mut Renaming) {
        self.atom.rename(renaming);
    }

    pub(crate) fn offset(&mut self, by: usize) {
        if by == 0 {
            return;
        }
        self.atom.offset(by);
    }

    fn is_equational_tautology(&self) -> bool {
        if !self.polarity {
            return false;
        }
        self.atom
            .as_slice()
            .as_equation()
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

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct Split {
    pub(crate) literals: Vec<Literal>,
    pub(crate) variables: usize,
}

impl Split {
    pub(crate) fn symbols(&self) -> impl Iterator<Item = &Rc<Symbol>> {
        self.literals.iter().flat_map(|literal| literal.symbols())
    }

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

    pub(crate) fn normalise(&mut self, renaming: &mut Renaming) {
        self.literals.sort_unstable();
        self.literals.dedup();
        renaming.clear();
        for literal in &mut self.literals {
            literal.rename(renaming);
        }
        self.variables = renaming.len();
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
    pub(crate) splits: Vec<Rc<Split>>,
}

impl Clause {
    pub(crate) fn symbols(&self) -> impl Iterator<Item = &Rc<Symbol>> {
        self.splits.iter().flat_map(|split| split.symbols())
    }
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

#[derive(Debug, Default)]
pub(crate) struct Matrix {
    pub(crate) clauses: Vec<(Clause, Info)>,
    pub(crate) goal_clauses: Vec<usize>,
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