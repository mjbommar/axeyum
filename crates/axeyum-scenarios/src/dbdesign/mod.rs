//! Relational **database design** as a decision problem with small,
//! replayable certificates.
//!
//! The classical questions a schema designer asks — *does my dependency set
//! force this dependency?*, *is this a candidate key?*, *is this schema in
//! BCNF?*, *does this decomposition lose information?*, *is this query
//! redundant given that one?* — are all logical implication problems over
//! finite structures. Every one of them has a certificate that is far smaller
//! and far dumber than the algorithm that finds it:
//!
//! | question | positive certificate | negative certificate |
//! |---|---|---|
//! | `F ⊨ X → Y` | an **Armstrong derivation** (reflexivity / augmentation / transitivity) | a **two-tuple relation** satisfying `F` and violating `X → Y` |
//! | `X` is a superkey | the derivation of `X → R` | a two-tuple relation whose tuples agree on `X` |
//! | `R` is in BCNF | one derivation per dependency in `F` | a violating dependency **plus** the two-tuple relation for it |
//! | `R₁ ⋈ R₂ ⋈ …` is lossless | a **chase trace** ending in an all-distinguished row | the final tableau, read as a relation, with a **spurious tuple** |
//! | `Q₁ ⊆ Q₂` | a **homomorphism** `Q₂ → freeze(Q₁)` (Chandra–Merlin) | `freeze(Q₁)` itself, on which `Q₂` misses the frozen head |
//!
//! That table is this project's identity sentence written in relational
//! algebra: *untrusted fast search, trusted small checking*. Finding a
//! homomorphism is NP-complete; checking one is a nested loop over the atoms.
//!
//! # What is trusted, and what is not
//!
//! Nothing in this module asks you to believe its search. Every function that
//! *finds* something returns a certificate, and every certificate has a
//! `check_*` function that re-derives the claim from the certificate alone,
//! sharing no code with the finder:
//!
//! * [`armstrong::check_derivation`] implements exactly the three Armstrong
//!   axioms and the citation of a given dependency. It does not know that
//!   attribute closure exists.
//! * [`armstrong::check_two_tuple_witness`] evaluates dependencies against two
//!   concrete rows. It does not know that closure exists either.
//! * [`decomposition::check_chase_trace`] replays equations onto a freshly
//!   built tableau, checking each one is licensed by a dependency in `F`.
//! * [`cq::check_homomorphism`] applies a map to atoms and looks them up.
//!
//! The [`encode`] module turns the same questions into Boolean [`axeyum_ir`]
//! terms, so the solver decides them independently of the combinatorial
//! routines here — and when the solver answers `sat`, its **model is the
//! certificate**: the set of attributes it makes true is an agreement set, and
//! the two-tuple relation built from it is checked by the same
//! evaluator-grade routine as any other witness.
//!
//! # Attribution
//!
//! None of the mathematics is ours. Armstrong's axioms and their completeness
//! are Armstrong (1974); attribute closure in linear time is Beeri and
//! Bernstein (1979); the tableau chase for lossless join is Aho, Beeri and
//! Ullman (1979); the homomorphism theorem for conjunctive queries is Chandra
//! and Merlin (1977). See `artifacts/facts/F-*.json` for the citations carried
//! with each recorded result.

pub mod armstrong;
pub mod cq;
pub mod decomposition;
pub mod encode;
pub mod normal_forms;

mod parse;

pub use parse::{Decomposition, Expectation, Instance};

use core::fmt;

/// The largest number of attributes a [`Schema`] may declare.
///
/// Attribute sets are a `u64` bitmask, which makes subset and union tests one
/// machine instruction and — the part that matters here — makes iteration
/// order a total order on attribute index rather than a hash order.
pub const MAX_ATTRIBUTES: usize = 64;

/// Anything that can go wrong building, parsing or checking a design instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DbDesignError(String);

impl DbDesignError {
    /// Wrap a message.
    pub fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }

    /// The message, borrowed.
    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for DbDesignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl core::error::Error for DbDesignError {}

/// A set of attributes, as a bitmask over attribute indices.
///
/// Bit `i` is set exactly when the attribute with index `i` in the owning
/// [`Schema`] is a member. Iteration is by ascending index, so every printed
/// set, every derivation and every certificate this module emits is
/// byte-identical across runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct AttrSet(u64);

impl AttrSet {
    /// The empty set.
    pub const EMPTY: Self = Self(0);

    /// The set containing just attribute `index`.
    ///
    /// # Panics
    ///
    /// If `index >= MAX_ATTRIBUTES`.
    pub fn singleton(index: usize) -> Self {
        assert!(index < MAX_ATTRIBUTES, "attribute index out of range");
        Self(1u64 << index)
    }

    /// The set of the first `n` attributes.
    ///
    /// # Panics
    ///
    /// If `n > MAX_ATTRIBUTES`.
    pub fn full(n: usize) -> Self {
        assert!(n <= MAX_ATTRIBUTES, "attribute count out of range");
        if n == MAX_ATTRIBUTES {
            Self(u64::MAX)
        } else {
            Self((1u64 << n) - 1)
        }
    }

    /// Build from an iterator of attribute indices.
    ///
    /// # Panics
    ///
    /// If any index is `>= MAX_ATTRIBUTES`.
    pub fn from_indices(indices: impl IntoIterator<Item = usize>) -> Self {
        let mut set = Self::EMPTY;
        for index in indices {
            set = set.with(index);
        }
        set
    }

    /// Is attribute `index` a member?
    pub fn contains(self, index: usize) -> bool {
        index < MAX_ATTRIBUTES && (self.0 >> index) & 1 == 1
    }

    /// This set with `index` added.
    ///
    /// # Panics
    ///
    /// If `index >= MAX_ATTRIBUTES`.
    #[must_use]
    pub fn with(self, index: usize) -> Self {
        assert!(index < MAX_ATTRIBUTES, "attribute index out of range");
        Self(self.0 | (1u64 << index))
    }

    /// This set with `index` removed.
    #[must_use]
    pub fn without(self, index: usize) -> Self {
        if index >= MAX_ATTRIBUTES {
            self
        } else {
            Self(self.0 & !(1u64 << index))
        }
    }

    /// Union.
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Intersection.
    #[must_use]
    pub fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Set difference `self \ other`.
    #[must_use]
    pub fn difference(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }

    /// Is `self ⊆ other`?
    pub fn is_subset_of(self, other: Self) -> bool {
        self.0 & !other.0 == 0
    }

    /// Is this the empty set?
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Cardinality.
    pub fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    /// The member indices, ascending.
    pub fn iter(self) -> impl Iterator<Item = usize> {
        let bits = self.0;
        (0..MAX_ATTRIBUTES).filter(move |index| (bits >> index) & 1 == 1)
    }

    /// The raw bitmask, for callers that want to key a map on a set.
    pub fn bits(self) -> u64 {
        self.0
    }
}

/// A functional dependency `lhs → rhs`, with the label the instance gave it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fd {
    /// The label from the instance file; carried so a certificate can *name*
    /// the dependency it used rather than citing an index into a list the
    /// reader has to count.
    pub name: String,
    /// Determinant.
    pub lhs: AttrSet,
    /// Dependent.
    pub rhs: AttrSet,
}

/// A relation schema: named attributes plus a set of functional dependencies.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Schema {
    attributes: Vec<String>,
    fds: Vec<Fd>,
}

impl Schema {
    /// A schema over the named attributes, with no dependencies yet.
    ///
    /// # Errors
    ///
    /// If there are more than [`MAX_ATTRIBUTES`] names, or a name repeats.
    pub fn new(attributes: Vec<String>) -> Result<Self, DbDesignError> {
        if attributes.len() > MAX_ATTRIBUTES {
            return Err(DbDesignError::new(format!(
                "{} attributes declared; the limit is {MAX_ATTRIBUTES}",
                attributes.len()
            )));
        }
        for (index, name) in attributes.iter().enumerate() {
            if attributes[..index].contains(name) {
                return Err(DbDesignError::new(format!(
                    "attribute `{name}` is declared twice"
                )));
            }
        }
        Ok(Self {
            attributes,
            fds: Vec::new(),
        })
    }

    /// Append a dependency.
    ///
    /// # Errors
    ///
    /// If the label repeats one already present.
    pub fn push_fd(&mut self, fd: Fd) -> Result<(), DbDesignError> {
        if self.fds.iter().any(|existing| existing.name == fd.name) {
            return Err(DbDesignError::new(format!(
                "dependency label `{}` is used twice",
                fd.name
            )));
        }
        self.fds.push(fd);
        Ok(())
    }

    /// The attribute names, in declaration order.
    pub fn attributes(&self) -> &[String] {
        &self.attributes
    }

    /// The dependency set `F`, in declaration order.
    pub fn fds(&self) -> &[Fd] {
        &self.fds
    }

    /// How many attributes the schema has.
    pub fn arity(&self) -> usize {
        self.attributes.len()
    }

    /// The set of all attributes, i.e. `R` itself.
    pub fn all(&self) -> AttrSet {
        AttrSet::full(self.attributes.len())
    }

    /// The index of a declared attribute.
    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.attributes.iter().position(|known| known == name)
    }

    /// Parse a whitespace-separated attribute list into a set.
    ///
    /// # Errors
    ///
    /// If any name is not a declared attribute.
    pub fn parse_attrs(&self, text: &str) -> Result<AttrSet, DbDesignError> {
        let mut set = AttrSet::EMPTY;
        for token in text.split([' ', '\t', ',']).filter(|t| !t.is_empty()) {
            let index = self.index_of(token).ok_or_else(|| {
                DbDesignError::new(format!("`{token}` is not a declared attribute"))
            })?;
            set = set.with(index);
        }
        Ok(set)
    }

    /// Render an attribute set as a space-separated list of names, ascending
    /// by declaration index. `{}` for the empty set.
    pub fn render(&self, set: AttrSet) -> String {
        if set.is_empty() {
            return "{}".to_owned();
        }
        let names: Vec<&str> = set
            .iter()
            .filter(|&index| index < self.attributes.len())
            .map(|index| self.attributes[index].as_str())
            .collect();
        names.join(" ")
    }

    /// The **attribute closure** `X⁺` under `F`: every attribute functionally
    /// determined by `X`.
    ///
    /// This is the standard fixpoint (Beeri and Bernstein, 1979). It is the
    /// *finder*; nothing downstream trusts it, because
    /// [`armstrong::derive`] turns its work into a derivation that
    /// [`armstrong::check_derivation`] replays under the three axioms alone.
    pub fn closure(&self, x: AttrSet) -> AttrSet {
        let mut current = x;
        loop {
            let mut grew = false;
            for fd in &self.fds {
                if fd.lhs.is_subset_of(current) && !fd.rhs.is_subset_of(current) {
                    current = current.union(fd.rhs);
                    grew = true;
                }
            }
            if !grew {
                return current;
            }
        }
    }

    /// Does `F` imply `X → Y`? Decided by closure; certified elsewhere.
    pub fn implies(&self, x: AttrSet, y: AttrSet) -> bool {
        y.is_subset_of(self.closure(x))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn abcd() -> Schema {
        let mut schema = Schema::new(
            ["A", "B", "C", "D"]
                .into_iter()
                .map(str::to_owned)
                .collect(),
        )
        .unwrap();
        schema
            .push_fd(Fd {
                name: "f1".to_owned(),
                lhs: AttrSet::from_indices([0]),
                rhs: AttrSet::from_indices([1]),
            })
            .unwrap();
        schema
            .push_fd(Fd {
                name: "f2".to_owned(),
                lhs: AttrSet::from_indices([1]),
                rhs: AttrSet::from_indices([2]),
            })
            .unwrap();
        schema
    }

    #[test]
    fn attr_set_is_a_set() {
        let s = AttrSet::from_indices([0, 3, 3, 5]);
        assert_eq!(s.len(), 3);
        assert!(s.contains(3));
        assert!(!s.contains(1));
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![0, 3, 5]);
        assert!(AttrSet::from_indices([0, 3]).is_subset_of(s));
        assert!(!s.is_subset_of(AttrSet::from_indices([0, 3])));
        assert_eq!(s.difference(AttrSet::singleton(3)).len(), 2);
        assert_eq!(AttrSet::full(4).len(), 4);
        assert!(AttrSet::EMPTY.is_empty());
    }

    #[test]
    fn closure_is_transitive() {
        let schema = abcd();
        let a = AttrSet::from_indices([0]);
        assert_eq!(schema.closure(a), AttrSet::from_indices([0, 1, 2]));
        assert!(schema.implies(a, AttrSet::from_indices([2])));
        assert!(!schema.implies(a, AttrSet::from_indices([3])));
    }

    #[test]
    fn duplicate_names_are_refused() {
        assert!(Schema::new(vec!["A".to_owned(), "A".to_owned()]).is_err());
        let mut schema = abcd();
        assert!(
            schema
                .push_fd(Fd {
                    name: "f1".to_owned(),
                    lhs: AttrSet::EMPTY,
                    rhs: AttrSet::EMPTY,
                })
                .is_err()
        );
    }

    #[test]
    fn render_and_parse_round_trip() {
        let schema = abcd();
        let set = schema.parse_attrs("A C").unwrap();
        assert_eq!(schema.render(set), "A C");
        assert!(schema.parse_attrs("Z").is_err());
        assert_eq!(schema.render(AttrSet::EMPTY), "{}");
    }
}
