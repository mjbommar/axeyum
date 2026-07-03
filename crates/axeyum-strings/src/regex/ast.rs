//! The regex AST over [`CharPred`] leaves (T-C.2), with **native bounded
//! loops**.
//!
//! A [`Regex`] is a symbolic regular expression over the Unicode code-point
//! alphabet whose character leaves are [`CharPred`] interval-set predicates
//! (ADR-0054). The Boolean nodes ([`Union`](Regex::Union),
//! [`Inter`](Regex::Inter), [`Comp`](Regex::Comp)) are first-class: the
//! symbolic-derivative engine pushes them through derivatives lazily by De
//! Morgan (PLDI 2021), so intersection and complement never require
//! determinization.
//!
//! ## Native bounded loops — never pre-unrolled
//!
//! [`Regex::Loop`] `{lo, hi}` is a **native construct** (Veanes, LPAR 2024). It
//! is *never* expanded into `lo..hi` copies: pre-unrolling is the
//! correctness-and-blowup defect class of the bounded encoder that ADR-0054
//! replaces. `hi = None` denotes an unbounded upper bound (`ω`, i.e. `R{lo,}`).
//! [`Regex::plus`] and [`Regex::opt`] are constructors that build a
//! [`Loop`](Regex::Loop) / [`Union`](Regex::Union), not new node kinds.
//!
//! References: Brzozowski 1964; Owens et al. JFP 2009; PLDI 2021; LPAR 2024;
//! ADR-0054.

use super::predicate::CharPred;

/// A symbolic regular expression over [`CharPred`] character leaves.
///
/// Node semantics (`L(R)` is the language of `R`; `ε` the empty string, `∅` the
/// empty language, `Σ` the alphabet):
///
/// * [`Empty`](Self::Empty) — `{ε}`.
/// * [`None`](Self::None) — `∅` (matches nothing). Written `Regex::None` to
///   avoid confusion with [`Option::None`].
/// * [`Pred`](Self::Pred) — one character satisfying the predicate.
/// * [`Concat`](Self::Concat) — concatenation `L(a)·L(b)`.
/// * [`Union`](Self::Union) — `L(a) ∪ L(b)`.
/// * [`Inter`](Self::Inter) — `L(a) ∩ L(b)`.
/// * [`Comp`](Self::Comp) — complement `Σ* \ L(a)`.
/// * [`Star`](Self::Star) — Kleene star `L(a)*`.
/// * [`Loop`](Self::Loop) — bounded repetition `R{lo,hi}` (native; see the
///   [module docs](self)).
///
/// The derived [`Ord`]/[`Hash`]/[`Eq`] are used by similarity-canonicalization
/// and the derivative closure; they are *structural*, so canonicalization
/// ([`canon`](super::derivative::canon)) is what turns similar regexes into a
/// shared representative.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Regex {
    /// The empty string `ε` (`{ε}`).
    Empty,
    /// The empty language `∅` (matches nothing). This is `Regex::None`, not
    /// [`Option::None`].
    None,
    /// A single character satisfying the predicate.
    Pred(CharPred),
    /// Concatenation `a · b`.
    Concat(Box<Regex>, Box<Regex>),
    /// Union `a | b`.
    Union(Box<Regex>, Box<Regex>),
    /// Intersection `a & b`.
    Inter(Box<Regex>, Box<Regex>),
    /// Complement `∁ a` (`Σ* \ L(a)`).
    Comp(Box<Regex>),
    /// Kleene star `a*`.
    Star(Box<Regex>),
    /// Native bounded repetition `inner{lo, hi}`; `hi = None` means unbounded.
    Loop {
        /// The repeated sub-expression.
        inner: Box<Regex>,
        /// Minimum repetition count.
        lo: u32,
        /// Maximum repetition count, or `None` for unbounded (`ω`).
        hi: Option<u32>,
    },
}

impl Regex {
    /// The empty-string regex `ε`.
    #[must_use]
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// The empty-language regex `∅`.
    #[must_use]
    pub const fn none() -> Self {
        Self::None
    }

    /// A predicate leaf. An empty predicate is left as-is here;
    /// [`canon`](super::derivative::canon) folds it to [`None`](Self::None).
    #[must_use]
    pub const fn pred(p: CharPred) -> Self {
        Self::Pred(p)
    }

    /// A single-character leaf for code point `c`.
    #[must_use]
    pub fn character(c: u32) -> Self {
        Self::Pred(CharPred::singleton(c))
    }

    /// The `re.range lo hi` leaf.
    #[must_use]
    pub fn char_range(lo: u32, hi: u32) -> Self {
        Self::Pred(CharPred::range(lo, hi))
    }

    /// The `re.allchar` leaf (any single character).
    #[must_use]
    pub fn any_char() -> Self {
        Self::Pred(CharPred::all())
    }

    /// Concatenation `a · b`.
    #[must_use]
    pub fn concat(a: Self, b: Self) -> Self {
        Self::Concat(Box::new(a), Box::new(b))
    }

    /// Union `a | b`.
    #[must_use]
    pub fn union(a: Self, b: Self) -> Self {
        Self::Union(Box::new(a), Box::new(b))
    }

    /// Intersection `a & b`.
    #[must_use]
    pub fn inter(a: Self, b: Self) -> Self {
        Self::Inter(Box::new(a), Box::new(b))
    }

    /// Complement `∁ a`.
    #[must_use]
    pub fn comp(a: Self) -> Self {
        Self::Comp(Box::new(a))
    }

    /// Kleene star `a*`.
    #[must_use]
    pub fn star(a: Self) -> Self {
        Self::Star(Box::new(a))
    }

    /// Native bounded repetition `inner{lo, hi}` (`hi = None` ⇒ unbounded).
    #[must_use]
    pub fn repeat(inner: Self, lo: u32, hi: Option<u32>) -> Self {
        Self::Loop {
            inner: Box::new(inner),
            lo,
            hi,
        }
    }

    /// `a+` — one or more, as the native loop `a{1,}` (not pre-unrolled).
    #[must_use]
    pub fn plus(a: Self) -> Self {
        Self::repeat(a, 1, None)
    }

    /// `a?` — optional, as `a{0,1}`.
    #[must_use]
    pub fn opt(a: Self) -> Self {
        Self::repeat(a, 0, Some(1))
    }

    /// The universal language `Σ*` in canonical form (`∁∅`). Used as the
    /// absorbing element of union and the identity of intersection.
    #[must_use]
    pub fn universal() -> Self {
        Self::comp(Self::None)
    }

    /// Whether this node is the canonical universal language `∁∅`.
    #[must_use]
    pub fn is_universal(&self) -> bool {
        matches!(self, Self::Comp(inner) if **inner == Self::None)
    }
}
