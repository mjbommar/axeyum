//! Symbolic character predicates over the Unicode code-point alphabet (T-C.1).
//!
//! A [`CharPred`] is a **canonical sorted set of disjoint, non-adjacent
//! inclusive ranges** of Unicode code points over the alphabet
//! `0..=`[`ALPHABET_MAX`] — the `BitVec(18)` order fixed by ADR-0051. This is
//! the leaf alphabet of the symbolic-derivative regex engine (ADR-0054,
//! PLDI 2021): the whole point of an interval-set predicate is that we never
//! enumerate the 2^18 code points, yet can still compute `∧`/`∨`/`¬`,
//! emptiness, a witness, and — crucially for keeping derivative branching
//! finite — **mintermization** (partition a finite predicate set into disjoint
//! atoms so every input predicate is a union of atoms).
//!
//! ## Canonical form is semantic identity
//!
//! The stored ranges are always **sorted ascending, pairwise disjoint, and
//! non-adjacent** (for consecutive ranges `(a,b)`, `(c,d)` we have `c > b + 1`),
//! and clamped to `0..=`[`ALPHABET_MAX`]. Every constructor and Boolean
//! operation re-establishes this form, so **structural equality
//! ([`PartialEq`]) is exactly semantic equality** of the represented code-point
//! sets. This invariant is the reason [`CharPred`] can be used directly as a
//! `Hash`/`Ord` key (e.g. to coalesce transition-regex guards) and is asserted
//! by the `regex_predicate` property tests.
//!
//! References: PLDI 2021 (Stanford/Veanes/Bjørner symbolic derivatives);
//! the SMT-LIB Unicode string theory alphabet; ADR-0051 / ADR-0054.

use std::collections::{BTreeMap, BTreeSet};

/// The largest code point in the alphabet: `0x2FFFF` (the `BitVec(18)` upper
/// bound fixed by ADR-0051). The alphabet is `0..=ALPHABET_MAX` inclusive.
pub const ALPHABET_MAX: u32 = 0x2_FFFF;

/// A canonical set of Unicode code points, stored as sorted, disjoint,
/// non-adjacent inclusive ranges over `0..=`[`ALPHABET_MAX`].
///
/// See the [module docs](self) for the canonical-form invariant (structural
/// equality is semantic equality).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CharPred {
    /// Sorted, disjoint, non-adjacent inclusive `(lo, hi)` ranges, all within
    /// `0..=`[`ALPHABET_MAX`]. The empty vector is the empty predicate (∅).
    ranges: Vec<(u32, u32)>,
}

impl CharPred {
    /// The empty predicate (matches no code point).
    #[must_use]
    pub const fn none() -> Self {
        Self { ranges: Vec::new() }
    }

    /// The full alphabet predicate (`re.allchar`): every code point
    /// `0..=`[`ALPHABET_MAX`].
    #[must_use]
    pub fn all() -> Self {
        Self {
            ranges: vec![(0, ALPHABET_MAX)],
        }
    }

    /// The singleton predicate for one code point, or [`none`](Self::none) if
    /// `c` is outside the alphabet.
    #[must_use]
    pub fn singleton(c: u32) -> Self {
        if c <= ALPHABET_MAX {
            Self {
                ranges: vec![(c, c)],
            }
        } else {
            Self::none()
        }
    }

    /// The inclusive range `lo..=hi` (`re.range`), clamped to the alphabet.
    /// Returns [`none`](Self::none) when `lo > hi` or `lo` is out of range.
    #[must_use]
    pub fn range(lo: u32, hi: u32) -> Self {
        Self::from_ranges(vec![(lo, hi)])
    }

    /// Builds a canonical predicate from arbitrary (possibly overlapping,
    /// unsorted, out-of-range) inclusive ranges by clamping, sorting, and
    /// coalescing overlapping **and adjacent** ranges.
    #[must_use]
    pub fn from_ranges(raw: Vec<(u32, u32)>) -> Self {
        let mut cleaned: Vec<(u32, u32)> = raw
            .into_iter()
            .filter_map(|(lo, hi)| {
                if lo > hi || lo > ALPHABET_MAX {
                    None
                } else {
                    Some((lo, hi.min(ALPHABET_MAX)))
                }
            })
            .collect();
        cleaned.sort_unstable();
        let mut ranges: Vec<(u32, u32)> = Vec::with_capacity(cleaned.len());
        for (lo, hi) in cleaned {
            if let Some(last) = ranges.last_mut() {
                // `last.1 + 1` never overflows: `last.1 <= ALPHABET_MAX`.
                if lo <= last.1 + 1 {
                    if hi > last.1 {
                        last.1 = hi;
                    }
                    continue;
                }
            }
            ranges.push((lo, hi));
        }
        Self { ranges }
    }

    /// The canonical ranges, sorted, disjoint, and non-adjacent.
    #[must_use]
    pub fn ranges(&self) -> &[(u32, u32)] {
        &self.ranges
    }

    /// Whether the predicate matches no code point (∅).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// Whether the predicate matches the entire alphabet (`re.allchar`).
    #[must_use]
    pub fn is_all(&self) -> bool {
        self.ranges == [(0, ALPHABET_MAX)]
    }

    /// Whether `c` satisfies the predicate.
    #[must_use]
    pub fn contains(&self, c: u32) -> bool {
        // Ranges are sorted and disjoint; binary search on the lower bounds.
        match self.ranges.binary_search_by(|&(lo, _)| lo.cmp(&c)) {
            Ok(_) => true,
            Err(0) => false,
            Err(i) => {
                let (_, hi) = self.ranges[i - 1];
                c <= hi
            }
        }
    }

    /// The least code point satisfying the predicate, or `None` when empty.
    /// A total membership decision procedure needs a concrete witness to feed
    /// the replay matcher.
    #[must_use]
    pub fn witness(&self) -> Option<u32> {
        self.ranges.first().map(|&(lo, _)| lo)
    }

    /// Intersection (`∧`): code points satisfying both predicates.
    #[must_use]
    pub fn and(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        let (mut i, mut j) = (0usize, 0usize);
        while i < self.ranges.len() && j < other.ranges.len() {
            let (a0, a1) = self.ranges[i];
            let (b0, b1) = other.ranges[j];
            let lo = a0.max(b0);
            let hi = a1.min(b1);
            if lo <= hi {
                out.push((lo, hi));
            }
            if a1 < b1 {
                i += 1;
            } else {
                j += 1;
            }
        }
        // The pieces are already sorted, disjoint, and — because the inputs are
        // non-adjacent — non-adjacent; `from_ranges` re-normalizes defensively.
        Self::from_ranges(out)
    }

    /// Union (`∨`): code points satisfying either predicate.
    #[must_use]
    pub fn or(&self, other: &Self) -> Self {
        let mut raw = self.ranges.clone();
        raw.extend_from_slice(&other.ranges);
        Self::from_ranges(raw)
    }

    /// Complement (`¬`): code points in the alphabet not satisfying the
    /// predicate.
    #[must_use]
    pub fn not(&self) -> Self {
        let mut out = Vec::new();
        let mut next: u32 = 0;
        for &(lo, hi) in &self.ranges {
            if lo > next {
                out.push((next, lo - 1));
            }
            // `hi + 1 <= ALPHABET_MAX + 1 = 0x30000` — fits in `u32`.
            next = hi + 1;
        }
        if next <= ALPHABET_MAX {
            out.push((next, ALPHABET_MAX));
        }
        Self { ranges: out }
    }

    /// Mintermization: given a finite set of predicates, return the disjoint
    /// **atoms** that partition the whole alphabet such that every input
    /// predicate is exactly the union of the atoms it contains.
    ///
    /// This is what keeps derivative branching finite: after refining the
    /// alphabet by a regex's local predicates, each atom behaves uniformly, so
    /// the transition regex has one branch per atom rather than one per code
    /// point. The returned atoms are pairwise disjoint, non-empty, and their
    /// union is the entire alphabet `0..=`[`ALPHABET_MAX`] (the atom of code
    /// points in *no* input predicate — the derivative's "else" residual — is
    /// included when non-empty). With no input predicates the single atom is
    /// [`all`](Self::all).
    #[must_use]
    pub fn mintermize(preds: &[Self]) -> Vec<Self> {
        // Boundary "cut" points: the start of every range and one past every
        // range end, plus the alphabet endpoints. Between consecutive cuts the
        // membership signature (which predicates contain the interval) is
        // constant.
        let mut cuts: BTreeSet<u32> = BTreeSet::new();
        cuts.insert(0);
        cuts.insert(ALPHABET_MAX + 1);
        for p in preds {
            for &(lo, hi) in &p.ranges {
                cuts.insert(lo);
                cuts.insert(hi + 1);
            }
        }
        let cuts: Vec<u32> = cuts
            .into_iter()
            .filter(|&c| c <= ALPHABET_MAX + 1)
            .collect();

        // Group elementary intervals by their membership signature. `BTreeMap`
        // keeps the output deterministic (sorted by signature).
        let mut groups: BTreeMap<Vec<bool>, Vec<(u32, u32)>> = BTreeMap::new();
        for window in cuts.windows(2) {
            let lo = window[0];
            if lo > ALPHABET_MAX {
                continue;
            }
            let hi = (window[1] - 1).min(ALPHABET_MAX);
            if lo > hi {
                continue;
            }
            let sig: Vec<bool> = preds.iter().map(|p| p.contains(lo)).collect();
            groups.entry(sig).or_default().push((lo, hi));
        }

        groups.into_values().map(Self::from_ranges).collect()
    }
}
