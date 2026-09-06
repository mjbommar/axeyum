//! Persistent homology of a filtration, over `F_2`, `Q`, or `F_p` for a
//! caller-chosen small prime `p` (wave three).
//!
//! # What this computes
//!
//! A **filtration** is a total order on the simplices of a complex, given
//! here as `Vec<Vec<usize>>` (each entry a sorted, deduplicated vertex list),
//! such that every face of a simplex appears strictly before it -- the
//! standard requirement that lets each prefix of the list be read as an
//! actual sub-complex. [`persistent_homology`] validates this
//! (`build_boundary_columns` returns `None` on a violation) and then runs
//! the **standard column-reduction algorithm** (Zomorodian-Carlsson) over
//! `F_2`: each simplex's boundary, as a set of earlier-simplex indices, is a
//! column; columns are reduced left to right by adding (symmetric
//! difference, since coefficients are mod 2) an earlier column with the same
//! "low" (its highest surviving index) until either the column empties out
//! (a birth: a new cycle, possibly never killed) or its low is new (a death:
//! it kills the class born at that low).
//!
//! From the reduction: a **finite bar** is a pair `(birth, death)` for every
//! `low -> col` entry recorded during reduction, at dimension
//! `dim(simplex[birth])`; an **essential (infinite) bar** is any index whose
//! column reduces to empty and that is never later selected as a `low`.
//!
//! # What is certified
//!
//! [`PersistenceCertificate::verify`] re-derives every claim:
//!
//! - re-runs the reduction from `self.filtration` alone (an independent
//!   re-derivation, not a copy: `reduce_persistence` is deterministic, so a
//!   forged `low_to_col` disagrees with what a fresh run produces) and
//!   compares to the recorded `low_to_col` map (`reduction_matches`);
//! - recomputes the finite and essential bars from that (verified)
//!   `low_to_col` and compares to the recorded `pairs`/`essential`
//!   (`pairs_match`);
//! - checks **Euler-characteristic consistency at every filtration step**:
//!   the alternating sum of the prefix complex's own simplex counts must
//!   equal the alternating sum, by dimension, of the persistence diagram's
//!   bars alive at that step (`euler_characteristic_at_every_step`) -- a
//!   genuine additional identity (Euler-Poincare for every sub-level
//!   complex), not a restatement of the reduction.
//!
//! # Cost profile
//!
//! The reduction is `O(n^3)` worst case (each of `n` columns can be reduced
//! against up to `n` others, each an `O(n)` symmetric difference); the
//! Euler-characteristic guard is `O(n^2)` (checked at every one of `n`
//! steps). No Smith form, cofactor determinant, or `Rational` arithmetic is
//! involved anywhere in this module -- it is pure `F_2` combinatorics on
//! `BTreeSet<usize>`. The largest filtration exercised here is the 7-vertex
//! torus (42 simplices: 7 vertices, 21 edges, 14 triangles); see
//! [`super::coefficients`]'s doc comment for the whole-suite release timing.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use super::SimplicialComplex;

/// Finite bars, as `(dimension, birth, death)`.
type PersistencePairs = Vec<(usize, usize, usize)>;
/// Essential (infinite) bars, as `(dimension, birth)`.
type EssentialBars = Vec<(usize, usize)>;

/// Build, for every simplex in filtration order, its boundary column: the
/// set of indices (into `filtration`) of its codimension-1 faces. Returns
/// `None` if the filtration is invalid: a face missing from the list
/// entirely, or appearing at or after the simplex it bounds (the "every face
/// before its cofaces" requirement).
fn build_boundary_columns(filtration: &[Vec<usize>]) -> Option<Vec<BTreeSet<usize>>> {
    let mut index_of: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    for (i, simplex) in filtration.iter().enumerate() {
        let mut sorted = simplex.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != simplex.len() {
            return None; // a repeated vertex within one simplex: not a valid simplex
        }
        if index_of.insert(sorted, i).is_some() {
            return None; // the same simplex appears twice in the filtration
        }
    }
    let mut columns = Vec::with_capacity(filtration.len());
    for (i, simplex) in filtration.iter().enumerate() {
        let mut column = BTreeSet::new();
        if simplex.len() > 1 {
            for l in 0..simplex.len() {
                let mut face = simplex.clone();
                face.remove(l);
                let &face_idx = index_of.get(&face)?;
                if face_idx >= i {
                    return None; // a face appearing at or after its coface
                }
                column.insert(face_idx);
            }
        }
        columns.push(column);
    }
    Some(columns)
}

/// Run the standard column-reduction algorithm over `F_2` on the boundary
/// columns of a (already validated) filtration. Returns the fully reduced
/// columns and the `low -> col` map recorded during reduction.
fn reduce_persistence(
    mut columns: Vec<BTreeSet<usize>>,
) -> (Vec<BTreeSet<usize>>, BTreeMap<usize, usize>) {
    let mut low_to_col: BTreeMap<usize, usize> = BTreeMap::new();
    for j in 0..columns.len() {
        // The loop exits either when the column empties out (a birth,
        // possibly essential) or when its low is new (a finite pair).
        while let Some(&low) = columns[j].iter().next_back() {
            let Some(&pivot_col) = low_to_col.get(&low) else {
                low_to_col.insert(low, j);
                break; // a new low: (low, j) is a finite pair
            };
            let other = columns[pivot_col].clone();
            columns[j] = columns[j].symmetric_difference(&other).copied().collect();
        }
    }
    (columns, low_to_col)
}

/// Derive `(finite pairs, essential births)` from a fully reduced column
/// set's emptiness (one `bool` per filtration index -- field-independent,
/// since a birth/death pairing depends only on which columns emptied out,
/// not on the field the reduction ran over) and the reduction's `low_to_col`
/// map. Each finite pair is `(dimension, birth, death)` and each essential
/// birth is `(dimension, birth)`, both sorted. Shared by every producer in
/// this module ([`persistent_homology`] over `F_2`,
/// [`persistent_homology_over_q`] and [`persistent_homology_mod_p`] over a
/// general field) and by [`pairs_match`] (the guard that re-derives the same
/// thing from a certificate under test).
fn derive_pairs(
    filtration: &[Vec<usize>],
    is_empty: &[bool],
    low_to_col: &BTreeMap<usize, usize>,
) -> (PersistencePairs, EssentialBars) {
    let mut pairs: Vec<(usize, usize, usize)> = low_to_col
        .iter()
        .map(|(&birth, &death)| (filtration[birth].len() - 1, birth, death))
        .collect();
    pairs.sort_unstable();

    let mut essential: Vec<(usize, usize)> = (0..filtration.len())
        .filter(|&i| is_empty[i] && !low_to_col.contains_key(&i))
        .map(|i| (filtration[i].len() - 1, i))
        .collect();
    essential.sort_unstable();

    (pairs, essential)
}

/// A checkable certificate of the persistent homology (over `F_2`) of a
/// filtration. See the module documentation for what
/// [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistenceCertificate {
    /// The filtration: simplices (sorted vertex lists) in insertion order.
    pub filtration: Vec<Vec<usize>>,
    /// The `low -> col` map the standard reduction produced: `low_to_col[l] =
    /// j` records that column `j`, once fully reduced, has low `l` -- i.e.
    /// the pair `(birth = l, death = j)`.
    pub low_to_col: BTreeMap<usize, usize>,
    /// Finite bars, as `(dimension, birth, death)`, sorted.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, as `(dimension, birth)`, sorted.
    pub essential: Vec<(usize, usize)>,
}

/// The result of a successful [`PersistenceCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistenceReport {
    /// Finite bars, recomputed.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, recomputed.
    pub essential: Vec<(usize, usize)>,
}

/// Compute the persistent homology (over `F_2`) of `filtration`.
///
/// Returns `None` if `filtration` is not a valid filtration: a face missing
/// from the list, a face at or after its own coface, a repeated simplex, or
/// a simplex with a repeated vertex.
#[must_use]
pub fn persistent_homology(filtration: &[Vec<usize>]) -> Option<PersistenceCertificate> {
    let normalized: Vec<Vec<usize>> = filtration
        .iter()
        .map(|s| {
            let mut sorted = s.clone();
            sorted.sort_unstable();
            sorted
        })
        .collect();
    let columns = build_boundary_columns(&normalized)?;
    let (reduced, low_to_col) = reduce_persistence(columns);
    let is_empty: Vec<bool> = reduced.iter().map(BTreeSet::is_empty).collect();
    let (pairs, essential) = derive_pairs(&normalized, &is_empty, &low_to_col);

    Some(PersistenceCertificate {
        filtration: normalized,
        low_to_col,
        pairs,
        essential,
    })
}

/// Guard: re-running the reduction on `self.filtration` alone reproduces the
/// recorded `low_to_col` map exactly.
fn reduction_matches(certificate: &PersistenceCertificate) -> Result<Vec<BTreeSet<usize>>, String> {
    let columns = build_boundary_columns(&certificate.filtration)
        .ok_or_else(|| "the recorded filtration is not a valid filtration".to_string())?;
    let (reduced, low_to_col) = reduce_persistence(columns);
    if low_to_col != certificate.low_to_col {
        return Err(format!(
            "reduction mismatch: fresh reduction gives low_to_col {low_to_col:?}, certificate claims {:?}",
            certificate.low_to_col
        ));
    }
    Ok(reduced)
}

/// Guard: the recorded `pairs`/`essential` are exactly what
/// [`derive_pairs`]-style derivation gives from the (already verified)
/// `low_to_col` and `reduced` columns.
fn pairs_match(
    certificate: &PersistenceCertificate,
    reduced: &[BTreeSet<usize>],
) -> Result<(PersistencePairs, EssentialBars), String> {
    let is_empty: Vec<bool> = reduced.iter().map(BTreeSet::is_empty).collect();
    let (pairs, essential) =
        derive_pairs(&certificate.filtration, &is_empty, &certificate.low_to_col);
    if pairs != certificate.pairs {
        return Err(format!(
            "pairs mismatch: recomputed {pairs:?}, certificate claims {:?}",
            certificate.pairs
        ));
    }
    if essential != certificate.essential {
        return Err(format!(
            "essential bar mismatch: recomputed {essential:?}, certificate claims {:?}",
            certificate.essential
        ));
    }
    Ok((pairs, essential))
}

/// Guard: at every prefix length `m` in `1..=n`, the alternating sum of the
/// prefix complex's own simplex counts by dimension equals the alternating
/// sum, by dimension, of the persistence diagram's bars alive at step `m`
/// (born by index `m - 1`, not yet killed by index `m`) -- the
/// Euler-Poincare identity for every sub-level complex in the filtration.
/// Field-independent (an Euler characteristic identity holds over any
/// coefficient ring), so shared by every certificate type in this module.
fn euler_characteristic_at_every_step(
    filtration: &[Vec<usize>],
    pairs: &[(usize, usize, usize)],
    essential: &[(usize, usize)],
) -> Result<(), String> {
    let n = filtration.len();
    let mut complex_euler: Vec<i128> = Vec::with_capacity(n);
    let mut running = 0i128;
    for simplex in filtration {
        let dim = simplex.len() - 1;
        running += if dim % 2 == 0 { 1 } else { -1 };
        complex_euler.push(running);
    }

    for m in 1..=n {
        let bars_euler: i128 = pairs
            .iter()
            .filter(|&&(_, birth, death)| birth < m && death >= m)
            .map(|&(dim, _, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
            .sum::<i128>()
            + essential
                .iter()
                .filter(|&&(_, birth)| birth < m)
                .map(|&(dim, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
                .sum::<i128>();
        if bars_euler != complex_euler[m - 1] {
            return Err(format!(
                "Euler characteristic mismatch at filtration step {m}: complex gives {}, the persistence diagram gives {bars_euler}",
                complex_euler[m - 1]
            ));
        }
    }
    Ok(())
}

impl PersistenceCertificate {
    /// Re-derive every claim in this certificate from `self.filtration`
    /// alone. See the module documentation for exactly what each guard would
    /// miss if it were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first: an invalid filtration, a reduction mismatch, a
    /// pairs/essential mismatch, or an Euler-characteristic inconsistency at
    /// some filtration step.
    pub fn verify(&self) -> Result<PersistenceReport, String> {
        let reduced = reduction_matches(self)?;
        let (pairs, essential) = pairs_match(self, &reduced)?;
        euler_characteristic_at_every_step(&self.filtration, &self.pairs, &self.essential)?;
        Ok(PersistenceReport { pairs, essential })
    }
}

/// Build a [`SimplicialComplex`] from the first `m` simplices of a
/// filtration -- a convenience for constructing test fixtures and for a
/// caller who wants the actual complex at some step (not exercised by
/// [`verify`](PersistenceCertificate::verify), which works from simplex
/// counts alone).
#[must_use]
pub fn prefix_complex(filtration: &[Vec<usize>], m: usize) -> Option<SimplicialComplex> {
    let maximal: Vec<Vec<usize>> = filtration.get(..m)?.to_vec();
    // `from_maximal_simplices` closes under subsets already, and a prefix of
    // a valid filtration consists of simplices whose every face already
    // appears earlier in the same prefix, so treating each one as its own
    // "maximal" simplex and letting the constructor re-derive subsets is
    // safe (it will just re-insert already-present faces).
    SimplicialComplex::from_maximal_simplices(&maximal)
}

// =============================================================================
// Wave three: persistence over `Q` and over `F_p`, by the SAME column
// reduction with general field arithmetic.
// =============================================================================
//
// The `F_2` reduction above works on `BTreeSet<usize>` columns because mod-2
// coefficients are either present or absent -- addition IS symmetric
// difference. A general field needs an actual coefficient per row (a
// `BTreeMap<usize, F>`) and real scalar elimination (`column_j -=
// (low_j / low_pivot) * column_pivot`, not XOR), and needs SIGNED boundary
// columns (the alternating-face-removal sign convention
// [`super::boundary_matrix`] uses, since mod 2 makes signs irrelevant but
// mod `p` for odd `p`, or over `Q`, does not).
//
// [`FieldElement`] abstracts exactly the operations
// [`reduce_persistence_generic`] needs, so the reduction algorithm itself is
// written once and instantiated for [`Rational`] (`Q`, exact) and [`Fp`]
// (`F_p`, modular). [`derive_pairs`] and
// [`euler_characteristic_at_every_step`] above already work from
// field-independent data (`is_empty`/`pairs`/`essential`), so they are
// reused as-is, not reimplemented.

/// The operations the standard column-reduction algorithm needs from a
/// field: enough to build a signed boundary entry, add/negate/multiply, test
/// for zero, and invert a nonzero pivot.
trait FieldElement: Copy + PartialEq {
    fn zero() -> Self;
    fn from_sign(sign: i128) -> Self;
    fn is_zero(&self) -> bool;
    fn add(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    fn neg(self) -> Self;
    /// The multiplicative inverse. Only ever called on a genuinely nonzero
    /// pivot entry, so `None` here would indicate an internal bug (a
    /// "zero" pivot cannot occur by construction: `low` is defined as the
    /// highest row with a NONZERO entry).
    fn inv(self) -> Option<Self>;
}

impl FieldElement for Rational {
    fn zero() -> Self {
        Rational::integer(0)
    }
    fn from_sign(sign: i128) -> Self {
        Rational::integer(sign)
    }
    fn is_zero(&self) -> bool {
        Rational::is_zero(*self)
    }
    fn add(self, other: Self) -> Self {
        self + other
    }
    fn mul(self, other: Self) -> Self {
        self * other
    }
    fn neg(self) -> Self {
        -self
    }
    fn inv(self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(Rational::integer(1) / self)
        }
    }
}

/// An element of `F_p` (`p` a caller-chosen small prime, taken on faith --
/// see [`persistent_homology_mod_p`]'s doc): a value in `0..p`, carrying `p`
/// alongside it so [`FieldElement`]'s methods need no extra parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fp {
    value: i128,
    modulus: i128,
}

impl Fp {
    fn new(value: i128, modulus: i128) -> Fp {
        Fp {
            value: value.rem_euclid(modulus),
            modulus,
        }
    }
}

/// The extended Euclidean algorithm: returns `(g, x, y)` with `a*x + b*y =
/// g = gcd(a, b)`. Used only to invert a nonzero `F_p` element (`b` is
/// always the prime modulus there, so `g = 1` whenever `a != 0`).
fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        return (a, 1, 0);
    }
    let (g, x1, y1) = extended_gcd(b, a.rem_euclid(b));
    (g, y1, x1 - (a.div_euclid(b)) * y1)
}

impl FieldElement for Fp {
    fn zero() -> Self {
        Fp {
            value: 0,
            modulus: 0, // overwritten by every real use via `add`/`mul`'s operands
        }
    }
    fn from_sign(sign: i128) -> Self {
        // `from_sign` alone cannot carry a modulus (the trait has no
        // parameter for it); every call site in this module immediately
        // combines the result with an already-moduled `Fp` via `add`/`mul`,
        // which is why `zero()`'s placeholder modulus is harmless -- it is
        // never read on its own, only ever combined with a genuine value.
        Fp {
            value: sign,
            modulus: 0,
        }
    }
    fn is_zero(&self) -> bool {
        self.value == 0
    }
    fn add(self, other: Self) -> Self {
        let modulus = if self.modulus != 0 {
            self.modulus
        } else {
            other.modulus
        };
        Fp::new(self.value + other.value, modulus)
    }
    fn mul(self, other: Self) -> Self {
        let modulus = if self.modulus != 0 {
            self.modulus
        } else {
            other.modulus
        };
        Fp::new(self.value * other.value, modulus)
    }
    fn neg(self) -> Self {
        Fp::new(-self.value, self.modulus)
    }
    fn inv(self) -> Option<Self> {
        if self.value == 0 {
            return None;
        }
        let (g, x, _) = extended_gcd(self.value, self.modulus);
        if g != 1 {
            return None; // would mean `modulus` is not actually prime
        }
        Some(Fp::new(x, self.modulus))
    }
}

/// Whether `p` is prime, by trial division -- used to refuse a non-prime
/// `p` up front rather than silently computing over `Z/p` (a ring with zero
/// divisors, where "division" by a non-invertible nonzero element would
/// need to fail differently than this module's `inv` does).
fn is_small_prime(p: u32) -> bool {
    if p < 2 {
        return false;
    }
    if p.is_multiple_of(2) {
        return p == 2;
    }
    let mut d = 3u32;
    while d.saturating_mul(d) <= p {
        if p.is_multiple_of(d) {
            return false;
        }
        d += 2;
    }
    true
}

/// Build, for every simplex in a (already normalized: sorted vertex lists)
/// filtration, its SIGNED boundary column (row index -> `+1`/`-1`, the same
/// alternating-face-removal convention [`super::boundary_matrix`] uses) --
/// the field-independent input every field-based reduction in this module
/// lifts into its own coefficients via [`FieldElement::from_sign`]. Returns
/// `None` under the same validation [`build_boundary_columns`] performs: a
/// repeated simplex, a repeated vertex within one simplex, a missing face,
/// or a face appearing at or after its own coface.
fn build_signed_boundary_columns(filtration: &[Vec<usize>]) -> Option<Vec<BTreeMap<usize, i128>>> {
    let mut index_of: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    for (i, simplex) in filtration.iter().enumerate() {
        let mut sorted = simplex.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != simplex.len() {
            return None;
        }
        if index_of.insert(sorted, i).is_some() {
            return None;
        }
    }
    let mut columns = Vec::with_capacity(filtration.len());
    for (i, simplex) in filtration.iter().enumerate() {
        let mut column = BTreeMap::new();
        if simplex.len() > 1 {
            for l in 0..simplex.len() {
                let mut face = simplex.clone();
                face.remove(l);
                let &face_idx = index_of.get(&face)?;
                if face_idx >= i {
                    return None;
                }
                let sign: i128 = if l % 2 == 0 { 1 } else { -1 };
                column.insert(face_idx, sign);
            }
        }
        columns.push(column);
    }
    Some(columns)
}

/// The standard column-reduction algorithm, generalized from the `F_2`
/// [`reduce_persistence`] to any [`FieldElement`]: reduce each column
/// against an earlier column sharing the same `low` by SCALAR elimination
/// (`column_j -= (low_j * low_pivot^-1) * column_pivot`) rather than XOR,
/// until the column empties out (a birth) or its low is new (a death, or --
/// if never later selected as a low -- an essential birth).
fn reduce_persistence_generic<F: FieldElement>(
    mut columns: Vec<BTreeMap<usize, F>>,
) -> (Vec<BTreeMap<usize, F>>, BTreeMap<usize, usize>) {
    let mut low_to_col: BTreeMap<usize, usize> = BTreeMap::new();
    for j in 0..columns.len() {
        while let Some((&low, &low_value)) = columns[j].iter().next_back() {
            let Some(&pivot_col) = low_to_col.get(&low) else {
                low_to_col.insert(low, j);
                break;
            };
            let pivot_value = *columns[pivot_col]
                .get(&low)
                .expect("the pivot column's own recorded low is present in it");
            let factor = low_value.mul(
                pivot_value
                    .inv()
                    .expect("a recorded pivot value is nonzero by construction"),
            );
            let other = columns[pivot_col].clone();
            for (&row, &value) in &other {
                let scaled = factor.mul(value).neg();
                let updated = columns[j]
                    .get(&row)
                    .copied()
                    .unwrap_or_else(F::zero)
                    .add(scaled);
                if updated.is_zero() {
                    columns[j].remove(&row);
                } else {
                    columns[j].insert(row, updated);
                }
            }
        }
    }
    (columns, low_to_col)
}

/// Which field a [`FieldPersistenceCertificate`] ran the reduction over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Coefficients {
    /// The rationals, exact via [`Rational`].
    Q,
    /// `F_p` for the given prime `p`.
    Fp(u32),
}

/// A checkable certificate of the persistent homology of a filtration over
/// `Q` or `F_p`, mirroring [`PersistenceCertificate`]'s shape (see its
/// module documentation for what each field means and what
/// [`verify`](Self::verify) re-derives) but recording which
/// [`Coefficients`] the reduction ran over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldPersistenceCertificate {
    /// Which field this reduction ran over.
    pub coefficients: Coefficients,
    /// The filtration: simplices (sorted vertex lists) in insertion order.
    pub filtration: Vec<Vec<usize>>,
    /// The `low -> col` map the reduction produced.
    pub low_to_col: BTreeMap<usize, usize>,
    /// Finite bars, as `(dimension, birth, death)`, sorted.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, as `(dimension, birth)`, sorted.
    pub essential: Vec<(usize, usize)>,
}

/// The result of a successful [`FieldPersistenceCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldPersistenceReport {
    /// Finite bars, recomputed.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, recomputed.
    pub essential: Vec<(usize, usize)>,
}

/// Shared by every field-based producer: normalize, build signed boundary
/// columns, lift to `F` via `from_sign`, reduce, and derive the diagram.
fn persistent_homology_over_field<F: FieldElement>(
    filtration: &[Vec<usize>],
    coefficients: Coefficients,
) -> Option<FieldPersistenceCertificate> {
    let normalized: Vec<Vec<usize>> = filtration
        .iter()
        .map(|s| {
            let mut sorted = s.clone();
            sorted.sort_unstable();
            sorted
        })
        .collect();
    let signed = build_signed_boundary_columns(&normalized)?;
    let lifted: Vec<BTreeMap<usize, F>> = signed
        .iter()
        .map(|col| {
            col.iter()
                .map(|(&row, &sign)| (row, F::from_sign(sign)))
                .collect()
        })
        .collect();
    let (reduced, low_to_col) = reduce_persistence_generic(lifted);
    let is_empty: Vec<bool> = reduced.iter().map(BTreeMap::is_empty).collect();
    let (pairs, essential) = derive_pairs(&normalized, &is_empty, &low_to_col);
    Some(FieldPersistenceCertificate {
        coefficients,
        filtration: normalized,
        low_to_col,
        pairs,
        essential,
    })
}

/// Compute the persistent homology of `filtration` over `Q` (exact
/// rationals), by the same column-reduction algorithm [`persistent_homology`]
/// runs over `F_2`, generalized to real scalar elimination. Returns `None`
/// under the same filtration-validity conditions.
#[must_use]
pub fn persistent_homology_over_q(
    filtration: &[Vec<usize>],
) -> Option<FieldPersistenceCertificate> {
    persistent_homology_over_field::<Rational>(filtration, Coefficients::Q)
}

/// Compute the persistent homology of `filtration` over `F_p`.
///
/// Returns `None` if `filtration` is not a valid filtration, or if `p` is
/// not prime (checked by trial division: `F_p` is not a field, and this
/// module's reduction needs one, if `p` is composite).
#[must_use]
pub fn persistent_homology_mod_p(
    filtration: &[Vec<usize>],
    p: u32,
) -> Option<FieldPersistenceCertificate> {
    if !is_small_prime(p) {
        return None;
    }
    let modulus = i128::from(p);
    let normalized: Vec<Vec<usize>> = filtration
        .iter()
        .map(|s| {
            let mut sorted = s.clone();
            sorted.sort_unstable();
            sorted
        })
        .collect();
    let signed = build_signed_boundary_columns(&normalized)?;
    let lifted: Vec<BTreeMap<usize, Fp>> = signed
        .iter()
        .map(|col| {
            col.iter()
                .map(|(&row, &sign)| (row, Fp::new(sign, modulus)))
                .collect()
        })
        .collect();
    let (reduced, low_to_col) = reduce_persistence_generic(lifted);
    let is_empty: Vec<bool> = reduced.iter().map(BTreeMap::is_empty).collect();
    let (pairs, essential) = derive_pairs(&normalized, &is_empty, &low_to_col);
    Some(FieldPersistenceCertificate {
        coefficients: Coefficients::Fp(p),
        filtration: normalized,
        low_to_col,
        pairs,
        essential,
    })
}

impl FieldPersistenceCertificate {
    /// Re-derive every claim in this certificate from `(self.filtration,
    /// self.coefficients)` alone: re-running the SAME producer this
    /// certificate's `coefficients` names must reproduce the recorded
    /// `low_to_col`, `pairs`, and `essential` exactly, and the
    /// field-independent Euler-characteristic identity must hold at every
    /// step.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever check
    /// fails first: an invalid `p` (refused up front, same as the
    /// producer), an invalid filtration, a reduction (`low_to_col`)
    /// mismatch, a `pairs`/`essential` mismatch, or an Euler-characteristic
    /// inconsistency at some filtration step.
    pub fn verify(&self) -> Result<FieldPersistenceReport, String> {
        let rebuilt = match self.coefficients {
            Coefficients::Q => persistent_homology_over_q(&self.filtration),
            Coefficients::Fp(p) => persistent_homology_mod_p(&self.filtration, p),
        }
        .ok_or_else(|| {
            format!(
                "could not rebuild the {:?} persistence certificate from the recorded filtration",
                self.coefficients
            )
        })?;
        if rebuilt.low_to_col != self.low_to_col {
            return Err(format!(
                "reduction mismatch: fresh reduction gives low_to_col {:?}, certificate claims {:?}",
                rebuilt.low_to_col, self.low_to_col
            ));
        }
        if rebuilt.pairs != self.pairs {
            return Err(format!(
                "pairs mismatch: recomputed {:?}, certificate claims {:?}",
                rebuilt.pairs, self.pairs
            ));
        }
        if rebuilt.essential != self.essential {
            return Err(format!(
                "essential bar mismatch: recomputed {:?}, certificate claims {:?}",
                rebuilt.essential, self.essential
            ));
        }
        euler_characteristic_at_every_step(&self.filtration, &self.pairs, &self.essential)?;
        Ok(FieldPersistenceReport {
            pairs: rebuilt.pairs,
            essential: rebuilt.essential,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Coefficients, persistent_homology, persistent_homology_mod_p, persistent_homology_over_q,
    };
    use crate::homology::fixtures::rp2_6v;

    /// A filtration building the 3-vertex circle then filling it in: three
    /// vertices, then two edges, then the closing edge (which creates the
    /// `H_1` class), then the 2-simplex (which kills it).
    fn circle_then_fill() -> Vec<Vec<usize>> {
        vec![
            vec![0],
            vec![1],
            vec![2],
            vec![0, 1],
            vec![1, 2],
            vec![0, 2],    // the closing edge, index 5
            vec![0, 1, 2], // the triangle, index 6
        ]
    }

    #[test]
    fn circle_then_fill_has_one_h1_bar_born_at_the_closing_edge() {
        let filtration = circle_then_fill();
        let certificate = persistent_homology(&filtration).expect("valid filtration");
        certificate.verify().expect("certificate verifies");

        let h1_bars: Vec<_> = certificate
            .pairs
            .iter()
            .filter(|&&(dim, _, _)| dim == 1)
            .collect();
        assert_eq!(h1_bars.len(), 1, "expected exactly one H_1 bar");
        assert_eq!(
            *h1_bars[0],
            (1, 5, 6),
            "born at the closing edge, dying at the triangle"
        );

        // H_0: one essential bar (the whole complex's single surviving
        // component), and two finite bars (the merges as edges are added).
        let h0_essential: Vec<_> = certificate
            .essential
            .iter()
            .filter(|&&(dim, _)| dim == 0)
            .collect();
        assert_eq!(h0_essential.len(), 1);
        let h0_pairs: Vec<_> = certificate
            .pairs
            .iter()
            .filter(|&&(dim, _, _)| dim == 0)
            .collect();
        assert_eq!(h0_pairs.len(), 2);
    }

    /// The 7-vertex torus triangulation's own vertex/edge/triangle lists,
    /// concatenated in an order that is a valid filtration (every edge's
    /// vertices precede it; every triangle's edges precede it) -- vertices,
    /// then edges sorted lexicographically, then the 14 triangles in the
    /// order `homology.rs`'s own torus fixture lists them.
    fn torus_filtration() -> Vec<Vec<usize>> {
        let triangles: &[&[usize]] = &[
            &[0, 1, 3],
            &[0, 1, 5],
            &[0, 2, 3],
            &[0, 2, 6],
            &[0, 4, 5],
            &[0, 4, 6],
            &[1, 2, 4],
            &[1, 2, 6],
            &[1, 3, 4],
            &[1, 5, 6],
            &[2, 3, 5],
            &[2, 4, 5],
            &[3, 4, 6],
            &[3, 5, 6],
        ];
        let mut edges: std::collections::BTreeSet<[usize; 2]> = std::collections::BTreeSet::new();
        for triangle in triangles {
            for i in 0..3 {
                for j in (i + 1)..3 {
                    let mut pair = [triangle[i], triangle[j]];
                    pair.sort_unstable();
                    edges.insert(pair);
                }
            }
        }
        let mut filtration: Vec<Vec<usize>> = (0..7).map(|v| vec![v]).collect();
        filtration.extend(edges.iter().map(|e| e.to_vec()));
        filtration.extend(triangles.iter().map(|t| t.to_vec()));
        filtration
    }

    #[test]
    fn torus_filtration_verifies_and_matches_its_own_euler_characteristic() {
        let filtration = torus_filtration();
        assert_eq!(filtration.len(), 7 + 21 + 14);
        let certificate = persistent_homology(&filtration).expect("valid filtration");
        certificate.verify().expect("certificate verifies");
        // The full complex (all 42 simplices) has Euler characteristic 0
        // (the torus): 7 - 21 + 14 = 0. Confirm the diagram's own bars sum
        // to this at the final step, as a sanity check beside `verify`'s
        // own (per-step) Euler-characteristic guard.
        let n = filtration.len();
        let alive_euler: i128 = certificate
            .pairs
            .iter()
            .filter(|&&(_, birth, death)| birth < n && death >= n)
            .map(|&(dim, _, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
            .sum::<i128>()
            + certificate
                .essential
                .iter()
                .filter(|&&(_, birth)| birth < n)
                .map(|&(dim, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
                .sum::<i128>();
        assert_eq!(alive_euler, 0);
    }

    #[test]
    fn an_out_of_order_filtration_is_refused() {
        // The edge {0, 1} appears BEFORE vertex 1: invalid.
        let filtration = vec![vec![0], vec![0, 1], vec![1]];
        assert!(persistent_homology(&filtration).is_none());
    }

    #[test]
    fn a_filtration_with_a_missing_face_is_refused() {
        // The triangle's edge {1, 2} never appears at all.
        let filtration = vec![
            vec![0],
            vec![1],
            vec![2],
            vec![0, 1],
            vec![0, 2],
            vec![0, 1, 2],
        ];
        assert!(persistent_homology(&filtration).is_none());
    }

    /// ADVERSARIAL. Forge only the recorded `low_to_col` map (and the pairs
    /// derived from it, so `pairs_match` alone would not catch this),
    /// leaving `filtration` genuine. `reduction_matches` re-runs the
    /// reduction and disagrees. Confirmed by mutation: disabling only
    /// `reduction_matches` leaves every other test in this module green.
    #[test]
    fn verify_refuses_a_forged_low_to_col_with_matching_forged_pairs() {
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(
            certificate.verify().is_ok(),
            "genuine certificate must verify"
        );

        // Forge low_to_col to swap the death of the (5, 6) pair to a bogus
        // (5, 4): 4 is not >= 5, so this claims edge 4 (already present)
        // kills a class born at 5, an impossible ordering violation the
        // reduction itself would never produce.
        certificate.low_to_col.insert(5, 4);
        certificate.pairs = vec![(1, 5, 4)]
            .into_iter()
            .chain(
                certificate
                    .pairs
                    .iter()
                    .copied()
                    .filter(|&(_, b, _)| b != 5),
            )
            .collect();
        certificate.pairs.sort_unstable();
        let err = certificate
            .verify()
            .expect_err("a forged low_to_col must be refused");
        assert!(err.contains("reduction mismatch"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only `essential`, leaving `low_to_col` and `pairs`
    /// genuine: `pairs_match` recomputes essential bars from the (verified)
    /// reduction and disagrees. Confirmed by mutation: disabling only the
    /// essential-bar comparison in `pairs_match` leaves every other test in
    /// this module green.
    #[test]
    fn verify_refuses_a_forged_essential_bar() {
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(
            certificate.verify().is_ok(),
            "genuine certificate must verify"
        );

        certificate.essential.push((1, 6)); // a fabricated infinite H_1 bar
        certificate.essential.sort_unstable();
        let err = certificate
            .verify()
            .expect_err("a forged essential bar must be refused");
        assert!(err.contains("essential"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only `pairs` to swap a death index, keeping it
    /// consistent with what `low_to_col` alone implies (by ALSO forging
    /// `low_to_col` the same way) so this is really testing that
    /// `euler_characteristic_at_every_step` fires as a genuinely separate
    /// identity: shift the closing edge's death from the triangle (6) to
    /// one step earlier -- a value not reachable by any reduction of this
    /// filtration, but constructed here to isolate the Euler-characteristic
    /// guard specifically by leaving `reduction_matches` unable to run (it
    /// would already refuse this forgery too; this test instead calls the
    /// guard function directly with a hand-built inconsistent certificate,
    /// the same isolation pattern the parent module uses for its own
    /// hard-to-isolate guards).
    #[test]
    fn euler_characteristic_guard_refuses_a_bar_alive_at_the_wrong_step_directly() {
        use super::euler_characteristic_at_every_step;
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(
            euler_characteristic_at_every_step(
                &certificate.filtration,
                &certificate.pairs,
                &certificate.essential
            )
            .is_ok()
        );

        // Move the (1, 5, 6) bar's death one step earlier, to 5 itself --
        // an edge cannot die at its own birth index, so this both breaks
        // the Euler count at step 6 (the class is now claimed dead before
        // the triangle that actually kills it arrives) and is never
        // producible by a genuine reduction.
        certificate.pairs = certificate
            .pairs
            .iter()
            .map(|&(dim, birth, death)| {
                if (dim, birth, death) == (1, 5, 6) {
                    (dim, birth, 5)
                } else {
                    (dim, birth, death)
                }
            })
            .collect();
        let err = euler_characteristic_at_every_step(
            &certificate.filtration,
            &certificate.pairs,
            &certificate.essential,
        )
        .expect_err("a bar alive at the wrong step must be refused");
        assert!(err.contains("Euler characteristic mismatch"), "got: {err}");
    }

    // ---- wave three: persistence over Q and F_p ----

    /// A valid filtration of `rp2_6v()`: every vertex, then every edge, then
    /// every face, each group in the complex's own (sorted) order -- valid
    /// because every face's own faces already appear in an earlier group.
    fn rp2_filtration() -> Vec<Vec<usize>> {
        let complex = rp2_6v();
        let mut filtration = Vec::new();
        for k in 0..=complex.max_dimension() {
            filtration.extend(complex.simplices(k));
        }
        filtration
    }

    #[test]
    fn circle_then_fill_gives_the_same_bars_over_f2_q_and_f3() {
        let filtration = circle_then_fill();
        let over_f2 = persistent_homology(&filtration).expect("valid filtration");
        over_f2.verify().expect("F_2 certificate verifies");
        let over_q = persistent_homology_over_q(&filtration).expect("valid filtration");
        over_q.verify().expect("Q certificate verifies");
        let over_f3 =
            persistent_homology_mod_p(&filtration, 3).expect("valid filtration, p = 3 prime");
        over_f3.verify().expect("F_3 certificate verifies");

        assert_eq!(over_f2.pairs, over_q.pairs, "F_2 and Q pairs must agree");
        assert_eq!(
            over_f2.essential, over_q.essential,
            "F_2 and Q essential bars must agree"
        );
        assert_eq!(over_q.pairs, over_f3.pairs, "Q and F_3 pairs must agree");
        assert_eq!(
            over_q.essential, over_f3.essential,
            "Q and F_3 essential bars must agree"
        );
    }

    /// `RP^2`'s torsion bar appears over `F_2` only: `b(F_2) = (1, 1, 1)`
    /// (three essential bars) but `b(F_3) = b(Q) = (1, 0, 0)` (exactly one),
    /// matching the already-established Betti numbers in
    /// `homology::coefficients` and `homology` themselves -- this is the
    /// SAME phenomenon read off the persistence diagram of the full
    /// filtration instead of a one-shot homology computation.
    #[test]
    fn rp2_barcodes_differ_between_f2_and_f3_exactly_at_the_torsion_classes() {
        let filtration = rp2_filtration();
        assert_eq!(filtration.len(), 6 + 15 + 10);

        let over_f2 = persistent_homology_mod_p(&filtration, 2).expect("valid filtration");
        over_f2.verify().expect("F_2 certificate verifies");
        let over_f3 = persistent_homology_mod_p(&filtration, 3).expect("valid filtration");
        over_f3.verify().expect("F_3 certificate verifies");
        let over_q = persistent_homology_over_q(&filtration).expect("valid filtration");
        over_q.verify().expect("Q certificate verifies");

        assert_eq!(
            over_f2.essential.len(),
            3,
            "F_2: b = (1, 1, 1), three essential bars"
        );
        assert_eq!(
            over_f3.essential.len(),
            1,
            "F_3: b = (1, 0, 0), exactly one essential bar"
        );
        assert_eq!(
            over_q.essential.len(),
            1,
            "Q: b = (1, 0, 0), exactly one essential bar"
        );
        // The dimension-1 and dimension-2 classes born over F_2 (and never
        // killed) DO die over F_3/Q: they are finite bars there instead.
        assert!(
            over_f2.essential.iter().any(|&(dim, _)| dim == 1),
            "F_2 must have an essential H_1 bar"
        );
        assert!(
            over_f2.essential.iter().any(|&(dim, _)| dim == 2),
            "F_2 must have an essential H_2 bar"
        );
        assert!(
            over_f3.essential.iter().all(|&(dim, _)| dim == 0),
            "F_3's only essential bar must be at dimension 0"
        );
    }

    #[test]
    fn persistent_homology_mod_p_refuses_a_non_prime_modulus() {
        let filtration = circle_then_fill();
        assert!(persistent_homology_mod_p(&filtration, 4).is_none());
        assert!(persistent_homology_mod_p(&filtration, 1).is_none());
        // POSITIVE CONTROL: a genuine prime is accepted.
        assert!(persistent_homology_mod_p(&filtration, 5).is_some());
    }

    /// ADVERSARIAL. Forge only the recorded `pairs`, leaving `low_to_col`
    /// and `essential` genuine.
    #[test]
    fn verify_refuses_a_forged_field_persistence_pairs() {
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology_over_q(&filtration).expect("valid filtration");
        assert!(
            certificate.verify().is_ok(),
            "genuine certificate must verify"
        );
        assert_eq!(certificate.coefficients, Coefficients::Q);

        certificate.pairs.push((1, 0, 1)); // a fabricated bar
        let err = certificate
            .verify()
            .expect_err("a forged pairs list must be refused");
        assert!(err.contains("pairs mismatch"), "got: {err}");
    }
}
