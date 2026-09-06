//! Finite matrix groups over 𝔽ₚ, certified by encoding them as permutation
//! groups over [`crate::permgroup::PermutationGroup`].
//!
//! # The idea
//!
//! A matrix group has no native "order", "membership" or "isomorphism"
//! machinery here — but a *permutation* group does (Schreier–Sims, Sylow,
//! conjugacy classes, isomorphism testing, all in [`crate::permgroup`]). So
//! this module never reimplements group theory: it builds a faithful
//! permutation representation of the matrix group and hands the resulting
//! [`crate::permgroup::PermutationGroup`] to that machinery unchanged.
//!
//! Two actions are supported:
//!
//! - **Vector action** ([`ActionKind::Vector`]): each generator acts on the
//!   nonzero vectors of 𝔽ₚⁿ by `v ↦ Mv`. This action is **faithful for all
//!   of `GL(n, p)`**: if `M` fixes every nonzero vector then in particular it
//!   fixes every standard basis vector `e_i`, so `M = I`. So the permutation
//!   group built from a set of `GL(n, p)` generators under this action has
//!   *exactly* the order of the matrix group they generate — nothing is lost
//!   or collapsed.
//! - **Projective action** ([`ActionKind::Projective`]): each generator acts
//!   on the lines (1-dimensional subspaces) of 𝔽ₚⁿ, i.e. the points of
//!   `ℙⁿ⁻¹(𝔽ₚ)`, by `⟨v⟩ ↦ ⟨Mv⟩`. This action is *not* faithful on all of
//!   `GL(n, p)` — its kernel is exactly the scalar matrices `Z = {cI : c ∈
//!   𝔽ₚ*}` — but that is the point: handing `SL(n, p)` generators to this
//!   action and reading off the permutation group they generate gives
//!   exactly `PSL(n, p) = SL(n, p) / (SL(n, p) ∩ Z)` "for free", because two
//!   matrices differing by a scalar produce the *same* permutation, so
//!   Schreier–Sims computes the order of the image, not the preimage. No
//!   quotient is ever constructed by hand; it falls out of composing an
//!   honest group action with an existing, unmodified order algorithm. The
//!   same generators fed through [`MatrixGroup::from_generators_projective`]
//!   with `GL` generators instead give `PGL(n, p)`.
//!
//! For a fixed dimension `n`, the projective action has asymptotically fewer
//! points than the vector action (`(pⁿ − 1)/(p − 1)` vs. `pⁿ − 1`), which is
//! why it is also the natural choice once `p` is large enough that the
//! vector action's point count would be unusable — the doc for
//! [`MAX_POINTS`] states the bound both actions are refused above.
//!
//! # Certificates
//!
//! [`ActionCertificate::verify`] re-derives the *encoding* independently: it
//! re-enumerates the points from `(p, n, action)` alone (never trusting the
//! stored list), re-checks every generator is square, in-range and
//! invertible mod `p` (a singular matrix cannot act on the points at all, so
//! it is refused, not silently miscomputed), and re-computes each
//! generator's permutation image by matrix–vector multiplication mod `p`,
//! comparing every step to what the certificate claims. Once the encoding is
//! certified, every group property (order, membership, Sylow, conjugacy,
//! isomorphism, presentations) is certified by the unmodified
//! [`crate::permgroup`] certificates on the resulting
//! [`PermutationGroup`] — this module adds no new group-theoretic trust,
//! only a certified bridge into it.
//!
//! [`ElementOrderCertificate::verify`] independently cross-checks a single
//! matrix's order two ways: once via the (faithful, vector-action)
//! permutation's own order computation, and once by direct repeated modular
//! matrix multiplication confirming `M^k = I` and `M^(k/q) ≠ I` for every
//! prime `q | k` — two paths that share no code.
//!
//! # Reuse
//!
//! - [`crate::permgroup::PermutationGroup::from_generators`] and every
//!   certificate it and [`crate::permgroup_iso`]/[`crate::permgroup_sylow`]
//!   export are reused unchanged once the permutation images are built; no
//!   `permgroup*.rs` file is modified.
//! - [`crate::ntheory::is_prime`], [`crate::ntheory::mod_inverse`] and
//!   [`crate::ntheory::factorize`] are reused for primality, modular
//!   inversion (needed for both Gaussian-elimination determinants and
//!   projective-point normalization) and order minimality checking.
//! - `gfp.rs` and `matrix.rs` were read and do not fit: `gfp.rs` is
//!   univariate-*polynomial* arithmetic over 𝔽ₚ (a scalar would have to be
//!   smuggled in as a degree-0 polynomial, which buys nothing over plain
//!   `i128` modular arithmetic and would obscure the linear algebra below);
//!   `matrix.rs`'s `Matrix` stores symbolic `CasExpr` entries for exact
//!   rational/algebraic linear algebra, not reduced residues, and is a
//!   private module in this crate with no mod-`p` reduction anywhere in its
//!   API. So this module implements its own compact mod-`p` matrix–vector
//!   and matrix–matrix multiplication and a Gaussian-elimination
//!   determinant, all in terms of the `ntheory` primitives above.
//!
//! # Bounds
//!
//! Both actions decline outright, before doing any work, when the point
//! count would exceed [`MAX_POINTS`] — see that constant's doc. Once a
//! [`PermutationGroup`] exists, every bound documented on
//! [`crate::permgroup`] (the enumeration bound for conjugacy classes,
//! Sylow subgroups, cosets, the centre; the tighter bound for the derived
//! subgroup and invariants; [`crate::permgroup_iso::ISOMORPHISM_BOUND`] for
//! isomorphism testing) applies unchanged — `order()` itself is *not*
//! enumeration-bounded (Schreier–Sims never enumerates the group), so a
//! matrix group's order is always available even when, say, `invariants()`
//! or `isomorphism` on it must decline.
//!
//! # Out of scope
//!
//! Matrix groups over ℚ or ℤ (infinite, no permutation encoding applies),
//! infinite groups of any kind, characteristic polynomials or eigenvalues,
//! and representation theory beyond the one permutation representation
//! built here. None of these are attempted, partially or otherwise.

use crate::ntheory::{factorize, is_prime, mod_inverse};
use crate::permgroup::PermutationGroup;
use crate::permutation::Permutation;
use std::collections::{BTreeMap, BTreeSet};

/// An `n × n` matrix over 𝔽ₚ, stored row-major with every entry already
/// reduced into `0..p`.
pub type FpMatrix = Vec<Vec<i128>>;

/// The largest number of points ([`ActionKind::Vector`]: `pⁿ − 1`;
/// [`ActionKind::Projective`]: `(pⁿ − 1)/(p − 1)`) either action here will
/// enumerate before declining with [`MatrixGroupError::TooManyPoints`].
/// Chosen well above every group this module's own tests build (the
/// largest, `GL(2, 7)`, has 48 points) and well below where building the
/// point list itself would be the bottleneck, matching the refuse-rather-
/// than-hang discipline [`crate::permgroup::ENUMERATION_BOUND`] and its
/// siblings already use.
pub const MAX_POINTS: usize = 5_000;

/// Which set of points a [`MatrixGroup`] acts on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActionKind {
    /// The nonzero vectors of 𝔽ₚⁿ, `v ↦ Mv` — faithful for all of `GL(n, p)`.
    Vector,
    /// The lines (1-dimensional subspaces) of 𝔽ₚⁿ, `⟨v⟩ ↦ ⟨Mv⟩` — kernel is
    /// exactly the scalar matrices, so `SL`/`GL` generators give
    /// `PSL`/`PGL` as the image.
    Projective,
}

/// A reason [`MatrixGroup::from_generators`] or
/// [`MatrixGroup::from_generators_projective`] refused its input, or
/// [`order_of_element`] refused a matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatrixGroupError {
    /// `p` is not a prime, so `𝔽ₚ` is not a field.
    InvalidPrime,
    /// `n == 0`: no vector space, no action.
    InvalidDimension,
    /// A generator is not `n × n`.
    DimensionMismatch {
        /// Index into the generator list.
        generator_index: usize,
        /// The required row/column count.
        expected: usize,
        /// The generator's actual row count.
        rows: usize,
        /// The generator's actual (first-row) column count, or `expected`
        /// if the matrix has no rows.
        cols: usize,
    },
    /// A generator entry is outside `0..p`.
    EntryOutOfRange {
        /// Index into the generator list.
        generator_index: usize,
        /// Row of the offending entry.
        row: usize,
        /// Column of the offending entry.
        col: usize,
        /// The offending value.
        value: i128,
    },
    /// A generator's determinant mod `p` is `0`, so it does not act
    /// invertibly (and is not a member of `GL(n, p)` at all).
    SingularGenerator {
        /// Index into the generator list.
        generator_index: usize,
        /// The generator's determinant mod `p` (always `0` for this
        /// variant, carried for the caller's convenience).
        determinant: i128,
    },
    /// The point count (`pⁿ − 1` for [`ActionKind::Vector`], `(pⁿ −
    /// 1)/(p − 1)` for [`ActionKind::Projective`]) exceeds [`MAX_POINTS`],
    /// or overflows computing it at all.
    TooManyPoints {
        /// The prime.
        p: i128,
        /// The dimension.
        n: usize,
        /// Which action was requested.
        action: ActionKind,
    },
    /// An (already validated invertible) generator's recomputed image is
    /// not a bijection of the point list. Never observed — invertibility
    /// mod `p` makes the induced map on nonzero vectors (and hence on
    /// lines) bijective by construction — kept as a distinct, checkable
    /// refusal instead of a panic in case that argument is ever broken by
    /// a future edit.
    ActionNotBijective {
        /// Index into the generator list.
        generator_index: usize,
    },
}

// ---------------------------------------------------------------------------
// Mod-p linear algebra primitives (not reusing `gfp.rs` or `matrix.rs`; see
// the module doc's "Reuse" section for why neither fits).
// ---------------------------------------------------------------------------

fn reduce(x: i128, p: i128) -> i128 {
    let r = x % p;
    if r < 0 { r + p } else { r }
}

fn validate_matrix(
    p: i128,
    n: usize,
    generator_index: usize,
    mat: &FpMatrix,
) -> Result<(), MatrixGroupError> {
    if mat.len() != n {
        return Err(MatrixGroupError::DimensionMismatch {
            generator_index,
            expected: n,
            rows: mat.len(),
            cols: mat.first().map_or(n, Vec::len),
        });
    }
    for (row_idx, row) in mat.iter().enumerate() {
        if row.len() != n {
            return Err(MatrixGroupError::DimensionMismatch {
                generator_index,
                expected: n,
                rows: mat.len(),
                cols: row.len(),
            });
        }
        for (col_idx, &value) in row.iter().enumerate() {
            if value < 0 || value >= p {
                return Err(MatrixGroupError::EntryOutOfRange {
                    generator_index,
                    row: row_idx,
                    col: col_idx,
                    value,
                });
            }
        }
    }
    Ok(())
}

fn mat_vec_mul(mat: &FpMatrix, v: &[i128], p: i128) -> Vec<i128> {
    mat.iter()
        .map(|row| {
            let mut acc: i128 = 0;
            for (a, b) in row.iter().zip(v.iter()) {
                acc = reduce(acc + a * b, p);
            }
            acc
        })
        .collect()
}

fn mat_mat_mul(a: &FpMatrix, b: &FpMatrix, p: i128) -> FpMatrix {
    let n = a.len();
    let m = b.first().map_or(0, Vec::len);
    let mut out = vec![vec![0i128; m]; n];
    for i in 0..n {
        for (k, a_ik) in a[i].iter().enumerate() {
            if *a_ik == 0 {
                continue;
            }
            for j in 0..m {
                out[i][j] = reduce(out[i][j] + a_ik * b[k][j], p);
            }
        }
    }
    out
}

fn identity_matrix(n: usize) -> FpMatrix {
    let mut m = vec![vec![0i128; n]; n];
    for (i, row) in m.iter_mut().enumerate() {
        row[i] = 1;
    }
    m
}

fn is_identity(mat: &FpMatrix, n: usize) -> bool {
    mat.len() == n
        && mat.iter().enumerate().all(|(i, row)| {
            row.len() == n
                && row
                    .iter()
                    .enumerate()
                    .all(|(j, &v)| v == i128::from(i == j))
        })
}

fn mat_pow_mod(mat: &FpMatrix, mut exponent: u128, p: i128) -> FpMatrix {
    let n = mat.len();
    let mut result = identity_matrix(n);
    let mut base = mat.clone();
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = mat_mat_mul(&result, &base, p);
        }
        base = mat_mat_mul(&base, &base, p);
        exponent >>= 1;
    }
    result
}

/// The determinant of `matrix` mod `p`, by Gaussian elimination with partial
/// pivoting over the field `𝔽ₚ`.
///
/// `None` if `p` is not prime, `matrix` is not square, or any entry is
/// outside `0..p`.
#[must_use]
pub fn determinant_mod_p(matrix: &[Vec<i128>], p: i128) -> Option<i128> {
    if !is_prime(p) {
        return None;
    }
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return None;
    }
    if matrix
        .iter()
        .any(|row| row.iter().any(|&v| v < 0 || v >= p))
    {
        return None;
    }
    if n == 0 {
        return Some(1); // determinant of the empty matrix
    }
    let mut m: Vec<Vec<i128>> = matrix.to_vec();
    let mut det: i128 = 1;
    for col in 0..n {
        let Some(pivot_row) = (col..n).find(|&r| m[r][col] != 0) else {
            // No nonzero entry left in this column: the matrix is singular,
            // which is a valid answer (det = 0), not an invalid input.
            return Some(0);
        };
        if pivot_row != col {
            m.swap(pivot_row, col);
            det = reduce(-det, p);
        }
        let pivot = m[col][col];
        det = reduce(det * pivot, p);
        let inv = mod_inverse(pivot, p)?;
        for row in (col + 1)..n {
            let factor = reduce(m[row][col] * inv, p);
            if factor == 0 {
                continue;
            }
            for c in col..n {
                m[row][c] = reduce(m[row][c] - factor * m[col][c], p);
            }
        }
    }
    Some(det)
}

/// Every nonzero vector of `1`, or every normalized (first-nonzero-entry-is-1)
/// representative of a line of `𝔽ₚⁿ` for [`ActionKind::Projective`], as a
/// deterministic, lexicographically sorted list (`BTreeSet` insertion order).
///
/// `None` if the point count overflows or exceeds [`MAX_POINTS`].
fn enumerate_points(p: i128, n: usize, action: ActionKind) -> Option<Vec<Vec<i128>>> {
    let p_usize = usize::try_from(p).ok()?;
    let total = p_usize.checked_pow(u32::try_from(n).ok()?)?;
    if total == 0 {
        return None;
    }
    let mut set: BTreeSet<Vec<i128>> = BTreeSet::new();
    for idx in 0..total {
        let mut v = vec![0i128; n];
        let mut rem = idx;
        for slot in v.iter_mut().rev() {
            *slot = i128::try_from(rem % p_usize).ok()?;
            rem /= p_usize;
        }
        if v.iter().all(|&x| x == 0) {
            continue; // the zero vector is not a point of either action
        }
        let point = match action {
            ActionKind::Vector => v,
            ActionKind::Projective => normalize_projective(&v, p)?,
        };
        set.insert(point);
        if set.len() > MAX_POINTS {
            return None;
        }
    }
    Some(set.into_iter().collect())
}

/// Normalizes `v` (assumed nonzero) to the canonical representative of its
/// line: scale so the first nonzero entry becomes `1`.
fn normalize_projective(v: &[i128], p: i128) -> Option<Vec<i128>> {
    let (idx, &entry) = v.iter().enumerate().find(|&(_, &x)| x != 0)?;
    let inv = mod_inverse(entry, p)?;
    let mut out: Vec<i128> = v.iter().map(|&x| reduce(x * inv, p)).collect();
    out[idx] = 1; // exact, avoids a rounding artifact from the modular multiply
    Some(out)
}

// ---------------------------------------------------------------------------
// ActionCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate that `generator_images` is exactly the
/// permutation each of `generators` induces on `points`, under `action`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionCertificate {
    /// The prime.
    pub p: i128,
    /// The dimension.
    pub n: usize,
    /// Which action.
    pub action: ActionKind,
    /// The enumeration of points (vectors or normalized projective
    /// representatives), in the deterministic lexicographic order that
    /// [`Permutation`] indices in `generator_images` refer to.
    pub points: Vec<Vec<i128>>,
    /// The original generator matrices.
    pub generators: Vec<FpMatrix>,
    /// `generator_images[i]` is the permutation of `0..points.len()` that
    /// `generators[i]` induces on `points`.
    pub generator_images: Vec<Permutation>,
}

/// Why an [`ActionCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActionCertificateFailure {
    /// `p` is not prime.
    NotPrime,
    /// `n == 0`.
    InvalidDimension,
    /// The independently re-enumerated point list does not match `points`
    /// (wrong count, wrong order, or a point that isn't actually on the
    /// variety this action ranges over).
    PointsMismatch,
    /// `generators.len() != generator_images.len()`.
    GeneratorCountMismatch,
    /// A generator failed basic validation (wrong shape or an out-of-range
    /// entry).
    InvalidGeneratorMatrix {
        /// Index into the generator list.
        generator_index: usize,
    },
    /// A generator's determinant mod `p` is `0`.
    SingularGenerator {
        /// Index into the generator list.
        generator_index: usize,
    },
    /// The recomputed image of `generators[generator_index]` on `points` is
    /// not a bijection (never observed for an invertible generator; see
    /// [`MatrixGroupError::ActionNotBijective`]).
    ActionNotBijective {
        /// Index into the generator list.
        generator_index: usize,
    },
    /// The recomputed permutation for `generator_index` does not match the
    /// certificate's claimed `generator_images[generator_index]`.
    ImageMismatch {
        /// Index into the generator list.
        generator_index: usize,
    },
}

impl ActionCertificate {
    /// Independently re-derives every claim this certificate makes:
    /// re-enumerates the points from `(p, n, action)` alone, re-validates
    /// and re-checks invertibility of every generator, and recomputes every
    /// generator's permutation image by matrix–vector multiplication,
    /// comparing each to the stored claim.
    ///
    /// # Errors
    ///
    /// Returns the first [`ActionCertificateFailure`] guard that does not
    /// hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), ActionCertificateFailure> {
        if !is_prime(self.p) {
            return Err(ActionCertificateFailure::NotPrime);
        }
        if self.n == 0 {
            return Err(ActionCertificateFailure::InvalidDimension);
        }
        let expected_points = enumerate_points(self.p, self.n, self.action)
            .ok_or(ActionCertificateFailure::PointsMismatch)?;
        if expected_points != self.points {
            return Err(ActionCertificateFailure::PointsMismatch);
        }
        if self.generators.len() != self.generator_images.len() {
            return Err(ActionCertificateFailure::GeneratorCountMismatch);
        }
        let index: BTreeMap<&Vec<i128>, usize> = self
            .points
            .iter()
            .enumerate()
            .map(|(i, pt)| (pt, i))
            .collect();
        for (gi, mat) in self.generators.iter().enumerate() {
            validate_matrix(self.p, self.n, gi, mat).map_err(|_| {
                ActionCertificateFailure::InvalidGeneratorMatrix {
                    generator_index: gi,
                }
            })?;
            let det = determinant_mod_p(mat, self.p).ok_or(
                ActionCertificateFailure::InvalidGeneratorMatrix {
                    generator_index: gi,
                },
            )?;
            if det == 0 {
                return Err(ActionCertificateFailure::SingularGenerator {
                    generator_index: gi,
                });
            }
            let mut images = Vec::with_capacity(self.points.len());
            for point in &self.points {
                let raw = mat_vec_mul(mat, point, self.p);
                let mapped = match self.action {
                    ActionKind::Vector => Some(raw),
                    ActionKind::Projective => normalize_projective(&raw, self.p),
                };
                let mapped = mapped.ok_or(ActionCertificateFailure::ActionNotBijective {
                    generator_index: gi,
                })?;
                let target =
                    *index
                        .get(&mapped)
                        .ok_or(ActionCertificateFailure::ActionNotBijective {
                            generator_index: gi,
                        })?;
                images.push(target);
            }
            let recomputed = Permutation::from_images(images).ok_or(
                ActionCertificateFailure::ActionNotBijective {
                    generator_index: gi,
                },
            )?;
            if recomputed != self.generator_images[gi] {
                return Err(ActionCertificateFailure::ImageMismatch {
                    generator_index: gi,
                });
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// MatrixGroup
// ---------------------------------------------------------------------------

/// A finite matrix group over `𝔽ₚ`, encoded as a certified permutation
/// group by its action on vectors ([`ActionKind::Vector`]) or lines
/// ([`ActionKind::Projective`]) of `𝔽ₚⁿ`.
#[derive(Clone, Debug)]
pub struct MatrixGroup {
    action_certificate: ActionCertificate,
    permutation_group: PermutationGroup,
}

impl MatrixGroup {
    fn build(
        p: i128,
        n: usize,
        generators: Vec<FpMatrix>,
        action: ActionKind,
    ) -> Result<MatrixGroup, MatrixGroupError> {
        if !is_prime(p) {
            return Err(MatrixGroupError::InvalidPrime);
        }
        if n == 0 {
            return Err(MatrixGroupError::InvalidDimension);
        }
        for (gi, mat) in generators.iter().enumerate() {
            validate_matrix(p, n, gi, mat)?;
            let det = determinant_mod_p(mat, p).ok_or(MatrixGroupError::InvalidPrime)?;
            if det == 0 {
                return Err(MatrixGroupError::SingularGenerator {
                    generator_index: gi,
                    determinant: det,
                });
            }
        }
        let points = enumerate_points(p, n, action).ok_or(MatrixGroupError::TooManyPoints {
            p,
            n,
            action,
        })?;
        let index: BTreeMap<&Vec<i128>, usize> =
            points.iter().enumerate().map(|(i, pt)| (pt, i)).collect();
        let mut generator_images = Vec::with_capacity(generators.len());
        for (gi, mat) in generators.iter().enumerate() {
            let mut images = Vec::with_capacity(points.len());
            for point in &points {
                let raw = mat_vec_mul(mat, point, p);
                let mapped = match action {
                    ActionKind::Vector => Some(raw),
                    ActionKind::Projective => normalize_projective(&raw, p),
                };
                let mapped = mapped.ok_or(MatrixGroupError::ActionNotBijective {
                    generator_index: gi,
                })?;
                let target = *index
                    .get(&mapped)
                    .ok_or(MatrixGroupError::ActionNotBijective {
                        generator_index: gi,
                    })?;
                images.push(target);
            }
            let perm =
                Permutation::from_images(images).ok_or(MatrixGroupError::ActionNotBijective {
                    generator_index: gi,
                })?;
            generator_images.push(perm);
        }
        let degree = points.len();
        let action_certificate = ActionCertificate {
            p,
            n,
            action,
            points,
            generators,
            generator_images: generator_images.clone(),
        };
        let permutation_group = PermutationGroup::from_generators(generator_images, degree)
            .expect("every generator image has length `degree` by construction");
        Ok(MatrixGroup {
            action_certificate,
            permutation_group,
        })
    }

    /// Builds the matrix group generated by `generators` (each an `n × n`
    /// matrix over `𝔽ₚ`, entries in `0..p`), via its faithful action on the
    /// nonzero vectors of `𝔽ₚⁿ` — see the module doc for why this action is
    /// faithful for all of `GL(n, p)`.
    ///
    /// # Errors
    ///
    /// See [`MatrixGroupError`]: a non-prime `p`, `n == 0`, a malformed or
    /// singular generator, or a point count exceeding [`MAX_POINTS`].
    pub fn from_generators(
        p: i128,
        n: usize,
        generators: Vec<FpMatrix>,
    ) -> Result<MatrixGroup, MatrixGroupError> {
        Self::build(p, n, generators, ActionKind::Vector)
    }

    /// Builds the matrix group generated by `generators` via its action on
    /// the lines (projective points) of `𝔽ₚⁿ`. Feeding `SL(n, p)`
    /// generators produces `PSL(n, p)`; feeding `GL(n, p)` generators
    /// produces `PGL(n, p)` — see the module doc for why.
    ///
    /// # Errors
    ///
    /// Same as [`Self::from_generators`].
    pub fn from_generators_projective(
        p: i128,
        n: usize,
        generators: Vec<FpMatrix>,
    ) -> Result<MatrixGroup, MatrixGroupError> {
        Self::build(p, n, generators, ActionKind::Projective)
    }

    /// The prime `p`.
    #[must_use]
    pub fn p(&self) -> i128 {
        self.action_certificate.p
    }

    /// The dimension `n`.
    #[must_use]
    pub fn n(&self) -> usize {
        self.action_certificate.n
    }

    /// Which action this group was built with.
    #[must_use]
    pub fn action(&self) -> ActionKind {
        self.action_certificate.action
    }

    /// The certificate for the matrix-to-permutation encoding.
    #[must_use]
    pub fn action_certificate(&self) -> &ActionCertificate {
        &self.action_certificate
    }

    /// The certified permutation group this matrix group was encoded as —
    /// every [`crate::permgroup`] operation (order, membership, orbits,
    /// Sylow, conjugacy classes, isomorphism, presentations, …) applies to
    /// it unchanged.
    #[must_use]
    pub fn permutation_group(&self) -> &PermutationGroup {
        &self.permutation_group
    }

    /// The group's order, as claimed by its permutation group's own
    /// [`crate::permgroup::OrderCertificate`] (Schreier–Sims; not
    /// enumeration-bounded).
    #[must_use]
    pub fn order(&self) -> u128 {
        self.permutation_group.order()
    }

    /// A certificate for the general/special distinction: whether every
    /// generator has determinant `1` mod `p` (in which case the group they
    /// generate is contained in `SL(n, p)`, since determinant-1 matrices are
    /// closed under multiplication and inversion).
    #[must_use]
    pub fn special_certificate(&self) -> SpecialCertificate {
        let determinants: Vec<i128> = self
            .action_certificate
            .generators
            .iter()
            .map(|g| {
                determinant_mod_p(g, self.action_certificate.p)
                    .expect("generators were validated invertible at construction")
            })
            .collect();
        let is_special = determinants.iter().all(|&d| d == 1);
        SpecialCertificate {
            p: self.action_certificate.p,
            generators: self.action_certificate.generators.clone(),
            determinants,
            is_special,
        }
    }

    /// Whether every generator has determinant `1` mod `p` (see
    /// [`Self::special_certificate`]).
    #[must_use]
    pub fn is_special(&self) -> bool {
        self.special_certificate().is_special
    }
}

// ---------------------------------------------------------------------------
// SpecialCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for [`MatrixGroup::is_special`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecialCertificate {
    /// The prime.
    pub p: i128,
    /// The generators, in the same order as `determinants`.
    pub generators: Vec<FpMatrix>,
    /// `determinants[i]` is the determinant of `generators[i]` mod `p`.
    pub determinants: Vec<i128>,
    /// Whether every determinant is `1`.
    pub is_special: bool,
}

/// Why a [`SpecialCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecialFailure {
    /// `generators.len() != determinants.len()`.
    LengthMismatch,
    /// A recomputed determinant does not match the claim at that index.
    DeterminantMismatch {
        /// Index into the generator list.
        generator_index: usize,
    },
    /// The recomputed `is_special` (every determinant `== 1`) does not
    /// match the claim.
    ClassificationMismatch,
}

impl SpecialCertificate {
    /// Independently re-derives every claim: recomputes each generator's
    /// determinant mod `p` from scratch and recomputes `is_special` from
    /// those determinants.
    ///
    /// # Errors
    ///
    /// Returns the first [`SpecialFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), SpecialFailure> {
        if self.generators.len() != self.determinants.len() {
            return Err(SpecialFailure::LengthMismatch);
        }
        for (gi, (mat, &claimed)) in self
            .generators
            .iter()
            .zip(self.determinants.iter())
            .enumerate()
        {
            let recomputed =
                determinant_mod_p(mat, self.p).ok_or(SpecialFailure::DeterminantMismatch {
                    generator_index: gi,
                })?;
            if recomputed != claimed {
                return Err(SpecialFailure::DeterminantMismatch {
                    generator_index: gi,
                });
            }
        }
        let expected = self.determinants.iter().all(|&d| d == 1);
        if expected != self.is_special {
            return Err(SpecialFailure::ClassificationMismatch);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// ElementOrderCertificate / order_of_element
// ---------------------------------------------------------------------------

/// A checkable certificate for the order of a single matrix, cross-checked
/// two independent ways.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElementOrderCertificate {
    /// The prime.
    pub p: i128,
    /// The dimension.
    pub n: usize,
    /// The matrix.
    pub matrix: FpMatrix,
    /// The enumeration of nonzero vectors of `𝔽ₚⁿ` (the faithful vector
    /// action is always used here, never the projective one, precisely
    /// because faithfulness is what makes the permutation's order equal the
    /// matrix's order).
    pub points: Vec<Vec<i128>>,
    /// The permutation `matrix` induces on `points`.
    pub permutation: Permutation,
    /// The claimed order.
    pub claimed_order: u128,
}

/// Why an [`ElementOrderCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElementOrderFailure {
    /// `p` is not prime.
    NotPrime,
    /// The matrix is malformed or has an out-of-range entry.
    InvalidMatrix,
    /// The matrix's determinant mod `p` is `0`.
    Singular,
    /// The re-enumerated point list does not match `points`.
    PointsMismatch,
    /// The recomputed permutation does not match `permutation`.
    PermutationMismatch,
    /// `permutation.order()` does not match `claimed_order`.
    PermutationOrderMismatch {
        /// The permutation's own (independently recomputed) order.
        expected: u128,
    },
    /// Direct repeated modular matrix multiplication does not confirm
    /// `matrix^claimed_order == I`.
    RepeatedMultiplicationMismatch,
    /// `matrix^(claimed_order / q) == I` for some prime `q | claimed_order`,
    /// so `claimed_order` is not minimal.
    NotMinimal {
        /// The prime factor for which the smaller power was already the
        /// identity.
        prime_factor: i128,
    },
}

impl ElementOrderCertificate {
    /// Independently re-derives every claim this certificate makes: re-runs
    /// every [`ActionCertificate`]-style validation on `matrix` (primality,
    /// shape, range, invertibility), re-enumerates `points`, recomputes
    /// `permutation` from scratch and compares, re-derives its order via
    /// [`Permutation::order`] (path 1), and independently confirms
    /// minimality via direct repeated modular matrix multiplication (path
    /// 2) — `matrix^claimed_order == I` and `matrix^(claimed_order / q) !=
    /// I` for every prime `q` dividing `claimed_order`.
    ///
    /// # Errors
    ///
    /// Returns the first [`ElementOrderFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), ElementOrderFailure> {
        if !is_prime(self.p) {
            return Err(ElementOrderFailure::NotPrime);
        }
        validate_matrix(self.p, self.n, 0, &self.matrix)
            .map_err(|_| ElementOrderFailure::InvalidMatrix)?;
        let det =
            determinant_mod_p(&self.matrix, self.p).ok_or(ElementOrderFailure::InvalidMatrix)?;
        if det == 0 {
            return Err(ElementOrderFailure::Singular);
        }
        let expected_points = enumerate_points(self.p, self.n, ActionKind::Vector)
            .ok_or(ElementOrderFailure::PointsMismatch)?;
        if expected_points != self.points {
            return Err(ElementOrderFailure::PointsMismatch);
        }
        let index: BTreeMap<&Vec<i128>, usize> = self
            .points
            .iter()
            .enumerate()
            .map(|(i, pt)| (pt, i))
            .collect();
        let mut images = Vec::with_capacity(self.points.len());
        for point in &self.points {
            let raw = mat_vec_mul(&self.matrix, point, self.p);
            let target = *index
                .get(&raw)
                .ok_or(ElementOrderFailure::PermutationMismatch)?;
            images.push(target);
        }
        let recomputed =
            Permutation::from_images(images).ok_or(ElementOrderFailure::PermutationMismatch)?;
        if recomputed != self.permutation {
            return Err(ElementOrderFailure::PermutationMismatch);
        }
        // Path 1: the permutation's own order.
        let perm_order = self
            .permutation
            .order()
            .expect("a permutation of a finite set has a finite order");
        if perm_order != self.claimed_order {
            return Err(ElementOrderFailure::PermutationOrderMismatch {
                expected: perm_order,
            });
        }
        // Path 2: direct repeated modular matrix multiplication, sharing no
        // code with `Permutation::order`.
        let full_power = mat_pow_mod(&self.matrix, self.claimed_order, self.p);
        if !is_identity(&full_power, self.n) {
            return Err(ElementOrderFailure::RepeatedMultiplicationMismatch);
        }
        let order_i128 =
            i128::try_from(self.claimed_order).map_err(|_| ElementOrderFailure::InvalidMatrix)?;
        for (prime, _) in factorize(order_i128) {
            let reduced = self.claimed_order / u128::try_from(prime).unwrap_or(1);
            if reduced == 0 {
                continue;
            }
            let partial_power = mat_pow_mod(&self.matrix, reduced, self.p);
            if is_identity(&partial_power, self.n) {
                return Err(ElementOrderFailure::NotMinimal {
                    prime_factor: prime,
                });
            }
        }
        Ok(())
    }
}

/// Computes the order of `matrix` (an `n × n` matrix over `𝔽ₚ`) via its
/// permutation on the nonzero vectors of `𝔽ₚⁿ` (faithful, so the
/// permutation's order is exactly the matrix's order), cross-checked by
/// direct repeated modular matrix multiplication.
///
/// # Errors
///
/// See [`MatrixGroupError`]: a non-prime `p`, `n == 0`, a malformed or
/// singular matrix, or a point count exceeding [`MAX_POINTS`].
pub fn order_of_element(
    p: i128,
    n: usize,
    matrix: FpMatrix,
) -> Result<ElementOrderCertificate, MatrixGroupError> {
    if !is_prime(p) {
        return Err(MatrixGroupError::InvalidPrime);
    }
    if n == 0 {
        return Err(MatrixGroupError::InvalidDimension);
    }
    validate_matrix(p, n, 0, &matrix)?;
    let det = determinant_mod_p(&matrix, p).ok_or(MatrixGroupError::InvalidPrime)?;
    if det == 0 {
        return Err(MatrixGroupError::SingularGenerator {
            generator_index: 0,
            determinant: det,
        });
    }
    let points =
        enumerate_points(p, n, ActionKind::Vector).ok_or(MatrixGroupError::TooManyPoints {
            p,
            n,
            action: ActionKind::Vector,
        })?;
    let index: BTreeMap<&Vec<i128>, usize> =
        points.iter().enumerate().map(|(i, pt)| (pt, i)).collect();
    let mut images = Vec::with_capacity(points.len());
    for point in &points {
        let raw = mat_vec_mul(&matrix, point, p);
        let target = *index
            .get(&raw)
            .ok_or(MatrixGroupError::ActionNotBijective { generator_index: 0 })?;
        images.push(target);
    }
    let permutation = Permutation::from_images(images)
        .ok_or(MatrixGroupError::ActionNotBijective { generator_index: 0 })?;
    let claimed_order = permutation
        .order()
        .expect("a permutation of a finite set has a finite order");
    Ok(ElementOrderCertificate {
        p,
        n,
        matrix,
        points,
        permutation,
        claimed_order,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::permgroup::{IsomorphismDecision, NonIsomorphismReason, distinguish, isomorphism};
    use std::time::{Duration, Instant};

    fn assert_under_5s(start: Instant, label: &str) {
        let elapsed = start.elapsed();
        assert!(
            elapsed < Duration::from_secs(5),
            "{label} took {elapsed:?}, over the 5s single-threaded debug budget"
        );
    }

    // Two transvections generate SL(2, p) for any prime p (standard fact:
    // elementary transvections generate SL(n, K)); this is also verified
    // computationally below by checking the resulting order against the
    // classical formula |SL(2, p)| = p(p^2 - 1).
    fn sl2_transvections(_p: i128) -> Vec<FpMatrix> {
        vec![
            vec![vec![1, 1], vec![0, 1]], // E12(1)
            vec![vec![1, 0], vec![1, 1]], // E21(1)
        ]
    }

    // A primitive root mod p, for the small primes this module's tests use.
    fn primitive_root(p: i128) -> i128 {
        match p {
            3 => 2,
            5 => 2,
            7 => 3,
            _ => panic!("no primitive root tabulated for p = {p}"),
        }
    }

    // GL(2, p) generators: the two SL(2, p) transvections plus diag(g, 1)
    // for a primitive root g, which has determinant g (a generator of
    // F_p*); SL(2,p) is normal with GL/SL cyclic of order p-1 generated by
    // det, so this set generates all of GL(2, p) (see the module doc).
    fn gl2_generators(p: i128) -> Vec<FpMatrix> {
        let mut gens = sl2_transvections(p);
        gens.push(vec![vec![primitive_root(p), 0], vec![0, 1]]);
        gens
    }

    // All six elementary transvections E_ij(1), i != j, on 3 points --
    // these generate SL(3, p) = GL(3, 2) at p = 2 (the only unit is 1).
    fn gl3_f2_generators() -> Vec<FpMatrix> {
        let mut gens = Vec::new();
        for i in 0..3usize {
            for j in 0..3usize {
                if i == j {
                    continue;
                }
                let mut m = identity_matrix(3);
                m[i][j] = 1;
                gens.push(m);
            }
        }
        gens
    }

    fn a5_on_five_points() -> PermutationGroup {
        let five_cycle = Permutation::from_images(vec![1, 2, 3, 4, 0]).unwrap();
        let three_cycle = Permutation::from_images(vec![1, 2, 0, 3, 4]).unwrap();
        PermutationGroup::from_generators(vec![five_cycle, three_cycle], 5).unwrap()
    }

    // D_12 (order 24, symmetries of a regular 12-gon): rotation r (a
    // 12-cycle) and reflection s.
    fn d12() -> PermutationGroup {
        let r = Permutation::from_images((1..12).chain(std::iter::once(0)).collect()).unwrap();
        let s = Permutation::from_images((0..12).map(|i| (12 - i) % 12).collect()).unwrap();
        PermutationGroup::from_generators(vec![r, s], 12).unwrap()
    }

    #[test]
    fn gl2_f3_order_is_48() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators(3, 2, gl2_generators(3)).unwrap();
        assert_eq!(g.order(), 48);
        g.action_certificate().verify().unwrap();
        g.permutation_group().order_certificate().verify().unwrap();
        assert_under_5s(start, "gl2_f3_order_is_48");
    }

    #[test]
    fn sl2_f3_order_is_24() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators(3, 2, sl2_transvections(3)).unwrap();
        assert_eq!(g.order(), 24);
        assert!(g.is_special());
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "sl2_f3_order_is_24");
    }

    #[test]
    fn gl2_f5_order_is_480() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators(5, 2, gl2_generators(5)).unwrap();
        // Classical formula: |GL(2, q)| = (q^2 - 1)(q^2 - q).
        assert_eq!(g.order(), (25 - 1) * (25 - 5));
        assert_eq!(g.order(), 480);
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "gl2_f5_order_is_480");
    }

    #[test]
    fn sl2_f5_order_is_120() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators(5, 2, sl2_transvections(5)).unwrap();
        // Classical formula: |SL(2, q)| = q(q^2 - 1).
        assert_eq!(g.order(), 5 * (25 - 1));
        assert_eq!(g.order(), 120);
        assert!(g.is_special());
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "sl2_f5_order_is_120");
    }

    #[test]
    fn gl3_f2_order_is_168() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators(2, 3, gl3_f2_generators()).unwrap();
        // Classical formula: |GL(n, q)| = prod_{i=0}^{n-1} (q^n - q^i).
        let classical: u128 = (0..3u32).map(|i| (8 - 2i128.pow(i)) as u128).product();
        assert_eq!(g.order(), classical);
        assert_eq!(g.order(), 168);
        // Over F2 the only unit is 1, so GL(3, 2) = SL(3, 2).
        assert!(g.is_special());
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "gl3_f2_order_is_168");
    }

    #[test]
    fn psl2_f5_order_is_60() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators_projective(5, 2, sl2_transvections(5)).unwrap();
        // |PSL(2, 5)| = |SL(2, 5)| / |{+-I} ∩ SL| = 120 / 2.
        assert_eq!(g.order(), 60);
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "psl2_f5_order_is_60");
    }

    #[test]
    fn psl2_f5_isomorphic_to_a5() {
        let start = Instant::now();
        let psl = MatrixGroup::from_generators_projective(5, 2, sl2_transvections(5)).unwrap();
        let a5 = a5_on_five_points();
        // A generating claim needs its own check: a 5-cycle and a 3-cycle
        // on 5 points, both even, generate a subgroup of A5 -- confirm it
        // is all of A5 (order 60), not some proper subgroup, before using
        // it as the isomorphism target.
        assert_eq!(a5.order(), 60);
        assert_eq!(psl.order(), a5.order());
        match isomorphism(psl.permutation_group(), &a5) {
            IsomorphismDecision::Isomorphic(cert) => cert.verify().unwrap(),
            other => panic!("expected PSL(2,5) isomorphic to A5, got {other:?}"),
        }
        assert_under_5s(start, "psl2_f5_isomorphic_to_a5");
    }

    #[test]
    fn psl2_f7_order_is_168() {
        let start = Instant::now();
        let g = MatrixGroup::from_generators_projective(7, 2, sl2_transvections(7)).unwrap();
        // |PSL(2, 7)| = |SL(2, 7)| / 2 = (7 * 48) / 2.
        assert_eq!(g.order(), 7 * (49 - 1) / 2);
        assert_eq!(g.order(), 168);
        g.action_certificate().verify().unwrap();
        assert_under_5s(start, "psl2_f7_order_is_168");
    }

    #[test]
    fn psl2_f7_isomorphic_to_gl3_f2() {
        let start = Instant::now();
        let psl = MatrixGroup::from_generators_projective(7, 2, sl2_transvections(7)).unwrap();
        let gl32 = MatrixGroup::from_generators(2, 3, gl3_f2_generators()).unwrap();
        assert_eq!(psl.order(), gl32.order());
        match isomorphism(psl.permutation_group(), gl32.permutation_group()) {
            IsomorphismDecision::Isomorphic(cert) => cert.verify().unwrap(),
            other => panic!("expected PSL(2,7) isomorphic to GL(3,2), got {other:?}"),
        }
        assert_under_5s(start, "psl2_f7_isomorphic_to_gl3_f2");
    }

    #[test]
    fn sl2_f3_not_isomorphic_to_d12() {
        let start = Instant::now();
        let sl23 = MatrixGroup::from_generators(3, 2, sl2_transvections(3)).unwrap();
        let d12 = d12();
        assert_eq!(sl23.order(), d12.order());
        assert_eq!(sl23.order(), 24);
        match isomorphism(sl23.permutation_group(), &d12) {
            IsomorphismDecision::NotIsomorphic(reason) => match *reason {
                NonIsomorphismReason::Invariants(cert) => {
                    cert.verify().unwrap();
                    assert!(
                        cert.difference.is_some(),
                        "same-order groups must differ somewhere to be distinguished by invariants alone"
                    );
                }
                NonIsomorphismReason::ExhaustedSearch(_) => {
                    panic!(
                        "expected SL(2,3) vs D12 to be distinguished by invariants alone, not by exhaustive search"
                    )
                }
            },
            other => panic!("expected SL(2,3) not isomorphic to D12, got {other:?}"),
        }
        // Same check via distinguish() directly, reusing the exact route
        // isomorphism() itself takes.
        let cert = distinguish(sl23.permutation_group(), &d12).unwrap();
        cert.verify().unwrap();
        assert!(cert.difference.is_some());
        assert_under_5s(start, "sl2_f3_not_isomorphic_to_d12");
    }

    #[test]
    fn determinant_mod_p_matches_hand_computation() {
        // det([[2, 3], [1, 4]]) = 8 - 3 = 5 = 0 mod 5, and = 5 mod 7.
        let m = vec![vec![2, 3], vec![1, 4]];
        assert_eq!(determinant_mod_p(&m, 7), Some(5));
        assert_eq!(determinant_mod_p(&m, 5), Some(0));
        // det(I_3) = 1 for any prime.
        assert_eq!(determinant_mod_p(&identity_matrix(3), 5), Some(1));
    }

    #[test]
    fn order_of_element_matches_matrix_power() {
        let start = Instant::now();
        // E12(1) = [[1,1],[0,1]] over F5 has order 5 (it's a transvection;
        // (E12(1))^k = [[1,k],[0,1]], identity first at k = 5).
        let m = vec![vec![1, 1], vec![0, 1]];
        let cert = order_of_element(5, 2, m).unwrap();
        assert_eq!(cert.claimed_order, 5);
        cert.verify().unwrap();
        assert_under_5s(start, "order_of_element_matches_matrix_power");
    }

    #[test]
    fn singular_generator_refused_by_determinant() {
        // [[1,1],[1,1]] has determinant 0 mod any prime.
        let m = vec![vec![1, 1], vec![1, 1]];
        match MatrixGroup::from_generators(5, 2, vec![m]) {
            Err(MatrixGroupError::SingularGenerator {
                generator_index: 0,
                determinant: 0,
            }) => {}
            other => panic!("expected SingularGenerator, got {other:?}"),
        }
    }

    #[test]
    fn non_square_generator_refused() {
        let m = vec![vec![1, 0, 0], vec![0, 1, 0]]; // 2x3, not square
        match MatrixGroup::from_generators(5, 2, vec![m]) {
            Err(MatrixGroupError::DimensionMismatch {
                generator_index: 0, ..
            }) => {}
            other => panic!("expected DimensionMismatch, got {other:?}"),
        }
    }

    #[test]
    fn entry_out_of_range_refused() {
        let m = vec![vec![1, 0], vec![0, 5]]; // 5 is out of range for p = 5
        match MatrixGroup::from_generators(5, 2, vec![m]) {
            Err(MatrixGroupError::EntryOutOfRange {
                generator_index: 0, ..
            }) => {}
            other => panic!("expected EntryOutOfRange, got {other:?}"),
        }
    }

    #[test]
    fn non_prime_modulus_refused() {
        let m = vec![vec![1, 1], vec![0, 1]];
        match MatrixGroup::from_generators(4, 2, vec![m]) {
            Err(MatrixGroupError::InvalidPrime) => {}
            other => panic!("expected InvalidPrime, got {other:?}"),
        }
    }

    #[test]
    fn forged_action_certificate_with_wrong_image_rejected() {
        let g = MatrixGroup::from_generators(3, 2, sl2_transvections(3)).unwrap();
        let mut forged = g.action_certificate().clone();
        // Swap two entries of the first generator's image permutation --
        // still a valid bijection (so `Permutation::from_images` accepts
        // it), but no longer the true image of matrix-vector multiplication.
        let perm = &forged.generator_images[0];
        let mut swapped: Vec<usize> = (0..perm.len()).map(|i| perm.apply(i).unwrap()).collect();
        swapped.swap(0, 1);
        forged.generator_images[0] = Permutation::from_images(swapped).unwrap();
        match forged.verify() {
            Err(ActionCertificateFailure::ImageMismatch { generator_index: 0 }) => {}
            other => panic!("expected ImageMismatch, got {other:?}"),
        }
    }

    #[test]
    fn forged_action_certificate_smuggling_singular_generator_rejected() {
        let g = MatrixGroup::from_generators(3, 2, sl2_transvections(3)).unwrap();
        let mut forged = g.action_certificate().clone();
        // Smuggle in a singular matrix as the first generator, keeping its
        // (now-meaningless) claimed image permutation unchanged.
        forged.generators[0] = vec![vec![1, 1], vec![1, 1]];
        match forged.verify() {
            Err(ActionCertificateFailure::SingularGenerator { generator_index: 0 }) => {}
            other => panic!("expected SingularGenerator, got {other:?}"),
        }
    }

    #[test]
    fn group_above_permgroup_bound_declines_without_hanging() {
        let start = Instant::now();
        // GL(2, 7): order (49-1)(49-7) = 48 * 42 = 2016, over
        // DERIVED_SUBGROUP_ENUMERATION_BOUND (2000) that invariants() (and
        // hence distinguish()/isomorphism()) uses, but order() itself needs
        // no enumeration at all and stays cheap.
        let g = MatrixGroup::from_generators(7, 2, gl2_generators(7)).unwrap();
        assert_eq!(g.order(), 2016);
        match g.permutation_group().invariants() {
            Err(crate::permgroup::PermgroupError::TooLarge { bound, actual }) => {
                assert_eq!(bound, 2000);
                assert_eq!(actual, 2016);
            }
            other => panic!("expected TooLarge, got {other:?}"),
        }
        assert_under_5s(
            start,
            "group_above_permgroup_bound_declines_without_hanging",
        );
    }

    #[test]
    fn too_many_points_refused_without_hanging() {
        let start = Instant::now();
        // p = 101, n = 2: 101^2 - 1 = 10200 nonzero vectors, over
        // MAX_POINTS (5000).
        match MatrixGroup::from_generators(101, 2, vec![identity_matrix(2)]) {
            Err(MatrixGroupError::TooManyPoints { p: 101, n: 2, .. }) => {}
            other => panic!("expected TooManyPoints, got {other:?}"),
        }
        assert_under_5s(start, "too_many_points_refused_without_hanging");
    }
}
