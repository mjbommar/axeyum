//! `psatz` — a **Positivstellensatz producer**: it searches for a
//! sum-of-squares certificate of a polynomial inequality and, when it finds
//! one, **emits a kernel proof term**.
//!
//! This is the fifth tactic-layer producer in the sense of
//! [ADR-0601](../../../docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
//! after `linarith` (ADR-1576), `ring` (ADR-1582), `decide` and `simp`:
//! untrusted search (here a rational LDLᵀ factorization of a Gram matrix),
//! trusted checking ([`Kernel::add_declaration`](crate::Kernel::add_declaration)).
//! It adds **no** trusted surface of its own: the returned `ExprId` is an
//! unchecked term the caller pushes through the kernel exactly as it pushes a
//! hand-written one, and every step of the emitted term is an application of a
//! theorem the carrier's prelude already proved.
//!
//! ## What "producer" buys over the existing SOS route
//!
//! `axeyum-solver`'s `reconstruct_sos_proof` is a **refutation** route: it takes
//! an asserted `p < 0` and builds `False`. It is measured, it works, and exactly
//! one of its shapes (`x*x < 0`) reaches `Kernel::add_declaration` today, through
//! `generalize_over_ordered_ring`. A *producer* is the other direction: it takes
//! the POSITIVE goal `a ≤ b` and returns a proof of it, so the result is a
//! theorem a library can cite rather than a discharged contradiction. See
//! ADR-1649 for the measurement that motivated the split.
//!
//! ## Contract
//!
//! - **Input**: a goal `Rat.le lhs rhs` (see [`rat`]; the ℚ carrier is the one
//!   this module instantiates — see that module's docs for why ℚ and not
//!   `CReal`), plus zero or more hypotheses `Rat.le Rat.zero hᵢ`.
//! - **Output**: `Ok(ExprId)` — an unchecked proof term of that goal — or
//!   `Err(`[`Decline`]`)`, a *typed refusal* naming what the producer could not
//!   do. A `Decline` never asserts the goal is false, with the two documented
//!   exceptions [`Decline::NotPsd`] and [`Decline::PsdNotSos`], which are
//!   positive findings the search establishes (see their own docs).
//!
//! ## The search, and its completeness boundary
//!
//! For a goal whose difference `rhs − lhs` is a polynomial of **total degree
//! ≤ 2**, the search is COMPLETE: a quadratic form's Gram matrix over the affine
//! basis `(1, x₁, …, xₙ)` is unique, `p` is a sum of squares of rational affine
//! forms **iff** that matrix is positive semidefinite, and rational LDLᵀ decides
//! PSD-ness exactly (see [`Psd::factor`]). A negative pivot is therefore not a
//! decline but a *finding*: the goal is false, and [`Decline::NotPsd`] says so.
//!
//! Above degree 2 the Gram matrix is no longer unique — the search would be a
//! semidefinite program over the free directions, which this producer does not
//! implement — so it declines [`Decline::DegreeUnsupported`] **unless** the
//! caller supplies a [`DualWitness`], a moment functional that the producer
//! VERIFIES and which, when it verifies, proves the goal's difference is not a
//! sum of squares at that degree ([`Decline::PsdNotSos`]). That is the honest
//! shape of the Motzkin case: the repository's CAS holds the witness, the
//! producer holds the check, and neither holds a claim it did not establish.
//!
//! ## Rational weights, and why a SCALE appears in the certificate
//!
//! LDLᵀ produces `p = Σ dₖ ℓₖ²` with *rational* `dₖ > 0` and rational `ℓₖ`. The
//! ring producer that proves the certificate's identity
//! ([`crate::ring::rat`]) recognizes only the literals `{-1, 0, 1}` — a
//! rational literal in ℚ is a normalized `num/den` pair with no free structural
//! reduction, so `ring::rat` treats one as an opaque ATOM and the identity would
//! not close. The certificate therefore clears denominators: every `ℓₖ` is
//! scaled to integer coefficients and the whole identity is multiplied by one
//! positive integer `M`, leaving
//!
//! ```text
//! M · p  =  Σₖ (kₖ copies of ℓₖ′²)          kₖ ∈ ℕ₊, ℓₖ′ integer-coefficient
//! ```
//!
//! with every coefficient in `{repeated addition}` reach. The proof then divides
//! by `M` again (`rat::divide_by_scale`) using `le_or_lt` + a strict fold, so
//! the scale never reaches the statement. `a² + b² + c² ≥ ab + bc + ca` is the
//! case that forces this: its Gram matrix has half-integer off-diagonals, so no
//! unit-weight integer-form decomposition of it exists at all, and `M = 4`
//! (`4p = (2a−b−c)² + 3(b−c)²`) is not an implementation convenience.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use std::collections::BTreeMap;

pub mod rat;

#[cfg(test)]
mod tests;

/// Largest denominator-clearing scale `M` the emitter will unroll.
///
/// `M` becomes an `M`-fold repeated addition in the emitted term and an `M`-step
/// strict-inequality fold in `rat::divide_by_scale`, so it is a direct term-size
/// cost. 64 is ~16x the largest scale any covered case needs (`M = 4`, the
/// three-variable AM–GM), which makes it a threshold rather than a guess.
pub const MAX_SCALE: i128 = 64;

/// Largest absolute integer coefficient allowed inside one cleared linear form.
///
/// A coefficient `c` on a variable is emitted as `c` repeated additions
/// (`ring::rat` has no numeral-scaling reduction — see the module docs), so this
/// bounds the emitted form's width.
pub const MAX_FORM_COEFF: i128 = 8;

/// Largest total number of squares (counting multiplicity `kₖ`) in a
/// certificate.
pub const MAX_SQUARES: usize = 32;

/// Why the producer emitted no term.
///
/// Every variant is a refusal to produce, **not** a claim that the goal is
/// false — except [`Self::NotPsd`] and [`Self::PsdNotSos`], each of which is a
/// positive finding the search established and whose docs say exactly what was
/// established.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decline {
    /// The goal's head is not the carrier's `le` applied to two arguments.
    GoalNotLe,
    /// A hypothesis' shape is not `le zero h`.
    HypothesisNotNonneg,
    /// A subterm of the goal is outside the polynomial fragment
    /// (`+`, `*`, `neg`, `zero`, `one`, atoms). `Rat.sub`, `Rat.inv`,
    /// `Rat.div` and `Rat.pow` are all outside it: they are *definitions* over
    /// the primitives, and the ring producer that closes the certificate's
    /// identity does not unfold them either.
    NonPolynomial,
    /// The goal's difference has total degree `degree > 2` and no
    /// [`DualWitness`] was supplied, so the search has nothing to run: above
    /// degree 2 the Gram matrix is not unique and finding one is a semidefinite
    /// program this producer does not implement.
    DegreeUnsupported {
        /// The measured total degree of `rhs − lhs`.
        degree: usize,
    },
    /// **A finding, not a decline in the usual sense**: the difference's Gram
    /// matrix is not positive semidefinite, so `rhs − lhs` takes a strictly
    /// negative value somewhere and the goal is FALSE as a universally
    /// quantified statement. Carries the basis index whose pivot decided it.
    ///
    /// Sound because the degree-≤2 Gram matrix is unique: there is no other
    /// matrix the search could have tried.
    NotPsd {
        /// Index into the affine basis `(1, x₁, …, xₙ)` at which LDLᵀ found a
        /// negative pivot, or a zero pivot with a nonzero entry beside it.
        pivot: usize,
    },
    /// **A finding**: a supplied [`DualWitness`] VERIFIED — its moment matrix is
    /// positive semidefinite and it is strictly negative on the difference — so
    /// the difference is not a sum of squares of polynomials of the witness'
    /// half-degree. The Motzkin form is the canonical instance.
    ///
    /// This says nothing about whether the goal is TRUE: the Motzkin form is
    /// nonnegative everywhere and still not a sum of squares. That gap is
    /// exactly what this refusal reports.
    PsdNotSos,
    /// A [`DualWitness`] was supplied and did NOT verify — either its moment
    /// matrix is not PSD or it is nonnegative on the difference. Distinct from
    /// [`Self::PsdNotSos`] so an unchecked witness can never be mistaken for a
    /// checked one.
    DualWitnessInvalid,
    /// The denominator-clearing scale `M` exceeds [`MAX_SCALE`].
    ScaleTooLarge {
        /// The scale the certificate would have needed.
        scale: i128,
    },
    /// A cleared linear form carries a coefficient beyond [`MAX_FORM_COEFF`], or
    /// the certificate has more than [`MAX_SQUARES`] squares.
    CertificateTooLarge,
    /// Exact `i128` rational arithmetic overflowed during the search. Never a
    /// wrong answer: the search stops instead of wrapping.
    Overflow,
    /// The ring producer declined the certificate's identity
    /// `M·(rhs − lhs) = Σ …`. A certificate the search believes and the ring
    /// normalizer will not confirm is a refusal, never an emitted term.
    Ring(crate::ring::Decline),
}

// ---------------------------------------------------------------------------
// exact rational arithmetic
// ---------------------------------------------------------------------------

/// An exact rational over `i128`, kept in lowest terms with a positive
/// denominator.
///
/// Every operation is checked: an overflow returns `None` and the search turns
/// it into [`Decline::Overflow`]. Wrapping here would be a wrong certificate,
/// and a wrong certificate is caught by the kernel — but only after the search
/// has claimed success, which is the failure mode worth refusing outright.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Q {
    /// Numerator; carries the sign.
    num: i128,
    /// Denominator; always `> 0`.
    den: i128,
}

/// The greatest common divisor of `|a|` and `|b|`, as a non-negative `i128`.
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    // `a` is an absolute value of an `i128`, so it fits back only when it is not
    // `2^127`; that value can only arise from `i128::MIN`, which the callers'
    // own bounds exclude, and the saturating conversion keeps the function total.
    i128::try_from(a).unwrap_or(i128::MAX)
}

impl Q {
    /// `n / d` in lowest terms, or `None` when `d == 0` or the normalization
    /// overflows.
    #[must_use]
    pub fn new(n: i128, d: i128) -> Option<Self> {
        if d == 0 {
            return None;
        }
        let g = gcd(n, d);
        if g == 0 {
            return Some(Self { num: 0, den: 1 });
        }
        let (mut num, mut den) = (n.checked_div(g)?, d.checked_div(g)?);
        if den < 0 {
            num = num.checked_neg()?;
            den = den.checked_neg()?;
        }
        Some(Self { num, den })
    }

    /// The integer `n`.
    #[must_use]
    pub fn integer(n: i128) -> Self {
        Self { num: n, den: 1 }
    }

    /// `0`.
    #[must_use]
    pub fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    /// Whether this is exactly `0`.
    #[must_use]
    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    /// Whether this is strictly negative.
    #[must_use]
    pub fn is_negative(self) -> bool {
        self.num < 0
    }

    /// The numerator, in lowest terms.
    #[must_use]
    pub fn numerator(self) -> i128 {
        self.num
    }

    /// The denominator, in lowest terms; always `> 0`.
    #[must_use]
    pub fn denominator(self) -> i128 {
        self.den
    }

    /// `self + other`, or `None` on overflow.
    #[must_use]
    pub fn add(self, other: Self) -> Option<Self> {
        let n = self
            .num
            .checked_mul(other.den)?
            .checked_add(other.num.checked_mul(self.den)?)?;
        Self::new(n, self.den.checked_mul(other.den)?)
    }

    /// `self - other`, or `None` on overflow.
    #[must_use]
    pub fn sub(self, other: Self) -> Option<Self> {
        self.add(other.neg()?)
    }

    /// `self * other`, or `None` on overflow.
    #[must_use]
    pub fn mul(self, other: Self) -> Option<Self> {
        Self::new(
            self.num.checked_mul(other.num)?,
            self.den.checked_mul(other.den)?,
        )
    }

    /// `self / other`, or `None` when `other` is zero or on overflow.
    #[must_use]
    pub fn div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        Self::new(
            self.num.checked_mul(other.den)?,
            self.den.checked_mul(other.num)?,
        )
    }

    /// `-self`, or `None` on overflow.
    #[must_use]
    pub fn neg(self) -> Option<Self> {
        Some(Self {
            num: self.num.checked_neg()?,
            den: self.den,
        })
    }
}

/// The least common multiple of two positive `i128`s, or `None` on overflow.
fn lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd(a, b);
    a.checked_div(g)?.checked_mul(b)
}

// ---------------------------------------------------------------------------
// polynomials
// ---------------------------------------------------------------------------

/// A monomial: the **sorted multiset** of variable indices it multiplies.
///
/// `x²y` over `x ↦ 0`, `y ↦ 1` is `vec![0, 0, 1]`. The empty vector is the
/// constant monomial `1`. Sorting is what makes structural equality value
/// equality, exactly as `ring::rat`'s `sort_factors` does one level down.
pub type Mono = Vec<usize>;

/// A multivariate polynomial over ℚ with the zero coefficient never stored.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Poly {
    terms: BTreeMap<Mono, Q>,
}

impl Poly {
    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    /// The constant polynomial `c`.
    #[must_use]
    pub fn constant(c: Q) -> Self {
        let mut p = Self::zero();
        let _ = p.checked_add_term(Vec::new(), c);
        p
    }

    /// The polynomial `xᵢ`.
    #[must_use]
    pub fn var(i: usize) -> Self {
        let mut p = Self::zero();
        let _ = p.checked_add_term(vec![i], Q::integer(1));
        p
    }

    /// Whether the polynomial is identically zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The coefficient of `m` (zero when absent).
    #[must_use]
    pub fn coeff(&self, m: &[usize]) -> Q {
        self.terms.get(m).copied().unwrap_or_else(Q::zero)
    }

    /// The `(monomial, coefficient)` pairs, in the canonical monomial order.
    pub fn terms(&self) -> impl Iterator<Item = (&Mono, &Q)> {
        self.terms.iter()
    }

    /// The total degree; the zero polynomial has degree `0`.
    #[must_use]
    pub fn degree(&self) -> usize {
        self.terms.keys().map(Vec::len).max().unwrap_or(0)
    }

    /// Add `c · m` in place, or `None` on overflow.
    fn checked_add_term(&mut self, mut m: Mono, c: Q) -> Option<()> {
        if c.is_zero() {
            return Some(());
        }
        m.sort_unstable();
        let slot = self.terms.entry(m.clone()).or_insert_with(Q::zero);
        *slot = slot.add(c)?;
        if slot.is_zero() {
            self.terms.remove(&m);
        }
        Some(())
    }

    /// `self + other`, or `None` on overflow.
    #[must_use]
    pub fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.checked_add_term(m.clone(), *c)?;
        }
        Some(out)
    }

    /// `self - other`, or `None` on overflow.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (m, c) in &other.terms {
            out.checked_add_term(m.clone(), c.neg()?)?;
        }
        Some(out)
    }

    /// `self * other`, or `None` on overflow.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Self> {
        let mut out = Self::zero();
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                let mut m = ma.clone();
                m.extend_from_slice(mb);
                out.checked_add_term(m, ca.mul(*cb)?)?;
            }
        }
        Some(out)
    }

    /// `-self`, or `None` on overflow.
    #[must_use]
    pub fn neg(&self) -> Option<Self> {
        let mut out = Self::zero();
        for (m, c) in &self.terms {
            out.checked_add_term(m.clone(), c.neg()?)?;
        }
        Some(out)
    }

    /// `k · self` for an integer `k`, or `None` on overflow.
    #[must_use]
    pub fn scale(&self, k: Q) -> Option<Self> {
        let mut out = Self::zero();
        for (m, c) in &self.terms {
            out.checked_add_term(m.clone(), c.mul(k)?)?;
        }
        Some(out)
    }
}

// ---------------------------------------------------------------------------
// rational LDL^T: the PSD decision
// ---------------------------------------------------------------------------

/// The LDLᵀ factorization of a symmetric rational matrix: `A = Σᵢ dᵢ · ℓᵢ ℓᵢᵀ`
/// with every `dᵢ > 0` and `ℓᵢ` a vector whose `i`-th entry is `1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Psd {
    /// One `(dᵢ, ℓᵢ)` pair per strictly positive pivot, in pivot order. Zero
    /// pivots contribute nothing and are dropped.
    pub squares: Vec<(Q, Vec<Q>)>,
}

impl Psd {
    /// Decide whether the symmetric matrix `a` (given in full, `n × n`) is
    /// positive semidefinite, and factor it when it is.
    ///
    /// **This is a decision, not a heuristic.** For a PSD matrix a zero diagonal
    /// pivot forces its whole row and column to be zero, so plain LDLᵀ without
    /// pivoting never gets stuck on one: a zero pivot beside a nonzero entry is
    /// itself a proof that the matrix is indefinite. That is why
    /// [`Decline::NotPsd`] is reported as a finding.
    ///
    /// # Errors
    ///
    /// [`Decline::NotPsd`] with the deciding pivot index, or
    /// [`Decline::Overflow`] if exact `i128` rational arithmetic overflows.
    pub fn factor(a: &[Vec<Q>]) -> Result<Self, Decline> {
        let n = a.len();
        let mut work = a.to_vec();
        let mut squares = Vec::new();
        for i in 0..n {
            let pivot = work[i][i];
            if pivot.is_negative() {
                return Err(Decline::NotPsd { pivot: i });
            }
            if pivot.is_zero() {
                // PSD forces the rest of this row to vanish; a nonzero entry
                // beside a zero pivot is a 2x2 minor with negative determinant.
                for j in (i + 1)..n {
                    if !work[i][j].is_zero() {
                        return Err(Decline::NotPsd { pivot: i });
                    }
                }
                continue;
            }
            let mut column = vec![Q::zero(); n];
            column[i] = Q::integer(1);
            for j in (i + 1)..n {
                column[j] = work[i][j].div(pivot).ok_or(Decline::Overflow)?;
            }
            for r in (i + 1)..n {
                for c in (i + 1)..n {
                    let delta = column[r]
                        .mul(column[c])
                        .and_then(|v| v.mul(pivot))
                        .ok_or(Decline::Overflow)?;
                    work[r][c] = work[r][c].sub(delta).ok_or(Decline::Overflow)?;
                }
            }
            squares.push((pivot, column));
        }
        Ok(Self { squares })
    }

    /// Whether `a` is positive semidefinite, discarding the factorization.
    ///
    /// # Errors
    ///
    /// [`Decline::Overflow`] when the exact arithmetic overflows; a non-PSD
    /// matrix is `Ok(false)`, not an error, because callers that only need the
    /// verdict (the [`DualWitness`] check) treat non-PSD as an ordinary answer.
    pub fn is_psd(a: &[Vec<Q>]) -> Result<bool, Decline> {
        match Self::factor(a) {
            Ok(_) => Ok(true),
            Err(Decline::NotPsd { .. }) => Ok(false),
            Err(other) => Err(other),
        }
    }
}

// ---------------------------------------------------------------------------
// the dual side: a checked witness that a polynomial is NOT a sum of squares
// ---------------------------------------------------------------------------

/// A moment functional `L` on the degree-`2·half_degree` monomials, offered as a
/// witness that a polynomial is **not** a sum of squares.
///
/// The producer never searches for one of these — finding it is a semidefinite
/// program. It **checks** one: if `L`'s moment matrix over the monomials of
/// degree exactly `half_degree` is positive semidefinite and `L(p) < 0`, then
/// `p` is not a sum of squares of forms of that degree, because `p = Σ qₖ²`
/// would give `L(p) = Σ qₖᵀ M qₖ ≥ 0`.
///
/// The repository's CAS holds the Motzkin instance
/// (`axeyum_cas::sos::corpus::motzkin_psd_not_sos`); this type is where such a
/// witness meets a checker.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DualWitness {
    /// Half the degree of the form the witness is about.
    pub half_degree: usize,
    /// `L(m)` for each monomial `m`. A monomial absent from the map takes `0`.
    pub moments: BTreeMap<Mono, Q>,
}

impl DualWitness {
    /// `L(m)`.
    fn moment(&self, m: &[usize]) -> Q {
        let mut key = m.to_vec();
        key.sort_unstable();
        self.moments.get(&key).copied().unwrap_or_else(Q::zero)
    }

    /// `L(p)` — the functional extended linearly to a polynomial.
    fn apply(&self, p: &Poly) -> Option<Q> {
        let mut acc = Q::zero();
        for (m, c) in p.terms() {
            acc = acc.add(self.moment(m).mul(*c)?)?;
        }
        Some(acc)
    }

    /// Verify this witness against `p` over `vars` variables: the moment matrix
    /// over the degree-`half_degree` monomials must be PSD and `L(p)` strictly
    /// negative.
    ///
    /// Returns `Ok(true)` only when BOTH hold — that is the statement "`p` is
    /// not a sum of squares of forms of degree `half_degree`".
    ///
    /// # Errors
    ///
    /// [`Decline::Overflow`] when the exact arithmetic overflows.
    pub fn verifies(&self, p: &Poly, vars: usize) -> Result<bool, Decline> {
        let basis = monomials_of_degree(vars, self.half_degree);
        let n = basis.len();
        let mut matrix = vec![vec![Q::zero(); n]; n];
        for (i, bi) in basis.iter().enumerate() {
            for (j, bj) in basis.iter().enumerate() {
                let mut product = bi.clone();
                product.extend_from_slice(bj);
                matrix[i][j] = self.moment(&product);
            }
        }
        if !Psd::is_psd(&matrix)? {
            return Ok(false);
        }
        let value = self.apply(p).ok_or(Decline::Overflow)?;
        Ok(value.is_negative())
    }
}

/// Every monomial of **exactly** `degree` in `vars` variables, in the canonical
/// sorted-multiset order.
#[must_use]
pub fn monomials_of_degree(vars: usize, degree: usize) -> Vec<Mono> {
    if vars == 0 {
        return if degree == 0 {
            vec![Vec::new()]
        } else {
            Vec::new()
        };
    }
    fn walk(vars: usize, degree: usize, start: usize, current: &mut Mono, out: &mut Vec<Mono>) {
        if current.len() == degree {
            out.push(current.clone());
            return;
        }
        for v in start..vars {
            current.push(v);
            walk(vars, degree, v, current, out);
            current.pop();
        }
    }
    let mut out = Vec::new();
    let mut current = Vec::new();
    walk(vars, degree, 0, &mut current, &mut out);
    out.sort();
    out
}

// ---------------------------------------------------------------------------
// the certificate
// ---------------------------------------------------------------------------

/// One nonnegative atom of a certificate, with the multiplicity it is repeated
/// at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `ℓ²` for the integer-coefficient linear form `ℓ`, whose nonnegativity is
    /// the carrier's `sq_nonneg`.
    ///
    /// The form is `(constant, [(variable index, coefficient)])`, with every
    /// coefficient nonzero and the variable indices ascending.
    Square {
        /// The form's constant term.
        constant: i128,
        /// The form's variable coefficients, ascending by index, never zero.
        linear: Vec<(usize, i128)>,
    },
    /// `hᵢ · hⱼ` for two hypotheses `0 ≤ hᵢ`, `0 ≤ hⱼ` the caller supplied —
    /// the Positivstellensatz step beyond pure SOS, whose nonnegativity is the
    /// carrier's `mul_nonneg`. `i == j` is allowed and means `hᵢ²` derived from
    /// the hypothesis rather than from `sq_nonneg`.
    HypothesisProduct(usize, usize),
}

/// A certificate that `scale · (rhs − lhs) = Σ (multiplicity × atom)`, with every
/// atom nonnegative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate {
    /// The positive integer `M` the identity is stated at. `1` means the
    /// identity is about the difference itself and no division step is emitted.
    pub scale: i128,
    /// The atoms, each with the positive integer multiplicity it is repeated at.
    pub atoms: Vec<(i128, Atom)>,
}

impl Certificate {
    /// The total number of summands the emitted term will carry.
    #[must_use]
    pub fn summands(&self) -> i128 {
        self.atoms.iter().map(|&(k, _)| k).sum()
    }

    /// The polynomial `Σ (multiplicity × atom)`, given each hypothesis'
    /// polynomial, or `None` on overflow.
    ///
    /// The search builds a certificate and then re-derives this sum to compare
    /// it against `scale · (rhs − lhs)`; the *kernel* re-derives it a third
    /// time, through `ring::rat`. Two independent confirmations of the same
    /// identity, and neither is the one that is trusted.
    #[must_use]
    pub fn expand(&self, hypotheses: &[Poly]) -> Option<Poly> {
        let mut acc = Poly::zero();
        for (multiplicity, atom) in &self.atoms {
            let term = match atom {
                Atom::Square { constant, linear } => {
                    let mut form = Poly::constant(Q::integer(*constant));
                    for &(v, c) in linear {
                        let scaled = Poly::var(v).scale(Q::integer(c))?;
                        form = form.add(&scaled)?;
                    }
                    form.mul(&form)?
                }
                Atom::HypothesisProduct(i, j) => {
                    let a = hypotheses.get(*i)?;
                    let b = hypotheses.get(*j)?;
                    a.mul(b)?
                }
            };
            acc = acc.add(&term.scale(Q::integer(*multiplicity))?)?;
        }
        Some(acc)
    }
}

// ---------------------------------------------------------------------------
// the search
// ---------------------------------------------------------------------------

/// Search for a certificate that `p ≥ 0`, over `vars` variables, using only
/// squares (no hypothesis products).
///
/// Complete for `p` of total degree ≤ 2 (see the module docs); declines
/// [`Decline::DegreeUnsupported`] above it.
///
/// # Errors
///
/// A [`Decline`] naming what stopped the search — including
/// [`Decline::NotPsd`], which is the *finding* that `p` is negative somewhere.
pub fn search_sos(p: &Poly, vars: usize) -> Result<Certificate, Decline> {
    let degree = p.degree();
    if degree > 2 {
        return Err(Decline::DegreeUnsupported { degree });
    }
    // The affine basis `(1, x_0, …, x_{vars-1})`: index 0 is the constant.
    let n = vars + 1;
    let mut gram = vec![vec![Q::zero(); n]; n];
    for (m, c) in p.terms() {
        match m.len() {
            0 => gram[0][0] = *c,
            1 => {
                // `c·xᵢ` splits evenly across the two symmetric off-diagonal
                // slots `(0, i+1)` and `(i+1, 0)`.
                let half = c.div(Q::integer(2)).ok_or(Decline::Overflow)?;
                gram[0][m[0] + 1] = half;
                gram[m[0] + 1][0] = half;
            }
            2 if m[0] == m[1] => gram[m[0] + 1][m[0] + 1] = *c,
            2 => {
                let half = c.div(Q::integer(2)).ok_or(Decline::Overflow)?;
                gram[m[0] + 1][m[1] + 1] = half;
                gram[m[1] + 1][m[0] + 1] = half;
            }
            // `Poly::degree` already bounded the length at 2.
            _ => return Err(Decline::DegreeUnsupported { degree }),
        }
    }
    let psd = Psd::factor(&gram)?;
    clear_denominators(&psd.squares)
}

/// Turn the rational-weight LDLᵀ squares `Σ dₖ ℓₖ²` into an integer-coefficient,
/// integer-multiplicity certificate at a single common scale `M`.
///
/// See the module docs for why the ring producer forces this.
///
/// # Errors
///
/// [`Decline::ScaleTooLarge`], [`Decline::CertificateTooLarge`] or
/// [`Decline::Overflow`].
fn clear_denominators(squares: &[(Q, Vec<Q>)]) -> Result<Certificate, Decline> {
    // Per square: scale the form to integer coefficients (by the lcm `cₖ` of its
    // coefficients' denominators), which turns the weight `dₖ` into `dₖ / cₖ²`.
    let mut weights: Vec<(Q, i128, Vec<Q>)> = Vec::new();
    for (weight, column) in squares {
        let mut clear = 1_i128;
        for entry in column {
            clear = lcm(clear, entry.denominator()).ok_or(Decline::Overflow)?;
        }
        let squared = clear.checked_mul(clear).ok_or(Decline::Overflow)?;
        let effective = weight.div(Q::integer(squared)).ok_or(Decline::Overflow)?;
        weights.push((effective, clear, column.clone()));
    }
    // The single scale that makes every effective weight an integer.
    let mut scale = 1_i128;
    for (effective, _, _) in &weights {
        scale = lcm(scale, effective.denominator()).ok_or(Decline::Overflow)?;
    }
    if scale > MAX_SCALE {
        return Err(Decline::ScaleTooLarge { scale });
    }
    let mut atoms = Vec::new();
    for (effective, clear, column) in &weights {
        let multiplicity = effective.mul(Q::integer(scale)).ok_or(Decline::Overflow)?;
        if multiplicity.denominator() != 1 || multiplicity.numerator() <= 0 {
            return Err(Decline::Overflow);
        }
        let multiplicity = multiplicity.numerator();
        let mut constant = 0_i128;
        let mut linear = Vec::new();
        for (index, entry) in column.iter().enumerate() {
            let scaled = entry.mul(Q::integer(*clear)).ok_or(Decline::Overflow)?;
            if scaled.denominator() != 1 {
                return Err(Decline::Overflow);
            }
            let coefficient = scaled.numerator();
            if coefficient == 0 {
                continue;
            }
            if coefficient.abs() > MAX_FORM_COEFF {
                return Err(Decline::CertificateTooLarge);
            }
            if index == 0 {
                constant = coefficient;
            } else {
                linear.push((index - 1, coefficient));
            }
        }
        atoms.push((multiplicity, Atom::Square { constant, linear }));
    }
    if atoms.is_empty() {
        // The identically-zero difference (`a ≤ a`, or a hypothesis product that
        // accounts for all of it). The emitter folds `add_nonneg` over the atom
        // list and has nothing to start from, so give it the trivial square
        // `0² ≥ 0` rather than an empty fold — which would otherwise surface as
        // a size complaint about a certificate that is too SMALL.
        atoms.push((
            1,
            Atom::Square {
                constant: 0,
                linear: Vec::new(),
            },
        ));
    }
    let certificate = Certificate { scale, atoms };
    if certificate.summands() > MAX_SQUARES as i128 {
        return Err(Decline::CertificateTooLarge);
    }
    Ok(certificate)
}

/// Search for a certificate that `p ≥ 0` given hypotheses `0 ≤ hᵢ`, landing the
/// ONE Positivstellensatz shape beyond pure SOS this producer covers:
/// `p = hᵢ·hⱼ + (a sum of squares)`.
///
/// The search tries the pure-SOS decomposition first and only then each
/// unordered pair `(i, j)` of hypotheses, in index order, subtracting `hᵢ·hⱼ`
/// and re-running the degree-≤2 search on the remainder. **Not covered**: more
/// than one product term, a product of three or more hypotheses, a product
/// carrying a multiplicity or a square weight, and any product whose remainder
/// is not itself degree ≤ 2. Those are a genuine SDP over the product cone,
/// not a bounded enumeration.
///
/// # Errors
///
/// The pure-SOS decline is returned when no product helps, so the caller sees
/// the reason the *primary* route failed rather than the last pair's.
pub fn search_with_hypotheses(
    p: &Poly,
    vars: usize,
    hypotheses: &[Poly],
) -> Result<Certificate, Decline> {
    let direct = search_sos(p, vars);
    if direct.is_ok() {
        return direct;
    }
    for i in 0..hypotheses.len() {
        for j in i..hypotheses.len() {
            let Some(product) = hypotheses[i].mul(&hypotheses[j]) else {
                continue;
            };
            let Some(remainder) = p.sub(&product) else {
                continue;
            };
            let Ok(rest) = search_sos(&remainder, vars) else {
                continue;
            };
            // The product enters at the certificate's scale, so it is repeated
            // `scale` times beside the scaled squares.
            let mut atoms = vec![(rest.scale, Atom::HypothesisProduct(i, j))];
            atoms.extend(rest.atoms.iter().cloned());
            let certificate = Certificate {
                scale: rest.scale,
                atoms,
            };
            if certificate.summands() > MAX_SQUARES as i128 {
                continue;
            }
            return Ok(certificate);
        }
    }
    direct
}
