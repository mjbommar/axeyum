//! Deciding the fibre `∃y. ⋀ᵢ qᵢ(y) ▷ᵢ 0` over a **real algebraic** `x = α`,
//! with every operation carried out in `K = ℚ(α) = ℚ[x]/(m)`.
//!
//! This is the engine that makes an irrational cell boundary decidable in
//! [`crate::qe::bivariate`]. A point cell of the projected `x`-line sits at a
//! root `α` of the projection's cut polynomial; substituting `α` into the atoms
//! turns their `y`-coefficients into elements of `K`, so the fibre is a
//! univariate problem over a *real algebraic field* rather than over ℚ.
//!
//! # The three things this needs, and where each comes from
//!
//! 1. **Exact arithmetic in `K`.** An element is a [`num_rational::BigRational`]
//!    polynomial of degree below `deg m`, reduced modulo `m`. Sum, difference
//!    and product are polynomial operations followed by one reduction; the
//!    **inverse** is the half-extended Euclidean algorithm modulo `m`.
//!
//! 2. **The sign of an element at `α`.** `e(α)` is a real number and its sign
//!    is decidable. `crate::qe::big`'s `sign_at_algebraic` settles `e(α) = 0`
//!    *exactly* — `α` is a root of `e` iff `gcd(m, e)` has a root in `α`'s
//!    isolating bracket, and `α` is `m`'s only root there — and, when
//!    `e(α) ≠ 0`, refines the bracket until `e` has **no** root inside it, at
//!    which point `e`'s sign is constant on the bracket and one rational
//!    evaluation gives the answer.
//!
//!    **Termination.** A nonzero `e` is a nonzero polynomial, so it has a
//!    nonzero (squarefree) part with finitely many real roots; the roots of `e`
//!    other than `α` are therefore bounded away from `α`, and once the bracket
//!    is narrower than that distance the root count inside it is zero and the
//!    loop exits. The step budget is a resource bound, never a semantic one:
//!    exhausting it is a decline, never a verdict.
//!
//! 3. **Real-root isolation over `K`.** Sturm's theorem needs only a chain of
//!    remainders and the ability to compare a value with zero, so it transfers
//!    verbatim: the chain `s₀ = p`, `s₁ = p′`, `sₖ = −rem(sₖ₋₂, sₖ₋₁)` is built
//!    with `K`-arithmetic, and the variation count at a **rational** `q` is read
//!    off the signs at `α` of the elements `sₖ(q) ∈ K`. Bisection from a Cauchy
//!    bound — whose coefficients are bounded above by evaluating `|e|` on the
//!    bracket, no interval arithmetic and no `f64` — then isolates every real
//!    root of the fibre polynomial.
//!
//! # Why the modulus need not be irreducible, and what happens when it is not
//!
//! `K = ℚ[x]/(m)` is a field only when `m` is irreducible, and the modulus this
//! module is handed is the projection's cut polynomial, which is square-free but
//! usually **not** irreducible. Rather than depend on a factorization over ℚ,
//! this module *splits on demand* (the classical D5 / dynamic-evaluation trick):
//!
//! - every operation that needs an inverse computes `gcd(e, m)` on the way;
//! - a **non-unit** gcd `d` is a proper factor of `m`, so `m` factors. Exactly
//!   one side of that factorization keeps `α` — decided by asking whether
//!   `d(α) = 0`, which is the exact test above — and the computation restarts
//!   with that side as the new modulus;
//! - likewise an element that is a nonzero polynomial but vanishes at `α`
//!   witnesses a split (`gcd(e, m)` again).
//!
//! Each split strictly lowers `deg m`, so at most `deg m` restarts happen. The
//! certificate records the **final** modulus and its checker re-runs everything
//! against that one; the split search is producer-side scaffolding the checker
//! never sees. Soundness does not depend on irreducibility at all: every ring
//! operation modulo any `m` with `m(α) = 0` computes the right value at `α`,
//! and every *division* performed was checked to be by a unit.
//!
//! # What this module does **not** do
//!
//! - It does not name a fibre sample by a minimal polynomial over ℚ. An
//!   algebraic sample is carried as **a polynomial over `K` plus a rational
//!   bracket** ([`FieldSample::Algebraic`]), which is what the Sturm machinery
//!   here produces directly. Obtaining the ℚ-minimal polynomial by a norm or a
//!   resultant would be a second, redundant representation carrying its own
//!   irreducibility obligation, so it is deliberately not done.
//! - It does not handle a second quantifier, or a third variable.

use core::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::{Relation, big};

/// How many bisections the `K`-isolation loop will spend separating the real
/// roots of one fibre polynomial before declining.
const MAX_ISOLATION_STEPS: usize = 512;

/// How many bisections the `K`-refinement loops (the sign at an algebraic
/// sample, the comparison against a rational, the separator search) will spend
/// before declining.
const MAX_REFINE_STEPS: usize = 512;

/// How many candidates the rational-root recogniser tests inside one bracket
/// before settling for an algebraic sample. Failing to recognise a rational
/// root costs an algebraic sample, never soundness.
const MAX_EXACTIFY_STEPS: usize = 20;

/// How many times the modulus may split before the fibre is declined. Each
/// split strictly lowers the degree, so `deg m` is already a bound; this is the
/// constant that makes the loop obviously finite.
const MAX_SPLITS: usize = 64;

// ============================================================================
// Faults.
// ============================================================================

/// Why a fibre certificate was refused. Every variant is a **distinct guard**;
/// [`Fault::Declined`] is the one that is not an accusation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// The recorded bracket does not hold exactly one root of the recorded
    /// modulus, so `α` names nothing, or names two things at once.
    ModulusNotIsolating {
        /// How many distinct real roots the bracket actually holds.
        roots_in_bracket: usize,
    },
    /// The recorded modulus is constant or zero, so it defines no `α`.
    ModulusDegenerate,
    /// The certificate records a different number of signs than the fibre has
    /// conjuncts, so some `qᵢ` is unaccounted for.
    SignCountMismatch {
        /// Signs recorded.
        recorded: usize,
        /// Conjuncts in the fibre.
        atoms: usize,
    },
    /// An algebraic fibre sample's bracket does not hold exactly one root of
    /// its recorded defining polynomial over `K`.
    SampleNotIsolating {
        /// How many roots the bracket actually holds.
        roots_in_bracket: usize,
    },
    /// A recomputed sign at `α` disagrees with the recorded one.
    SignMismatch {
        /// Index of the conjunct.
        index: usize,
        /// The sign the certificate claims.
        recorded: i8,
        /// The sign re-derived in `K`.
        recomputed: i8,
    },
    /// A conjunct's relation does not hold at the recomputed sign, so the
    /// witness does not satisfy the fibre.
    RelationFails {
        /// Index of the conjunct.
        index: usize,
        /// The recomputed sign at which the relation fails.
        sign: i8,
    },
    /// The refutation records the wrong number of cells for its root list
    /// (`2r + 1` are required for `r` roots).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required.
        expected: usize,
    },
    /// The refutation records the wrong number of open-cell samples
    /// (`r + 1` are required for `r` roots).
    OpenSampleCountMismatch {
        /// Open samples recorded.
        recorded: usize,
        /// Open samples required.
        expected: usize,
    },
    /// The `y`-cells do not cover ℝ in order: a root is not strictly between
    /// the open samples that are supposed to bracket it.
    CellOrderViolation {
        /// Index of the open sample that is out of place.
        index: usize,
    },
    /// The recorded root list misses a real root of some `qᵢ` over `K`, so the
    /// cells are not sign-invariant and the refutation proves nothing.
    IncompleteRootList {
        /// Index of the conjunct whose roots were miscounted.
        atom: usize,
        /// Its distinct real roots, by an independent `K`-Sturm count.
        sturm_count: usize,
        /// Recorded roots at which it vanishes.
        recorded: usize,
    },
    /// A cell names a conjunct the fibre does not have.
    ConjunctIndexOutOfRange {
        /// The offending cell.
        cell: usize,
        /// The out-of-range index it named.
        index: usize,
    },
    /// A cell's nominated conjunct **holds** there, so the cell is not refuted.
    ConjunctDoesNotFail {
        /// The offending cell.
        cell: usize,
        /// The conjunct the cell nominated.
        index: usize,
        /// The recomputed sign, at which the relation holds.
        sign: i8,
    },
    /// Exact arithmetic ran out of a named step budget, or the recorded modulus
    /// turned out to be reducible at `α` while the checker was re-deriving.
    /// Not a refusal of any claim.
    Declined(String),
}

/// The producer-side error: either a real fault, or a demand to restart with a
/// smaller modulus.
#[derive(Debug, Clone)]
enum Inner {
    /// The modulus factors; retry with this factor, which still has `α` as its
    /// unique root in the bracket.
    Split(Vec<BigRational>),
    /// A genuine fault.
    Fault(Fault),
}

impl From<Fault> for Inner {
    fn from(fault: Fault) -> Inner {
        Inner::Fault(fault)
    }
}

/// The producer-side result type.
type Kr<T> = Result<T, Inner>;

fn declined(reason: &str) -> Inner {
    Inner::Fault(Fault::Declined(reason.to_string()))
}

/// The checker's view of a producer error: a split means the recorded modulus
/// was not the final one, which is a decline rather than an accusation.
fn as_fault(inner: Inner) -> Fault {
    match inner {
        Inner::Fault(fault) => fault,
        Inner::Split(_) => Fault::Declined("the recorded modulus is reducible at α".to_string()),
    }
}

// ============================================================================
// ℚ[x] helpers that `qe::big` does not expose.
// ============================================================================

/// `(quotient, remainder)` of `a` on division by `b` over ℚ. `None` when `b` is
/// the zero polynomial.
fn divmod(a: &[BigRational], b: &[BigRational]) -> Option<(Vec<BigRational>, Vec<BigRational>)> {
    let b_degree = big::degree(b)?;
    let mut remainder = big::trim(a.to_vec());
    let leading = b[b_degree].clone();
    let mut quotient: Vec<BigRational> = Vec::new();
    while let Some(r_degree) = big::degree(&remainder) {
        if r_degree < b_degree {
            break;
        }
        let factor = &remainder[r_degree] / &leading;
        let shift = r_degree - b_degree;
        if quotient.len() < shift + 1 {
            quotient.resize(shift + 1, BigRational::zero());
        }
        quotient[shift] = factor.clone();
        for (index, coeff) in b.iter().enumerate().take(b_degree + 1) {
            remainder[index + shift] -= &factor * coeff;
        }
        remainder = big::trim(remainder);
    }
    Some((big::trim(quotient), remainder))
}

/// `a − b` over ℚ, LSB-first.
fn sub_poly(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![BigRational::zero(); a.len().max(b.len())];
    for (index, coeff) in a.iter().enumerate() {
        out[index] += coeff;
    }
    for (index, coeff) in b.iter().enumerate() {
        out[index] -= coeff;
    }
    big::trim(out)
}

/// `(g, s)` with `g = gcd(a, m)` monic and `s · a ≡ g (mod m)`.
///
/// The half-extended Euclidean algorithm: only the cofactor of `a` is tracked,
/// which is all an inverse modulo `m` needs. A unit `g` therefore hands back
/// `a⁻¹` directly, and a non-unit `g` hands back a proper factor of `m`.
fn xgcd(a: &[BigRational], m: &[BigRational]) -> (Vec<BigRational>, Vec<BigRational>) {
    let mut r0 = big::trim(m.to_vec());
    let mut r1 = big::trim(a.to_vec());
    let mut s0: Vec<BigRational> = Vec::new();
    let mut s1: Vec<BigRational> = vec![BigRational::one()];
    while big::degree(&r1).is_some() {
        let Some((quotient, remainder)) = divmod(&r0, &r1) else {
            break;
        };
        r0 = r1;
        r1 = remainder;
        let next = sub_poly(&s0, &big::mul(&quotient, &s1));
        s0 = s1;
        s1 = next;
    }
    match big::degree(&r0) {
        None => (Vec::new(), Vec::new()),
        Some(degree) => {
            let leading = r0[degree].clone();
            let g = big::trim(r0.iter().map(|c| c / &leading).collect());
            let s = big::trim(s0.iter().map(|c| c / &leading).collect());
            (g, s)
        }
    }
}

fn two() -> BigRational {
    BigRational::from_integer(BigInt::from(2))
}

// ============================================================================
// Elements of K.
// ============================================================================

/// An element of `K`: a `BigRational` polynomial in `α`, reduced modulo the
/// field's modulus and trimmed. The empty vector is zero.
pub type Element = Vec<BigRational>;

/// A polynomial in `y` over `K`, LSB-first: `p[j]` is the coefficient of `yʲ`.
pub type FieldPoly = Vec<Element>;

/// `a + b`, as polynomials in `α`. Reduction is unnecessary: both are already
/// reduced and the degree cannot grow.
fn add_elements(a: &Element, b: &Element) -> Element {
    let mut out = vec![BigRational::zero(); a.len().max(b.len())];
    for (index, coeff) in a.iter().enumerate() {
        out[index] += coeff;
    }
    for (index, coeff) in b.iter().enumerate() {
        out[index] += coeff;
    }
    big::trim(out)
}

/// `−a`.
fn neg_element(a: &Element) -> Element {
    a.iter().map(core::ops::Neg::neg).collect()
}

/// `a · q` for a rational `q`.
fn scale_element(a: &Element, factor: &BigRational) -> Element {
    if factor.is_zero() {
        return Vec::new();
    }
    a.iter().map(|c| c * factor).collect()
}

/// `−p`, coefficient by coefficient.
fn kneg_poly(p: &FieldPoly) -> FieldPoly {
    p.iter().map(neg_element).collect()
}

/// The `y`-degree of a `K`-polynomial that has already been trimmed by
/// [`RealField::ktrim`]. `None` is the zero polynomial.
fn kdegree(p: &FieldPoly) -> Option<usize> {
    if p.is_empty() {
        None
    } else {
        Some(p.len() - 1)
    }
}

// ============================================================================
// The field.
// ============================================================================

/// `K = ℚ[x]/(m)` presented by a **real** root `α` of `m`: the unique one in
/// the half-open bracket `(lower, upper]`.
///
/// `m` need not be irreducible; the module documentation explains how a
/// reducible modulus is split on demand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealField {
    modulus: Vec<BigRational>,
    lower: BigRational,
    upper: BigRational,
}

impl RealField {
    /// Present `K` by the unique root of `modulus` in `(lower, upper]`.
    ///
    /// # Errors
    ///
    /// [`Fault::ModulusDegenerate`] when `modulus` is constant or zero, and
    /// [`Fault::ModulusNotIsolating`] when the bracket does not hold exactly one
    /// root of it — the guard that stops `α` from naming nothing, or from
    /// naming two things at once.
    pub fn new(
        modulus: &[BigRational],
        lower: &BigRational,
        upper: &BigRational,
    ) -> Result<RealField, Fault> {
        if big::degree(modulus).is_none_or(|d| d == 0) {
            return Err(Fault::ModulusDegenerate);
        }
        let count = big::count_roots_in(modulus, lower, upper).ok_or_else(|| {
            Fault::Declined("the Sturm count over α's bracket declined".to_string())
        })?;
        if count != 1 {
            return Err(Fault::ModulusNotIsolating {
                roots_in_bracket: count,
            });
        }
        Ok(RealField {
            modulus: big::trim(modulus.to_vec()),
            lower: lower.clone(),
            upper: upper.clone(),
        })
    }

    /// The modulus `m`.
    pub fn modulus(&self) -> &[BigRational] {
        &self.modulus
    }

    /// `deg m`.
    pub fn degree(&self) -> usize {
        big::degree(&self.modulus).unwrap_or(0)
    }

    /// A ℚ-polynomial reduced to an element of `K`.
    pub fn reduce(&self, p: &[BigRational]) -> Element {
        big::rem(p, &self.modulus).unwrap_or_default()
    }

    /// `1 ∈ K`.
    fn one(&self) -> Element {
        self.reduce(&[BigRational::one()])
    }

    /// The exact sign of `e(α)`.
    ///
    /// A rational **interval evaluation** over `α`'s bracket is tried first: it
    /// costs `deg e` multiplications and, because the bracket arrives from an
    /// isolation that already narrowed it, decides the overwhelming majority of
    /// signs. Only when the enclosure straddles zero — which includes every
    /// genuine `e(α) = 0` — does the exact route run. The fast path can never
    /// return a wrong sign: an interval evaluation is an *enclosure* of `e(α)`,
    /// so a strictly positive enclosure means a strictly positive value.
    ///
    /// # Errors
    ///
    /// [`Fault::Declined`] if the refinement budget in `qe::big` runs out.
    pub fn sign(&self, e: &[BigRational]) -> Result<i8, Fault> {
        if big::degree(e).is_none() {
            return Ok(0);
        }
        if let Some(sign) = self.interval_sign(e) {
            return Ok(sign);
        }
        big::sign_at_algebraic(e, &self.modulus, &self.lower, &self.upper)
            .ok_or_else(|| Fault::Declined("the sign of an element at α declined".to_string()))
    }

    /// The sign of `e(α)` when a rational interval evaluation over
    /// `[lower, upper] ∋ α` already settles it, and `None` when the enclosure
    /// straddles zero.
    fn interval_sign(&self, e: &[BigRational]) -> Option<i8> {
        let mut low = BigRational::zero();
        let mut high = BigRational::zero();
        for coeff in e.iter().rev() {
            let products = [
                &low * &self.lower,
                &low * &self.upper,
                &high * &self.lower,
                &high * &self.upper,
            ];
            let mut next_low = products[0].clone();
            let mut next_high = products[0].clone();
            for product in &products[1..] {
                if *product < next_low {
                    next_low.clone_from(product);
                }
                if *product > next_high {
                    next_high.clone_from(product);
                }
            }
            low = next_low + coeff;
            high = next_high + coeff;
        }
        if low.is_positive() {
            Some(1)
        } else if high.is_negative() {
            Some(-1)
        } else {
            None
        }
    }

    /// A rational upper bound on `|e(α)|`: `Σⱼ |eⱼ| · Mʲ` for
    /// `M = ⌈max(|lower|, |upper|)⌉ ≥ |α|`. Exact, and never a `f64`.
    ///
    /// `M` is rounded **up to an integer** deliberately. The bracket endpoints
    /// arrive from a bisection and can carry forty-digit denominators; every
    /// subsequent bisection would then inherit them, and the isolation loop
    /// would spend its time on arithmetic rather than on halving. A coarser
    /// bound costs at most one extra halving.
    fn abs_bound(&self, e: &Element) -> BigRational {
        let magnitude =
            BigRational::from_integer(self.lower.abs().max(self.upper.abs()).ceil().to_integer());
        let mut power = BigRational::one();
        let mut total = BigRational::zero();
        for coeff in e {
            total += coeff.abs() * &power;
            power *= &magnitude;
        }
        total
    }

    /// The proper factor of `m` that keeps `α`, given an `e` that is a nonzero
    /// polynomial vanishing at `α`.
    fn split_on(&self, e: &[BigRational]) -> Kr<Vec<BigRational>> {
        let common = big::gcd(e, &self.modulus);
        match big::degree(&common) {
            Some(d) if d >= 1 && d < self.degree() => Ok(common),
            _ => Err(declined("a split of the modulus produced no proper factor")),
        }
    }

    /// `e⁻¹` in `K`, or a split when `e` is not a unit modulo `m`.
    fn invert(&self, e: &Element) -> Kr<Element> {
        if big::degree(e).is_none() {
            return Err(declined("the inverse of zero was requested"));
        }
        let (common, cofactor) = xgcd(e, &self.modulus);
        match big::degree(&common) {
            None => Err(declined("gcd(e, m) is zero")),
            Some(0) => Ok(self.reduce(&cofactor)),
            Some(_) => {
                // `common` is a proper factor of `m`; whichever side has `α` as
                // a root becomes the new modulus.
                if self.sign(&common)? == 0 {
                    Err(Inner::Split(common))
                } else {
                    let (quotient, _) = divmod(&self.modulus, &common)
                        .ok_or_else(|| declined("the modulus could not be divided"))?;
                    Err(Inner::Split(big::monic(&quotient)))
                }
            }
        }
    }

    /// `a · b` in `K`.
    fn mul(&self, a: &Element, b: &Element) -> Element {
        self.reduce(&big::mul(a, b))
    }
}

// ============================================================================
// Polynomials in `y` over K.
// ============================================================================

impl RealField {
    /// Drop the top `y`-coefficients that vanish at `α`.
    ///
    /// A coefficient that is a **nonzero polynomial** yet vanishes at `α` can
    /// only happen when `m` is reducible, and it is exactly the witness that
    /// splits it.
    fn ktrim(&self, mut p: FieldPoly) -> Kr<FieldPoly> {
        loop {
            let Some(top) = p.last().cloned() else {
                return Ok(p);
            };
            if big::degree(&top).is_none() {
                p.pop();
                continue;
            }
            if self.sign(&top)? == 0 {
                return Err(Inner::Split(self.split_on(&top)?));
            }
            return Ok(p);
        }
    }

    fn kmul(&self, a: &FieldPoly, b: &FieldPoly) -> FieldPoly {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut out = vec![Element::new(); a.len() + b.len() - 1];
        for (i, left) in a.iter().enumerate() {
            if big::degree(left).is_none() {
                continue;
            }
            for (j, right) in b.iter().enumerate() {
                let product = self.mul(left, right);
                out[i + j] = add_elements(&out[i + j], &product);
            }
        }
        out
    }

    /// `p(q)` for a **rational** `q`, by Horner in `K`.
    fn keval(&self, p: &FieldPoly, q: &BigRational) -> Element {
        let _ = &self.modulus;
        let mut acc = Element::new();
        for coeff in p.iter().rev() {
            acc = add_elements(&scale_element(&acc, q), coeff);
        }
        big::trim(acc)
    }

    /// `∂p/∂y`.
    fn kderivative(&self, p: &FieldPoly) -> FieldPoly {
        let _ = self;
        p.iter()
            .enumerate()
            .skip(1)
            .map(|(k, c)| scale_element(c, &BigRational::from_integer(BigInt::from(k))))
            .collect()
    }

    /// `(quotient, remainder)` of `a` on division by `b` over `K`.
    fn kdivrem(&self, a: &FieldPoly, b: &FieldPoly) -> Kr<(FieldPoly, FieldPoly)> {
        let divisor = self.ktrim(b.clone())?;
        let Some(b_degree) = kdegree(&divisor) else {
            return Err(declined("division by the zero polynomial over K"));
        };
        let inverse = self.invert(&divisor[b_degree])?;
        let mut remainder = self.ktrim(a.clone())?;
        let mut quotient: FieldPoly = Vec::new();
        while let Some(r_degree) = kdegree(&remainder) {
            if r_degree < b_degree {
                break;
            }
            let factor = self.mul(&remainder[r_degree], &inverse);
            let shift = r_degree - b_degree;
            if quotient.len() < shift + 1 {
                quotient.resize(shift + 1, Element::new());
            }
            quotient[shift] = add_elements(&quotient[shift], &factor);
            for (index, coeff) in divisor.iter().enumerate().take(b_degree + 1) {
                let product = self.mul(&factor, coeff);
                remainder[index + shift] =
                    add_elements(&remainder[index + shift], &neg_element(&product));
            }
            // The leading term cancels to the *zero polynomial* exactly, so the
            // trim below never has to decide a sign and the degree drops.
            remainder = self.ktrim(remainder)?;
        }
        Ok((quotient, remainder))
    }

    fn krem(&self, a: &FieldPoly, b: &FieldPoly) -> Kr<FieldPoly> {
        Ok(self.kdivrem(a, b)?.1)
    }

    /// `p` scaled so its leading coefficient is `1 ∈ K`.
    fn kmonic(&self, p: &FieldPoly) -> Kr<FieldPoly> {
        let trimmed = self.ktrim(p.clone())?;
        let Some(degree) = kdegree(&trimmed) else {
            return Ok(Vec::new());
        };
        let inverse = self.invert(&trimmed[degree])?;
        Ok(trimmed.iter().map(|c| self.mul(c, &inverse)).collect())
    }

    /// `gcd(a, b)` over `K`, monic.
    fn kgcd(&self, a: &FieldPoly, b: &FieldPoly) -> Kr<FieldPoly> {
        let mut left = self.ktrim(a.clone())?;
        let mut right = self.ktrim(b.clone())?;
        while kdegree(&right).is_some() {
            let next = self.krem(&left, &right)?;
            left = right;
            right = next;
        }
        self.kmonic(&left)
    }

    /// `p / gcd(p, p′)`: the same roots, each simple.
    fn ksquarefree(&self, p: &FieldPoly) -> Kr<FieldPoly> {
        let trimmed = self.ktrim(p.clone())?;
        let Some(degree) = kdegree(&trimmed) else {
            return Ok(Vec::new());
        };
        if degree == 0 {
            return self.kmonic(&trimmed);
        }
        let derivative = self.kderivative(&trimmed);
        let common = self.kgcd(&trimmed, &derivative)?;
        Ok(self.kdivrem(&trimmed, &common)?.0)
    }
}

// ============================================================================
// Sturm over K.
// ============================================================================

/// The Sturm chain of a `K`-polynomial, built from its square-free part, so
/// `V(lo) − V(hi)` counts the **distinct** real roots in `(lo, hi]`.
#[derive(Debug, Clone)]
struct KSturm {
    members: Vec<FieldPoly>,
}

impl KSturm {
    fn new(field: &RealField, p: &FieldPoly) -> Kr<KSturm> {
        let squarefree = field.ksquarefree(p)?;
        let mut members = vec![squarefree];
        let derivative = field.ktrim(field.kderivative(&members[0]))?;
        if kdegree(&derivative).is_none() {
            return Ok(KSturm { members });
        }
        members.push(derivative);
        loop {
            let len = members.len();
            let remainder = field.krem(&members[len - 2], &members[len - 1])?;
            if kdegree(&remainder).is_none() {
                break;
            }
            members.push(kneg_poly(&remainder));
        }
        Ok(KSturm { members })
    }

    /// Sign changes in the chain at the rational `x`, zeros skipped. Each sign
    /// is the sign **at `α`** of an element of `K`.
    fn variations(&self, field: &RealField, x: &BigRational) -> Kr<usize> {
        let mut variations = 0usize;
        let mut previous: Option<i8> = None;
        for member in &self.members {
            let value = field.keval(member, x);
            let sign = field.sign(&value)?;
            if sign == 0 {
                continue;
            }
            if previous.is_some_and(|prev| prev != sign) {
                variations += 1;
            }
            previous = Some(sign);
        }
        Ok(variations)
    }

    fn count_in(&self, field: &RealField, lo: &BigRational, hi: &BigRational) -> Kr<usize> {
        let low = self.variations(field, lo)?;
        let high = self.variations(field, hi)?;
        Ok(low.saturating_sub(high))
    }
}

// ============================================================================
// Isolation over K.
// ============================================================================

/// One isolated real root of a `K`-polynomial, bracketed by **rationals**.
#[derive(Debug, Clone, PartialEq, Eq)]
struct KIsolated {
    lo: BigRational,
    hi: BigRational,
    exact: bool,
}

impl RealField {
    /// A rational `B` with every real root of `p` inside `(−B, B]`: the Cauchy
    /// bound `1 + maxₖ |cₖ(α)|` of the monic form of `p`.
    fn root_bound(&self, p: &FieldPoly) -> Kr<BigRational> {
        let monic = self.kmonic(p)?;
        let mut best = BigRational::zero();
        for coeff in &monic {
            let bound = self.abs_bound(coeff);
            if bound > best {
                best = bound;
            }
        }
        Ok(best + BigRational::one())
    }

    /// Isolate every distinct real root of `p` over `K`, ascending.
    fn kisolate(&self, p: &FieldPoly) -> Kr<Vec<KIsolated>> {
        let squarefree = self.ksquarefree(p)?;
        if kdegree(&squarefree).is_none_or(|d| d == 0) {
            return Ok(Vec::new());
        }
        let chain = KSturm::new(self, &squarefree)?;
        let bound = self.root_bound(&squarefree)?;
        let total = chain.count_in(self, &-bound.clone(), &bound)?;
        if total == 0 {
            return Ok(Vec::new());
        }
        let mut pending: Vec<(BigRational, BigRational, usize)> =
            vec![(-bound.clone(), bound, total)];
        let mut found: Vec<KIsolated> = Vec::new();
        let mut steps = 0usize;
        while let Some((lo, hi, count)) = pending.pop() {
            if count == 0 {
                continue;
            }
            if count == 1 {
                found.push(self.exactify(&squarefree, &chain, lo, hi)?);
                continue;
            }
            steps += 1;
            if steps > MAX_ISOLATION_STEPS {
                return Err(declined("K-root isolation ran out of its bisection budget"));
            }
            let mid = (&lo + &hi) / two();
            let left = chain.count_in(self, &lo, &mid)?;
            pending.push((mid.clone(), hi, count - left));
            pending.push((lo, mid, left));
        }
        found.sort_by(|a, b| a.hi.cmp(&b.hi));
        Ok(found)
    }

    /// Narrow a single-root bracket, recognising a **rational** root exactly
    /// when the budget reaches it.
    fn exactify(
        &self,
        p: &FieldPoly,
        chain: &KSturm,
        mut lo: BigRational,
        mut hi: BigRational,
    ) -> Kr<KIsolated> {
        if self.sign(&self.keval(p, &hi))? == 0 {
            return Ok(KIsolated {
                lo,
                hi,
                exact: true,
            });
        }
        for _ in 0..MAX_EXACTIFY_STEPS {
            let candidate = big::simplest_between(&lo, &hi);
            if self.sign(&self.keval(p, &candidate))? == 0 {
                return Ok(KIsolated {
                    lo,
                    hi: candidate,
                    exact: true,
                });
            }
            let mid = (&lo + &hi) / two();
            if self.sign(&self.keval(p, &mid))? == 0 {
                return Ok(KIsolated {
                    lo,
                    hi: mid,
                    exact: true,
                });
            }
            if chain.count_in(self, &lo, &mid)? == 1 {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        Ok(KIsolated {
            lo,
            hi,
            exact: false,
        })
    }

    /// One rational sample strictly inside every open `y`-cell.
    fn open_cell_samples(&self, cut: &FieldPoly, roots: &[KIsolated]) -> Kr<Vec<BigRational>> {
        let Some(first) = roots.first() else {
            return Ok(vec![BigRational::zero()]);
        };
        let chain = KSturm::new(self, cut)?;
        let mut samples = vec![first.lo.clone()];
        for window in roots.windows(2) {
            let (previous, next) = (&window[0], &window[1]);
            let separator = if previous.exact {
                if previous.hi < next.lo {
                    next.lo.clone()
                } else {
                    self.strictly_below_root(&chain, &next.lo, &next.hi)?
                }
            } else {
                previous.hi.clone()
            };
            samples.push(separator);
        }
        let last = roots.last().expect("roots is non-empty");
        samples.push(&last.hi + BigRational::one());
        Ok(samples)
    }

    /// A rational strictly above `lo` and strictly below the unique root of the
    /// cut polynomial in `(lo, hi]`.
    fn strictly_below_root(
        &self,
        chain: &KSturm,
        lo: &BigRational,
        hi: &BigRational,
    ) -> Kr<BigRational> {
        let mut hi = hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let mid = (lo + &hi) / two();
            if chain.count_in(self, lo, &mid)? == 0 {
                return Ok(mid);
            }
            hi = mid;
        }
        Err(declined("two K-roots did not separate within the budget"))
    }
}

// ============================================================================
// Fibre sample points.
// ============================================================================

/// A point of ℝ named exactly inside the fibre: a rational, or the unique real
/// root of a `K`-polynomial in a rational bracket `(lower, upper]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldSample {
    /// An exact rational.
    Rational(BigRational),
    /// The unique real root of `defining` in `(lower, upper]`.
    Algebraic {
        /// The defining polynomial over `K`, LSB-first in `y`.
        defining: FieldPoly,
        /// The bracket's lower endpoint (exclusive).
        lower: BigRational,
        /// The bracket's upper endpoint (inclusive).
        upper: BigRational,
    },
}

impl FieldSample {
    fn from_isolated(defining: &FieldPoly, root: &KIsolated) -> FieldSample {
        if root.exact {
            FieldSample::Rational(root.hi.clone())
        } else {
            FieldSample::Algebraic {
                defining: defining.clone(),
                lower: root.lo.clone(),
                upper: root.hi.clone(),
            }
        }
    }
}

impl RealField {
    /// The exact sign of the `K`-polynomial `q` at a fibre sample.
    fn ksign_at_sample(&self, q: &FieldPoly, sample: &FieldSample) -> Kr<i8> {
        match sample {
            FieldSample::Rational(value) => {
                let evaluated = self.keval(q, value);
                Ok(self.sign(&evaluated)?)
            }
            FieldSample::Algebraic {
                defining,
                lower,
                upper,
            } => self.ksign_at_algebraic(q, defining, lower, upper),
        }
    }

    /// The sign of `q` at the unique root `β` of `defining` in `(lo, hi]`.
    ///
    /// `q(β) = 0` is settled *exactly*, by asking whether `gcd(defining, q)` has
    /// a root in the bracket. Only when the answer is "no" is the bracket
    /// refined, and then until `q` has **no** root inside it at all.
    fn ksign_at_algebraic(
        &self,
        q: &FieldPoly,
        defining: &FieldPoly,
        lo: &BigRational,
        hi: &BigRational,
    ) -> Kr<i8> {
        let trimmed = self.ktrim(q.clone())?;
        let Some(q_degree) = kdegree(&trimmed) else {
            return Ok(0);
        };
        let common = self.kgcd(defining, &trimmed)?;
        if kdegree(&common).is_some_and(|d| d >= 1)
            && KSturm::new(self, &common)?.count_in(self, lo, hi)? >= 1
        {
            return Ok(0);
        }
        if q_degree == 0 {
            return Ok(self.sign(&trimmed[0])?);
        }
        let defining_chain = KSturm::new(self, defining)?;
        let q_chain = KSturm::new(self, &trimmed)?;
        let mut lo = lo.clone();
        let mut hi = hi.clone();
        for _ in 0..MAX_REFINE_STEPS {
            if q_chain.count_in(self, &lo, &hi)? == 0 {
                let value = self.keval(&trimmed, &hi);
                return Ok(self.sign(&value)?);
            }
            let mid = (&lo + &hi) / two();
            if defining_chain.count_in(self, &lo, &mid)? == 1 {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        Err(declined(
            "the sign at a K-algebraic sample ran out of budget",
        ))
    }

    /// Where a fibre sample sits relative to a rational.
    fn kcompare_to_rational(&self, sample: &FieldSample, x: &BigRational) -> Kr<Ordering> {
        let (defining, lower, upper) = match sample {
            FieldSample::Rational(value) => return Ok(value.cmp(x)),
            FieldSample::Algebraic {
                defining,
                lower,
                upper,
            } => (defining, lower, upper),
        };
        let value = self.keval(defining, x);
        if self.sign(&value)? == 0 && lower < x && x <= upper {
            return Ok(Ordering::Equal);
        }
        let chain = KSturm::new(self, defining)?;
        let mut lo = lower.clone();
        let mut hi = upper.clone();
        for _ in 0..MAX_REFINE_STEPS {
            if *x <= lo {
                return Ok(Ordering::Greater);
            }
            if *x > hi {
                return Ok(Ordering::Less);
            }
            let mid = (&lo + &hi) / two();
            if chain.count_in(self, &lo, &mid)? == 1 {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        Err(declined("a K-algebraic comparison ran out of budget"))
    }
}

// ============================================================================
// Atoms, certificates, and their checkers.
// ============================================================================

/// One fibre conjunct `q(y) ▷ 0` with `q ∈ K[y]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldAtom {
    /// The polynomial in `y` over `K`.
    pub poly: FieldPoly,
    /// The comparison against `0`.
    pub relation: Relation,
}

/// A bivariate atom as this module wants it: `coefficients[j]` is the ℚ
/// polynomial in `x` multiplying `yʲ`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionAtom {
    /// The `y`-coefficients, each an LSB-first ℚ polynomial in `x`.
    pub coefficients: Vec<Vec<BigRational>>,
    /// The comparison against `0`.
    pub relation: Relation,
}

/// Substitute `x = α` into every atom: each `y`-coefficient is reduced modulo
/// the field's modulus.
///
/// This is a **pure function of the field and the atoms**, which is what lets a
/// checker re-derive the substituted fibre rather than trust the producer's.
pub fn substitute(field: &RealField, atoms: &[SubstitutionAtom]) -> Vec<FieldAtom> {
    atoms
        .iter()
        .map(|atom| {
            let mut poly: FieldPoly = atom.coefficients.iter().map(|c| field.reduce(c)).collect();
            while poly.last().is_some_and(|c| big::degree(c).is_none()) {
                poly.pop();
            }
            FieldAtom {
                poly,
                relation: atom.relation,
            }
        })
        .collect()
}

/// Witness that the fibre is **satisfiable**: one `y` at which every conjunct
/// holds, with the sign of every conjunct there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FibreWitness {
    /// The satisfying `y`.
    pub sample: FieldSample,
    /// `signs[i]` is the claimed sign at `α` of `atoms[i].poly` at `sample`.
    pub signs: Vec<i8>,
}

/// The conjunct that fails in one `y`-cell, and its sign there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FibreCellFailure {
    /// Index into the fibre's conjuncts.
    pub conjunct: usize,
    /// The sign that conjunct takes in this cell.
    pub sign: i8,
}

/// Witness that the fibre is **unsatisfiable**: the sign-invariant cell
/// decomposition of the `y`-line over `K`, and a failing conjunct per cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FibreRefutation {
    /// The distinct real roots of all the `qᵢ` over `K`, ascending.
    pub roots: Vec<FieldSample>,
    /// One rational sample per open cell; `roots.len() + 1` of them.
    pub open_samples: Vec<BigRational>,
    /// One failing conjunct per cell; `2·roots.len() + 1` of them.
    pub failures: Vec<FibreCellFailure>,
}

/// The verdict on a fibre, with its witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FibreDecision {
    /// Satisfiable.
    True(Box<FibreWitness>),
    /// Unsatisfiable.
    False(Box<FibreRefutation>),
}

/// The whole fibre over `x = α`, certificate and all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FibreCertificate {
    /// `α`'s defining polynomial: a square-free divisor of the caller's cut
    /// polynomial with `α` as its unique root in the bracket.
    pub modulus: Vec<BigRational>,
    /// `α`'s bracket, lower endpoint (exclusive).
    pub lower: BigRational,
    /// `α`'s bracket, upper endpoint (inclusive).
    pub upper: BigRational,
    /// The substituted atoms, with coefficients in `K`.
    pub atoms: Vec<FieldAtom>,
    /// The verdict and its witness.
    pub decision: FibreDecision,
}

impl FibreCertificate {
    /// The recorded verdict, without checking it.
    pub fn verdict(&self) -> bool {
        matches!(self.decision, FibreDecision::True(_))
    }

    /// Re-derive the fibre's verdict from the recorded modulus, bracket and
    /// atoms alone.
    ///
    /// Nothing the producer computed is reused: `α` is re-isolated by an
    /// independent Sturm count, every sign at `α` is recomputed by its own
    /// bracket refinement, and every `y`-cell is re-checked.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<bool, Fault> {
        let field = RealField::new(&self.modulus, &self.lower, &self.upper)?;
        match &self.decision {
            FibreDecision::True(witness) => check_witness(&field, &self.atoms, witness)
                .map(|()| true)
                .map_err(as_fault),
            FibreDecision::False(refutation) => check_refutation(&field, &self.atoms, refutation)
                .map(|()| false)
                .map_err(as_fault),
        }
    }
}

/// Every conjunct has a recomputed sign at the witness, and every relation
/// holds there.
fn check_witness(field: &RealField, atoms: &[FieldAtom], witness: &FibreWitness) -> Kr<()> {
    if witness.signs.len() != atoms.len() {
        return Err(Fault::SignCountMismatch {
            recorded: witness.signs.len(),
            atoms: atoms.len(),
        }
        .into());
    }
    check_sample_is_isolated(field, &witness.sample)?;
    for (index, atom) in atoms.iter().enumerate() {
        let recomputed = field.ksign_at_sample(&atom.poly, &witness.sample)?;
        if recomputed != witness.signs[index] {
            return Err(Fault::SignMismatch {
                index,
                recorded: witness.signs[index],
                recomputed,
            }
            .into());
        }
        if !atom.relation.holds(recomputed) {
            return Err(Fault::RelationFails {
                index,
                sign: recomputed,
            }
            .into());
        }
    }
    Ok(())
}

/// An algebraic fibre sample's bracket really holds one root of its defining
/// polynomial, by an independent `K`-Sturm count.
fn check_sample_is_isolated(field: &RealField, sample: &FieldSample) -> Kr<()> {
    let FieldSample::Algebraic {
        defining,
        lower,
        upper,
    } = sample
    else {
        return Ok(());
    };
    let count = KSturm::new(field, defining)?.count_in(field, lower, upper)?;
    if count == 1 {
        Ok(())
    } else {
        Err(Fault::SampleNotIsolating {
            roots_in_bracket: count,
        }
        .into())
    }
}

/// The full refutation check: counts, isolation, cell order, root-list
/// completeness, and a genuinely failing conjunct in every cell.
fn check_refutation(
    field: &RealField,
    atoms: &[FieldAtom],
    refutation: &FibreRefutation,
) -> Kr<()> {
    let expected_cells = 2 * refutation.roots.len() + 1;
    if refutation.failures.len() != expected_cells {
        return Err(Fault::CellCountMismatch {
            recorded: refutation.failures.len(),
            expected: expected_cells,
        }
        .into());
    }
    let expected_open = refutation.roots.len() + 1;
    if refutation.open_samples.len() != expected_open {
        return Err(Fault::OpenSampleCountMismatch {
            recorded: refutation.open_samples.len(),
            expected: expected_open,
        }
        .into());
    }
    for root in &refutation.roots {
        check_sample_is_isolated(field, root)?;
    }
    check_cell_order(field, refutation)?;
    check_root_list_complete(field, atoms, refutation)?;
    check_every_cell_fails(field, atoms, refutation)
}

/// `open_samples[k] < βₖ < open_samples[k+1]`, so the cells cover ℝ in order.
fn check_cell_order(field: &RealField, refutation: &FibreRefutation) -> Kr<()> {
    for (index, root) in refutation.roots.iter().enumerate() {
        let below = &refutation.open_samples[index];
        let above = &refutation.open_samples[index + 1];
        if field.kcompare_to_rational(root, below)? != Ordering::Greater {
            return Err(Fault::CellOrderViolation { index }.into());
        }
        if field.kcompare_to_rational(root, above)? != Ordering::Less {
            return Err(Fault::CellOrderViolation { index: index + 1 }.into());
        }
    }
    Ok(())
}

/// Every real root over `K` of every `qᵢ` appears in the recorded list, by an
/// independent `K`-Sturm count over that `qᵢ`'s own root bound.
fn check_root_list_complete(
    field: &RealField,
    atoms: &[FieldAtom],
    refutation: &FibreRefutation,
) -> Kr<()> {
    for (atom_index, atom) in atoms.iter().enumerate() {
        let trimmed = field.ktrim(atom.poly.clone())?;
        if kdegree(&trimmed).is_none_or(|d| d == 0) {
            continue; // vanishes everywhere, or nowhere
        }
        let bound = field.root_bound(&trimmed)?;
        let sturm_count = KSturm::new(field, &trimmed)?.count_in(field, &-bound.clone(), &bound)?;
        let mut recorded = 0usize;
        for root in &refutation.roots {
            if field.ksign_at_sample(&atom.poly, root)? == 0 {
                recorded += 1;
            }
        }
        if sturm_count != recorded {
            return Err(Fault::IncompleteRootList {
                atom: atom_index,
                sturm_count,
                recorded,
            }
            .into());
        }
    }
    Ok(())
}

/// Every cell nominates a conjunct that really fails there, at the recorded
/// sign.
fn check_every_cell_fails(
    field: &RealField,
    atoms: &[FieldAtom],
    refutation: &FibreRefutation,
) -> Kr<()> {
    for (cell, failure) in refutation.failures.iter().enumerate() {
        let sample = cell_sample_of(&refutation.roots, &refutation.open_samples, cell)
            .ok_or_else(|| declined("a cell index has no sample"))?;
        let Some(atom) = atoms.get(failure.conjunct) else {
            return Err(Fault::ConjunctIndexOutOfRange {
                cell,
                index: failure.conjunct,
            }
            .into());
        };
        let recomputed = field.ksign_at_sample(&atom.poly, &sample)?;
        if recomputed != failure.sign {
            return Err(Fault::SignMismatch {
                index: failure.conjunct,
                recorded: failure.sign,
                recomputed,
            }
            .into());
        }
        if atom.relation.holds(recomputed) {
            return Err(Fault::ConjunctDoesNotFail {
                cell,
                index: failure.conjunct,
                sign: recomputed,
            }
            .into());
        }
    }
    Ok(())
}

/// The interleaved sample of cell `index`: an open sample at even indices, a
/// root at odd ones.
fn cell_sample_of(
    roots: &[FieldSample],
    open_samples: &[BigRational],
    index: usize,
) -> Option<FieldSample> {
    if index.is_multiple_of(2) {
        open_samples
            .get(index / 2)
            .cloned()
            .map(FieldSample::Rational)
    } else {
        roots.get(index / 2).cloned()
    }
}

// ============================================================================
// The producer.
// ============================================================================

/// Decide `∃y. ⋀ᵢ pᵢ(α, y) ▷ᵢ 0` where `α` is the unique real root of
/// `defining` in `(lower, upper]`.
///
/// The modulus starts as `defining` and is split on demand whenever the
/// arithmetic meets a zero divisor; the certificate records the modulus that
/// the successful run used.
///
/// # Errors
///
/// The [`Fault`] naming the guard or the step budget that stopped it. A
/// successful return is a certificate, not a bare answer: call
/// [`FibreCertificate::verify`] on it.
pub fn decide_fibre(
    defining: &[BigRational],
    lower: &BigRational,
    upper: &BigRational,
    atoms: &[SubstitutionAtom],
) -> Result<FibreCertificate, Fault> {
    let mut modulus = big::trim(defining.to_vec());
    for _ in 0..MAX_SPLITS {
        let field = RealField::new(&modulus, lower, upper)?;
        let substituted = substitute(&field, atoms);
        match decide_over_field(&field, &substituted) {
            Ok(decision) => {
                return Ok(FibreCertificate {
                    modulus,
                    lower: lower.clone(),
                    upper: upper.clone(),
                    atoms: substituted,
                    decision,
                });
            }
            Err(Inner::Split(next)) => modulus = next,
            Err(Inner::Fault(fault)) => return Err(fault),
        }
    }
    Err(Fault::Declined(
        "the modulus split more times than its degree allows".to_string(),
    ))
}

/// The cut polynomial of the fibre: the square-free part of the product of
/// every conjunct that actually depends on `y`.
fn cut_polynomial(field: &RealField, atoms: &[FieldAtom]) -> Kr<FieldPoly> {
    let mut product: FieldPoly = vec![field.one()];
    for atom in atoms {
        let trimmed = field.ktrim(atom.poly.clone())?;
        if kdegree(&trimmed).is_none_or(|d| d == 0) {
            continue;
        }
        product = field.kmul(&product, &trimmed);
    }
    field.ksquarefree(&product)
}

/// Decide the fibre with a fixed modulus, or ask for a split.
fn decide_over_field(field: &RealField, atoms: &[FieldAtom]) -> Kr<FibreDecision> {
    let cut = cut_polynomial(field, atoms)?;
    let roots = field.kisolate(&cut)?;
    let open_samples = field.open_cell_samples(&cut, &roots)?;
    let root_samples: Vec<FieldSample> = roots
        .iter()
        .map(|root| FieldSample::from_isolated(&cut, root))
        .collect();

    let cells = 2 * root_samples.len() + 1;
    let mut failures: Vec<FibreCellFailure> = Vec::with_capacity(cells);
    for cell in 0..cells {
        let sample = cell_sample_of(&root_samples, &open_samples, cell)
            .ok_or_else(|| declined("a cell index has no sample"))?;
        let mut signs: Vec<i8> = Vec::with_capacity(atoms.len());
        for atom in atoms {
            signs.push(field.ksign_at_sample(&atom.poly, &sample)?);
        }
        match first_failure(atoms, &signs) {
            None => {
                return Ok(FibreDecision::True(Box::new(FibreWitness {
                    sample,
                    signs,
                })));
            }
            Some(failure) => failures.push(failure),
        }
    }
    Ok(FibreDecision::False(Box::new(FibreRefutation {
        roots: root_samples,
        open_samples,
        failures,
    })))
}

/// The first conjunct whose relation fails at the given signs, if any.
fn first_failure(atoms: &[FieldAtom], signs: &[i8]) -> Option<FibreCellFailure> {
    for (index, atom) in atoms.iter().enumerate() {
        let sign = signs[index];
        if !atom.relation.holds(sign) {
            return Some(FibreCellFailure {
                conjunct: index,
                sign,
            });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn qp(coefficients: &[i64]) -> Vec<BigRational> {
        coefficients.iter().copied().map(q).collect()
    }

    /// `ℚ(√2)` with `√2` bracketed in `(1, 2]`.
    fn sqrt2() -> RealField {
        RealField::new(&qp(&[-2, 0, 1]), &q(1), &q(2)).expect("√2 is isolated in (1, 2]")
    }

    #[test]
    fn a_bracket_holding_two_roots_is_refused_as_a_field_presentation() {
        // (−2, 2] holds both ±√2, so it names no single α.
        assert_eq!(
            RealField::new(&qp(&[-2, 0, 1]), &q(-2), &q(2)),
            Err(Fault::ModulusNotIsolating {
                roots_in_bracket: 2
            })
        );
        // The positive control: one root, accepted.
        assert!(RealField::new(&qp(&[-2, 0, 1]), &q(1), &q(2)).is_ok());
    }

    #[test]
    fn a_constant_modulus_defines_no_algebraic_number() {
        assert_eq!(
            RealField::new(&qp(&[1]), &q(0), &q(1)),
            Err(Fault::ModulusDegenerate)
        );
    }

    #[test]
    fn alpha_squared_is_two_and_its_sign_is_computed_at_alpha() {
        let field = sqrt2();
        // α² reduces to the constant 2, so α² − 2 is the zero element.
        let squared = field.mul(&qp(&[0, 1]), &qp(&[0, 1]));
        assert_eq!(squared, qp(&[2]));
        assert_eq!(field.sign(&qp(&[0, 1])).unwrap(), 1, "α = √2 > 0");
        assert_eq!(field.sign(&qp(&[-3, 2])).unwrap(), -1, "2√2 − 3 < 0");
        assert_eq!(field.sign(&qp(&[-1, 1])).unwrap(), 1, "√2 − 1 > 0");
    }

    #[test]
    fn the_interval_fast_path_never_disagrees_with_the_exact_sign_route() {
        // The bracket here is the wide (1, 2], so both paths get exercised.
        let field = sqrt2();
        let mut decided = 0usize;
        let mut deferred = 0usize;
        for element in [
            qp(&[0, 1]),     // α
            qp(&[-3, 2]),    // 2α − 3, negative but only just
            qp(&[-1, 1]),    // α − 1
            qp(&[5]),        // a constant
            qp(&[-2, 0, 1]), // x² − 2: the *zero* element at α
        ] {
            let exact = big::sign_at_algebraic(&element, field.modulus(), &q(1), &q(2))
                .expect("the exact route decides");
            match field.interval_sign(&element) {
                Some(fast) => {
                    assert_eq!(fast, exact, "the fast path disagreed on {element:?}");
                    decided += 1;
                }
                None => deferred += 1,
            }
            assert_eq!(field.sign(&element).unwrap(), exact);
        }
        assert!(decided > 0, "the fast path must decide something");
        assert!(
            deferred > 0,
            "the fast path must defer a zero element, which it can never prove"
        );
    }

    #[test]
    fn the_inverse_in_q_sqrt_two_is_exact() {
        let field = sqrt2();
        // (1 + α)⁻¹ = (α − 1)/1 since (1+√2)(√2−1) = 1.
        let inverse = field.invert(&qp(&[1, 1])).expect("1 + √2 is a unit");
        assert_eq!(inverse, qp(&[-1, 1]));
        assert_eq!(field.mul(&qp(&[1, 1]), &inverse), qp(&[1]));
    }

    #[test]
    fn a_reducible_modulus_splits_instead_of_dividing_by_a_zero_divisor() {
        // m = (x² − 2)(x − 5), α = √2 in (1, 2]. The element x − 5 is a zero
        // divisor modulo m but is *not* zero at α, so inverting it must split.
        let modulus = big::mul(&qp(&[-2, 0, 1]), &qp(&[-5, 1]));
        let field = RealField::new(&modulus, &q(1), &q(2)).expect("√2 is isolated");
        let split = field.invert(&qp(&[-5, 1]));
        let Err(Inner::Split(next)) = split else {
            panic!("inverting a zero divisor must ask for a split");
        };
        // The side keeping α is x² − 2.
        assert_eq!(next, qp(&[-2, 0, 1]));
    }

    #[test]
    fn the_fibre_of_y_squared_equals_alpha_squared_minus_two_is_the_repeated_root_zero() {
        // ∃y. y² + (x² − 2) = 0 at x = √2: the fibre is y² = 0, a repeated root.
        let atoms = vec![SubstitutionAtom {
            coefficients: vec![qp(&[-2, 0, 1]), qp(&[0]), qp(&[1])],
            relation: Relation::Eq,
        }];
        let certificate =
            decide_fibre(&qp(&[-2, 0, 1]), &q(1), &q(2), &atoms).expect("the fibre decides");
        assert!(certificate.verify().expect("the certificate verifies"));
        let FibreDecision::True(witness) = &certificate.decision else {
            panic!("y = 0 satisfies it");
        };
        assert_eq!(witness.sample, FieldSample::Rational(BigRational::zero()));
        // The substituted constant term is the *zero element* of K: x² − 2
        // reduces to nothing modulo x² − 2.
        assert_eq!(certificate.atoms[0].poly[0], Element::new());
    }

    #[test]
    fn a_forged_sign_at_alpha_is_refused_by_the_fibre_checker() {
        let atoms = vec![SubstitutionAtom {
            coefficients: vec![qp(&[0]), qp(&[1])],
            relation: Relation::Gt,
        }];
        let mut certificate =
            decide_fibre(&qp(&[-2, 0, 1]), &q(1), &q(2), &atoms).expect("the fibre decides");
        let FibreDecision::True(witness) = &mut certificate.decision else {
            panic!("y > 0 is satisfiable");
        };
        witness.signs[0] = -witness.signs[0];
        assert!(matches!(
            certificate.verify(),
            Err(Fault::SignMismatch { index: 0, .. })
        ));
    }

    #[test]
    fn a_modulus_whose_bracket_was_widened_is_refused() {
        let atoms = vec![SubstitutionAtom {
            coefficients: vec![qp(&[0]), qp(&[1])],
            relation: Relation::Gt,
        }];
        let mut certificate =
            decide_fibre(&qp(&[-2, 0, 1]), &q(1), &q(2), &atoms).expect("the fibre decides");
        certificate.lower = q(-2);
        assert_eq!(
            certificate.verify(),
            Err(Fault::ModulusNotIsolating {
                roots_in_bracket: 2
            })
        );
    }
}
