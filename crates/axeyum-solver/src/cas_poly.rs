//! The CAS bridge: exact polynomial normalization through `axeyum-cas`, used to
//! refute arithmetic disequalities and integer unit/divisibility equations
//! (ADR-0386).
//!
//! This is the **untrusted fast search** half of the bridge. It abstracts every
//! non-polynomial subterm of an assertion into an opaque atom, normalizes what
//! is left with [`MvPoly`] — `axeyum-cas`'s canonical sparse multivariate
//! polynomial over ℚ — and reads a refutation off the normal form. Two routes
//! are built on it:
//!
//! * [`cas_identity_refutation`] — an asserted `not (= lhs rhs)` whose two sides
//!   have the *same* polynomial normal form is unsatisfiable. This subsumes the
//!   reflexive case of [`crate::term_identity`] for arithmetic sorts and
//!   generalizes it from a syntactic match to a full ring normal form, so it
//!   fires through arbitrary re-association, re-ordering, distribution and
//!   cancellation.
//! * [`cas_int_units_refutation`] — an asserted integer equation whose normal
//!   form is `k·m = c` for a single monomial `m` is refuted when `k ∤ c`, or when
//!   an asserted bound puts one of `m`'s factors outside the divisors of `c/k`.
//!   `a ≥ 2 ∧ a·p = 1` is the smallest instance: `|a| ≤ 1` for any unit, so the
//!   bound refutes. Integer bit-blasting cannot close this — it reports "no
//!   model within the bounded integer width", which is `unknown`, not `unsat`.
//!
//! # Trust
//!
//! Neither route is trusted. Each builds a certificate and hands it to
//! [`crate::cas_certificate`], a checker that imports nothing from `axeyum-cas`
//! and re-derives the refutation from the original assertions with its own
//! expander. A refutation whose certificate does not re-check is **discarded**
//! (reported as [`CasOutcome::VerifierRejected`]), never returned. `MvPoly` is
//! therefore a search engine here, not an oracle.

use std::collections::BTreeMap;

use axeyum_cas::{
    CofactorLimits, CofactorOutcome, MvPoly, reduce_many_with_cofactors, reduce_with_cofactors,
    unit_ideal_cofactors,
};
use axeyum_ir::{Op, Rational, Sort, TermArena, TermId, TermNode};

use crate::cas_certificate::{
    AtomMonomial, AtomPoly, MAX_ATOMS, MAX_DEPTH, MAX_MONOMIALS, MAX_STEPS,
    check_cas_ideal_certificate, check_cas_identity_certificate, check_cas_int_units_certificate,
    derive_bound, match_disequality, match_equality, top_conjuncts,
};

/// A self-checking refutation of an asserted arithmetic disequality whose two
/// sides share a polynomial normal form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CasIdentityCertificate {
    /// The top-level conjunct asserting `not (= lhs rhs)`.
    pub assertion: TermId,
    /// The left side of the negated equality.
    pub lhs: TermId,
    /// The right side of the negated equality.
    pub rhs: TermId,
    /// The shared canonical normal form of `lhs` and `rhs`, over the opaque
    /// atoms both sides were abstracted to. This is the re-checkable witness:
    /// [`check_cas_identity_certificate`] re-expands both sides independently
    /// and compares against it.
    pub normal_form: AtomPoly,
}

/// Which arithmetic fact refutes an integer `k·m = c` equation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CasIntUnitsKind {
    /// `k ∤ c`: the monomial is an integer, so `k·m` only ever hits multiples of
    /// `k`, and `c` is not one. No bounds are needed.
    CoefficientNonDivisor,
    /// `c ≠ 0`, so every factor of `m` divides `c/k` and lies in
    /// `[−|c/k|, |c/k|]`; an asserted bound puts one of them outside that window.
    DivisorBound,
    /// `c = 0`, so some factor of `m` must be zero; every factor is bounded away
    /// from zero.
    ZeroProduct,
}

/// An integer bound on one opaque atom, together with the asserted conjunct that
/// states it. The checker re-reads the bound off `source` rather than trusting
/// the numbers here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CasIntBound {
    /// The top-level conjunct asserting the bound.
    pub source: TermId,
    /// The bounded atom.
    pub atom: TermId,
    /// Claimed lower bound (`atom ≥ lower`).
    pub lower: Option<i128>,
    /// Claimed upper bound (`atom ≤ upper`).
    pub upper: Option<i128>,
}

/// A self-checking refutation of an integer equation of the form `k·m = c`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CasIntUnitsCertificate {
    /// The top-level conjunct asserting the equation.
    pub equation: TermId,
    /// Which arithmetic fact refutes it.
    pub kind: CasIntUnitsKind,
    /// The single non-constant monomial `m` of the equation's normal form, as
    /// `(atom, exponent)` pairs sorted by atom.
    pub monomial: AtomMonomial,
    /// The integer coefficient `k` of `m` (never zero).
    pub coefficient: i128,
    /// The integer constant `c`, so the equation reads `k·m = c`.
    pub constant: i128,
    /// The asserted bounds the refutation uses (empty for
    /// [`CasIntUnitsKind::CoefficientNonDivisor`]).
    pub bounds: Vec<CasIntBound>,
}

// --- route 3: ideal / positivity combination ---------------------------------

/// The arithmetic fact a cited top-level conjunct contributes to a
/// [`CasIdealCertificate`], always oriented as `poly ⋈ 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CasHypothesisKind {
    /// From an `=`: the polynomial is zero in every model.
    Equality,
    /// From a `≥` or `≤`: the polynomial is non-negative in every model.
    NonNegative,
    /// From a `>` or `<`: the polynomial is strictly positive in every model.
    Positive,
}

/// One term of the linear combination a [`CasIdealCertificate`] exhibits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CasIdealEntry {
    /// A cited top-level conjunct, the fact it asserts, and the multiplier
    /// applied to that fact.
    ///
    /// For [`CasHypothesisKind::Equality`] the multiplier is an arbitrary
    /// polynomial — that is what makes the certificate a Nullstellensatz one. For
    /// the two inequality kinds it must be a **strictly positive rational
    /// constant**: a polynomial multiplier can take a negative value and would
    /// flip the inequality.
    Asserted {
        /// The top-level conjunct this entry reads its fact off.
        conjunct: TermId,
        /// Which fact that conjunct asserts.
        kind: CasHypothesisKind,
        /// The polynomial (equalities) or positive rational constant
        /// (inequalities) the fact is multiplied by.
        multiplier: AtomPoly,
    },
    /// A tautological non-negative term `coefficient · monomial` whose every
    /// exponent is even. No citation is needed: an even power of a real number is
    /// non-negative, so `coefficient > 0` makes the whole term non-negative at
    /// every valuation of the atoms.
    ///
    /// This is what lets the route close systems whose refutation needs a fact
    /// nobody wrote down — `x + y = 3 ∧ x·y = 5` is unsatisfiable over ℝ because
    /// `x² + y²` is congruent to `−1` modulo the ideal, and no assertion mentions
    /// `x² + y²`.
    EvenMonomial {
        /// The monomial, every exponent even and every atom `Int`/`Real`-sorted.
        monomial: AtomMonomial,
        /// A strictly positive rational coefficient.
        coefficient: Rational,
    },
    /// The **product** of two cited non-negativities, scaled by a strictly
    /// positive rational constant. `p ≥ 0` and `q ≥ 0` give `p·q ≥ 0` at every
    /// real valuation, so this contributes non-negatively without either factor
    /// being a constant.
    ///
    /// This is the entry that reaches a degree-2 argument no rational multiplier
    /// can express. `M ≥ 1 ∧ w ≥ 1 ⊢ M·w ≥ M` is the smallest instance and is
    /// exactly the Rado campaign's micro-lemma `M6`: the refutation is
    /// `(M − M·w) + (M−1)(w−1) + (w−1) = 0`, and the middle term is the product
    /// of the two asserted bounds. No strictness is ever claimed for a product,
    /// even when both factors are strict.
    AssertedProduct {
        /// The first cited conjunct; must assert a non-negativity or positivity.
        first: TermId,
        /// The second cited conjunct; may be the same as `first` (a square).
        second: TermId,
        /// A strictly positive rational constant, as an [`AtomPoly`].
        multiplier: AtomPoly,
    },
}

/// A self-checking refutation exhibiting an explicit linear combination of
/// asserted arithmetic facts (and tautological squares) that collapses to a
/// constant contradicting its own sign.
///
/// This generalizes [`CasIdentityCertificate`], which is the one-entry case with
/// multiplier `1`. Its verification is described in full on
/// [`check_cas_ideal_certificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CasIdealCertificate {
    /// The terms of the combination, in a deterministic order.
    pub entries: Vec<CasIdealEntry>,
    /// The constant the combination is claimed to equal. Re-derived by the
    /// checker; stored so a printed certificate is auditable.
    pub constant: Rational,
}

/// What a CAS route concluded. Every variant other than [`CasOutcome::Refuted`]
/// is a **decline**, and each carries enough detail to explain the decline in a
/// route trace — silent declines are the diagnosability bug this dispatch has
/// already been bitten by once (see the `record_nia_decline` note in
/// `crate::auto`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CasOutcome<C> {
    /// The route refuted the query; the certificate re-checked.
    Refuted(C),
    /// No assertion had a shape this route handles, so nothing ran.
    NoCandidate,
    /// A candidate shape was present but was not refuted; the payload says why.
    NotRefuted(&'static str),
    /// A candidate refutation was found but the independent checker rejected it,
    /// so it was discarded. **This is never expected**: it means the CAS normal
    /// form and the checker's expansion disagree, and it should be investigated
    /// rather than tolerated.
    VerifierRejected,
}

// --- term → MvPoly -----------------------------------------------------------

/// The opaque-atom abstraction shared by both sides of one comparison.
///
/// Atoms are interned by [`TermId`]. The arena is hash-consed, so distinct ids
/// are distinct syntactic terms and two atoms are identified exactly when they
/// are the same term — the only identification that would be unsound is merging
/// two different terms, which cannot happen here.
#[derive(Debug, Default)]
struct AtomTable {
    order: Vec<TermId>,
    index: BTreeMap<TermId, usize>,
}

impl AtomTable {
    fn intern(&mut self, term: TermId) -> Option<usize> {
        if let Some(&existing) = self.index.get(&term) {
            return Some(existing);
        }
        if self.order.len() >= MAX_ATOMS {
            return None;
        }
        let next = self.order.len();
        self.order.push(term);
        self.index.insert(term, next);
        Some(next)
    }

    /// The `MvPoly` variable name for atom `index`.
    ///
    /// Zero-padded so `MvPoly`'s alphabetical variable ranking coincides with the
    /// numeric one; the normal form is re-sorted by [`TermId`] before it reaches
    /// a certificate, so this only affects `MvPoly`-internal ordering, but a
    /// deterministic public artifact starts with deterministic names.
    fn name(index: usize) -> String {
        format!("v{index:06}")
    }

    fn term_of(&self, name: &str) -> Option<TermId> {
        let index: usize = name.strip_prefix('v')?.parse().ok()?;
        self.order.get(index).copied()
    }

    /// The interned atoms in interning order — deterministic, since interning
    /// follows the deterministic term walk.
    fn atoms(&self) -> &[TermId] {
        &self.order
    }

    fn len(&self) -> usize {
        self.order.len()
    }

    fn index_of(&self, term: TermId) -> Option<usize> {
        self.index.get(&term).copied()
    }
}

/// Normalizes `term` into an [`MvPoly`] over the opaque atoms in `table`.
///
/// Returns `None` when the term leaves the handled fragment, when a coefficient
/// or exponent would leave the exact `i128`/`u32` range, or when one of the
/// deterministic ceilings (atoms, monomials, steps, depth) trips. Declining is
/// always safe: the caller reports `unknown`, never a verdict.
fn to_poly(
    arena: &TermArena,
    term: TermId,
    table: &mut AtomTable,
    steps: &mut u32,
    depth: u32,
) -> Option<MvPoly> {
    if depth > MAX_DEPTH {
        return None;
    }
    *steps = steps.checked_sub(1)?;

    let poly = match arena.node(term) {
        TermNode::IntConst(value) => MvPoly::constant(Rational::checked_new(*value, 1)?),
        TermNode::RealConst(value) => MvPoly::constant(*value),
        TermNode::App { op, args } => match op {
            Op::IntAdd | Op::RealAdd => {
                let mut acc = MvPoly::zero();
                for &arg in args {
                    acc = acc.add(&to_poly(arena, arg, table, steps, depth + 1)?)?;
                    capped(&acc)?;
                }
                acc
            }
            Op::IntSub | Op::RealSub => {
                // SMT-LIB's `-` is unary negation at arity 1 and subtraction at
                // arity >= 2. The arena only ever builds `IntSub`/`RealSub`
                // binary (unary `-` becomes `IntNeg`/`RealNeg`), but reading a
                // one-argument node as "the first operand" would silently drop
                // the negation, so the arity is required rather than assumed.
                if args.len() < 2 {
                    return None;
                }
                let mut iter = args.iter();
                let mut acc = to_poly(arena, *iter.next()?, table, steps, depth + 1)?;
                for &arg in iter {
                    acc = acc.sub(&to_poly(arena, arg, table, steps, depth + 1)?)?;
                    capped(&acc)?;
                }
                acc
            }
            Op::IntNeg | Op::RealNeg => {
                let [inner] = &**args else { return None };
                to_poly(arena, *inner, table, steps, depth + 1)?.neg()?
            }
            Op::IntMul | Op::RealMul => {
                let mut acc = MvPoly::constant(Rational::integer(1));
                for &arg in args {
                    acc = acc.mul(&to_poly(arena, arg, table, steps, depth + 1)?)?;
                    capped(&acc)?;
                }
                acc
            }
            // `/` by a nonzero rational literal is exact scaling. Every other
            // divisor — including a literal zero, whose SMT-LIB value is
            // unspecified — falls through to the opaque-atom case.
            Op::RealDiv if divisors_are_nonzero_literals(arena, args) => {
                let mut iter = args.iter();
                let mut acc = to_poly(arena, *iter.next()?, table, steps, depth + 1)?;
                for &arg in iter {
                    let TermNode::RealConst(value) = arena.node(arg) else {
                        return None;
                    };
                    let scale = Rational::checked_new(value.denominator(), value.numerator())?;
                    acc = acc.mul(&MvPoly::constant(scale))?;
                    capped(&acc)?;
                }
                acc
            }
            _ => atom_poly(arena, term, table)?,
        },
        _ => atom_poly(arena, term, table)?,
    };
    capped(&poly)?;
    Some(poly)
}

fn capped(poly: &MvPoly) -> Option<()> {
    (poly.term_count() <= MAX_MONOMIALS).then_some(())
}

fn divisors_are_nonzero_literals(arena: &TermArena, args: &[TermId]) -> bool {
    args.len() >= 2
        && args[1..]
            .iter()
            .all(|&arg| matches!(arena.node(arg), TermNode::RealConst(v) if !v.is_zero()))
}

fn atom_poly(arena: &TermArena, term: TermId, table: &mut AtomTable) -> Option<MvPoly> {
    if !matches!(arena.sort_of(term), Sort::Int | Sort::Real) {
        return None;
    }
    Some(MvPoly::var(&AtomTable::name(table.intern(term)?)))
}

/// Re-keys an [`MvPoly`] normal form from `MvPoly` variable names onto the
/// [`TermId`]s of the atoms, in the canonical order the checker uses.
fn normal_form(poly: &MvPoly, table: &AtomTable) -> Option<AtomPoly> {
    let mut out: AtomPoly = Vec::with_capacity(poly.term_count());
    for (mono, coeff) in poly.terms() {
        let mut factors: AtomMonomial = Vec::new();
        for (name, exp) in mono.powers() {
            factors.push((table.term_of(name)?, exp));
        }
        factors.sort_unstable();
        out.push((factors, *coeff));
    }
    out.sort_by(|left, right| left.0.cmp(&right.0));
    Some(out)
}

// --- route 1: polynomial identity refutation ---------------------------------

/// Refutes an asserted arithmetic disequality whose two sides are equal as
/// polynomials in their opaque atoms.
///
/// Sound because polynomial identity in the atoms means the two sides denote the
/// same value *for every* assignment to those atoms — in particular for whatever
/// the abstracted subterms actually denote — so `not (= lhs rhs)` has no model
/// and the whole conjunction is `unsat`.
///
/// The returned certificate has already passed
/// [`check_cas_identity_certificate`]; a candidate that fails it is reported as
/// [`CasOutcome::VerifierRejected`] instead.
#[must_use]
pub fn cas_identity_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> CasOutcome<CasIdentityCertificate> {
    let mut saw_candidate = false;
    let mut declined = "no arithmetic disequality had equal polynomial normal forms";

    for assertion in top_conjuncts(arena, assertions) {
        let Some((lhs, rhs)) = match_disequality(arena, assertion) else {
            continue;
        };
        if !matches!(arena.sort_of(lhs), Sort::Int | Sort::Real)
            || arena.sort_of(lhs) != arena.sort_of(rhs)
        {
            continue;
        }
        saw_candidate = true;

        let mut table = AtomTable::default();
        let mut steps = MAX_STEPS;
        let (Some(left), Some(right)) = (
            to_poly(arena, lhs, &mut table, &mut steps, 0),
            to_poly(arena, rhs, &mut table, &mut steps, 0),
        ) else {
            declined = "polynomial normalization hit a ceiling or left the handled fragment";
            continue;
        };
        let Some(difference) = left.sub(&right) else {
            declined = "polynomial subtraction overflowed the exact coefficient range";
            continue;
        };
        if !difference.is_zero() {
            continue;
        }
        let Some(form) = normal_form(&left, &table) else {
            declined = "normal form could not be re-keyed onto the abstracted atoms";
            continue;
        };
        let cert = CasIdentityCertificate {
            assertion,
            lhs,
            rhs,
            normal_form: form,
        };
        if !check_cas_identity_certificate(arena, assertions, &cert) {
            return CasOutcome::VerifierRejected;
        }
        return CasOutcome::Refuted(cert);
    }

    if saw_candidate {
        CasOutcome::NotRefuted(declined)
    } else {
        CasOutcome::NoCandidate
    }
}

// --- route 2: integer units and divisibility ---------------------------------

/// Refutes an asserted integer equation whose normal form is `k·m = c` for a
/// single monomial `m`, using divisibility rather than bit-blasting.
///
/// Three exact facts close the shapes the width ladder reports `unknown` on:
///
/// * `k ∤ c` — `m` takes integer values, so `k·m` cannot equal `c`.
/// * `c ≠ 0` — each factor of `m` divides `c/k`, hence `1 ≤ |factor| ≤ |c/k|`; an
///   asserted bound outside that window refutes. `a ≥ 2 ∧ a·p = 1` is this case
///   with `|c/k| = 1`.
/// * `c = 0` — some factor is zero; if every factor is bounded away from zero,
///   the equation has no solution.
///
/// The returned certificate has already passed
/// [`check_cas_int_units_certificate`].
#[must_use]
pub fn cas_int_units_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> CasOutcome<CasIntUnitsCertificate> {
    let conjuncts = top_conjuncts(arena, assertions);
    let mut saw_candidate = false;
    let mut declined = "no integer equation normalized to a refutable k·m = c";

    for &equation in &conjuncts {
        let Some((lhs, rhs)) = match_equality(arena, equation) else {
            continue;
        };
        if arena.sort_of(lhs) != Sort::Int || arena.sort_of(rhs) != Sort::Int {
            continue;
        }
        saw_candidate = true;

        let mut table = AtomTable::default();
        let mut steps = MAX_STEPS;
        let (Some(left), Some(right)) = (
            to_poly(arena, lhs, &mut table, &mut steps, 0),
            to_poly(arena, rhs, &mut table, &mut steps, 0),
        ) else {
            declined = "polynomial normalization hit a ceiling or left the handled fragment";
            continue;
        };
        let Some(difference) = left.sub(&right) else {
            declined = "polynomial subtraction overflowed the exact coefficient range";
            continue;
        };
        let Some(form) = normal_form(&difference, &table) else {
            declined = "normal form could not be re-keyed onto the abstracted atoms";
            continue;
        };
        let Some((monomial, coefficient, constant)) = single_monomial_equation(&form) else {
            continue;
        };
        let Some(cert) =
            refute_monomial_equation(arena, &conjuncts, equation, monomial, coefficient, constant)
        else {
            declined = "normalized to k·m = c, but no asserted bound puts a factor of m \
                        outside the divisors of c/k";
            continue;
        };
        if !check_cas_int_units_certificate(arena, assertions, &cert) {
            return CasOutcome::VerifierRejected;
        }
        return CasOutcome::Refuted(cert);
    }

    if saw_candidate {
        CasOutcome::NotRefuted(declined)
    } else {
        CasOutcome::NoCandidate
    }
}

// --- route 3: multivariate ideal / positivity refutation ---------------------

/// Ceiling on asserted equations used as ideal generators.
const MAX_IDEAL_GENERATORS: usize = 8;
/// Ceiling on asserted inequalities considered as combination terms.
const MAX_IDEAL_INEQUALITIES: usize = 8;
/// Ceiling on distinct opaque atoms across the whole system. `Buchberger` under
/// `lex` is doubly exponential in the variable count in the worst case, so this
/// is the ceiling that actually bounds the search; the step budget below is the
/// backstop.
const MAX_IDEAL_ATOMS: usize = 8;

/// Step ceilings for the cofactor-tracked Gröbner search. Step *counts*, never a
/// clock — determinism is a public API promise.
fn ideal_limits() -> CofactorLimits {
    CofactorLimits {
        reduction_steps: 6_000,
        pair_iterations: 1_500,
        basis_size: 32,
        poly_terms: 256,
    }
}

/// One asserted hypothesis, normalized to `poly ⋈ 0` over the shared atoms.
struct Hypothesis {
    conjunct: TermId,
    kind: CasHypothesisKind,
    poly: MvPoly,
    /// `p > 0` strengthens to `p ≥ 1` when the comparison is integer-sorted and
    /// the polynomial has integer coefficients.
    integer_valued: bool,
}

/// Refutes a **system** of asserted polynomial (in)equalities by exhibiting an
/// explicit combination of them that collapses to a constant of the wrong sign.
///
/// This is the multivariate generalization of [`cas_identity_refutation`], and it
/// is the route that reaches shapes no other engine in the dispatch does. The
/// existing nonlinear engines are structurally narrower:
/// `nra_real_root` decides one shared real variable exactly and a two-variable
/// component by resultants; `nra` admits at most two cross-products before
/// declining ("this needs a nlsat/CAD engine"); `nia-bounded-blast` needs a
/// provable finite box on every variable; `int-blast-ladder` answers a symbolic
/// system with "no model within the bounded integer width 32", which is
/// `unknown`. None of them reasons about the *ideal* the equations generate.
///
/// Three refutation shapes are tried, in this order:
///
/// 1. **Unit ideal.** `1 = Σ cᵢ·gᵢ` for the asserted equations `gᵢ = 0` — the
///    weak Nullstellensatz. The system then has no common zero over any field
///    containing ℚ, so none over ℝ and none over ℤ.
/// 2. **Squares modulo the ideal.** A sum of squares of atoms that is congruent
///    to a *negative* constant modulo the ideal. `x + y = 3 ∧ x·y = 5` is the
///    smallest instance: `x² + y² ≡ 9 − 10 = −1`, and a sum of squares cannot be
///    negative. Note that nothing in the query mentions `x² + y²` — the square
///    terms are tautologies the certificate supplies.
/// 3. **An asserted inequality modulo the ideal.** An asserted `p ⋈ 0` whose
///    normal form modulo the equations is a constant that contradicts `⋈`.
///
/// Every candidate is handed to [`check_cas_ideal_certificate`], which re-derives
/// the whole combination without any `axeyum-cas` code in the loop. A candidate
/// that fails is reported as [`CasOutcome::VerifierRejected`], never returned.
#[must_use]
pub fn cas_ideal_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> CasOutcome<CasIdealCertificate> {
    let conjuncts = top_conjuncts(arena, assertions);
    let mut table = AtomTable::default();
    let mut steps = MAX_STEPS;
    let mut equalities: Vec<Hypothesis> = Vec::new();
    let mut inequalities: Vec<Hypothesis> = Vec::new();
    let mut nonlinear = false;

    for &conjunct in &conjuncts {
        let Some((kind, high, low, sort)) = comparison_shape(arena, conjunct) else {
            continue;
        };
        let (Some(left), Some(right)) = (
            to_poly(arena, high, &mut table, &mut steps, 0),
            to_poly(arena, low, &mut table, &mut steps, 0),
        ) else {
            continue;
        };
        let Some(poly) = left.sub(&right) else {
            continue;
        };
        if poly.total_degree() >= 2 {
            nonlinear = true;
        }
        let integer_valued = sort == Sort::Int && poly.terms().all(|(_, coeff)| coeff.is_integer());
        let hypothesis = Hypothesis {
            conjunct,
            kind,
            poly,
            integer_valued,
        };
        match kind {
            CasHypothesisKind::Equality => equalities.push(hypothesis),
            CasHypothesisKind::NonNegative | CasHypothesisKind::Positive => {
                inequalities.push(hypothesis);
            }
        }
    }

    // The route earns its place only on systems the linear engines cannot handle.
    // A purely linear system is `lia-simplex`/`lra`'s job and is decided far
    // faster there, so declining here keeps the fast path free.
    //
    // An *equation-free* system is still a candidate: the positivity search below
    // needs no ideal at all (`M ≥ 1 ∧ w ≥ 1 ∧ M·w < M` has no equations and is
    // refuted by the product of the two bounds). It does need two hypotheses to
    // combine.
    if !nonlinear || equalities.len() + inequalities.len() < 2 {
        return CasOutcome::NoCandidate;
    }
    if equalities.len() > MAX_IDEAL_GENERATORS
        || table.len() > MAX_IDEAL_ATOMS
        || inequalities.len() > MAX_IDEAL_INEQUALITIES
    {
        return CasOutcome::NotRefuted(
            "nonlinear system exceeds the deterministic generator/atom/inequality ceilings",
        );
    }
    inequalities.truncate(MAX_IDEAL_INEQUALITIES);

    let generators: Vec<MvPoly> = equalities.iter().map(|eq| eq.poly.clone()).collect();
    let limits = ideal_limits();

    // 1. The unit ideal: `Σ cᵢ·gᵢ = 1` with every `gᵢ = 0`.
    match unit_ideal_cofactors(&generators, limits) {
        CofactorOutcome::Reduced {
            cofactors,
            remainder,
        } if remainder.is_zero() => {
            if let Some(cert) =
                build_certificate(&table, &equalities, &cofactors, None, Rational::integer(1))
            {
                return finish(arena, assertions, cert);
            }
        }
        CofactorOutcome::Declined => {
            return CasOutcome::NotRefuted(
                "cofactor-tracked Gröbner reduction hit a deterministic step ceiling",
            );
        }
        CofactorOutcome::Reduced { .. } => {}
    }
    // 2. Sums of atom squares congruent to a negative constant modulo the ideal.
    if let Some(cert) = try_square_combination(&table, &equalities, &generators, limits) {
        return finish(arena, assertions, cert);
    }
    // 3. An asserted inequality whose normal form modulo the ideal is a constant.
    if let Some(cert) =
        try_inequality_combination(&table, &equalities, &inequalities, &generators, limits)
    {
        return finish(arena, assertions, cert);
    }
    // 4. A non-negative combination of hypotheses, their pairwise products and
    //    atom squares that collapses to a constant below its own floor.
    if let Some(cert) =
        try_positivity_combination(&table, &equalities, &inequalities, &generators, limits)
    {
        return finish(arena, assertions, cert);
    }
    CasOutcome::NotRefuted(
        "no combination of the asserted equations collapsed to a constant of the refuting sign",
    )
}

/// Searches for a sum of atom squares whose normal form modulo the ideal is a
/// *negative* constant. A sum of squares is non-negative at every real
/// valuation, so a negative congruence class refutes the equations outright.
fn try_square_combination(
    table: &AtomTable,
    equalities: &[Hypothesis],
    generators: &[MvPoly],
    limits: CofactorLimits,
) -> Option<CasIdealCertificate> {
    for squares in square_candidates(table) {
        let target = sum_of_squares(table, &squares)?;
        let CofactorOutcome::Reduced {
            cofactors,
            remainder,
        } = reduce_with_cofactors(generators, &target, limits)
        else {
            continue;
        };
        let Some(constant) = constant_value(&remainder) else {
            continue;
        };
        if constant.numerator() >= 0 {
            continue;
        }
        let Some(negated) = negate_all(&cofactors) else {
            continue;
        };
        if let Some(cert) = build_certificate(
            table,
            equalities,
            &negated,
            Some(&Contribution::Squares(&squares)),
            constant,
        ) {
            return Some(cert);
        }
    }
    None
}

/// Searches for an asserted inequality whose normal form modulo the ideal is a
/// constant its own comparison forbids.
fn try_inequality_combination(
    table: &AtomTable,
    equalities: &[Hypothesis],
    inequalities: &[Hypothesis],
    generators: &[MvPoly],
    limits: CofactorLimits,
) -> Option<CasIdealCertificate> {
    for inequality in inequalities {
        let CofactorOutcome::Reduced {
            cofactors,
            remainder,
        } = reduce_with_cofactors(generators, &inequality.poly, limits)
        else {
            continue;
        };
        let Some(constant) = constant_value(&remainder) else {
            continue;
        };
        if !contradicts(inequality, constant) {
            continue;
        }
        let Some(negated) = negate_all(&cofactors) else {
            continue;
        };
        if let Some(cert) = build_certificate(
            table,
            equalities,
            &negated,
            Some(&Contribution::Inequality(inequality)),
            constant,
        ) {
            return Some(cert);
        }
    }
    None
}

/// Ceiling on non-negative candidate terms in the positivity search. The subset
/// enumeration below is cubic in this, so it is the number that bounds the cost.
const MAX_POSITIVITY_CANDIDATES: usize = 24;
/// Largest combination the positivity search considers. Three is what the Rado
/// campaign's `M6` needs (a strict hypothesis, a product of two bounds, and one
/// bound alone) and it keeps the enumeration at a few thousand vector sums.
const MAX_POSITIVITY_SUBSET: usize = 3;

/// Where one non-negative candidate term of the positivity search came from.
#[derive(Debug, Clone, Copy)]
enum CandidateSource {
    /// An asserted inequality, used with multiplier `1`.
    Single(usize),
    /// The product of two asserted inequalities (possibly the same one twice).
    Product(usize, usize),
    /// The square of one opaque atom.
    Square(TermId),
}

/// A term known to be non-negative in every model, reduced modulo the ideal.
struct Candidate {
    source: CandidateSource,
    /// The normal form of the term modulo the asserted equations.
    residue: MvPoly,
    /// The equality cofactors that witness that reduction.
    cofactors: Vec<MvPoly>,
    /// What this term provably contributes at minimum: `1` for an
    /// integer-sorted strict inequality (`p > 0` over ℤ is `p ≥ 1`), else `0`.
    floor: Rational,
    /// True for a real-sorted strict inequality, whose contribution is strictly
    /// positive but has no rational floor.
    real_strict: bool,
}

/// Searches for a non-negative combination — of asserted inequalities, their
/// pairwise products, and atom squares — that is congruent modulo the ideal to a
/// constant strictly below the floor the combination provably exceeds.
///
/// This is the shape that needs a *product*, and no rational multiplier can
/// express it. `M ≥ 1 ∧ w ≥ 1 ∧ M·w < M` — the Rado campaign's micro-lemma `M6`,
/// which its `L3` was hand-split to reach — is refuted by
///
/// ```text
/// (M − M·w)  +  (M−1)(w−1)  +  (w−1)  =  0
/// ```
///
/// where the first term is `≥ 1` (an integer strictly above zero), the second is
/// a product of two asserted non-negativities, and the third is one of them
/// alone. The sum is identically `0`, which is below the floor `1`.
///
/// The search reduces every candidate modulo one shared Gröbner basis, then
/// enumerates unit-coefficient subsets up to [`MAX_POSITIVITY_SUBSET`]. It is
/// deliberately *incomplete*: general non-negative multipliers are a linear
/// program over the residues, which is not wired. A refutation needing `2x² + 3y²`
/// is missed.
fn try_positivity_combination(
    table: &AtomTable,
    equalities: &[Hypothesis],
    inequalities: &[Hypothesis],
    generators: &[MvPoly],
    limits: CofactorLimits,
) -> Option<CasIdealCertificate> {
    let candidates = build_candidates(table, inequalities, generators, limits)?;
    let count = candidates.len();
    // Deterministic ascending index order at every level.
    for first in 0..count {
        for second in first..count {
            for third in second..count {
                let mut chosen = vec![first];
                if second != first {
                    chosen.push(second);
                }
                if third != second {
                    chosen.push(third);
                }
                if chosen.len() > MAX_POSITIVITY_SUBSET {
                    continue;
                }
                if let Some(cert) =
                    try_subset(table, equalities, inequalities, &candidates, &chosen)
                {
                    return Some(cert);
                }
            }
        }
    }
    None
}

/// Builds the non-negative candidate terms and reduces them modulo one shared
/// Gröbner basis. `None` when a reduction declines, which makes the whole search
/// decline rather than run on a partial candidate set.
fn build_candidates(
    table: &AtomTable,
    inequalities: &[Hypothesis],
    generators: &[MvPoly],
    limits: CofactorLimits,
) -> Option<Vec<Candidate>> {
    let mut sources: Vec<(CandidateSource, MvPoly, Rational, bool)> = Vec::new();
    for (index, hypothesis) in inequalities.iter().enumerate() {
        let strict = hypothesis.kind == CasHypothesisKind::Positive;
        let floor = if strict && hypothesis.integer_valued {
            Rational::integer(1)
        } else {
            Rational::zero()
        };
        sources.push((
            CandidateSource::Single(index),
            hypothesis.poly.clone(),
            floor,
            strict && !hypothesis.integer_valued,
        ));
    }
    for left in 0..inequalities.len() {
        for right in left..inequalities.len() {
            // A product of two non-negatives is non-negative; no strictness is
            // claimed for it even when both factors are strict.
            let product = inequalities[left].poly.mul(&inequalities[right].poly)?;
            sources.push((
                CandidateSource::Product(left, right),
                product,
                Rational::zero(),
                false,
            ));
        }
    }
    for &atom in table.atoms() {
        let index = table.index_of(atom)?;
        let square = MvPoly::var(&AtomTable::name(index)).pow(2)?;
        sources.push((
            CandidateSource::Square(atom),
            square,
            Rational::zero(),
            false,
        ));
    }
    sources.truncate(MAX_POSITIVITY_CANDIDATES);

    let targets: Vec<MvPoly> = sources.iter().map(|(_, poly, _, _)| poly.clone()).collect();
    let reduced = reduce_many_with_cofactors(generators, &targets, limits);
    let mut candidates = Vec::with_capacity(sources.len());
    for ((source, _, floor, real_strict), outcome) in sources.into_iter().zip(reduced) {
        let CofactorOutcome::Reduced {
            cofactors,
            remainder,
        } = outcome
        else {
            return None;
        };
        candidates.push(Candidate {
            source,
            residue: remainder,
            cofactors,
            floor,
            real_strict,
        });
    }
    Some(candidates)
}

/// Tests one unit-coefficient subset: the residues must sum to a constant below
/// the subset's own provable floor.
fn try_subset(
    table: &AtomTable,
    equalities: &[Hypothesis],
    inequalities: &[Hypothesis],
    candidates: &[Candidate],
    chosen: &[usize],
) -> Option<CasIdealCertificate> {
    let mut residue = MvPoly::zero();
    let mut floor = Rational::zero();
    let mut real_strict = false;
    for &index in chosen {
        let candidate = &candidates[index];
        residue = residue.add(&candidate.residue)?;
        floor = floor.checked_add(candidate.floor)?;
        real_strict |= candidate.real_strict;
    }
    let constant = constant_value(&residue)?;
    let order = constant.checked_cmp(&floor)?;
    let refutes = match order {
        core::cmp::Ordering::Less => true,
        core::cmp::Ordering::Equal => real_strict,
        core::cmp::Ordering::Greater => false,
    };
    if !refutes {
        return None;
    }
    // `Σ candidates = Σ cofactors·G + Σ residues`, so subtracting the summed
    // cofactor combination from the candidates leaves exactly the constant.
    let mut cofactors = vec![MvPoly::zero(); equalities.len()];
    for &index in chosen {
        for (slot, share) in cofactors.iter_mut().zip(candidates[index].cofactors.iter()) {
            *slot = slot.add(share)?;
        }
    }
    let mut entries = Vec::with_capacity(chosen.len() + equalities.len());
    for &index in chosen {
        entries.push(candidate_entry(&candidates[index], inequalities));
    }
    for (equality, cofactor) in equalities.iter().zip(cofactors.iter()) {
        if cofactor.is_zero() {
            continue;
        }
        entries.push(CasIdealEntry::Asserted {
            conjunct: equality.conjunct,
            kind: CasHypothesisKind::Equality,
            multiplier: normal_form(&cofactor.neg()?, table)?,
        });
    }
    Some(CasIdealCertificate { entries, constant })
}

/// The certificate entry for one candidate, always with multiplier `1`.
fn candidate_entry(candidate: &Candidate, inequalities: &[Hypothesis]) -> CasIdealEntry {
    let one: AtomPoly = vec![(Vec::new(), Rational::integer(1))];
    match candidate.source {
        CandidateSource::Single(index) => CasIdealEntry::Asserted {
            conjunct: inequalities[index].conjunct,
            kind: inequalities[index].kind,
            multiplier: one,
        },
        CandidateSource::Product(left, right) => CasIdealEntry::AssertedProduct {
            first: inequalities[left].conjunct,
            second: inequalities[right].conjunct,
            multiplier: one,
        },
        CandidateSource::Square(atom) => CasIdealEntry::EvenMonomial {
            monomial: vec![(atom, 2)],
            coefficient: Rational::integer(1),
        },
    }
}

/// Hands a candidate to the independent checker; a candidate that fails is
/// discarded, never returned as a verdict.
fn finish(
    arena: &TermArena,
    assertions: &[TermId],
    cert: CasIdealCertificate,
) -> CasOutcome<CasIdealCertificate> {
    if check_cas_ideal_certificate(arena, assertions, &cert) {
        CasOutcome::Refuted(cert)
    } else {
        CasOutcome::VerifierRejected
    }
}

/// The non-equality term a certificate carries alongside the equation cofactors.
enum Contribution<'a> {
    /// Tautological atom squares, each with coefficient `1`.
    Squares(&'a [TermId]),
    /// One asserted inequality, with multiplier `1`.
    Inequality(&'a Hypothesis),
}

/// Reads a top-level conjunct as `high ⋈ low` with the polynomial oriented so
/// the asserted fact is `high − low ⋈ 0`.
fn comparison_shape(
    arena: &TermArena,
    conjunct: TermId,
) -> Option<(CasHypothesisKind, TermId, TermId, Sort)> {
    let TermNode::App { op, args } = arena.node(conjunct) else {
        return None;
    };
    let [left, right] = &**args else { return None };
    let sort = arena.sort_of(*left);
    if sort != arena.sort_of(*right) || !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    let (kind, flip) = match op {
        Op::Eq => (CasHypothesisKind::Equality, false),
        Op::IntGe | Op::RealGe => (CasHypothesisKind::NonNegative, false),
        Op::IntLe | Op::RealLe => (CasHypothesisKind::NonNegative, true),
        Op::IntGt | Op::RealGt => (CasHypothesisKind::Positive, false),
        Op::IntLt | Op::RealLt => (CasHypothesisKind::Positive, true),
        _ => return None,
    };
    let (high, low) = if flip {
        (*right, *left)
    } else {
        (*left, *right)
    };
    Some((kind, high, low, sort))
}

/// The candidate square sets, in a deterministic order: every atom alone first
/// (the cheapest certificate wins), then all atoms together.
fn square_candidates(table: &AtomTable) -> Vec<Vec<TermId>> {
    let atoms = table.atoms();
    let mut candidates: Vec<Vec<TermId>> = atoms.iter().map(|&atom| vec![atom]).collect();
    if atoms.len() > 1 {
        candidates.push(atoms.to_vec());
    }
    candidates
}

/// `Σ aᵢ²` over the given atoms, as an [`MvPoly`] in the atom variable names.
fn sum_of_squares(table: &AtomTable, atoms: &[TermId]) -> Option<MvPoly> {
    let mut acc = MvPoly::zero();
    for atom in atoms {
        let index = table.index_of(*atom)?;
        acc = acc.add(&MvPoly::var(&AtomTable::name(index)).pow(2)?)?;
    }
    Some(acc)
}

/// Negates every cofactor, or `None` on an exact-range overflow.
fn negate_all(cofactors: &[MvPoly]) -> Option<Vec<MvPoly>> {
    cofactors.iter().map(MvPoly::neg).collect()
}

/// The value of a constant [`MvPoly`], or `None` when a non-constant monomial
/// survives.
fn constant_value(poly: &MvPoly) -> Option<Rational> {
    if poly.is_zero() {
        return Some(Rational::zero());
    }
    let mut terms = poly.terms();
    let (monomial, coefficient) = terms.next()?;
    if terms.next().is_some() || monomial.total_degree() != 0 {
        return None;
    }
    Some(*coefficient)
}

/// Whether an asserted inequality congruent to `constant` modulo the ideal is
/// contradicted by that value.
fn contradicts(inequality: &Hypothesis, constant: Rational) -> bool {
    let numerator = constant.numerator();
    match inequality.kind {
        // `p ≥ 0` yet `p ≡ c < 0`.
        CasHypothesisKind::NonNegative => numerator < 0,
        // `p > 0` yet `p ≡ c ≤ 0`; over ℤ the strict form is `p ≥ 1`, so `c < 1`
        // suffices — but for an integer-valued `p` that is the same condition.
        CasHypothesisKind::Positive => {
            if inequality.integer_valued {
                constant
                    .checked_cmp(&Rational::integer(1))
                    .is_some_and(core::cmp::Ordering::is_lt)
            } else {
                numerator <= 0
            }
        }
        CasHypothesisKind::Equality => false,
    }
}

/// Assembles the certificate: one [`CasIdealEntry::Asserted`] equality entry per
/// generator with a nonzero cofactor, plus the non-equality contribution.
fn build_certificate(
    table: &AtomTable,
    equalities: &[Hypothesis],
    cofactors: &[MvPoly],
    contribution: Option<&Contribution<'_>>,
    constant: Rational,
) -> Option<CasIdealCertificate> {
    let mut entries = Vec::new();
    match contribution {
        Some(Contribution::Squares(atoms)) => {
            for &atom in *atoms {
                entries.push(CasIdealEntry::EvenMonomial {
                    monomial: vec![(atom, 2)],
                    coefficient: Rational::integer(1),
                });
            }
        }
        Some(Contribution::Inequality(inequality)) => {
            entries.push(CasIdealEntry::Asserted {
                conjunct: inequality.conjunct,
                kind: inequality.kind,
                multiplier: vec![(Vec::new(), Rational::integer(1))],
            });
        }
        None => {}
    }
    for (equality, cofactor) in equalities.iter().zip(cofactors.iter()) {
        if cofactor.is_zero() {
            continue;
        }
        entries.push(CasIdealEntry::Asserted {
            conjunct: equality.conjunct,
            kind: CasHypothesisKind::Equality,
            multiplier: normal_form(cofactor, table)?,
        });
    }
    Some(CasIdealCertificate { entries, constant })
}

/// Reads `k·m = c` off the normal form of `lhs − rhs`: exactly one non-constant
/// monomial `m` with integer coefficient `k`, plus an optional integer constant.
fn single_monomial_equation(form: &AtomPoly) -> Option<(AtomMonomial, i128, i128)> {
    let mut monomial: Option<(AtomMonomial, i128)> = None;
    let mut constant = 0i128;
    for (mono, coeff) in form {
        if !coeff.is_integer() {
            return None;
        }
        let value = coeff.numerator();
        if mono.is_empty() {
            constant = value;
        } else if monomial.is_some() {
            return None;
        } else {
            monomial = Some((mono.clone(), value));
        }
    }
    let (mono, coefficient) = monomial?;
    // `lhs − rhs = k·m + constant = 0`, i.e. `k·m = −constant`.
    Some((mono, coefficient, constant.checked_neg()?))
}

/// Builds the certificate for whichever of the three exact facts closes
/// `k·m = c`, or `None` when none of them does.
fn refute_monomial_equation(
    arena: &TermArena,
    conjuncts: &[TermId],
    equation: TermId,
    monomial: AtomMonomial,
    coefficient: i128,
    constant: i128,
) -> Option<CasIntUnitsCertificate> {
    if coefficient == 0 {
        return None;
    }
    // `checked_abs` rather than `abs`: `i128::MIN` has no positive magnitude, and
    // an arithmetic panic on a pathological coefficient is not an acceptable way
    // to decline.
    let magnitude = coefficient.checked_abs()?;
    // `k ∤ c` — no bounds needed, and `axeyum_cas::ntheory::gcd` is the exact
    // integer-divisibility primitive (it returns a non-negative value, and
    // `gcd(k, c) = |k|` exactly when `k | c`).
    if constant != 0 && axeyum_cas::ntheory::gcd(coefficient, constant) != magnitude {
        return Some(CasIntUnitsCertificate {
            equation,
            kind: CasIntUnitsKind::CoefficientNonDivisor,
            monomial,
            coefficient,
            constant,
            bounds: Vec::new(),
        });
    }

    if constant == 0 {
        // `k·m = 0` ⇒ some factor is zero. Refuted when every factor is bounded
        // away from zero.
        let mut bounds = Vec::with_capacity(monomial.len());
        for &(atom, _) in &monomial {
            let bound = tightest_bound(arena, conjuncts, atom, |lower, upper| {
                lower.is_some_and(|value| value >= 1) || upper.is_some_and(|value| value <= -1)
            })?;
            bounds.push(bound);
        }
        return Some(CasIntUnitsCertificate {
            equation,
            kind: CasIntUnitsKind::ZeroProduct,
            monomial,
            coefficient,
            constant,
            bounds,
        });
    }

    // `k·m = c ≠ 0` with `k | c` ⇒ every factor divides `c/k`, so each lies in
    // `[−|c/k|, |c/k|]`. One asserted bound outside that window refutes.
    let limit = constant.checked_div(coefficient)?.checked_abs()?;
    for &(atom, _) in &monomial {
        if let Some(bound) = tightest_bound(arena, conjuncts, atom, |lower, upper| {
            lower.is_some_and(|value| value > limit) || upper.is_some_and(|value| value < -limit)
        }) {
            return Some(CasIntUnitsCertificate {
                equation,
                kind: CasIntUnitsKind::DivisorBound,
                monomial,
                coefficient,
                constant,
                bounds: vec![bound],
            });
        }
    }
    None
}

/// The first asserted conjunct that bounds `atom` in a way `accept` approves.
///
/// The bound itself is read by [`derive_bound`], which lives in the checker
/// module: there is exactly one implementation of "what does this conjunct say
/// about this term", and it is the one on the trusted side.
fn tightest_bound(
    arena: &TermArena,
    conjuncts: &[TermId],
    atom: TermId,
    accept: impl Fn(Option<i128>, Option<i128>) -> bool,
) -> Option<CasIntBound> {
    conjuncts.iter().find_map(|&source| {
        let (lower, upper) = derive_bound(arena, source, atom);
        accept(lower, upper).then_some(CasIntBound {
            source,
            atom,
            lower,
            upper,
        })
    })
}

#[cfg(test)]
mod tests {
    use axeyum_ir::TermArena;

    use super::{CasIntUnitsKind, CasOutcome, cas_identity_refutation, cas_int_units_refutation};

    /// `not ((a+b)² = a² + 2ab + b²)` is refuted, and the refutation carries a
    /// three-monomial normal form that re-checked before it was returned.
    #[test]
    fn binomial_square_disequality_is_refuted() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let sum = arena.int_add(a, b).unwrap();
        let squared = arena.int_mul(sum, sum).unwrap();
        let aa = arena.int_mul(a, a).unwrap();
        let bb = arena.int_mul(b, b).unwrap();
        let ab = arena.int_mul(a, b).unwrap();
        let two = arena.int_const(2);
        let two_ab = arena.int_mul(two, ab).unwrap();
        let partial = arena.int_add(aa, two_ab).unwrap();
        let expanded = arena.int_add(partial, bb).unwrap();
        let eq = arena.eq(squared, expanded).unwrap();
        let diseq = arena.not(eq).unwrap();

        let CasOutcome::Refuted(cert) = cas_identity_refutation(&arena, &[diseq]) else {
            panic!("expected a refutation");
        };
        assert_eq!(cert.assertion, diseq);
        assert_eq!(cert.normal_form.len(), 3);
    }

    /// NEGATIVE CONTROL: one coefficient off. The route must report that it saw
    /// a candidate and could not close it — not a refutation, and not silence.
    #[test]
    fn near_miss_disequality_declines_with_a_reason() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let sum = arena.int_add(a, b).unwrap();
        let squared = arena.int_mul(sum, sum).unwrap();
        let aa = arena.int_mul(a, a).unwrap();
        let bb = arena.int_mul(b, b).unwrap();
        let ab = arena.int_mul(a, b).unwrap();
        let three = arena.int_const(3);
        let three_ab = arena.int_mul(three, ab).unwrap();
        let partial = arena.int_add(aa, three_ab).unwrap();
        let expanded = arena.int_add(partial, bb).unwrap();
        let eq = arena.eq(squared, expanded).unwrap();
        let diseq = arena.not(eq).unwrap();

        assert!(matches!(
            cas_identity_refutation(&arena, &[diseq]),
            CasOutcome::NotRefuted(_)
        ));
    }

    /// A query with no arithmetic disequality reports [`CasOutcome::NoCandidate`],
    /// which is what keeps unrelated route traces free of a `cas-*` entry.
    #[test]
    fn a_query_without_a_disequality_has_no_candidate() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let one = arena.int_const(1);
        let ge = arena.int_ge(a, one).unwrap();
        assert_eq!(
            cas_identity_refutation(&arena, &[ge]),
            CasOutcome::NoCandidate
        );
    }

    /// `a ≥ 2 ∧ a·p = 1`: the units refutation, with the divisor-bound argument.
    #[test]
    fn units_equation_is_refuted_by_a_divisor_bound() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let p = arena.int_var("p").unwrap();
        let two = arena.int_const(2);
        let one = arena.int_const(1);
        let bound = arena.int_ge(a, two).unwrap();
        let product = arena.int_mul(a, p).unwrap();
        let equation = arena.eq(product, one).unwrap();

        let CasOutcome::Refuted(cert) = cas_int_units_refutation(&arena, &[bound, equation]) else {
            panic!("expected a refutation");
        };
        assert_eq!(cert.kind, CasIntUnitsKind::DivisorBound);
        assert_eq!((cert.coefficient, cert.constant), (1, 1));
        assert_eq!(cert.bounds.len(), 1);
        assert_eq!(cert.bounds[0].source, bound);
    }

    /// NEGATIVE CONTROL: `a ≥ 1 ∧ a·p = 1` is satisfiable at `a = p = 1`.
    #[test]
    fn units_equation_at_the_bound_is_not_refuted() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let p = arena.int_var("p").unwrap();
        let one = arena.int_const(1);
        let bound = arena.int_ge(a, one).unwrap();
        let product = arena.int_mul(a, p).unwrap();
        let equation = arena.eq(product, one).unwrap();

        assert!(matches!(
            cas_int_units_refutation(&arena, &[bound, equation]),
            CasOutcome::NotRefuted(_)
        ));
    }

    /// `2·a·b = 3` needs no bound: an even left side never equals an odd one.
    #[test]
    fn odd_constant_refutes_an_even_product() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let two = arena.int_const(2);
        let three = arena.int_const(3);
        let ab = arena.int_mul(a, b).unwrap();
        let doubled = arena.int_mul(two, ab).unwrap();
        let equation = arena.eq(doubled, three).unwrap();

        let CasOutcome::Refuted(cert) = cas_int_units_refutation(&arena, &[equation]) else {
            panic!("expected a refutation");
        };
        assert_eq!(cert.kind, CasIntUnitsKind::CoefficientNonDivisor);
        assert!(cert.bounds.is_empty());
    }

    /// NEGATIVE CONTROL: `2·a·b = 4` is solvable, so the parity argument must not
    /// fire when the coefficient divides the constant.
    #[test]
    fn even_constant_does_not_refute_an_even_product() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let two = arena.int_const(2);
        let four = arena.int_const(4);
        let ab = arena.int_mul(a, b).unwrap();
        let doubled = arena.int_mul(two, ab).unwrap();
        let equation = arena.eq(doubled, four).unwrap();

        assert!(matches!(
            cas_int_units_refutation(&arena, &[equation]),
            CasOutcome::NotRefuted(_)
        ));
    }

    /// A zero product with every factor bounded away from zero.
    #[test]
    fn zero_product_with_nonzero_factors_is_refuted() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let one = arena.int_const(1);
        let zero = arena.int_const(0);
        let a_bound = arena.int_ge(a, one).unwrap();
        let b_bound = arena.int_ge(b, one).unwrap();
        let product = arena.int_mul(a, b).unwrap();
        let equation = arena.eq(product, zero).unwrap();

        let CasOutcome::Refuted(cert) =
            cas_int_units_refutation(&arena, &[a_bound, b_bound, equation])
        else {
            panic!("expected a refutation");
        };
        assert_eq!(cert.kind, CasIntUnitsKind::ZeroProduct);
        assert_eq!(cert.bounds.len(), 2, "one bound per factor");
    }

    /// NEGATIVE CONTROL: drop one factor's bound and the zero product is
    /// satisfiable again.
    #[test]
    fn zero_product_with_an_unbounded_factor_is_not_refuted() {
        let mut arena = TermArena::new();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let one = arena.int_const(1);
        let zero = arena.int_const(0);
        let b_bound = arena.int_ge(b, one).unwrap();
        let product = arena.int_mul(a, b).unwrap();
        let equation = arena.eq(product, zero).unwrap();

        assert!(matches!(
            cas_int_units_refutation(&arena, &[b_bound, equation]),
            CasOutcome::NotRefuted(_)
        ));
    }

    /// `3·(div x 3) = x + 1` must not be refuted: the quotient is opaque, so the
    /// normal form is `3·q − x = 1`, a two-atom monomial equation with no single
    /// monomial — the route declines rather than reasoning about `div`.
    #[test]
    fn an_opaque_quotient_equation_declines() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let three = arena.int_const(3);
        let one = arena.int_const(1);
        let quotient = arena.int_div(x, three).unwrap();
        let scaled = arena.int_mul(three, quotient).unwrap();
        let shifted = arena.int_add(x, one).unwrap();
        let equation = arena.eq(scaled, shifted).unwrap();

        assert!(matches!(
            cas_int_units_refutation(&arena, &[equation]),
            CasOutcome::NotRefuted(_)
        ));
    }
}
