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

use axeyum_cas::MvPoly;
use axeyum_ir::{Op, Rational, Sort, TermArena, TermId, TermNode};

use crate::cas_certificate::{
    AtomMonomial, AtomPoly, MAX_ATOMS, MAX_DEPTH, MAX_MONOMIALS, MAX_STEPS,
    check_cas_identity_certificate, check_cas_int_units_certificate, derive_bound,
    match_disequality, match_equality, top_conjuncts,
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
