//! Monomial bound refutations: per-variable bounds multiply into a bound on a
//! monomial that contradicts an asserted atom.
//!
//! # The three shapes, all from committed corpus files
//!
//! ```text
//! cli__regress1__nl__ones.smt2
//!   (assert (>= a 1)) … (assert (>= d 1))   (assert (< (* a b c d) 1))
//!   -- each factor >= 1, so the product >= 1
//!
//! cli__regress0__arith__mult.01.smt2
//!   (assert (>= n 1)) (assert (<= n 1)) (assert (>= x 1)) (assert (<= x 1))
//!   (assert (not (= (* x n) 1)))
//!   -- both pinned to [1,1], so the product is exactly 1
//!
//! cli__regress1__nl__simple-mono-unsat.smt2
//!   (assert (or (= a 4) (= a 3))) (assert (> b 0)) (assert (> c 0))
//!   (assert (< (* a b c d d) 0))
//!   -- a >= 3, b > 0, c > 0, and d^2 >= 0 whatever d is, so the product >= 0
//! ```
//!
//! All three shipped as bare `Evidence::Unsat(None)`. `nra.rs` already computes
//! this reasoning internally (`interval_refutation`, `atom_interval_infeasible`)
//! and discards the derivation, so the artifact existed and nothing emitted it —
//! the same observation that produced [`crate::nia_univariate_cert`] and
//! [`crate::nra_product_cert`].
//!
//! # Even exponents are the interesting case
//!
//! `d` in `simple-mono-unsat` has NO asserted bound at all. It does not need
//! one: `d^2 >= 0` for every real `d`, so an even exponent contributes a
//! nonnegative factor unconditionally. That is what lets a monomial with a
//! completely unconstrained variable still have a lower bound of zero — and it
//! is also the one place a sign error would be invisible, because an ODD
//! exponent on an unbounded variable makes the monomial unbounded below and the
//! refutation false. The parity check is therefore carried in the certificate
//! and re-derived.
//!
//! # Scope
//!
//! Lower bounds must be **nonnegative**. Multiplying bounds is monotone only on
//! the nonnegative orthant; with a possibly-negative factor the product's bound
//! requires all four corner products and a sign case analysis, which this module
//! declines rather than approximates. Every corpus shape above lives in the
//! nonnegative case.
//!
//! Names, not `SymbolId`s: ids are arena-local and meaningless against the fresh
//! parse re-validation uses.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A rational on the wire: `(numerator, denominator)`.
type WireRat = (i128, i128);

/// What the certificate proves about the monomial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MonomialBound {
    /// `M >= lo`, refuting `M < lo'` for any `lo' <= lo`.
    AtLeast(WireRat),
    /// `M == value` (every factor pinned), refuting `M != value`.
    Exactly(WireRat),
}

/// A refutation from per-variable bounds on one monomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MonomialBoundRefutationCertificate {
    /// `(variable, exponent, lower bound or None when the exponent is even and
    /// the variable is unbounded)`, sorted by name.
    factors: Vec<(String, u32, Option<WireRat>)>,
    /// Upper bounds, present only for the `Exactly` case.
    uppers: Vec<(String, WireRat)>,
    /// What the factors multiply to.
    bound: MonomialBound,
    /// The constant the refuted atom compares against.
    refuted_against: WireRat,
}

impl MonomialBoundRefutationCertificate {
    /// What this certificate proves about the monomial.
    #[must_use]
    pub const fn bound(&self) -> MonomialBound {
        self.bound
    }

    /// `(variable, exponent, lower bound)` for each factor.
    #[must_use]
    pub fn factors(&self) -> &[(String, u32, Option<WireRat>)] {
        &self.factors
    }
}

fn rat(w: WireRat) -> Option<Rational> {
    Rational::checked_new(w.0, w.1)
}

fn wire(r: Rational) -> WireRat {
    (r.numerator(), r.denominator())
}

/// A real/int constant, or `None`.
fn constant(arena: &TermArena, term: TermId) -> Option<Rational> {
    match arena.node(term) {
        TermNode::RealConst(v) => Some(*v),
        TermNode::IntConst(v) => Some(Rational::integer(*v)),
        TermNode::App { op, args } => match (op, &**args) {
            (Op::RealNeg | Op::IntNeg, [only]) => constant(arena, *only)?.checked_neg(),
            (Op::IntToReal, [only]) => constant(arena, *only),
            _ => None,
        },
        _ => None,
    }
}

fn var_name(arena: &TermArena, term: TermId) -> Option<String> {
    match arena.node(term) {
        TermNode::Symbol(s) => Some(arena.symbol(*s).0.to_owned()),
        _ => None,
    }
}

/// Flatten a product into its factor terms.
fn flatten_mul(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::RealMul | Op::IntMul,
            args,
        } => {
            for &a in &**args {
                flatten_mul(arena, a, out);
            }
        }
        _ => out.push(term),
    }
}

/// A product of plain variables, as `name -> exponent`. Declines on a constant
/// or compound factor.
fn monomial(arena: &TermArena, term: TermId) -> Option<BTreeMap<String, u32>> {
    let mut factors = Vec::new();
    flatten_mul(arena, term, &mut factors);
    if factors.len() < 2 {
        return None;
    }
    let mut out: BTreeMap<String, u32> = BTreeMap::new();
    for f in factors {
        let name = var_name(arena, f)?;
        *out.entry(name).or_insert(0) += 1;
    }
    Some(out)
}

/// Per-variable bounds collected from top-level conjuncts.
#[derive(Default)]
struct Bounds {
    lower: BTreeMap<String, Rational>,
    upper: BTreeMap<String, Rational>,
}

impl Bounds {
    fn note_lower(&mut self, name: String, value: Rational) {
        self.lower
            .entry(name)
            .and_modify(|e| {
                if value > *e {
                    *e = value;
                }
            })
            .or_insert(value);
    }

    fn note_upper(&mut self, name: String, value: Rational) {
        self.upper
            .entry(name)
            .and_modify(|e| {
                if value < *e {
                    *e = value;
                }
            })
            .or_insert(value);
    }
}

/// `(or (= x k1) (= x k2) …)` -> `(x, min k, max k)`.
///
/// EVERY arm must be an equality pinning the SAME variable. One arm that is
/// anything else means the disjunction constrains nothing, and taking the hull
/// of the arms that do match would invent a bound the query never asserts.
fn disjunction_hull(arena: &TermArena, args: &[TermId]) -> Option<(String, Rational, Rational)> {
    if args.is_empty() {
        return None;
    }
    let mut name: Option<String> = None;
    let mut values: Vec<Rational> = Vec::new();
    for &arm in args {
        let TermNode::App {
            op: Op::Eq,
            args: eq,
        } = arena.node(arm)
        else {
            return None;
        };
        let [l, r] = &**eq else { return None };
        let (n, k) = var_name(arena, *l)
            .zip(constant(arena, *r))
            .or_else(|| var_name(arena, *r).zip(constant(arena, *l)))?;
        if name.get_or_insert_with(|| n.clone()) != &n {
            return None;
        }
        values.push(k);
    }
    let name = name?;
    let mut lo = values[0];
    let mut hi = values[0];
    for &v in &values {
        if v < lo {
            lo = v;
        }
        if v > hi {
            hi = v;
        }
    }
    Some((name, lo, hi))
}

/// Read `x >= k`, `x > k`, `x <= k`, `x < k`, `x = k`, and a disjunction of
/// `(= x k)` (whose hull is `[min k, max k]`).
///
/// A strict `x > k` yields the NON-strict `x >= k`, which is weaker and always
/// sound; nothing here needs the strictness, and carrying it would add a case
/// to the bound arithmetic for no reach.
fn collect_bounds(arena: &TermArena, conjuncts: &[TermId]) -> Bounds {
    let mut bounds = Bounds::default();
    for &c in conjuncts {
        // The disjunction case FIRST. A two-argument `BoolOr` also destructures
        // as `[lhs, rhs]`, so checking the comparison shape first matched it,
        // fell through the `match op` with no arm, and hit the `continue` —
        // leaving this branch unreachable. Measured: `(or (= a 4) (= a 3))`
        // produced no bound for `a` at all, and the refutation silently declined.
        if let TermNode::App {
            op: Op::BoolOr,
            args,
        } = arena.node(c)
        {
            if let Some((name, lo, hi)) = disjunction_hull(arena, args) {
                bounds.note_lower(name.clone(), lo);
                bounds.note_upper(name, hi);
            }
            continue;
        }
        if let TermNode::App { op, args } = arena.node(c)
            && let [lhs, rhs] = &**args
        {
            let pair = var_name(arena, *lhs).zip(constant(arena, *rhs));
            let flipped = var_name(arena, *rhs).zip(constant(arena, *lhs));
            match op {
                Op::RealGe | Op::IntGe | Op::RealGt | Op::IntGt => {
                    if let Some((n, k)) = pair {
                        bounds.note_lower(n, k);
                    }
                    if let Some((n, k)) = flipped {
                        bounds.note_upper(n, k);
                    }
                }
                Op::RealLe | Op::IntLe | Op::RealLt | Op::IntLt => {
                    if let Some((n, k)) = pair {
                        bounds.note_upper(n, k);
                    }
                    if let Some((n, k)) = flipped {
                        bounds.note_lower(n, k);
                    }
                }
                Op::Eq => {
                    if let Some((n, k)) = pair.or(flipped) {
                        bounds.note_lower(n.clone(), k);
                        bounds.note_upper(n, k);
                    }
                }
                _ => {}
            }
        }
    }
    bounds
}

/// `base^exp` by repeated exact multiplication.
fn pow(base: Rational, exp: u32) -> Option<Rational> {
    let mut acc = Rational::integer(1);
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

/// The refuted atom: `(< M k)` / `(<= M k)` or `(not (= M k))`.
enum Refuted {
    /// `M < k` (or `M <= k`); a lower bound `>= k` refutes the strict form.
    Below(Rational, bool),
    /// `M != k`; an exact value `== k` refutes it.
    NotEqual(Rational),
}

fn refuted_atom(arena: &TermArena, conjunct: TermId) -> Option<(BTreeMap<String, u32>, Refuted)> {
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(conjunct)
        && let [inner] = &**args
        && let TermNode::App {
            op: Op::Eq,
            args: eq,
        } = arena.node(*inner)
        && let [eq_lhs, eq_rhs] = &**eq
    {
        if let Some(m) = monomial(arena, *eq_lhs)
            && let Some(k) = constant(arena, *eq_rhs)
        {
            return Some((m, Refuted::NotEqual(k)));
        }
        if let Some(m) = monomial(arena, *eq_rhs)
            && let Some(k) = constant(arena, *eq_lhs)
        {
            return Some((m, Refuted::NotEqual(k)));
        }
        return None;
    }
    let TermNode::App { op, args } = arena.node(conjunct) else {
        return None;
    };
    let [cmp_lhs, cmp_rhs] = &**args else {
        return None;
    };
    let strict = matches!(op, Op::RealLt | Op::IntLt);
    if !matches!(op, Op::RealLt | Op::IntLt | Op::RealLe | Op::IntLe) {
        return None;
    }
    let mono = monomial(arena, *cmp_lhs)?;
    let against = constant(arena, *cmp_rhs)?;
    Some((mono, Refuted::Below(against, strict)))
}

/// Derive a certificate from the exact source query, or decline.
#[must_use]
pub fn monomial_bound_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<MonomialBoundRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &a in assertions {
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    let bounds = collect_bounds(arena, &conjuncts);

    for &c in &conjuncts {
        let Some((mono, refuted)) = refuted_atom(arena, c) else {
            continue;
        };
        let zero = Rational::integer(0);

        // Lower bound on the monomial. A factor contributes `lo^e` when it has a
        // NONNEGATIVE lower bound; an even exponent with no such bound
        // contributes 0, because `x^even >= 0` for every real x. An odd exponent
        // with no nonnegative lower bound leaves the monomial unbounded below.
        let mut factors: Vec<(String, u32, Option<WireRat>)> = Vec::new();
        let mut product = Rational::integer(1);
        let mut any_unbounded = false;
        let mut ok = true;
        for (name, &exp) in &mono {
            match bounds.lower.get(name) {
                Some(&lo) if lo >= zero => {
                    factors.push((name.clone(), exp, Some(wire(lo))));
                    let Some(term) = pow(lo, exp) else {
                        ok = false;
                        break;
                    };
                    let Some(next) = product.checked_mul(term) else {
                        ok = false;
                        break;
                    };
                    product = next;
                }
                _ if exp % 2 == 0 => {
                    factors.push((name.clone(), exp, None));
                    any_unbounded = true;
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        // An unbounded even factor can be 0, so the product's floor collapses.
        let derived_lo = if any_unbounded { zero } else { product };

        match refuted {
            Refuted::Below(k, strict) => {
                let closes = if strict {
                    derived_lo >= k
                } else {
                    derived_lo > k
                };
                if closes {
                    return Some(MonomialBoundRefutationCertificate {
                        factors,
                        uppers: Vec::new(),
                        bound: MonomialBound::AtLeast(wire(derived_lo)),
                        refuted_against: wire(k),
                    });
                }
            }
            Refuted::NotEqual(k) => {
                // Every factor must be pinned: lo == hi, and no even-exponent
                // wildcard, or the monomial is not a single value.
                if any_unbounded {
                    continue;
                }
                let mut uppers = Vec::new();
                let mut pinned = Rational::integer(1);
                let mut all_pinned = true;
                for (name, &exp) in &mono {
                    let (Some(&lo), Some(&hi)) = (bounds.lower.get(name), bounds.upper.get(name))
                    else {
                        all_pinned = false;
                        break;
                    };
                    if lo != hi || lo < zero {
                        all_pinned = false;
                        break;
                    }
                    uppers.push((name.clone(), wire(hi)));
                    let Some(term) = pow(lo, exp) else {
                        all_pinned = false;
                        break;
                    };
                    let Some(next) = pinned.checked_mul(term) else {
                        all_pinned = false;
                        break;
                    };
                    pinned = next;
                }
                if all_pinned && pinned == k {
                    return Some(MonomialBoundRefutationCertificate {
                        factors,
                        uppers,
                        bound: MonomialBound::Exactly(wire(pinned)),
                        refuted_against: wire(k),
                    });
                }
            }
        }
    }
    None
}

/// Independently re-validate against the **original** assertions.
///
/// Two stages, and deliberately NOT `fresh == *certificate`. Re-running the
/// producer and comparing is the shortest thing to write, and it was the first
/// version here — but it subsumes every other check, so mutation testing showed
/// the arithmetic guards killing NOTHING: a forged certificate simply failed the
/// equality before any of them ran. A checker whose guards cannot be exercised
/// is a checker whose guards are not there.
///
/// So: stage 1 binds the carried numbers to bounds the query actually asserts,
/// and stage 2 re-derives the bound from those numbers alone.
#[must_use]
/// Stage 1: every carried number is something this query actually asserts.
fn binds_to_query(
    arena: &TermArena,
    conjuncts: &[TermId],
    bounds: &Bounds,
    certificate: &MonomialBoundRefutationCertificate,
    against: Rational,
) -> bool {
    let zero = Rational::integer(0);
    let carried: BTreeMap<String, u32> = certificate
        .factors
        .iter()
        .map(|(n, e, _)| (n.clone(), *e))
        .collect();

    let mut atom_matches = false;
    for &c in conjuncts {
        let Some((mono, refuted)) = refuted_atom(arena, c) else {
            continue;
        };
        if mono != carried {
            continue;
        }
        // The atom's KIND must match the bound's kind -- a lower bound refutes
        // `M < k`, an exact value refutes `M != k`, and crossing them proves
        // nothing -- and the constant must be the one carried.
        let kind_ok = matches!(
            (&refuted, certificate.bound),
            (Refuted::Below(_, _), MonomialBound::AtLeast(_))
                | (Refuted::NotEqual(_), MonomialBound::Exactly(_))
        );
        let constant_ok = match &refuted {
            Refuted::Below(k, _) | Refuted::NotEqual(k) => *k == against,
        };
        if kind_ok && constant_ok {
            atom_matches = true;
            break;
        }
    }
    if !atom_matches {
        return false;
    }

    certificate.factors.iter().all(|(name, _, lo)| match lo {
        Some(w) => rat(*w).is_some_and(|value| bounds.lower.get(name) == Some(&value)),
        // Claiming no bound is only honest when the query really gives none
        // this module would use.
        None => bounds.lower.get(name).is_none_or(|&found| found < zero),
    })
}

/// Stage 2: the bound follows from the carried numbers, re-derived here.
fn arithmetic_holds(
    bounds: &Bounds,
    certificate: &MonomialBoundRefutationCertificate,
    against: Rational,
) -> bool {
    let zero = Rational::integer(0);
    let mut product = Rational::integer(1);
    let mut any_unbounded = false;
    for (_, exp, lo) in &certificate.factors {
        let Some(w) = lo else {
            // No bound is sound ONLY for an even exponent: `x^2 >= 0` holds for
            // every real x, while an odd power of an unbounded variable is
            // unbounded below and the refutation is false.
            if exp % 2 != 0 {
                return false;
            }
            any_unbounded = true;
            continue;
        };
        let Some(value) = rat(*w) else { return false };
        // Multiplying bounds is monotone only on the nonnegative orthant.
        if value < zero {
            return false;
        }
        let Some(term) = pow(value, *exp) else {
            return false;
        };
        let Some(next) = product.checked_mul(term) else {
            return false;
        };
        product = next;
    }

    match certificate.bound {
        MonomialBound::AtLeast(w) => {
            let Some(claimed) = rat(w) else { return false };
            let derived = if any_unbounded { zero } else { product };
            claimed == derived && claimed >= against
        }
        MonomialBound::Exactly(w) => {
            let Some(claimed) = rat(w) else { return false };
            if any_unbounded || certificate.uppers.len() != certificate.factors.len() {
                return false;
            }
            // Pinned means lower == upper, asserted, for every factor. A lower
            // bound alone is not a pin.
            let pinned = certificate.uppers.iter().all(|(name, hi)| {
                rat(*hi).is_some_and(|value| {
                    bounds.upper.get(name) == Some(&value) && bounds.lower.get(name) == Some(&value)
                })
            });
            pinned && claimed == product && claimed == against
        }
    }
}

/// Independently re-validate against the **original** assertions.
///
/// Two stages, and deliberately NOT `fresh == *certificate`. Re-running the
/// producer and comparing is the shortest thing to write, and it was the first
/// version here — but it subsumes every other check, so mutation testing showed
/// the arithmetic guards killing NOTHING: a forged certificate failed the
/// equality before any of them ran. A checker whose guards cannot be exercised
/// is a checker whose guards are not there.
#[must_use]
pub fn check_monomial_bound_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &MonomialBoundRefutationCertificate,
) -> bool {
    let mut conjuncts = Vec::new();
    for &a in assertions {
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    let bounds = collect_bounds(arena, &conjuncts);
    let Some(against) = rat(certificate.refuted_against) else {
        return false;
    };
    binds_to_query(arena, &conjuncts, &bounds, certificate, against)
        && arithmetic_holds(&bounds, certificate, against)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__ones.smt2`
    const ONES: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)(declare-fun b () Real)\n\
        (declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (>= a 1))(assert (>= b 1))(assert (>= c 1))(assert (>= d 1))\n\
        (assert (or (= a 1) (= b 1) (= c 1) (= d 1)))\n\
        (assert (< (* a b c d) 1))\n(check-sat)";
    /// `cli__regress0__arith__mult.01.smt2`
    const MULT01: &str = "(set-logic QF_NRA)\n(declare-fun n () Real)(declare-fun x () Real)\n\
        (assert (>= n 1))(assert (<= n 1))(assert (<= x 1))(assert (>= x 1))\n\
        (assert (not (= (* x n) 1)))\n(check-sat)";
    /// `cli__regress1__nl__simple-mono-unsat.smt2`
    const SIMPLE_MONO: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)(declare-fun b () Real)\n\
        (declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (or (= a 4) (= a 3)))(assert (> b 0))(assert (> c 0))\n\
        (assert (< (* a b c d d) 0))\n(check-sat)";

    /// **SATISFIABLE** at b = 1, d = -1. `d` has an ODD exponent and no bound,
    /// so `b*d` is unbounded below. This is the soundness crux of the module.
    const ODD_UNBOUNDED_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun b () Real)(declare-fun d () Real)\n\
        (assert (> b 0))(assert (< (* b d) 0))\n(check-sat)";

    /// **SATISFIABLE** at a = -1, b = 1. A NEGATIVE lower bound breaks the
    /// monotonicity that makes multiplying bounds valid.
    const NEGATIVE_LOWER_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a (- 5)))(assert (>= b 1))(assert (< (* a b) 0))\n(check-sat)";

    /// **SATISFIABLE**: one arm of the disjunction is not an equality, so it
    /// pins nothing and `a` may be arbitrarily large or small.
    const PARTIAL_DISJUNCTION_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (or (= a 4) (< a 0)))(assert (>= b 1))\n\
        (assert (< (* a b) 1))\n(check-sat)";

    fn query(text: &str) -> (axeyum_ir::TermArena, Vec<TermId>) {
        let p = parse_script(text).expect("parses");
        (p.arena, p.assertions)
    }

    fn cert_for(text: &str) -> MonomialBoundRefutationCertificate {
        let (arena, assertions) = query(text);
        monomial_bound_refutation(&arena, &assertions).expect("certificate")
    }

    #[test]
    fn all_three_corpus_shapes_certify_and_verify() {
        for text in [ONES, MULT01, SIMPLE_MONO] {
            let (arena, assertions) = query(text);
            let cert = monomial_bound_refutation(&arena, &assertions).expect("certificate");
            assert!(check_monomial_bound_refutation(&arena, &assertions, &cert));
            let (fresh, fresh_assertions) = query(text);
            assert!(
                check_monomial_bound_refutation(&fresh, &fresh_assertions, &cert),
                "a name-keyed certificate must survive a fresh parse"
            );
        }
    }

    #[test]
    fn the_three_shapes_exercise_three_different_derivations() {
        // Without this, one shape could cover all three fixtures and two
        // branches of the checker would never run.
        assert_eq!(cert_for(ONES).bound(), MonomialBound::AtLeast((1, 1)));
        assert_eq!(cert_for(MULT01).bound(), MonomialBound::Exactly((1, 1)));
        let mono = cert_for(SIMPLE_MONO);
        assert_eq!(mono.bound(), MonomialBound::AtLeast((0, 1)));
        // `d` carries NO bound and exponent 2 -- the even-exponent wildcard.
        assert!(
            mono.factors()
                .iter()
                .any(|(name, exp, lo)| name == "d" && *exp == 2 && lo.is_none()),
            "{:?}",
            mono.factors()
        );
    }

    #[test]
    fn an_odd_exponent_on_an_unbounded_variable_is_declined() {
        let (arena, assertions) = query(ODD_UNBOUNDED_SAT);
        assert!(
            monomial_bound_refutation(&arena, &assertions).is_none(),
            "b*d with d unbounded is unbounded below; certifying it is a wrong unsat"
        );
    }

    /// **SATISFIABLE** at a = 0, b = 0. Two negative lower bounds multiply to a
    /// POSITIVE 6, so without the nonnegativity requirement the producer would
    /// derive `ab >= 6` and refute `ab < 6` — on a query that is satisfiable.
    /// `NEGATIVE_LOWER_SAT` does not isolate this: there the bogus product is
    /// negative and the refutation fails anyway.
    const NEGATIVE_PAIR_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a (- 2)))(assert (>= b (- 3)))\n\
        (assert (< (* a b) 6))\n(check-sat)";

    #[test]
    fn two_negative_lower_bounds_must_not_multiply_into_a_positive_bound() {
        let (arena, assertions) = query(NEGATIVE_PAIR_SAT);
        assert!(
            monomial_bound_refutation(&arena, &assertions).is_none(),
            "(-2)*(-3) = 6 is not a lower bound for a*b; a = b = 0 satisfies this query"
        );
    }

    #[test]
    fn a_negative_lower_bound_is_declined() {
        let (arena, assertions) = query(NEGATIVE_LOWER_SAT);
        assert!(monomial_bound_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn a_disjunction_with_a_non_equality_arm_pins_nothing() {
        let (arena, assertions) = query(PARTIAL_DISJUNCTION_SAT);
        assert!(
            monomial_bound_refutation(&arena, &assertions).is_none(),
            "taking the hull of only the arms that match invents a bound the query never asserts"
        );
    }

    #[test]
    fn a_certificate_for_another_query_is_rejected() {
        let cert = cert_for(ONES);
        let (arena, assertions) = query(SIMPLE_MONO);
        assert!(!check_monomial_bound_refutation(&arena, &assertions, &cert));
    }

    #[test]
    fn a_bound_the_factors_do_not_multiply_to_is_rejected() {
        let (arena, assertions) = query(ONES);
        let mut forged = cert_for(ONES);
        forged.bound = MonomialBound::AtLeast((7, 1));
        assert!(!check_monomial_bound_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn claiming_no_bound_for_an_odd_exponent_is_rejected() {
        // The forgery the even-exponent rule exists to stop: drop `a`'s bound
        // while leaving its exponent at 1.
        let (arena, assertions) = query(ONES);
        let mut forged = cert_for(ONES);
        for factor in &mut forged.factors {
            if factor.0 == "a" {
                factor.2 = None;
            }
        }
        assert!(!check_monomial_bound_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_negative_carried_lower_bound_is_rejected() {
        let (arena, assertions) = query(ONES);
        let mut forged = cert_for(ONES);
        forged.factors[0].2 = Some((-1, 1));
        assert!(!check_monomial_bound_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    // ---- forgeries that PASS stage 1, so each stage-2 guard stands alone ----
    //
    // Mutation testing found every stage-2 guard killing nothing: stage 1 is
    // strictly stronger for the obvious forgeries and rejected them first. Each
    // certificate below is one the query genuinely supports at stage 1, so only
    // the named arithmetic guard prevents certifying a SATISFIABLE query.

    #[test]
    fn an_odd_unbounded_factor_forged_as_a_zero_bound_is_rejected() {
        // `b > 0`, `b*d < 0`, `d` unbounded. Stage 1 accepts: the atom matches,
        // b's lower bound really is 0, and d really has none. Only the
        // even-exponent parity rule stops `b*d >= 0` — which is false, since
        // d = -1 satisfies the query.
        let (arena, assertions) = query(ODD_UNBOUNDED_SAT);
        let forged = MonomialBoundRefutationCertificate {
            factors: vec![("b".to_owned(), 1, Some((0, 1))), ("d".to_owned(), 1, None)],
            uppers: Vec::new(),
            bound: MonomialBound::AtLeast((0, 1)),
            refuted_against: (0, 1),
        };
        assert!(
            !check_monomial_bound_refutation(&arena, &assertions, &forged),
            "an odd power of an unbounded variable has no lower bound"
        );
    }

    #[test]
    fn negative_bounds_forged_into_a_positive_product_are_rejected() {
        // `a >= -2`, `b >= -3`, `ab < 6`. Stage 1 accepts — both bounds are
        // exactly what the query asserts — and (-2)*(-3) = 6 would refute
        // `ab < 6`. The query is satisfiable at a = b = 0.
        let (arena, assertions) = query(NEGATIVE_PAIR_SAT);
        let forged = MonomialBoundRefutationCertificate {
            factors: vec![
                ("a".to_owned(), 1, Some((-2, 1))),
                ("b".to_owned(), 1, Some((-3, 1))),
            ],
            uppers: Vec::new(),
            bound: MonomialBound::AtLeast((6, 1)),
            refuted_against: (6, 1),
        };
        assert!(
            !check_monomial_bound_refutation(&arena, &assertions, &forged),
            "multiplying bounds is monotone only on the nonnegative orthant"
        );
    }

    #[test]
    fn a_refuted_constant_the_query_never_asserts_is_rejected() {
        // Stage 1's atom binding in isolation: the factors and bounds are
        // exactly ONES's, and `1 >= 0` passes stage 2 — but the query asserts
        // `< 1`, not `< 0`, so no such atom exists to refute.
        let (arena, assertions) = query(ONES);
        let mut forged = cert_for(ONES);
        forged.refuted_against = (0, 1);
        assert!(!check_monomial_bound_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_lower_bound_tighter_than_the_query_asserts_is_rejected() {
        // Stage 1's bound binding in isolation: claim `a >= 2` where the query
        // says `a >= 1`. The arithmetic is then self-consistent (product 2,
        // bound 2, and 2 >= 1), so only the binding catches it.
        let (arena, assertions) = query(ONES);
        let mut forged = cert_for(ONES);
        for factor in &mut forged.factors {
            if factor.0 == "a" {
                factor.2 = Some((2, 1));
            }
        }
        forged.bound = MonomialBound::AtLeast((2, 1));
        assert!(!check_monomial_bound_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    /// **SATISFIABLE** at x = 2, n = 1. Lower bounds only — nothing pins either
    /// variable, so the product is not forced to 1.
    const LOWER_ONLY_NOT_EQUAL_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun n () Real)\n\
        (assert (>= x 1))(assert (>= n 1))\n\
        (assert (not (= (* x n) 1)))\n(check-sat)";

    #[test]
    fn an_unpinned_factor_forged_as_exact_is_rejected() {
        // `Exactly` requires lower == upper for every factor, ASSERTED. Here the
        // query gives lower bounds of 1 and no uppers at all, so stage 1 passes
        // (the atom matches, and both lower bounds are exactly as carried) and
        // the arithmetic is self-consistent (1 * 1 == 1 == the refuted
        // constant). Only the upper-bound pinning check stops this certifying a
        // query that x = 2, n = 1 satisfies.
        //
        // The previous version of this test used ONES, which has no
        // `not (= …)` atom at all — so stage 1 rejected it and the pinning guard
        // was never reached. Mutation testing reported the guard as killing
        // nothing, and it was right.
        let (arena, assertions) = query(LOWER_ONLY_NOT_EQUAL_SAT);
        let forged = MonomialBoundRefutationCertificate {
            factors: vec![
                ("n".to_owned(), 1, Some((1, 1))),
                ("x".to_owned(), 1, Some((1, 1))),
            ],
            uppers: vec![("n".to_owned(), (1, 1)), ("x".to_owned(), (1, 1))],
            bound: MonomialBound::Exactly((1, 1)),
            refuted_against: (1, 1),
        };
        assert!(
            !check_monomial_bound_refutation(&arena, &assertions, &forged),
            "a lower bound is not a pin; x = 2, n = 1 satisfies this query"
        );
    }

    #[test]
    fn the_unpinned_query_is_also_declined_by_the_producer() {
        let (arena, assertions) = query(LOWER_ONLY_NOT_EQUAL_SAT);
        assert!(monomial_bound_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn exact_arithmetic_holds_for_repeated_and_fractional_bounds() {
        // `pow` is what turns per-variable bounds into a monomial bound.
        assert_eq!(pow(Rational::new(3, 2), 2), Some(Rational::new(9, 4)));
        assert_eq!(pow(Rational::integer(2), 10), Some(Rational::integer(1024)));
        assert_eq!(pow(Rational::integer(5), 0), Some(Rational::integer(1)));
    }
}
