//! Degree-2 Positivstellensatz refutations: two asserted hypotheses whose
//! **product** is exactly the polynomial a third assertion claims is negative.
//!
//! # The shape
//!
//! Four committed `QF_NRA` corpus instances share one argument, and all shipped
//! as bare `Evidence::Unsat(None)`. Two of them are a bare product:
//!
//! ```text
//! cli__regress1__nl__coeff-unsat-base.smt2
//!   (assert (> a 0)) (assert (> b 0)) (assert (>= a (* 3 b)))
//!   (assert (< (* a a) (* 3 a b)))
//!   -- (a − 3b) ≥ 0 times a > 0 gives a² − 3ab ≥ 0, refuting a² − 3ab < 0
//!
//! cli__regress1__nl__simple-mono.smt2
//!   (assert (> z 0)) (assert (> x y)) (assert (< (* x z) (* y z)))
//!   -- (x − y) > 0 times z > 0 gives xz − yz > 0, refuting xz − yz < 0
//! ```
//!
//! Both are decided today by `nra_real_root`'s CAD, which is *more* machinery
//! than the argument needs and emits nothing a third party can read. The
//! certificate here is two polynomial factors and a sign rule, checkable with
//! exact rational arithmetic and no CAD at all.
//!
//! The other two of the four (`coeff-unsat`, `combine`) need the product **plus**
//! a linear step — `(a−3b)(a+3b) ≥ 0` then `a² ≥ 9b² > 8b²`, and
//! `(ab−1)(c−1) > 0` then `abc > ab + c − 1 > 1`. Those are a genuine Handelman
//! combination with more than one product term, and this module deliberately
//! declines them rather than guessing: a certificate that covered them by
//! accident would be a certificate nobody could check by reading it.
//!
//! # Why the polynomial is keyed on NAMES
//!
//! `nra_real_root::MultiPoly` exists and is exact, but it is private and keyed on
//! `SymbolId`, which is arena-local. A certificate holding arena ids is
//! meaningless against the fresh parse that re-validation uses — the failure
//! `crates/axeyum-solver/tests/certified_implies_revalidatable.rs` was written to
//! catch. So this carries a small polynomial keyed on **source variable names**,
//! which come from the query text and survive re-parsing.
//!
//! # Sign bookkeeping is the whole soundness argument
//!
//! `p ≥ 0` and `q ≥ 0` give `pq ≥ 0`, which refutes `pq < 0` but **not**
//! `pq ≤ 0`. Only when both factors are strict does `pq > 0` follow and refute
//! `pq ≤ 0` as well. Getting that backwards would certify a satisfiable query,
//! so the strictness of every atom is carried in the certificate and re-derived
//! by the checker.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, Sort, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A monomial as sorted `(variable name, exponent)` pairs. `[]` is the constant.
pub(crate) type Mono = Vec<(String, u32)>;

/// A multivariate polynomial over the rationals, keyed on source names.
///
/// Shared with [`crate::nra_handelman_cert`], which needs the same exact,
/// arena-free arithmetic for its multi-term combinations. It is deliberately one
/// implementation: two polynomial types keyed on names would be two chances to
/// disagree about what `a*b` means, and the certificates are only as good as
/// this multiplication.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct NamedPoly {
    terms: BTreeMap<Mono, Rational>,
}

impl NamedPoly {
    /// The monomial-to-coefficient map, ascending by monomial. No zero
    /// coefficients are ever stored, so `terms().next().is_none()` is
    /// `is_zero()`.
    pub(crate) fn terms(&self) -> impl Iterator<Item = (&Mono, &Rational)> {
        self.terms.iter()
    }

    /// The total degree: the largest monomial exponent sum. Zero for the zero
    /// polynomial and for a constant.
    pub(crate) fn degree(&self) -> u32 {
        self.terms
            .keys()
            .map(|mono| mono.iter().map(|(_, exp)| *exp).sum::<u32>())
            .max()
            .unwrap_or(0)
    }

    /// The coefficient of the empty monomial.
    pub(crate) fn constant_term(&self) -> Rational {
        self.terms
            .get(&Vec::new())
            .copied()
            .unwrap_or_else(Rational::zero)
    }

    /// Every variable name occurring in any monomial, ascending.
    pub(crate) fn variables(&self) -> Vec<String> {
        let mut names: Vec<String> = self
            .terms
            .keys()
            .flat_map(|mono| mono.iter().map(|(name, _)| name.clone()))
            .collect();
        names.sort();
        names.dedup();
        names
    }

    /// `self` scaled by `factor`. `None` on `i128` overflow.
    pub(crate) fn scale(&self, factor: Rational) -> Option<Self> {
        let mut out = NamedPoly::default();
        for (mono, &coeff) in &self.terms {
            out.add_term(mono.clone(), coeff.checked_mul(factor)?)?;
        }
        Some(out)
    }

    pub(crate) fn constant(value: Rational) -> Self {
        let mut poly = NamedPoly::default();
        if !value.is_zero() {
            poly.terms.insert(Vec::new(), value);
        }
        poly
    }

    pub(crate) fn var(name: &str) -> Self {
        let mut poly = NamedPoly::default();
        poly.terms
            .insert(vec![(name.to_owned(), 1)], Rational::integer(1));
        poly
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub(crate) fn add_term(&mut self, mono: Mono, coeff: Rational) -> Option<()> {
        if coeff.is_zero() {
            return Some(());
        }
        match self.terms.get(&mono).copied() {
            None => {
                self.terms.insert(mono, coeff);
            }
            Some(existing) => {
                let sum = existing.checked_add(coeff)?;
                if sum.is_zero() {
                    self.terms.remove(&mono);
                } else {
                    self.terms.insert(mono, sum);
                }
            }
        }
        Some(())
    }

    pub(crate) fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (mono, &coeff) in &other.terms {
            out.add_term(mono.clone(), coeff)?;
        }
        Some(out)
    }

    pub(crate) fn neg(&self) -> Option<Self> {
        let mut out = NamedPoly::default();
        for (mono, &coeff) in &self.terms {
            out.add_term(mono.clone(), coeff.checked_neg()?)?;
        }
        Some(out)
    }

    pub(crate) fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    pub(crate) fn mul(&self, other: &Self) -> Option<Self> {
        let mut out = NamedPoly::default();
        for (lhs_mono, &lhs_coeff) in &self.terms {
            for (rhs_mono, &rhs_coeff) in &other.terms {
                let mut merged: BTreeMap<String, u32> = BTreeMap::new();
                for (name, exp) in lhs_mono.iter().chain(rhs_mono.iter()) {
                    let slot = merged.entry(name.clone()).or_insert(0);
                    *slot = slot.checked_add(*exp)?;
                }
                let mono: Mono = merged.into_iter().collect();
                out.add_term(mono, lhs_coeff.checked_mul(rhs_coeff)?)?;
            }
        }
        Some(out)
    }

    /// Deterministic wire form: `[(monomial, numerator, denominator)]`.
    pub(crate) fn to_wire(&self) -> Vec<(Mono, i128, i128)> {
        self.terms
            .iter()
            .map(|(mono, coeff)| (mono.clone(), coeff.numerator(), coeff.denominator()))
            .collect()
    }
}

/// How an atom compares its polynomial to zero, after normalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomSign {
    /// `p = 0`. Produced only by [`atom_or_equality`]; [`atom`] never returns it,
    /// so the two-factor product route below is unaffected by its existence.
    Zero,
    /// `p > 0`
    Positive,
    /// `p >= 0`
    Nonnegative,
    /// `p < 0`
    Negative,
    /// `p <= 0`
    Nonpositive,
}

/// A refutation by one product of two asserted hypotheses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealProductRefutationCertificate {
    /// First factor: its polynomial (wire form) and its asserted sign.
    left: (Vec<(Mono, i128, i128)>, AtomSign),
    /// Second factor.
    right: (Vec<(Mono, i128, i128)>, AtomSign),
    /// The refuted atom: `left * right` as a polynomial, and the sign the query
    /// asserts for it.
    refuted: (Vec<(Mono, i128, i128)>, AtomSign),
}

impl RealProductRefutationCertificate {
    /// The asserted signs of the two factors and of the refuted atom.
    #[must_use]
    pub const fn signs(&self) -> (AtomSign, AtomSign, AtomSign) {
        (self.left.1, self.right.1, self.refuted.1)
    }
}

/// `t` as a polynomial over source names, or `None` for anything outside
/// `{+, -, *, neg, rational constant, variable}`.
///
/// # A symbol is turned into a variable WITHOUT consulting its sort
///
/// Every caller reaches this through a numeric relation (`RealGt`, `IntLe`, …)
/// whose operands are numeric by construction — except `Op::Eq`, which is
/// sort-polymorphic. [`atom_or_equality`] therefore checks the operand sort
/// itself before calling in; without that a Boolean `(= p q)` would become the
/// real equation `p - q = 0` and a Handelman combination could "refute" a query
/// about Booleans.
pub(crate) fn to_poly(arena: &TermArena, term: TermId) -> Option<NamedPoly> {
    match arena.node(term) {
        TermNode::RealConst(value) => Some(NamedPoly::constant(*value)),
        TermNode::IntConst(value) => Some(NamedPoly::constant(Rational::integer(*value))),
        TermNode::Symbol(symbol) => Some(NamedPoly::var(arena.symbol(*symbol).0)),
        TermNode::App { op, args } => {
            let parts: Option<Vec<NamedPoly>> = args.iter().map(|&a| to_poly(arena, a)).collect();
            let parts = parts?;
            match op {
                Op::RealAdd | Op::IntAdd => parts
                    .iter()
                    .try_fold(NamedPoly::default(), |acc, p| acc.add(p)),
                Op::RealMul | Op::IntMul => parts
                    .iter()
                    .try_fold(NamedPoly::constant(Rational::integer(1)), |acc, p| {
                        acc.mul(p)
                    }),
                Op::RealSub | Op::IntSub => {
                    let [lhs, rhs] = parts.as_slice() else {
                        return None;
                    };
                    lhs.sub(rhs)
                }
                Op::RealNeg | Op::IntNeg => {
                    let [only] = parts.as_slice() else {
                        return None;
                    };
                    only.neg()
                }
                Op::IntToReal => {
                    let [only] = parts.as_slice() else {
                        return None;
                    };
                    Some(only.clone())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Normalize a comparison conjunct to `(polynomial, sign)` with the polynomial
/// on the left of zero.
pub(crate) fn atom(arena: &TermArena, conjunct: TermId) -> Option<(NamedPoly, AtomSign)> {
    let TermNode::App { op, args } = arena.node(conjunct) else {
        return None;
    };
    let [lhs, rhs] = &**args else { return None };
    let (left, right) = (to_poly(arena, *lhs)?, to_poly(arena, *rhs)?);
    let difference = left.sub(&right)?;
    // `l > r` is `l - r > 0`; `l < r` is `l - r < 0`; and so on.
    let sign = match op {
        Op::RealGt | Op::IntGt => AtomSign::Positive,
        Op::RealGe | Op::IntGe => AtomSign::Nonnegative,
        Op::RealLt | Op::IntLt => AtomSign::Negative,
        Op::RealLe | Op::IntLe => AtomSign::Nonpositive,
        _ => return None,
    };
    Some((difference, sign))
}

/// [`atom`], extended with numeric **equalities** as [`AtomSign::Zero`].
///
/// `Op::Eq` is sort-polymorphic, so the operand sort is checked here rather than
/// in [`to_poly`]: a Boolean or bit-vector equality is refused outright.
pub(crate) fn atom_or_equality(
    arena: &TermArena,
    conjunct: TermId,
) -> Option<(NamedPoly, AtomSign)> {
    if let Some(found) = atom(arena, conjunct) {
        return Some(found);
    }
    let TermNode::App { op: Op::Eq, args } = arena.node(conjunct) else {
        return None;
    };
    let [lhs, rhs] = &**args else { return None };
    if !matches!(arena.sort_of(*lhs), Sort::Real | Sort::Int)
        || !matches!(arena.sort_of(*rhs), Sort::Real | Sort::Int)
    {
        return None;
    }
    let difference = to_poly(arena, *lhs)?.sub(&to_poly(arena, *rhs)?)?;
    Some((difference, AtomSign::Zero))
}

/// Does `p ⋈ 0` mean `p` is at least zero?
const fn is_lower_bound(sign: AtomSign) -> bool {
    matches!(sign, AtomSign::Positive | AtomSign::Nonnegative)
}

/// Given the two factors' signs, what does the product's sign refute?
///
/// `p ≥ 0` and `q ≥ 0` give `pq ≥ 0`, which contradicts `pq < 0` but NOT
/// `pq ≤ 0` — the product may be exactly zero. Only two strict factors give
/// `pq > 0`, which contradicts both. Reversing this certifies satisfiable
/// queries, so it is stated once, here, and re-derived by the checker.
const fn product_refutes(left: AtomSign, right: AtomSign, refuted: AtomSign) -> bool {
    if !is_lower_bound(left) || !is_lower_bound(right) {
        return false;
    }
    let product_is_strict =
        matches!(left, AtomSign::Positive) && matches!(right, AtomSign::Positive);
    match refuted {
        AtomSign::Negative => true,
        AtomSign::Nonpositive => product_is_strict,
        // A product of lower bounds says nothing about an EQUALITY: `pq >= 0` is
        // perfectly consistent with `pq = 0`.
        AtomSign::Positive | AtomSign::Nonnegative | AtomSign::Zero => false,
    }
}

/// Derive a certificate from the exact source query, or decline.
#[must_use]
pub fn real_product_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<RealProductRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    let atoms: Vec<(NamedPoly, AtomSign)> =
        conjuncts.iter().filter_map(|&c| atom(arena, c)).collect();

    for (refuted_poly, refuted_sign) in &atoms {
        if is_lower_bound(*refuted_sign) || refuted_poly.is_zero() {
            continue;
        }
        for (i, (left_poly, left_sign)) in atoms.iter().enumerate() {
            if !is_lower_bound(*left_sign) || left_poly.is_zero() {
                continue;
            }
            for (right_poly, right_sign) in atoms.iter().skip(i) {
                if !is_lower_bound(*right_sign) || right_poly.is_zero() {
                    continue;
                }
                if !product_refutes(*left_sign, *right_sign, *refuted_sign) {
                    continue;
                }
                let Some(product) = left_poly.mul(right_poly) else {
                    continue;
                };
                if product == *refuted_poly {
                    return Some(RealProductRefutationCertificate {
                        left: (left_poly.to_wire(), *left_sign),
                        right: (right_poly.to_wire(), *right_sign),
                        refuted: (refuted_poly.to_wire(), *refuted_sign),
                    });
                }
            }
        }
    }
    None
}

/// Rebuild a polynomial from its wire form. `None` on a malformed entry, which
/// a forged certificate can contain.
pub(crate) fn from_wire(wire: &[(Mono, i128, i128)]) -> Option<NamedPoly> {
    let mut poly = NamedPoly::default();
    for (mono, num, den) in wire {
        if *den == 0 {
            return None;
        }
        let mut normalized = mono.clone();
        normalized.sort();
        normalized.dedup_by(|a, b| a.0 == b.0);
        if normalized.len() != mono.len() {
            return None; // a repeated variable in one monomial is malformed
        }
        // Defence-in-depth, and UNREACHABLE behind stage 1: a zero exponent
        // encodes a constant as `[(x, 0)]`, which is a distinct key from the
        // real constant `[]`, so such a polynomial matches no asserted atom and
        // stage 1 rejects it first. Mutation testing reports this as killing
        // nothing, which is the correct result rather than a missing test.
        if normalized.iter().any(|(_, exp)| *exp == 0) {
            return None;
        }
        poly.add_term(normalized, Rational::checked_new(*num, *den)?)?;
    }
    Some(poly)
}

/// Independently re-validate against the **original** assertions.
///
/// Three stages: the query really asserts these three atoms with these signs;
/// the product of the two factors really is the refuted polynomial; and the sign
/// rule really closes.
#[must_use]
pub fn check_real_product_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &RealProductRefutationCertificate,
) -> bool {
    let (Some(left), Some(right), Some(refuted)) = (
        from_wire(&certificate.left.0),
        from_wire(&certificate.right.0),
        from_wire(&certificate.refuted.0),
    ) else {
        return false;
    };

    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    let atoms: Vec<(NamedPoly, AtomSign)> =
        conjuncts.iter().filter_map(|&c| atom(arena, c)).collect();
    let asserted = |poly: &NamedPoly, sign: AtomSign| {
        atoms
            .iter()
            .any(|(found, found_sign)| found == poly && *found_sign == sign)
    };

    // Stage 1: every part of the certificate is something this query says.
    if !asserted(&left, certificate.left.1)
        || !asserted(&right, certificate.right.1)
        || !asserted(&refuted, certificate.refuted.1)
    {
        return false;
    }
    // Stage 2: the product really is the refuted polynomial.
    let Some(product) = left.mul(&right) else {
        return false;
    };
    if product != refuted {
        return false;
    }
    // Stage 3: and the signs really contradict.
    product_refutes(
        certificate.left.1,
        certificate.right.1,
        certificate.refuted.1,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__coeff-unsat-base.smt2`: (a−3b) ≥ 0 times a > 0.
    const COEFF_BASE: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (> a 0))(assert (> b 0))(assert (>= a (* 3 b)))\n\
        (assert (< (* a a) (* 3 a b)))\n(check-sat)";

    /// `cli__regress1__nl__simple-mono.smt2`: (x−y) > 0 times z > 0.
    const SIMPLE_MONO: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun y () Real)(declare-fun z () Real)\n\
        (assert (> z 0))(assert (> x y))(assert (< (* x z) (* y z)))\n(check-sat)";

    /// **SATISFIABLE** at x = y = 0. `x ≥ 0` and `y ≥ 0` give `xy ≥ 0`, which does
    /// NOT contradict `xy ≤ 0`. The whole soundness argument of this module is
    /// that non-strict factors refute `< 0` and not `≤ 0`.
    const NONSTRICT_SAT: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun y () Real)\n\
        (assert (>= x 0))(assert (>= y 0))(assert (<= (* x y) 0))\n(check-sat)";

    /// `cli__regress1__nl__combine.smt2`: needs the product PLUS a linear step,
    /// and is deliberately out of scope.
    const COMBINE: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
        (assert (> c 1))(assert (> (* a b) 1))(assert (< (* a b c) 1))\n(check-sat)";

    fn query(text: &str) -> (axeyum_ir::TermArena, Vec<TermId>) {
        let p = parse_script(text).expect("parses");
        (p.arena, p.assertions)
    }

    fn cert_for(text: &str) -> RealProductRefutationCertificate {
        let (arena, assertions) = query(text);
        real_product_refutation(&arena, &assertions).expect("certificate")
    }

    #[test]
    fn both_bare_product_corpus_shapes_certify_and_verify() {
        for text in [COEFF_BASE, SIMPLE_MONO] {
            let (arena, assertions) = query(text);
            let cert = real_product_refutation(&arena, &assertions).expect("certificate");
            assert!(check_real_product_refutation(&arena, &assertions, &cert));
            // ...and against a parse sharing no state, which is what the
            // name-keyed polynomial exists for.
            let (fresh, fresh_assertions) = query(text);
            assert!(check_real_product_refutation(
                &fresh,
                &fresh_assertions,
                &cert
            ));
        }
    }

    #[test]
    fn the_signs_are_recorded_not_assumed() {
        assert_eq!(
            cert_for(COEFF_BASE).signs(),
            (
                AtomSign::Positive,
                AtomSign::Nonnegative,
                AtomSign::Negative
            )
        );
        assert_eq!(
            cert_for(SIMPLE_MONO).signs(),
            (AtomSign::Positive, AtomSign::Positive, AtomSign::Negative)
        );
    }

    #[test]
    fn nonstrict_factors_do_not_refute_a_nonstrict_product() {
        // THE soundness case. Certifying this would report a satisfiable query
        // as unsat.
        let (arena, assertions) = query(NONSTRICT_SAT);
        assert!(
            real_product_refutation(&arena, &assertions).is_none(),
            "x >= 0 and y >= 0 give xy >= 0, which is consistent with xy <= 0 at x = 0"
        );
    }

    #[test]
    fn strict_factors_do_refute_a_nonstrict_product() {
        // The other half: without this the guard could be satisfied by never
        // refuting `<= 0` at all.
        let text = "(set-logic QF_NRA)\n\
            (declare-fun x () Real)(declare-fun y () Real)\n\
            (assert (> x 0))(assert (> y 0))(assert (<= (* x y) 0))\n(check-sat)";
        let (arena, assertions) = query(text);
        assert!(real_product_refutation(&arena, &assertions).is_some());
    }

    #[test]
    fn a_refutation_needing_more_than_one_product_is_declined() {
        // `combine` needs (ab−1)(c−1) > 0 AND then abc > ab + c − 1 > 1. Out of
        // scope on purpose; certifying it by accident would produce an artifact
        // nobody could check by reading it.
        let (arena, assertions) = query(COMBINE);
        assert!(real_product_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn a_certificate_for_another_query_is_rejected() {
        let cert = cert_for(COEFF_BASE);
        let (arena, assertions) = query(SIMPLE_MONO);
        assert!(!check_real_product_refutation(&arena, &assertions, &cert));
    }

    #[test]
    fn a_product_that_is_not_the_refuted_polynomial_is_rejected() {
        // Stage 2 in isolation: both factors and the refuted atom are genuinely
        // asserted by COEFF_BASE (`a > 0`, `b > 0`, `a² − 3ab < 0`), but a·b is
        // not a² − 3ab.
        let (arena, assertions) = query(COEFF_BASE);
        let forged = RealProductRefutationCertificate {
            left: (NamedPoly::var("a").to_wire(), AtomSign::Positive),
            right: (NamedPoly::var("b").to_wire(), AtomSign::Positive),
            refuted: cert_for(COEFF_BASE).refuted.clone(),
        };
        assert!(!check_real_product_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_sign_the_query_does_not_assert_is_rejected() {
        // Stage 1: `a > 0` is asserted, `a >= 0` is not, and swapping the two
        // would silently weaken the refutation.
        let (arena, assertions) = query(SIMPLE_MONO);
        let mut forged = cert_for(SIMPLE_MONO);
        forged.left.1 = AtomSign::Nonnegative;
        assert!(!check_real_product_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_malformed_wire_polynomial_is_rejected() {
        let (arena, assertions) = query(SIMPLE_MONO);
        let mut forged = cert_for(SIMPLE_MONO);
        // Zero denominator, and a zero exponent: both are shapes a hand-written
        // certificate can contain and neither can come from `to_wire`.
        forged.left.0 = vec![(vec![("z".to_owned(), 1)], 1, 0)];
        assert!(!check_real_product_refutation(&arena, &assertions, &forged));
        forged = cert_for(SIMPLE_MONO);
        forged.left.0 = vec![(vec![("z".to_owned(), 0)], 1, 1)];
        assert!(!check_real_product_refutation(&arena, &assertions, &forged));
        forged = cert_for(SIMPLE_MONO);
        forged.left.0 = vec![(vec![("z".to_owned(), 1), ("z".to_owned(), 1)], 1, 1)];
        assert!(!check_real_product_refutation(&arena, &assertions, &forged));
    }

    #[test]
    fn a_factor_asserted_negative_cannot_be_used_as_a_lower_bound() {
        // `x < 0` and `y >= 0` give `xy <= 0`, which is CONSISTENT with
        // `xy < 0` -- satisfiable at x = -1, y = 1. Every part of this forgery
        // is genuinely asserted by the query, and the product really does equal
        // the refuted polynomial, so stages 1 and 2 both pass. Only the
        // lower-bound requirement inside `product_refutes` prevents certifying
        // a satisfiable query as unsat.
        let text = "(set-logic QF_NRA)\n\
            (declare-fun x () Real)(declare-fun y () Real)\n\
            (assert (< x 0))(assert (>= y 0))(assert (< (* x y) 0))\n(check-sat)";
        let (arena, assertions) = query(text);
        assert!(
            real_product_refutation(&arena, &assertions).is_none(),
            "the producer must not use a negative factor as a lower bound"
        );
        let forged = RealProductRefutationCertificate {
            left: (NamedPoly::var("x").to_wire(), AtomSign::Negative),
            right: (NamedPoly::var("y").to_wire(), AtomSign::Nonnegative),
            refuted: (
                NamedPoly::var("x")
                    .mul(&NamedPoly::var("y"))
                    .unwrap()
                    .to_wire(),
                AtomSign::Negative,
            ),
        };
        assert!(
            !check_real_product_refutation(&arena, &assertions, &forged),
            "the CHECKER must reject it too"
        );
    }

    #[test]
    fn polynomial_arithmetic_is_exact() {
        // The certificate is only as good as this multiplication.
        let x = NamedPoly::var("x");
        let y = NamedPoly::var("y");
        let x_minus_y = x.sub(&y).unwrap();
        let z = NamedPoly::var("z");
        let product = x_minus_y.mul(&z).unwrap();
        // (x − y)·z = xz − yz
        let xz = x.mul(&z).unwrap();
        let yz = y.mul(&z).unwrap();
        assert_eq!(product, xz.sub(&yz).unwrap());
        // and (x − y)(x + y) = x² − y²
        let x_plus_y = x.add(&y).unwrap();
        let diff_of_squares = x_minus_y.mul(&x_plus_y).unwrap();
        let x2 = x.mul(&x).unwrap();
        let y2 = y.mul(&y).unwrap();
        assert_eq!(diff_of_squares, x2.sub(&y2).unwrap());
    }
}
