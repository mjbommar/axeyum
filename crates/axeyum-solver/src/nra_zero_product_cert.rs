//! Monomial-divisibility refutations: `M = 0` and `M' ≠ 0` where every factor of
//! `M` is a factor of `M'`.
//!
//! # Why
//!
//! Two `QF_NRA` corpus instances are refuted by nothing more than "this product
//! divides that one", and both shipped as bare `Evidence::Unsat(None)`:
//!
//! ```text
//! cli__regress1__nl__zero-subset.smt2
//!   (assert (= (* a b c d) 0))
//!   (assert (not (= (* a b c d e) 0)))
//!
//! cli__regress0__nl__subs0-unsat-confirm.smt2
//!   (assert (or (= v1 0) (= v2 0)))
//!   (assert (not (= (* v1 v2 v3 v4 v5 v6 v7) 0)))
//! ```
//!
//! In the first, `abcde = (abcd)·e = 0·e = 0`. In the second, whichever disjunct
//! holds contributes a zero factor to the seven-way product. Neither needs CAD,
//! interval reasoning, or a Positivstellensatz — the argument is multiset
//! containment over factor names, and a reader can check it by eye.
//!
//! This is the companion observation to
//! [`crate::nia_univariate_cert`]: that certificate is exercised only by
//! synthetic queries, because the committed `QF_NIA` corpus rows are `div`/`mod`
//! and multivariate shapes it declines. **This one covers real corpus files**,
//! which is the difference between a certificate that could matter and one that
//! demonstrably does.
//!
//! # The certificate carries NAMES, not ids
//!
//! Factors are recorded by their **source symbol names**, read from
//! `TermArena::symbol`. A `SymbolId` is arena-local and means nothing against a
//! fresh parse of the same file — the failure
//! `crates/axeyum-solver/tests/certified_implies_revalidatable.rs` exists to
//! catch, where `UnsatQuantInstanceSet` shipped `certified=1` over a re-check
//! that had FAILED. Names come from the query text, so they survive re-parsing.
//!
//! # What the checker shares with the producer, stated plainly
//!
//! Both flatten `RealMul` the same way. That flattening is not re-derived
//! independently, and claiming otherwise would be false. What the checker does
//! not share is everything else: it re-scans the **original untouched
//! assertions** rather than any solver state, and re-establishes the containment
//! itself. So it catches a certificate about a different query, a containment
//! that does not hold, and a disjunct with no zeroing factor — and it does not
//! catch a bug in `flatten_real_mul`, which is covered by that function's own
//! tests instead. Saying which half is which is the point.

use std::collections::BTreeMap;

use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::term_walk::collect_top_binary_conjuncts as collect_top_conjuncts;

/// A refutation of `M = 0` (or a disjunction of variable-zeroings) against
/// `M' ≠ 0`, where every zeroed factor divides `M'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealZeroProductRefutationCertificate {
    /// One entry per case. A direct `M = 0` has exactly one entry, holding
    /// `M`'s factor names; a `(or (= v 0) …)` has one entry per disjunct.
    /// **Every** entry must divide the nonzero monomial, or the case split is
    /// not covered.
    zeroing_cases: Vec<Vec<String>>,
    /// Factor names of the monomial asserted non-zero, with multiplicity.
    nonzero_factors: Vec<String>,
}

impl RealZeroProductRefutationCertificate {
    /// The zeroing cases, each a factor-name list.
    #[must_use]
    pub fn zeroing_cases(&self) -> &[Vec<String>] {
        &self.zeroing_cases
    }

    /// The non-zero monomial's factor names.
    #[must_use]
    pub fn nonzero_factors(&self) -> &[String] {
        &self.nonzero_factors
    }
}

/// Flatten a `RealMul` tower into its factor terms.
fn flatten_real_mul(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::RealMul,
            args,
        } => {
            for &arg in &**args {
                flatten_real_mul(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

/// The source names of a product's factors, or `None` if any factor is not a
/// plain variable.
///
/// Constants and compound factors are refused rather than approximated: a
/// constant factor changes the argument (`0 · x` is zero for a different
/// reason), and a compound factor would need syntactic equality that the name
/// representation cannot express.
fn factor_names(arena: &TermArena, term: TermId) -> Option<Vec<String>> {
    let mut factors = Vec::new();
    flatten_real_mul(arena, term, &mut factors);
    if factors.len() < 2 {
        return None; // not a product
    }
    let mut names = Vec::with_capacity(factors.len());
    for factor in factors {
        let TermNode::Symbol(symbol) = arena.node(factor) else {
            return None;
        };
        names.push(arena.symbol(*symbol).0.to_owned());
    }
    names.sort();
    Some(names)
}

/// `t` is a real variable: its source name.
fn var_name(arena: &TermArena, term: TermId) -> Option<String> {
    match arena.node(term) {
        TermNode::Symbol(symbol) => Some(arena.symbol(*symbol).0.to_owned()),
        _ => None,
    }
}

fn is_real_zero(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::RealConst(v) if v.is_zero())
}

/// `(= e 0)` or `(= 0 e)` — the non-zero side.
fn equals_zero(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [lhs, rhs] = &**args else { return None };
    if is_real_zero(arena, *rhs) {
        Some(*lhs)
    } else if is_real_zero(arena, *lhs) {
        Some(*rhs)
    } else {
        None
    }
}

/// The zeroing cases contributed by one conjunct, if it is one.
///
/// Two accepted shapes: a direct product-is-zero, and a disjunction whose every
/// arm zeroes a single variable. A disjunction with even one arm that is not a
/// variable-zeroing is refused entirely — a partially covered case split proves
/// nothing.
fn zeroing_cases(arena: &TermArena, conjunct: TermId) -> Option<Vec<Vec<String>>> {
    if let Some(product) = equals_zero(arena, conjunct)
        && let Some(names) = factor_names(arena, product)
    {
        return Some(vec![names]);
    }
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(conjunct)
    else {
        return None;
    };
    if args.is_empty() {
        return None;
    }
    let mut cases = Vec::with_capacity(args.len());
    for &arm in &**args {
        let zeroed = equals_zero(arena, arm)?;
        cases.push(vec![var_name(arena, zeroed)?]);
    }
    Some(cases)
}

/// `(not (= M 0))` — the factor names of `M`.
fn nonzero_product(arena: &TermArena, conjunct: TermId) -> Option<Vec<String>> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(conjunct)
    else {
        return None;
    };
    let [inner] = &**args else { return None };
    factor_names(arena, equals_zero(arena, *inner)?)
}

/// Multiset containment: does every name in `needle` appear in `haystack` at
/// least as often?
fn divides(needle: &[String], haystack: &[String]) -> bool {
    let mut have: BTreeMap<&str, usize> = BTreeMap::new();
    for name in haystack {
        *have.entry(name.as_str()).or_default() += 1;
    }
    for name in needle {
        match have.get_mut(name.as_str()) {
            Some(count) if *count > 0 => *count -= 1,
            _ => return false,
        }
    }
    true
}

/// Derive a certificate from the exact source query, or decline.
#[must_use]
pub fn real_zero_product_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<RealZeroProductRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    // The non-zero monomial first: there is usually exactly one, and it bounds
    // what any zeroing case has to divide.
    for &nonzero_conjunct in &conjuncts {
        let Some(nonzero_factors) = nonzero_product(arena, nonzero_conjunct) else {
            continue;
        };
        for &zero_conjunct in &conjuncts {
            if zero_conjunct == nonzero_conjunct {
                continue;
            }
            let Some(cases) = zeroing_cases(arena, zero_conjunct) else {
                continue;
            };
            // EVERY case must divide, or the split leaves a branch open.
            if cases.iter().all(|case| divides(case, &nonzero_factors)) {
                return Some(RealZeroProductRefutationCertificate {
                    zeroing_cases: cases,
                    nonzero_factors,
                });
            }
        }
    }
    None
}

/// Independently re-validate against the **original** assertions.
///
/// Two stages: the certificate must describe monomials this query actually
/// asserts, and the containment must hold for every case.
#[must_use]
pub fn check_real_zero_product_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &RealZeroProductRefutationCertificate,
) -> bool {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    // Stage 1: this query really asserts a non-zero monomial with exactly these
    // factors, and really asserts these zeroings.
    let asserts_nonzero = conjuncts
        .iter()
        .filter_map(|&c| nonzero_product(arena, c))
        .any(|found| found == certificate.nonzero_factors);
    if !asserts_nonzero {
        return false;
    }
    let asserts_zeroing = conjuncts
        .iter()
        .filter_map(|&c| zeroing_cases(arena, c))
        .any(|found| found == certificate.zeroing_cases);
    if !asserts_zeroing {
        return false;
    }

    // Stage 2: and the argument actually closes -- every case, not merely one.
    //
    // The emptiness checks are defence-in-depth and are UNREACHABLE while stage 1
    // stands: no query asserts an empty case list or an empty case, so stage 1
    // rejects such a certificate first. Mutation testing reports them as killing
    // nothing, and that is the correct result rather than a missing test —
    // `all()` over an empty list is vacuously `true`, so if stage 1 is ever
    // loosened these become load-bearing immediately.
    !certificate.zeroing_cases.is_empty()
        && certificate
            .zeroing_cases
            .iter()
            .all(|case| !case.is_empty() && divides(case, &certificate.nonzero_factors))
}

#[cfg(test)]
mod tests {
    //! The checker must reject a forged certificate, and each guard is asserted
    //! on its own: a single "some tampering is caught" test passes while all but
    //! one guard is deleted.

    use super::*;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__zero-subset.smt2`, verbatim in shape.
    const ZERO_SUBSET: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\n\
        (declare-fun d () Real)(declare-fun e () Real)\n\
        (assert (= (* a b c d) 0))\n\
        (assert (not (= (* a b c d e) 0)))\n\
        (check-sat)";

    /// `cli__regress0__nl__subs0-unsat-confirm.smt2`, verbatim in shape.
    const DISJUNCTIVE: &str = "(set-logic QF_NRA)\n\
        (declare-fun v1 () Real)(declare-fun v2 () Real)(declare-fun v3 () Real)\n\
        (declare-fun v4 () Real)(declare-fun v5 () Real)\n\
        (assert (or (= v1 0) (= v2 0)))\n\
        (assert (not (= (* v1 v2 v3 v4 v5) 0)))\n\
        (check-sat)";

    /// SATISFIABLE: `x` is zeroed but is NOT a factor of the non-zero product.
    /// The negative control for containment — set `a·b·c = 0` aside, nothing
    /// here forces `d·e` to vanish.
    const NOT_A_FACTOR: &str = "(set-logic QF_NRA)\n\
        (declare-fun x () Real)(declare-fun d () Real)(declare-fun e () Real)\n\
        (assert (= (* x x) 0))\n\
        (assert (not (= (* d e) 0)))\n\
        (check-sat)";

    /// SATISFIABLE: only ONE arm of the split zeroes a factor. `v9` is free, so
    /// the second arm leaves the product non-zero. A checker that accepted a
    /// partially covered case split would certify this.
    const PARTIAL_SPLIT: &str = "(set-logic QF_NRA)\n\
        (declare-fun v1 () Real)(declare-fun v9 () Real)(declare-fun v3 () Real)\n\
        (assert (or (= v1 0) (= v9 0)))\n\
        (assert (not (= (* v1 v3) 0)))\n\
        (check-sat)";

    fn query(text: &str) -> (axeyum_ir::TermArena, Vec<TermId>) {
        let parsed = parse_script(text).expect("parses");
        (parsed.arena, parsed.assertions)
    }

    fn cert_for(text: &str) -> RealZeroProductRefutationCertificate {
        let (arena, assertions) = query(text);
        real_zero_product_refutation(&arena, &assertions)
            .unwrap_or_else(|| panic!("expected a certificate"))
    }

    #[test]
    fn both_corpus_shapes_produce_a_certificate_that_verifies() {
        for text in [ZERO_SUBSET, DISJUNCTIVE] {
            let (arena, assertions) = query(text);
            let cert = real_zero_product_refutation(&arena, &assertions).expect("certificate");
            assert!(check_real_zero_product_refutation(
                &arena,
                &assertions,
                &cert
            ));
            // ...and against a SECOND parse sharing no state with the first.
            let (fresh_arena, fresh_assertions) = query(text);
            assert!(
                check_real_zero_product_refutation(&fresh_arena, &fresh_assertions, &cert),
                "a certificate carrying source NAMES must survive a fresh parse"
            );
        }
    }

    #[test]
    fn the_disjunctive_form_records_every_arm() {
        let cert = cert_for(DISJUNCTIVE);
        assert_eq!(
            cert.zeroing_cases(),
            &[vec!["v1".to_owned()], vec!["v2".to_owned()]]
        );
        assert_eq!(cert.nonzero_factors().len(), 5);
    }

    #[test]
    fn a_zeroed_term_that_is_not_a_factor_is_declined() {
        let (arena, assertions) = query(NOT_A_FACTOR);
        assert!(real_zero_product_refutation(&arena, &assertions).is_none());
    }

    #[test]
    fn a_partially_covered_case_split_is_declined() {
        let (arena, assertions) = query(PARTIAL_SPLIT);
        assert!(
            real_zero_product_refutation(&arena, &assertions).is_none(),
            "one arm leaves the product non-zero; certifying this would be a wrong unsat"
        );
    }

    #[test]
    fn a_certificate_for_another_query_is_rejected() {
        let cert = cert_for(ZERO_SUBSET);
        let (arena, assertions) = query(DISJUNCTIVE);
        assert!(!check_real_zero_product_refutation(
            &arena,
            &assertions,
            &cert
        ));
    }

    #[test]
    fn a_containment_that_does_not_hold_is_rejected() {
        // Stage 2 in isolation: name a zeroing factor the product does not have.
        let mut forged = cert_for(ZERO_SUBSET);
        forged.zeroing_cases = vec![vec!["zzz".to_owned()]];
        let (arena, assertions) = query(ZERO_SUBSET);
        assert!(!check_real_zero_product_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn dropping_an_uncovered_arm_from_the_split_is_rejected() {
        // The forgery that a weaker checker would accept: keep only the arm that
        // DOES divide, silently discarding the one that does not.
        let (arena, assertions) = query(PARTIAL_SPLIT);
        let forged = RealZeroProductRefutationCertificate {
            zeroing_cases: vec![vec!["v1".to_owned()]],
            nonzero_factors: vec!["v1".to_owned(), "v3".to_owned()],
        };
        assert!(
            !check_real_zero_product_refutation(&arena, &assertions, &forged),
            "a case list the query does not assert must not be accepted"
        );
    }

    #[test]
    fn an_empty_case_list_is_rejected() {
        // Vacuous truth: `all()` over an empty list is `true`, so without the
        // explicit emptiness guard this forgery certifies anything.
        let (arena, assertions) = query(ZERO_SUBSET);
        let mut forged = cert_for(ZERO_SUBSET);
        forged.zeroing_cases = Vec::new();
        assert!(!check_real_zero_product_refutation(
            &arena,
            &assertions,
            &forged
        ));
        forged = cert_for(ZERO_SUBSET);
        forged.zeroing_cases = vec![Vec::new()];
        assert!(!check_real_zero_product_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_nonzero_factor_list_the_query_does_not_assert_is_rejected() {
        let mut forged = cert_for(ZERO_SUBSET);
        forged.nonzero_factors.push("e".to_owned()); // e appears twice: not what is asserted
        let (arena, assertions) = query(ZERO_SUBSET);
        assert!(!check_real_zero_product_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_containment_failure_the_query_genuinely_asserts_is_rejected() {
        // Isolates STAGE 2. Both halves of this certificate really are asserted
        // by the query -- `(* x x) = 0` and `(* d e) != 0` -- so stage 1 passes
        // and only the containment check stands between it and a wrong `unsat`
        // on a SATISFIABLE query.
        let (arena, assertions) = query(NOT_A_FACTOR);
        let forged = RealZeroProductRefutationCertificate {
            zeroing_cases: vec![vec!["x".to_owned(), "x".to_owned()]],
            nonzero_factors: vec!["d".to_owned(), "e".to_owned()],
        };
        assert!(
            !check_real_zero_product_refutation(&arena, &assertions, &forged),
            "x does not divide d*e; accepting this certifies a satisfiable query"
        );
    }

    #[test]
    fn a_disjunct_that_zeroes_a_non_variable_is_declined() {
        // `(= (+ v2 v3) 0)` is a zeroing, but of a SUM. A sum vanishing says
        // nothing about a product containing its summands, so this arm cannot
        // contribute and the whole split must be refused. The query is
        // satisfiable (v1 = 1, v3 = 1, v2 = -1).
        let text = "(set-logic QF_NRA)\n\
            (declare-fun v1 () Real)(declare-fun v2 () Real)(declare-fun v3 () Real)\n\
            (assert (or (= v1 0) (= (+ v2 v3) 0)))\n\
            (assert (not (= (* v1 v3) 0)))\n\
            (check-sat)";
        let (arena, assertions) = query(text);
        assert!(
            real_zero_product_refutation(&arena, &assertions).is_none(),
            "an arm zeroing a sum must not be read as zeroing a factor"
        );
    }

    #[test]
    fn multiplicity_is_respected_not_just_membership() {
        // `a·a = 0` DOES divide `a·a·b`, but does NOT divide `a·b`. A set-based
        // containment check would wrongly accept the second.
        assert!(divides(
            &["a".to_owned(), "a".to_owned()],
            &["a".to_owned(), "a".to_owned(), "b".to_owned()]
        ));
        assert!(!divides(
            &["a".to_owned(), "a".to_owned()],
            &["a".to_owned(), "b".to_owned()]
        ));
    }
}
