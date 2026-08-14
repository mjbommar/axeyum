//! Small checked Boolean-simplification refutations.
//!
//! This module recognizes assertions that normalize to Boolean `false` using a
//! deliberately tiny simplifier: constants, equality reflexivity, double
//! negation, associative/idempotent `and`/`or`, and complement pairs
//! (`p ∧ ¬p`, `p ∨ ¬p`), plus equality of two Boolean formulas that are the
//! same up to bound-variable renaming and the quantifier-negation duality
//! (`F:quantifier-negation-duality`). Other non-Boolean-theory structure is kept
//! opaque, so every accepted certificate is re-checkable by re-running the same
//! normalizer over the original assertions.
//!
//! Quantified subformulas stay opaque *atoms* here — nothing is instantiated,
//! skolemized, or expanded. The only thing this module knows about a quantifier
//! is when two of them are the same formula written differently.

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::alpha_equivalent;

/// A self-checking refutation: one original assertion simplifies to `false`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolSimplificationRefutationCertificate {
    /// The original top-level assertion that normalizes to Boolean `false`, or
    /// the first assertion when the whole assertion conjunction normalizes to
    /// `false`.
    pub assertion: TermId,
    /// Whether the certificate uses the conjunction of all assertions.
    pub combined_assertions: bool,
}

/// Returns a certificate when any assertion is propositionally `false` under the
/// small checked Boolean normalizer, or when the conjunction of all assertions is
/// propositionally `false`.
#[must_use]
pub fn bool_simplification_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolSimplificationRefutationCertificate> {
    if let Some(cert) = assertions.iter().copied().find_map(|assertion| {
        matches!(simplify_bool(arena, assertion), BoolExpr::False).then_some(
            BoolSimplificationRefutationCertificate {
                assertion,
                combined_assertions: false,
            },
        )
    }) {
        return Some(cert);
    }

    let first = assertions.first().copied()?;
    matches!(simplify_nary(arena, true, assertions), BoolExpr::False).then_some(
        BoolSimplificationRefutationCertificate {
            assertion: first,
            combined_assertions: true,
        },
    )
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum BoolExpr {
    False,
    True,
    Atom(TermId),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
}

fn simplify_bool(arena: &TermArena, term: TermId) -> BoolExpr {
    match arena.node(term) {
        TermNode::BoolConst(false) => BoolExpr::False,
        TermNode::BoolConst(true) => BoolExpr::True,
        // Reflexivity, and — for Boolean-sorted operands only — equivalence up
        // to bound-variable renaming and the quantifier-negation duality
        // (`F:quantifier-negation-duality`). The extra predicate allocates
        // nothing and rewrites nothing: it decides the identity by walking the
        // two *original* operands, which is what keeps this checker independent
        // of the canonicalizer rule that reaches the same conclusion.
        TermNode::App { op: Op::Eq, args }
            if args.len() == 2 && bool_operands_equivalent(arena, args[0], args[1]) =>
        {
            BoolExpr::True
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => simplify_not(simplify_bool(arena, args[0])),
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => simplify_nary(arena, true, args),
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => simplify_nary(arena, false, args),
        _ => BoolExpr::Atom(term),
    }
}

/// Whether the two operands of an `=` provably denote the same value.
///
/// Structural identity settles it for every sort. Beyond that, only
/// **Boolean-sorted** operands are considered, and only by
/// [`alpha_equivalent`], which is confined to bound-variable renaming and the
/// quantifier-negation duality. The sort guard is not decoration: it keeps a
/// quantifier walk off every bit-vector and integer equality this normalizer
/// scans, and makes the admitted reasoning exactly "these two formulas are the
/// same formula".
fn bool_operands_equivalent(arena: &TermArena, left: TermId, right: TermId) -> bool {
    left == right
        || (arena.sort_of(left) == Sort::Bool
            && arena.sort_of(right) == Sort::Bool
            && alpha_equivalent(arena, left, right))
}

fn simplify_not(expr: BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::False => BoolExpr::True,
        BoolExpr::True => BoolExpr::False,
        BoolExpr::Not(inner) => *inner,
        other => BoolExpr::Not(Box::new(other)),
    }
}

fn simplify_nary(arena: &TermArena, is_and: bool, args: &[TermId]) -> BoolExpr {
    let mut set = BTreeSet::new();
    for &arg in args {
        match simplify_bool(arena, arg) {
            BoolExpr::False if is_and => return BoolExpr::False,
            BoolExpr::True if !is_and => return BoolExpr::True,
            BoolExpr::True | BoolExpr::False => {}
            BoolExpr::And(items) if is_and => set.extend(items),
            BoolExpr::Or(items) if !is_and => set.extend(items),
            item => {
                set.insert(item);
            }
        }
    }

    for item in &set {
        if set.contains(&complement(item)) {
            return if is_and {
                BoolExpr::False
            } else {
                BoolExpr::True
            };
        }
    }
    if is_and {
        for item in &set {
            if let BoolExpr::Not(inner) = item
                && let BoolExpr::And(items) = &**inner
                && items.iter().all(|conjunct| set.contains(conjunct))
            {
                return BoolExpr::False;
            }
        }
    }

    let items: Vec<_> = set.into_iter().collect();
    match items.as_slice() {
        [] if is_and => BoolExpr::True,
        [] => BoolExpr::False,
        [single] => single.clone(),
        _ if is_and => BoolExpr::And(items),
        _ => BoolExpr::Or(items),
    }
}

fn complement(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Not(inner) => (**inner).clone(),
        other => BoolExpr::Not(Box::new(other.clone())),
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};
    use axeyum_smtlib::parse_script;

    use super::bool_simplification_refutation;

    #[test]
    fn recognizes_negated_complement_tautology() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let not_p = arena.not(p).unwrap();
        let tautology = arena.or(p, not_p).unwrap();
        let assertion = arena.not(tautology).unwrap();

        let cert = bool_simplification_refutation(&arena, &[assertion])
            .expect("not (p or not p) simplifies to false");
        assert_eq!(cert.assertion, assertion);
        assert!(!cert.combined_assertions);
    }

    #[test]
    fn rejects_bare_tautology_assertion() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let not_p = arena.not(p).unwrap();
        let tautology = arena.or(p, not_p).unwrap();

        assert!(bool_simplification_refutation(&arena, &[tautology]).is_none());
    }

    #[test]
    fn recognizes_cross_assertion_negated_conjunction() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let q_symbol = arena.declare("q", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let q = arena.var(q_symbol);
        let both = arena.and(p, q).unwrap();
        let not_both = arena.not(both).unwrap();

        let cert = bool_simplification_refutation(&arena, &[not_both, p, q])
            .expect("not (p and q), p, q simplifies to false");
        assert_eq!(cert.assertion, not_both);
        assert!(cert.combined_assertions);
    }

    #[test]
    fn recognizes_reflexive_disequality_inside_conjunction() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let q_symbol = arena.declare("q", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let q = arena.var(q_symbol);
        let p_eq_p = arena.eq(p, p).unwrap();
        let not_p_eq_p = arena.not(p_eq_p).unwrap();
        let assertion = arena.and(q, not_p_eq_p).unwrap();

        let cert = bool_simplification_refutation(&arena, &[assertion])
            .expect("q and not (p = p) simplifies to false");
        assert_eq!(cert.assertion, assertion);
        assert!(!cert.combined_assertions);
    }

    #[test]
    fn recognizes_issue3970_purified_distinct_contradiction() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__issue3970-nl-ext-purify.smt2"
        ))
        .expect("issue3970 parses");
        let cert = bool_simplification_refutation(&script.arena, &script.assertions)
            .expect("issue3970 contains a checked Boolean/reflexivity contradiction");
        assert!(!cert.combined_assertions);
    }

    /// `F:quantifier-negation-duality`: the negation of the duality identities
    /// normalizes to `false` here, on the *original* parsed assertions, with no
    /// rewriting in between.
    #[test]
    fn recognizes_negated_quantifier_negation_duality() {
        let script = parse_script(include_str!(
            "../../../artifacts/facts/smt2/neg-quantifier-negation-duality.smt2"
        ))
        .expect("duality benchmark parses");
        let cert = bool_simplification_refutation(&script.arena, &script.assertions)
            .expect("negated quantifier-negation duality normalizes to false");
        assert_eq!(cert.assertion, script.assertions[0]);
        assert!(!cert.combined_assertions);
    }

    /// SOUNDNESS NEGATIVE. Every near-miss of the duality is `sat`, so the
    /// normalizer must refuse each one. These are the shapes the new equality
    /// case newly *looks* at, which is exactly where the corpus gives no cover.
    ///
    /// * `not (forall x. P x)` vs `forall x. not (P x)` — quantifier not flipped.
    /// * `not (forall x. P x)` vs `exists x. P x` — body not negated.
    /// * `not (exists x. P x)` vs `exists x. not (P x)` — quantifier not flipped.
    /// * `forall x. P x` vs `exists x. P x` — no negation at all.
    /// * `not (forall x. P x)` vs `exists y. not (P z)` — wrong bound variable.
    #[test]
    fn refuses_every_near_miss_of_the_duality() {
        const NEAR_MISSES: &[&str] = &[
            "(= (not (forall ((x U)) (P x))) (forall ((x U)) (not (P x))))",
            "(= (not (forall ((x U)) (P x))) (exists ((x U)) (P x)))",
            "(= (not (exists ((x U)) (P x))) (exists ((x U)) (not (P x))))",
            "(= (forall ((x U)) (P x)) (exists ((x U)) (P x)))",
            "(= (not (forall ((x U)) (P x))) (exists ((y U)) (not (P z))))",
            // The duality holds for `P`, but these relate *different*
            // predicates, so nothing may be concluded.
            "(= (not (forall ((x U)) (P x))) (exists ((x U)) (not (Q x))))",
        ];
        for claim in NEAR_MISSES {
            let source = format!(
                "(set-logic UF)\n\
                 (declare-sort U 0)\n\
                 (declare-fun P (U) Bool)\n\
                 (declare-fun Q (U) Bool)\n\
                 (declare-const z U)\n\
                 (assert (not {claim}))\n\
                 (check-sat)\n"
            );
            let script = parse_script(&source).expect("near-miss parses");
            assert!(
                bool_simplification_refutation(&script.arena, &script.assertions).is_none(),
                "the normalizer refuted a satisfiable near-miss: {claim}"
            );
        }
    }
}
