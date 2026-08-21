//! The only claim that matters here is that the trusted kernel infers the
//! assembled term to `False` over a carrier with **no** assumptions. Everything
//! else is the boundary: which shapes decline, and why each guard is not
//! decoration.

use super::*;
use crate::string_length_cert::string_length_refutation;
use axeyum_smtlib::{SExpr, read_all};

/// `corpus/public-curated/non-incremental/QF_S/cvc5-regress-clean/r0_QF_SLIA_str004.smt2`,
/// verbatim. `|xx| = |xx| + |yy|` forces `|yy| = 0`, contradicting `|yy| > |xx| >= 0`.
/// Its combination uses a STRICT fact, so it routes through the mixed engine.
const STR004: &str = "(set-logic QF_SLIA)\n(set-info :status unsat)\n\
    (declare-fun xx () String)\n(declare-fun yy () String)\n\
    (assert (> (str.len yy) (str.len xx)))\n\
    (assert (= xx (str.++ xx yy)))\n(check-sat)";

/// `corpus/public-curated/non-incremental/QF_S/cvc5-regress-clean/r0_QF_S_str005.smt2`,
/// verbatim. Every fact is non-strict, so it routes through the general engine.
const STR005: &str = "(set-logic QF_S)\n(set-info :status unsat)\n\
    (declare-fun yy () String)\n\
    (assert (= (str.len yy) 0))\n(assert (not (= yy \"\")))\n(check-sat)";

/// `corpus/public-curated/non-incremental/QF_SLIA/…/r1_QF_SLIA_str-code-unsat-2.smt2`
/// — well, `QF_S/`, where the corpus files it. A two-arm case split.
const CODE2: &str = "(set-logic QF_SLIA)\n(set-info :status unsat)\n\
    (declare-fun x () String)\n(assert (= (str.len x) 1))\n\
    (assert (or (< (str.to_code x) 0) \
    (> (str.to_code x) 10000000000000000000000000000)))\n(check-sat)";

fn commands(text: &str) -> Vec<SExpr> {
    read_all(text).expect("reads")
}

fn certificate(text: &str) -> StringLengthRefutationCertificate {
    string_length_refutation(&commands(text)).expect("certificate")
}

fn reconstructs(text: &str) -> String {
    reconstruct_string_length_to_lean_module(&certificate(text)).expect("reconstruction succeeds")
}

fn declines(certificate: &StringLengthRefutationCertificate) -> String {
    match reconstruct_string_length_to_lean_module(certificate) {
        Err(ReconstructError::UnsupportedTerm { term }) => term,
        other => panic!("expected an UnsupportedTerm decline; got {other:?}"),
    }
}

/// **The measurement that decides whether any of this is worth having.**
///
/// `LraReconstructCtx::new()` builds `AxReal` — the legacy AXIOMATIZED ordered
/// field, 30 assumptions, this repository's only nonzero trusted-surface row. A
/// refutation checked there rests on all 30. `try_new_over_integers` builds the
/// constructed `Int` development, whose 30 ordered-ring declarations are
/// theorems and whose axiom footprint is empty.
///
/// So this asserts the emitted module is over the CONSTRUCTED integers. Without
/// it the route could be a 30-axiom proof wearing the same test name — and note
/// that `contains("Real.")` would match `CReal.` too, which is why the carrier
/// is decided by the declaration prefix the integer development actually emits.
#[test]
fn the_refutation_kernel_checks_over_the_constructed_integers() {
    for text in [STR004, STR005] {
        let module = reconstructs(text);
        assert!(
            !module.contains("AxReal."),
            "the module must not name the axiomatized ordered field"
        );
        assert!(
            module.contains("Int."),
            "the module must be over the constructed integer development"
        );
    }
}

#[test]
fn the_kernel_infers_the_str004_refutation_to_false() {
    // `reconstruct_string_length` gates on this internally; assert it again from
    // outside so the gate cannot be deleted silently.
    let mut ctx = LraReconstructCtx::try_new_over_integers().expect("integer development builds");
    let proof =
        reconstruct_string_length(&mut ctx, &certificate(STR004)).expect("reconstruction succeeds");
    let inferred = ctx.kernel_mut().infer(proof).expect("infer");
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(ctx.kernel_mut().def_eq(inferred, false_));
}

#[test]
fn the_kernel_infers_the_str005_refutation_to_false() {
    let mut ctx = LraReconstructCtx::try_new_over_integers().expect("integer development builds");
    let proof =
        reconstruct_string_length(&mut ctx, &certificate(STR005)).expect("reconstruction succeeds");
    let inferred = ctx.kernel_mut().infer(proof).expect("infer");
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(ctx.kernel_mut().def_eq(inferred, false_));
}

/// The two engines own disjoint shapes and both are reached: `str004`'s
/// combination has a strict fact and `str005`'s has none. Swapping the dispatch
/// either way makes one of the two reconstructions above decline, which is why
/// both corpus fixtures are kept rather than one.
#[test]
fn both_corpus_shapes_reach_a_different_engine() {
    let strict = certificate(STR004);
    let checked = checked_refutation(&strict).expect("re-checks");
    assert!(
        checked.branches[0].iter().any(|f| f.rel == Rel::Gt),
        "str004 must carry a strict fact"
    );
    let nonstrict = certificate(STR005);
    let checked = checked_refutation(&nonstrict).expect("re-checks");
    assert!(
        checked.branches[0].iter().all(|f| f.rel != Rel::Gt),
        "str005 must carry no strict fact"
    );
}

/// A case split declines. Refuting ONE arm of a several-arm split says nothing
/// about the query: a model satisfies at least one disjunct, and this
/// certificate's first arm (`str.to_code x < 0`) closes on its own with a tiny
/// combination — so without this guard the route would emit a kernel-checked
/// module for a refutation of a strictly stronger query than the one it claims.
#[test]
fn a_case_split_certificate_is_declined_not_half_reconstructed() {
    let cert = certificate(CODE2);
    assert!(cert.is_case_split() && cert.branch_count() == 2);
    let reason = declines(&cert);
    assert!(
        reason.contains("case analysis") && reason.contains("2 branches"),
        "the decline must name the case analysis it will not build: {reason}"
    );
}

/// The degenerate split: a `(or A)` with a single disjunct passes the
/// branch-count guard, because there is exactly one branch. It still declines,
/// and for a different reason: the query asserts the DISJUNCTION, so minting `A`
/// as a hypothesis assumes something no assertion states.
#[test]
fn a_single_disjunct_or_is_declined_because_the_query_does_not_assert_the_disjunct() {
    let text = "(set-logic QF_S)\n(declare-fun x () String)\n\
        (assert (or (< (str.len x) 0)))\n(check-sat)";
    let cert = certificate(text);
    assert!(
        cert.is_case_split() && cert.branch_count() == 1,
        "the fixture must reach the arm guard, not the branch-count guard"
    );
    let reason = declines(&cert);
    assert!(
        reason.contains("assumes a disjunct"),
        "the decline must name the assumed disjunct: {reason}"
    );
}

/// The resource guard, and the calibration that makes it one.
///
/// The ordered-ring engine counts a constant `k` as `k` copies of `one`, and the
/// kernel walks the resulting left-nested `add` chain recursively — so an
/// oversized combination does not run slowly, it aborts the process. The budget
/// therefore has to be pinned from BOTH sides: a fixture at the budget must
/// still reconstruct (or the guard is hiding a route that never worked), and one
/// just over it must decline.
///
/// The over-budget fixture is deliberately only just over. At `10^28` — what
/// `r1_QF_SLIA_str-code-unsat-2` actually names — deleting the guard would kill
/// the whole test binary with a stack overflow instead of failing this one test,
/// which is a mutation result nobody can read.
#[test]
fn the_unary_budget_is_pinned_from_both_sides() {
    // cost = 2k + 2 for this shape, so k = 63 is exactly the budget.
    let at_budget = "(set-logic QF_S)\n(declare-fun x () String)\n\
        (assert (<= (str.len x) (- 63)))\n(check-sat)";
    let module = reconstruct_string_length_to_lean_module(&certificate(at_budget))
        .expect("a combination AT the budget must still reconstruct");
    assert!(!module.is_empty());

    let over = "(set-logic QF_S)\n(declare-fun x () String)\n\
        (assert (<= (str.len x) (- 64)))\n(check-sat)";
    let cert = certificate(over);
    assert!(!cert.is_case_split());
    let reason = declines(&cert);
    assert!(
        reason.contains("unary terms") && reason.contains("128"),
        "the decline must report the size it refused and the budget: {reason}"
    );
}

/// The gate: the facts come only from a re-check against the certificate's own
/// carried commands. Re-pointing a valid certificate at a different script must
/// leave nothing to reconstruct.
#[test]
fn a_certificate_re_pointed_at_another_script_is_declined() {
    let mut forged = certificate(STR004);
    forged.testing_set_commands(commands(STR005));
    let reason = declines(&forged);
    assert!(
        reason.contains("does not re-check"),
        "the decline must be the re-check failing, not a shape decline: {reason}"
    );
}

/// The hypotheses are exactly the certificate's facts — one per fact, and
/// nothing else. A route that minted an extra assumption would still produce a
/// `False` the kernel accepts; only counting catches it.
#[test]
fn the_module_mints_one_hypothesis_per_checked_fact_and_no_more() {
    for text in [STR004, STR005] {
        let cert = certificate(text);
        let facts = checked_refutation(&cert).expect("re-checks").branches[0].len();
        let module = reconstruct_string_length_to_lean_module(&cert).expect("reconstruction");
        let minted = module
            .lines()
            .filter(|line| line.starts_with("axiom ") && line.contains(".hyp."))
            .count();
        assert_eq!(
            minted, facts,
            "one hypothesis per checked fact, no more:\n{module}"
        );
    }
}

/// An asserted EQUALITY enters the kernel as an equality, and the `<=` half the
/// fold needs is derived from it inside the kernel.
///
/// Without the override this is `str005`'s `(assert (= (str.len yy) 0))` entering
/// as `|yy| <= 0` — strictly weaker than the source says, and precisely the
/// distinction the certificate's own fact table turns on, since an equality is
/// the only fact a negative multiplier may scale. Both corpus shapes have
/// exactly one equality fact, so the count is pinned rather than merely tested
/// for presence.
#[test]
fn an_asserted_equality_enters_as_an_equality_not_as_its_weaker_half() {
    for text in [STR004, STR005] {
        let cert = certificate(text);
        let checked = checked_refutation(&cert).expect("re-checks");
        let equality_facts = checked.branches[0]
            .iter()
            .filter(|f| f.rel == Rel::Eq)
            .count();
        assert_eq!(
            equality_facts, 1,
            "the fixture must carry one equality fact"
        );

        let module = reconstruct_string_length_to_lean_module(&cert).expect("reconstruction");
        let equality_hypotheses = module
            .lines()
            .filter(|line| {
                line.starts_with("axiom ") && line.contains(".hyp.") && line.contains("Eq.")
            })
            .count();
        assert_eq!(
            equality_hypotheses, equality_facts,
            "every equality fact must be assumed as an equality:\n{module}"
        );
    }
}

/// The abstraction variables are named after the source they abstract, which is
/// the only thing letting a referee line the emitted hypotheses up against the
/// `.smt2` file.
#[test]
fn the_abstraction_variables_carry_their_source_names() {
    let module = reconstructs(STR004);
    assert!(
        module.contains("len_xx") && module.contains("len_yy"),
        "the module should name `len_xx` / `len_yy`:\n{module}"
    );
}

/// Determinism is a public API promise, and a reconstruction that renamed its
/// constants per run would break every downstream digest.
#[test]
fn the_rendered_module_is_deterministic() {
    assert_eq!(reconstructs(STR005), reconstructs(STR005));
}
