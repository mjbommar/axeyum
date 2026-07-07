//! Tests for the regex-membership derivative-emptiness → kernel-checked Lean
//! reconstruction.
//!
//! Positive: each empty-language membership problem reconstructs to a module whose
//! `False` proof the kernel already checked (a successful return *is* the kernel
//! gate — [`RegexCtx::gate_and_render`] `infer`s + `def_eq False`-compares before
//! rendering). Declines: a satisfiable problem is safely declined (an `Err`, never
//! a wrong `False`). Negative: a deliberately wrong discriminator term is rejected
//! by the kernel gate (never a bogus `False`).

use axeyum_strings::Membership;
use axeyum_strings::regex::Regex;

use super::*;

/// A concrete literal regex from a `&str`, as a left-nested concatenation of
/// single-character leaves (`""` is `ε`).
fn lit(s: &str) -> Regex {
    let mut acc: Option<Regex> = None;
    for c in s.chars() {
        let ch = Regex::character(c as u32);
        acc = Some(match acc {
            None => ch,
            Some(prev) => Regex::concat(prev, ch),
        });
    }
    acc.unwrap_or_else(Regex::empty)
}

/// Reconstruct through the public entry, asserting the module was kernel-checked
/// (the `Ok` return is the `infer` + `def_eq False` gate) and carries the theorem.
fn reconstruct(problem: &Membership) -> String {
    let src = reconstruct_regex_emptiness_to_lean_module(problem)
        .expect("empty-language membership reconstructs + kernel-checks to False");
    assert!(src.contains("theorem"), "renders a Lean theorem module");
    assert!(
        src.contains(REGEX_LEAN_THEOREM),
        "module carries the refutation theorem name"
    );
    src
}

// ----- positive: empty-language memberships reconstruct ----------------------

#[test]
fn empty_language_none_membership_reconstructs() {
    // x ∈ re.none — membership in the empty language (the degenerate closure {∅}).
    let problem = Membership {
        positives: vec![Regex::none()],
        ..Membership::default()
    };
    reconstruct(&problem);
}

#[test]
fn intersection_empty_membership_reconstructs() {
    // x ∈ (ab)* ∩ (ababac)*  with len ≥ 2 — a multi-state nullable-free closure
    // (the `intersection_empty_is_unsat` shape); only common member is ε.
    let problem = Membership {
        positives: vec![Regex::star(lit("ab")), Regex::star(lit("ababac"))],
        len_lo: 2,
        ..Membership::default()
    };
    reconstruct(&problem);
}

#[test]
fn inclusion_empty_membership_reconstructs() {
    // s ∈ A*  ∧  s ∉ (A|B)*  — inclusion emptiness (A* ⊆ (A|B)*), a positive +
    // negative (complemented) intersection whose closure is nullable-free.
    let problem = Membership {
        positives: vec![Regex::star(lit("A"))],
        negatives: vec![Regex::star(Regex::union(lit("A"), lit("B")))],
        ..Membership::default()
    };
    reconstruct(&problem);
}

#[test]
fn disjoint_char_intersection_membership_reconstructs() {
    // x ∈ "a" ∩ x ∈ "b" with len 1 — two disjoint single-character classes.
    let problem = Membership {
        positives: vec![lit("a"), lit("b")],
        len_lo: 1,
        len_hi: Some(1),
        ..Membership::default()
    };
    reconstruct(&problem);
}

// ----- declines: a satisfiable problem is not (wrongly) reconstructed ---------

#[test]
fn satisfiable_membership_is_declined() {
    // x ∈ (ab)*  with len ≥ 2 — satisfiable (witness "ab"); there is NO emptiness
    // certificate, so the reconstructor declines (never a wrong False).
    let problem = Membership {
        positives: vec![Regex::star(lit("ab"))],
        len_lo: 2,
        ..Membership::default()
    };
    assert!(
        reconstruct_regex_emptiness_to_lean_module(&problem).is_err(),
        "a satisfiable membership has no emptiness certificate to reconstruct"
    );
}

#[test]
fn complement_singleton_satisfiable_is_declined() {
    // x ∈ ∁("a") with len 1 — satisfiable (any single char ≠ "a"); declined.
    let problem = Membership {
        negatives: vec![lit("a")],
        len_lo: 1,
        len_hi: Some(1),
        ..Membership::default()
    };
    assert!(
        reconstruct_regex_emptiness_to_lean_module(&problem).is_err(),
        "a satisfiable complement membership is declined, not reconstructed"
    );
}

// ----- negative: the kernel rejects a wrong proof ----------------------------

#[test]
fn kernel_rejects_reflexive_bool_discriminator() {
    // A deliberately wrong closing step: feed the `Bool.true ≠ Bool.false`
    // discriminator a *reflexive* `Eq Bool true true` instead of `Eq Bool true
    // false`. The assembled term infers to `d true = True`, not `False`, so the
    // kernel gate (`infer` + `def_eq False`) must reject it — never a bogus `False`.
    let mut ctx = RegexCtx::new(1, 1);
    let bool_const = ctx.bool_const();
    let bool_true = ctx.bool_true();
    let bogus_heq = ctx.eq_refl(bool_const, bool_true); // Eq Bool true true
    let bogus_proof = ctx.bool_true_ne_false(bogus_heq);
    let result = ctx.gate_and_render(bogus_proof);
    assert!(
        matches!(result, Err(ReconstructError::KernelRejected { .. })),
        "the kernel must reject a discriminator built over a reflexive equality"
    );
}
