//! A `Real` Farkas refutation, restated over the **integers**, axiom-free.
//!
//! `generalize_over_ordered_ring` abstracts a Farkas refutation over the 22 laws
//! of an ordered commutative ring, leaving an axiom-free theorem that holds in
//! any model of them. `Real` is one such model. `ℤ` is another —
//! `build_int_model_of_arith` discharges all 22 with witnesses whose axiom
//! footprints are empty — and until now nothing instantiated at it.
//!
//! # The gap this closes
//!
//! Measured 2026-08-17, a conjunctive integer system whose *rational* relaxation
//! is already infeasible had no reconstruction at all:
//!
//! ```text
//! (set-logic QF_IDL) x - y <= 1, y - x <= -3   scan=ArithDpll -> StructuralAttestation
//! (set-logic QF_LIA) x > 5, x < 3              scan=ArithDpll -> StructuralAttestation
//! ```
//!
//! A structural attestation is an `axiom P` / `axiom ¬P` shim carrying none of
//! the reasoning. Yet `x > 5 ∧ x < 3` is refuted by ordinary Farkas, and a
//! Farkas combination uses only ring operations and order — never division,
//! which is exactly why the abstraction is possible in the first place. The
//! proof existed; only a `Real`-shaped destination for it did.
//!
//! Nothing here is relaxed and no `Int → Real` embedding is involved. The
//! generalized theorem is applied to `ℤ`'s own symbols and law witnesses, so the
//! hypotheses it is left waiting for are integer constraints.

#![cfg(feature = "full")]

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{
    LraReconstructCtx, RingTelescope, generalize_over_ordered_ring, instantiate_at_int_model,
    reconstruct_lra_proof,
};

/// `x < y ∧ y < x` — refuted by transitivity and irreflexivity alone.
fn strict_cycle() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let y = arena.real_var("y").expect("real variable");
    let a1 = arena.real_lt(x, y).expect("x < y");
    let a2 = arena.real_lt(y, x).expect("y < x");
    (arena, vec![a1, a2])
}

/// `x + y + z ≤ 1 ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z` — a genuine Farkas combination.
fn farkas_three() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let y = arena.real_var("y").expect("real variable");
    let z = arena.real_var("z").expect("real variable");
    let one = arena.real_const(axeyum_ir::Rational::integer(1));
    let xy = arena.real_add(x, y).expect("x + y");
    let xyz = arena.real_add(xy, z).expect("x + y + z");
    let a1 = arena.real_le(xyz, one).expect("x + y + z <= 1");
    let a2 = arena.real_le(one, x).expect("1 <= x");
    let a3 = arena.real_le(one, y).expect("1 <= y");
    let a4 = arena.real_le(one, z).expect("1 <= z");
    (arena, vec![a1, a2, a3, a4])
}

struct Measured {
    label: &'static str,
    ring_binders: usize,
    generalized_footprint: usize,
    int_footprint: Vec<String>,
    laws: usize,
    symbols: usize,
}

fn measure(label: &'static str, build: fn() -> (TermArena, Vec<TermId>)) -> Measured {
    let (arena, assertions) = build();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("LRA refutation");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("generalizes over the ordered ring");
    let at_int = instantiate_at_int_model(&mut ctx, &generalized).expect("instantiates at Z");
    Measured {
        label,
        ring_binders: generalized.ring_binders,
        generalized_footprint: generalized.footprint.len(),
        int_footprint: at_int.axiom_footprint,
        laws: at_int.laws_modelled,
        symbols: at_int.symbols_interpreted,
    }
}

/// The result: the same refutation, over `ℤ`, resting on nothing.
#[test]
fn a_farkas_refutation_becomes_an_axiom_free_theorem_about_the_integers() {
    for (label, build) in [
        (
            "strict-cycle",
            strict_cycle as fn() -> (TermArena, Vec<TermId>),
        ),
        (
            "farkas-three",
            farkas_three as fn() -> (TermArena, Vec<TermId>),
        ),
    ] {
        let m = measure(label, build);
        println!(
            "  {:<14} ring_binders={} generalized_footprint={} int: {} symbols + {} laws, \
             footprint={:?}",
            m.label, m.ring_binders, m.generalized_footprint, m.symbols, m.laws, m.int_footprint
        );
        assert_eq!(
            m.generalized_footprint, 0,
            "{}: the generalized theorem is supposed to be axiom-free before anything is \
             instantiated",
            m.label
        );
        assert!(
            m.int_footprint.is_empty(),
            "{}: the integer instantiation rests on {:?}. The generalized theorem is axiom-free \
             and every law witness the integer model supplies has an empty footprint, so a \
             non-empty footprint here means ℤ is carrying an assumption — a finding, not a \
             formality",
            m.label,
            m.int_footprint
        );
        assert_eq!(
            (m.symbols, m.laws),
            (8, 22),
            "{}: the ordered-ring interface is 8 carrier/operation symbols and 22 laws; a \
             different count means the model no longer covers what the refutation abstracts",
            m.label
        );
    }
}

/// An empty footprint on a VACUOUS statement would mean nothing, so read what
/// was actually proved.
///
/// The statement must be about `Int` — the integer model's carrier — and must
/// still carry the refutation's hypotheses. A theorem of `∀ …, True` also has an
/// empty footprint.
#[test]
fn the_integer_statement_is_about_int_and_keeps_its_hypotheses() {
    // `farkas_three`, not `strict_cycle`: the latter's refutation carries a
    // single variable binder on the REAL side too (measured, and unchanged by
    // this route), so it cannot show that several distinct integer variables
    // survive the instantiation.
    let (arena, assertions) = farkas_three();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("LRA refutation");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("generalizes");
    let at_int = instantiate_at_int_model(&mut ctx, &generalized).expect("instantiates at Z");
    let rendered = ctx.kernel().render_lean(at_int.statement);
    println!(
        "  statement: {rendered}\n  var_binders={} hyp_binders={} ring_binders={}",
        generalized.var_binders, generalized.hyp_binders, generalized.ring_binders
    );
    assert!(
        rendered.contains("Int"),
        "the instantiated statement never mentions Int, so it is not a theorem about the \
         integers: {rendered}"
    );
    assert!(
        rendered.contains("False"),
        "the statement no longer concludes False, so it is not a refutation: {rendered}"
    );
    assert!(
        rendered.contains("Int.le") || rendered.contains("Int.lt"),
        "the statement carries no order hypotheses over Int; an empty axiom footprint on a \
         statement that dropped its hypotheses would prove nothing: {rendered}"
    );
    assert_eq!(
        (generalized.var_binders, generalized.hyp_binders),
        (3, 4),
        "this fixture is x+y+z<=1 with 1<=x, 1<=y, 1<=z — three distinct variables and four \
         constraints. If they collapse, the instantiated theorem is weaker than the refutation \
         it claims to restate"
    );
}

/// Negative control: the instantiation is not a formality the kernel waves through.
///
/// Applying the generalized theorem to the integer model has to typecheck. If it
/// were accepted regardless of the arguments, the test above would prove nothing
/// — so this feeds it a refutation generalized under the *tight* telescope,
/// which abstracts only the laws the proof uses. Those are a strict subset, and
/// the model interprets every one of them, so it must still succeed; what it
/// must NOT do is succeed by ignoring its arguments.
#[test]
fn the_tight_telescope_also_instantiates_and_stays_axiom_free() {
    let (arena, assertions) = strict_cycle();
    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("LRA refutation");
    let tight = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used)
        .expect("tight generalization");
    assert!(
        tight.ring_binders < 30,
        "the tight telescope should abstract fewer than the full 30, else this is the same case"
    );
    let at_int = instantiate_at_int_model(&mut ctx, &tight).expect("tight form instantiates at Z");
    println!(
        "  tight          ring_binders={} int footprint={:?}",
        tight.ring_binders, at_int.axiom_footprint
    );
    assert!(
        at_int.axiom_footprint.is_empty(),
        "tight integer instantiation rests on {:?}",
        at_int.axiom_footprint
    );
}

/// A shape this route inherits, pinned rather than quietly relied on.
///
/// `strict_cycle` (`x < y ∧ y < x`) generalizes with **one** variable binder on
/// the REAL side, not two — measured 2026-08-17, and unchanged by anything here,
/// so the integer instantiation faithfully reproduces it. `farkas_three` keeps
/// all three. I have not explained the collapse and am not asserting it is a
/// defect; it is recorded so that if it changes, the change is noticed rather
/// than absorbed, and so nobody reads the one-variable strict-cycle statement as
/// evidence that this route drops variables.
#[test]
fn the_refutations_binder_shapes_are_what_was_measured() {
    for (label, build, expected) in [
        (
            "strict_cycle",
            strict_cycle as fn() -> (TermArena, Vec<TermId>),
            (1usize, 2usize),
        ),
        (
            "farkas_three",
            farkas_three as fn() -> (TermArena, Vec<TermId>),
            (3, 4),
        ),
    ] {
        let (arena, assertions) = build();
        let mut ctx = LraReconstructCtx::new();
        let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions).expect("refutation");
        let g = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used).expect("gen");
        println!(
            "  {label}: assertions={} var_binders={} hyp_binders={} ring_used={}",
            assertions.len(),
            g.var_binders,
            g.hyp_binders,
            g.ring_used.len()
        );
        assert_eq!(
            (g.var_binders, g.hyp_binders),
            expected,
            "{label}: the refutation's binder shape moved"
        );
    }
}

/// The motivating query, closed: `x > 5 ∧ x < 3`.
///
/// This is the exact `(set-logic QF_LIA)` instance that routes to `ArithDpll`
/// and renders a structural attestation — an `axiom P` / `axiom ¬P` shim with
/// none of the reasoning in it. Its real analogue reconstructs by Farkas, and
/// instantiating that at ℤ produces an axiom-free integer refutation of the same
/// constraints. So the reasoning for this query is available today; what is
/// missing is only the dispatch that reaches for it.
#[test]
fn the_query_that_renders_an_attestation_has_an_axiom_free_integer_refutation() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let five = arena.real_const(axeyum_ir::Rational::integer(5));
    let three = arena.real_const(axeyum_ir::Rational::integer(3));
    let a1 = arena.real_lt(five, x).expect("5 < x");
    let a2 = arena.real_lt(x, three).expect("x < 3");

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2]).expect("Farkas refutation");
    let generalized = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
        .expect("generalizes over the ordered ring");
    let at_int = instantiate_at_int_model(&mut ctx, &generalized).expect("instantiates at Z");

    let rendered = ctx.kernel().render_lean(at_int.statement);
    println!("  x>5 & x<3 over Z: {rendered}");
    assert!(
        at_int.axiom_footprint.is_empty(),
        "the integer refutation of x>5 & x<3 rests on {:?}",
        at_int.axiom_footprint
    );
    assert!(
        rendered.contains("Int") && rendered.contains("False"),
        "not an integer refutation: {rendered}"
    );
    assert_eq!(
        (generalized.var_binders, generalized.hyp_binders),
        (1, 2),
        "one variable and two constraints, matching the query"
    );
}
