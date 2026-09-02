//! Tests for `creal/lub_boundary.rs` — ADR-0603 row 2 for the least upper
//! bound property (Spivak ch. 8).
//!
//! In its own file rather than in `creal_tests.rs` because that file is the
//! append point every concurrent `creal` lane collides on; the inventory
//! shards under `creal/inventory/` exist for exactly the same reason.
//!
//! **The non-vacuity control is the test that matters here.**
//! `CReal.lub_decides_em` is a REFUTATION shaped as an implication, so if its
//! two supremum hypotheses had no models at all it would be unfalsifiable —
//! precisely the "checker that cannot fail" defect this repository audits
//! against, arriving as a theorem rather than as a script. ADR-0603
//! Amendment 2 makes such a control mandatory, and `creal/extreme_value.rs`'s
//! row 2 carries the analogous pair.
//!
//! So: discharge BOTH hypotheses at a proposition whose truth this kernel
//! already knows, and let the kernel infer the conclusion. Nothing is
//! assumed; the witnesses are built and `Kernel::infer` accepts them.

use super::convergence::exists_intro;
use super::creal_tests::built;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, on_a_deep_stack};

/// **The non-vacuity control.** At `A := True` the set `lubSet True` is
/// `(−∞, 0] ∪ (−∞, 1] = (−∞, 1]`, whose supremum genuinely is `1`, and both
/// of `lub_decides_em`'s hypotheses are dischargeable:
///
/// - the upper-bound half is `CReal.lubSet_bounded` at `A := True`, verbatim
///   and with no transport at all;
/// - the approximation half takes the witness `x := 1` itself, since
///   `1 ∈ lubSet True` (the right disjunct, `And.intro True.intro
///   (le_refl one)`) and the hypothesis `t < 1` IS the required `t < x`.
///
/// The conclusion is then pinned VERBATIM against an independently built
/// `Or True (Not True)` rather than loosely matched, so a theorem concluding
/// some other disjunction cannot pass.
///
/// Note what this does and does not show. It shows the hypotheses have a
/// model, so the implication is not vacuous. It does **not** weaken the
/// boundary: at a DECIDABLE `A` the conclusion `Or A (Not A)` is available
/// anyway, which is exactly why this instance is safe to exhibit and why no
/// analogous discharge exists for an arbitrary `Prop`.
#[test]
fn lub_supremum_hypotheses_are_satisfiable_at_a_decidable_proposition() {
    on_a_deep_stack(lub_supremum_hypotheses_are_satisfiable_at_a_decidable_proposition_body);
}

fn lub_supremum_hypotheses_are_satisfiable_at_a_decidable_proposition_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let true_p = d.kernel().const_(p.rat.int.logic.true_, vec![]);
    let true_intro = d.kernel().const_(p.rat.int.logic.true_intro, vec![]);
    let and_intro = p.rat.int.logic.and_intro;

    // hub : ∀ x, lubSet True x → le x one — `lubSet_bounded` at `A := True`.
    let hub = d.lemma(p.lub_boundary.lub_set_bounded, &[true_p]);

    // `1 ∈ lubSet True`, through the right disjunct.
    let one_is_member = {
        let below = d.const_app(p.le, &[one_c, zero_c]);
        let inside = d.const_app(p.le, &[one_c, one_c]);
        let raised = d.and(true_p, inside);
        let refl_one = d.lemma(p.le_refl, &[one_c]);
        let pair = d.const_app(and_intro, &[true_p, inside, true_intro, refl_one]);
        d.or_inr(below, raised, pair)
    };

    // happrox : ∀ t, lt t one → Exists CReal (fun x => And (lubSet True x) (lt t x)).
    let happrox = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ht_ty = d.const_app(p.lt, &[t, one_c]);
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);

        let predicate = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let member = d.const_app(p.lub_boundary.lub_set, &[true_p, x]);
            let strict = d.const_app(p.lt, &[t, x]);
            let body = d.and(member, strict);
            d.lam_fv(x_fv, carrier, body)
        };

        let member_ty = d.const_app(p.lub_boundary.lub_set, &[true_p, one_c]);
        let strict_ty = d.const_app(p.lt, &[t, one_c]);
        let pair = d.const_app(and_intro, &[member_ty, strict_ty, one_is_member, ht]);
        let witness = exists_intro(&mut d, p, carrier, predicate, one_c, pair);

        let with_ht = d.lam_fv(ht_fv, ht_ty, witness);
        d.lam_fv(t_fv, carrier, with_ht)
    };

    let instance = d.lemma(
        p.lub_boundary.lub_decides_em,
        &[true_p, one_c, hub, happrox],
    );
    let ty = d.kernel().infer(instance).unwrap_or_else(|error| {
        panic!(
            "lub_decides_em refused a DISCHARGED pair of supremum hypotheses \
             at A := True, s := 1, so the row-2 statement would be vacuous: \
             {error:?}"
        )
    });

    let expected = {
        let not_true = d.not(true_p);
        d.or(true_p, not_true)
    };
    assert_eq!(
        d.kernel().render_lean(ty),
        d.kernel().render_lean(expected),
        "a supremum for `lubSet A` must conclude exactly `Or A (Not A)` — \
         unrestricted excluded middle at that proposition — and nothing else"
    );
}

/// **The negative control**, differing from the test above in ONE small term:
/// the membership witness takes `Or.inl` (claiming `1 ≤ 0`) where the proof
/// in hand is `And True (le one one)`. The kernel must refuse.
///
/// Deliberately a change of HEAD CONSTANT (`And` against `CReal.le`) rather
/// than a change of arguments inside one `CReal.le`: a FAILING `def_eq` has
/// no early exit, and transposing two real-valued arguments would set the
/// checker unfolding `CReal.le`'s sequence definition without bound. Two
/// mismatched head constants whnf to a Pi against an inductive application
/// and fail immediately.
#[test]
fn lub_membership_witness_must_take_the_correct_disjunct() {
    on_a_deep_stack(lub_membership_witness_must_take_the_correct_disjunct_body);
}

fn lub_membership_witness_must_take_the_correct_disjunct_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let true_p = d.kernel().const_(p.rat.int.logic.true_, vec![]);
    let true_intro = d.kernel().const_(p.rat.int.logic.true_intro, vec![]);
    let and_intro = p.rat.int.logic.and_intro;

    let below = d.const_app(p.le, &[one_c, zero_c]);
    let inside = d.const_app(p.le, &[one_c, one_c]);
    let raised = d.and(true_p, inside);
    let refl_one = d.lemma(p.le_refl, &[one_c]);
    let pair = d.const_app(and_intro, &[true_p, inside, true_intro, refl_one]);

    // The positive control, in the SAME test: the correct disjunct is accepted.
    let good = d.or_inr(below, raised, pair);
    assert!(
        d.kernel().infer(good).is_ok(),
        "the positive control must type-check, or this test measures nothing"
    );

    let bad = d.or_inl(below, raised, pair);
    assert!(
        d.kernel().infer(bad).is_err(),
        "`Or.inl` here claims `1 <= 0`; the kernel must refuse the \
         `And True (le one one)` proof supplied for it"
    );
}

/// The four declarations exist with the kinds this file claims, and every one
/// of them has an EMPTY `Kernel::axiom_footprint`.
///
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` already
/// covers these through the inventory shard, and derives its coverage from
/// `kernel.environment()` rather than from a list. This test is the named,
/// quotable form for the fact ledger: it names the four declarations
/// explicitly, so a fact citing it fails if any one of them is removed,
/// downgraded to an `Axiom`, or acquires a footprint.
#[test]
fn lub_boundary_declarations_are_derived_and_axiom_free() {
    on_a_deep_stack(lub_boundary_declarations_are_derived_and_axiom_free_body);
}

fn lub_boundary_declarations_are_derived_and_axiom_free_body() {
    let (kernel, p) = built();
    let expected: [(&str, crate::NameId, &str); 4] = [
        ("CReal.lubSet", p.lub_boundary.lub_set, "def"),
        (
            "CReal.lubSet_inhabited",
            p.lub_boundary.lub_set_inhabited,
            "theorem",
        ),
        (
            "CReal.lubSet_bounded",
            p.lub_boundary.lub_set_bounded,
            "theorem",
        ),
        (
            "CReal.lub_decides_em",
            p.lub_boundary.lub_decides_em,
            "theorem",
        ),
    ];
    for (label, name, kind) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} was interned but never declared"));
        match kind {
            "theorem" => assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "{label} must be a checked Theorem"
            ),
            "def" => assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "{label} must be a Definition"
            ),
            _ => unreachable!(),
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}

/// **The statement says what this file claims it says.** Renders
/// `CReal.lub_decides_em`'s declared type and requires it to mention the
/// counterexample family, the negation, and a `Prop`-sorted binder — with a
/// positive control (`Or`) that must be present and a NEGATIVE control
/// (`CReal.evtLinear`) that must be absent, so a rendering change that
/// silently produced an empty or unrelated string cannot pass.
///
/// This exists because the row-2 claim is a claim about a STATEMENT, and this
/// repository's own gotcha list records prose about kernel contents being
/// wrong repeatedly. The type is read from `kernel.environment()`, never from
/// this file's doc comments.
#[test]
fn lub_decides_em_states_excluded_middle_over_the_counterexample_family() {
    on_a_deep_stack(lub_decides_em_states_excluded_middle_over_the_counterexample_family_body);
}

fn lub_decides_em_states_excluded_middle_over_the_counterexample_family_body() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.lub_boundary.lub_decides_em)
        .expect("CReal.lub_decides_em must be declared");
    let ty = match declaration {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("CReal.lub_decides_em must be a Theorem, got {other:?}"),
    };
    let rendered = kernel.render_lean(ty);

    for needle in ["lubSet", "Not", "Or", "Prop", "Exists"] {
        assert!(
            rendered.contains(needle),
            "`CReal.lub_decides_em`'s type must mention `{needle}`; it rendered as {rendered}"
        );
    }
    assert!(
        !rendered.contains("evtLinear"),
        "negative control: the LUB row-2 statement must not be the EVT one"
    );
}
