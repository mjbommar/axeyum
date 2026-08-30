//! Tests for slice 4.
//!
//! Two `Definition`s land in this file (`ipc_ctx_meet`, `ipc_sat`), and the
//! kernel admitting a `Definition` proves only that it is well-formed — a
//! function returning garbage has the same type as the right one. So both are
//! pinned by **evaluation at concrete arguments against hand-computed
//! values**, with every expected number worked out in a comment before the
//! assertion, and with a negative control that varies one small subterm (never
//! a whole `riemannSum`-sized term — a failing `def_eq` has no early exit).
//!
//! Chain values are `0`/`1`/`2` and variable indices are `0`/`1` throughout:
//! these numerals are unary, so keeping the magnitudes tiny is what keeps the
//! reduction budget small.

use super::*;
use crate::Kernel;

/// `succ^n zero`, for `n <= 2` only.
fn num(kernel: &mut Kernel, p: &IpcSoundnessPrelude, n: u32) -> ExprId {
    let mut e = kernel.const_(p.provable.heyting.nat.zero, vec![]);
    let succ = kernel.const_(p.provable.heyting.nat.succ, vec![]);
    for _ in 0..n {
        e = kernel.app(succ, e);
    }
    e
}

fn apply(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// `Formula.var k`.
fn var(kernel: &mut Kernel, p: &IpcSoundnessPrelude, k: u32) -> ExprId {
    let idx = num(kernel, p, k);
    let var_const = kernel.const_(p.provable.heyting.var, vec![]);
    kernel.app(var_const, idx)
}

fn bot(kernel: &mut Kernel, p: &IpcSoundnessPrelude) -> ExprId {
    kernel.const_(p.provable.heyting.bot, vec![])
}

fn imp(kernel: &mut Kernel, p: &IpcSoundnessPrelude, a: ExprId, b: ExprId) -> ExprId {
    let c = kernel.const_(p.provable.heyting.imp, vec![]);
    apply(kernel, c, &[a, b])
}

fn nil(kernel: &mut Kernel, p: &IpcSoundnessPrelude) -> ExprId {
    kernel.const_(p.provable.nil, vec![])
}

fn cons(kernel: &mut Kernel, p: &IpcSoundnessPrelude, head: ExprId, tail: ExprId) -> ExprId {
    let c = kernel.const_(p.provable.cons, vec![]);
    apply(kernel, c, &[head, tail])
}

/// `fun _ => k`, a constant valuation.
fn valuation_const(kernel: &mut Kernel, p: &IpcSoundnessPrelude, k: u32) -> ExprId {
    let value = num(kernel, p, k);
    let nat_ty = kernel.const_(p.provable.heyting.nat.nat, vec![]);
    let anon = kernel.anon();
    // The binder is unused, so the body needs no abstraction.
    kernel.lam(anon, nat_ty, value, BinderInfo::Default)
}

/// `fun n => n`: `v 0 = 0`, `v 1 = 1`.
fn valuation_identity(kernel: &mut Kernel, p: &IpcSoundnessPrelude) -> ExprId {
    let id = 979_001_u64;
    let fv = kernel.fvar(id);
    let nat_ty = kernel.const_(p.provable.heyting.nat.nat, vec![]);
    let body = kernel.abstract_fvars(fv, &[id]);
    let anon = kernel.anon();
    kernel.lam(anon, nat_ty, body, BinderInfo::Default)
}

fn ctx_meet(kernel: &mut Kernel, p: &IpcSoundnessPrelude, l: ExprId, v: ExprId) -> ExprId {
    let c = kernel.const_(p.ctx_meet, vec![]);
    apply(kernel, c, &[l, v])
}

fn eval_at(kernel: &mut Kernel, p: &IpcSoundnessPrelude, f: ExprId, v: ExprId) -> ExprId {
    let c = kernel.const_(p.eval, vec![]);
    apply(kernel, c, &[f, v])
}

fn build() -> (Kernel, IpcSoundnessPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_ipc_soundness_prelude(&mut kernel).expect("slice-4 prelude must build");
    (kernel, prelude)
}

#[test]
fn slice_four_prelude_builds_and_declares_everything_it_names() {
    let (kernel, p) = build();
    for name in [
        p.ctx_meet,
        p.sat,
        p.le_of_ble_eq_false,
        p.meet3_le_left,
        p.meet3_le_right,
        p.le_meet3,
        p.le_join3_left,
        p.le_join3_right,
        p.meet_absorb_le,
        p.or_elim_chain,
        p.himp3_intro,
        p.himp3_elim,
        p.ctx_meet_le_top,
        p.soundness,
        p.sat_le_ctx_meet,
        p.soundness_sat,
        p.sat_not_vacuous,
        p.pem_not_provable,
    ] {
        assert!(
            kernel.environment().get(name).is_some(),
            "every name the prelude reports must be in the environment"
        );
    }
}

#[test]
fn the_theorems_are_theorems_and_the_definitions_are_definitions() {
    let (kernel, p) = build();
    for name in [p.ctx_meet, p.sat] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(crate::Declaration::Definition { .. })
            ),
            "ipc_ctx_meet / ipc_sat must be Definitions"
        );
    }
    for name in [
        p.meet3_le_left,
        p.himp3_intro,
        p.ctx_meet_le_top,
        p.soundness,
        p.soundness_sat,
        p.sat_not_vacuous,
        p.pem_not_provable,
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(crate::Declaration::Theorem { .. })
            ),
            "the results must be Theorems, not Definitions or Axioms"
        );
    }
}

#[test]
fn everything_this_slice_declares_is_axiom_free() {
    let mut kernel = Kernel::new();
    let p = build_ipc_soundness_prelude(&mut kernel).expect("slice-4 prelude must build");
    for name in [
        p.ctx_meet,
        p.sat,
        p.le_of_ble_eq_false,
        p.meet3_le_left,
        p.meet3_le_right,
        p.le_meet3,
        p.le_join3_left,
        p.le_join3_right,
        p.meet_absorb_le,
        p.or_elim_chain,
        p.himp3_intro,
        p.himp3_elim,
        p.ctx_meet_le_top,
        p.soundness,
        p.sat_le_ctx_meet,
        p.soundness_sat,
        p.sat_not_vacuous,
        p.pem_not_provable,
    ] {
        let footprint = kernel
            .axiom_footprint(name)
            .expect("axiom_footprint must succeed for a declared name");
        assert!(
            footprint.is_empty(),
            "slice 4 must be axiom-free; {name:?} depends on {footprint:?}"
        );
    }
}

// -- `ipc_ctx_meet` is a Definition: evaluate it -----------------------------

#[test]
fn ctx_meet_of_nil_is_the_chain_top() {
    // `ipc_ctx_meet nil v = 2` for any `v` (the empty meet is the top).
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 1);
    let l = nil(&mut kernel, &p);
    let lhs = ctx_meet(&mut kernel, &p, l, v);
    let two = num(&mut kernel, &p, 2);
    assert!(
        kernel.def_eq(lhs, two).expect("def_eq must not error"),
        "ipc_ctx_meet nil v must reduce to 2"
    );
}

#[test]
fn ctx_meet_of_a_singleton_is_that_formulas_value() {
    // v := fun _ => 1, so eval (var 0) v = 1 and
    // ipc_ctx_meet [var 0] v = meet3 1 2 = min 1 2 = 1.
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 1);
    let x = var(&mut kernel, &p, 0);
    let base = nil(&mut kernel, &p);
    let l = cons(&mut kernel, &p, x, base);
    let lhs = ctx_meet(&mut kernel, &p, l, v);
    let one = num(&mut kernel, &p, 1);
    assert!(
        kernel.def_eq(lhs, one).expect("def_eq must not error"),
        "ipc_ctx_meet [var 0] (const 1) must reduce to 1"
    );

    // Negative control, varying ONE small subterm (the expected numeral) so
    // the failing def_eq stays tiny: it must NOT also be 0.
    let zero = num(&mut kernel, &p, 0);
    assert!(
        !kernel.def_eq(lhs, zero).expect("def_eq must not error"),
        "ipc_ctx_meet [var 0] (const 1) must not be 0 -- the check would be vacuous"
    );
}

#[test]
fn ctx_meet_reads_the_head_formula_not_a_fixed_slot() {
    // Identity valuation: v 0 = 0, v 1 = 1. Same list SHAPE, different head:
    //   ipc_ctx_meet [var 0] id = meet3 0 2 = 0
    //   ipc_ctx_meet [var 1] id = meet3 1 2 = 1
    // Two different answers from one code path is what shows the head is read.
    let (mut kernel, p) = build();
    let v = valuation_identity(&mut kernel, &p);
    let base = nil(&mut kernel, &p);

    let x0 = var(&mut kernel, &p, 0);
    let l0 = cons(&mut kernel, &p, x0, base);
    let m0 = ctx_meet(&mut kernel, &p, l0, v);
    let zero = num(&mut kernel, &p, 0);
    assert!(
        kernel.def_eq(m0, zero).expect("def_eq must not error"),
        "ipc_ctx_meet [var 0] id must reduce to 0"
    );

    let x1 = var(&mut kernel, &p, 1);
    let l1 = cons(&mut kernel, &p, x1, base);
    let m1 = ctx_meet(&mut kernel, &p, l1, v);
    let one = num(&mut kernel, &p, 1);
    assert!(
        kernel.def_eq(m1, one).expect("def_eq must not error"),
        "ipc_ctx_meet [var 1] id must reduce to 1"
    );
}

#[test]
fn ctx_meet_takes_the_meet_over_the_whole_list() {
    // Identity valuation, ctx = [var 1, var 0]:
    //   ipc_ctx_meet [var 1, var 0] id = meet3 1 (meet3 0 2) = meet3 1 0 = 0.
    // The tail's `var 0` is what drags it to 0, so a `ipc_ctx_meet` that
    // ignored the tail would answer 1 here and fail.
    let (mut kernel, p) = build();
    let v = valuation_identity(&mut kernel, &p);
    let base = nil(&mut kernel, &p);
    let x0 = var(&mut kernel, &p, 0);
    let tail = cons(&mut kernel, &p, x0, base);
    let x1 = var(&mut kernel, &p, 1);
    let l = cons(&mut kernel, &p, x1, tail);
    let lhs = ctx_meet(&mut kernel, &p, l, v);
    let zero = num(&mut kernel, &p, 0);
    assert!(
        kernel.def_eq(lhs, zero).expect("def_eq must not error"),
        "ipc_ctx_meet [var 1, var 0] id must reduce to 0"
    );
    let one = num(&mut kernel, &p, 1);
    assert!(
        !kernel.def_eq(lhs, one).expect("def_eq must not error"),
        "it must NOT be 1 -- that is the answer a tail-ignoring definition gives"
    );
}

#[test]
fn ctx_meet_of_bot_is_the_chain_bottom() {
    // eval bot v = 0, so ipc_ctx_meet [bot] v = meet3 0 2 = 0.
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 2);
    let b = bot(&mut kernel, &p);
    let base = nil(&mut kernel, &p);
    let l = cons(&mut kernel, &p, b, base);
    let lhs = ctx_meet(&mut kernel, &p, l, v);
    let zero = num(&mut kernel, &p, 0);
    assert!(
        kernel.def_eq(lhs, zero).expect("def_eq must not error"),
        "ipc_ctx_meet [bot] v must reduce to 0"
    );
}

// -- `ipc_sat` is a Definition: evaluate it, and check it can be FALSE -------

#[test]
fn sat_of_nil_is_true() {
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 1);
    let l = nil(&mut kernel, &p);
    let sat_const = kernel.const_(p.sat, vec![]);
    let lhs = apply(&mut kernel, sat_const, &[l, v]);
    let true_ = kernel.const_(p.provable.heyting.nat.logic.true_, vec![]);
    assert!(
        kernel.def_eq(lhs, true_).expect("def_eq must not error"),
        "ipc_sat nil v must reduce to True"
    );
}

#[test]
fn sat_is_satisfied_by_a_valuation_that_sends_the_context_to_top() {
    // v := fun _ => 2, so eval (var 0) v = 2 and
    // ipc_sat [var 0] v = And (Eq Nat 2 2) True, which is inhabited by
    // `And.intro rfl True.intro`. Landing it as a Theorem is the check.
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 2);
    let x = var(&mut kernel, &p, 0);
    let base = nil(&mut kernel, &p);
    let l = cons(&mut kernel, &p, x, base);
    let sat_const = kernel.const_(p.sat, vec![]);
    let stated = apply(&mut kernel, sat_const, &[l, v]);

    let logic = p.provable.heyting.nat.logic;
    let ev = eval_at(&mut kernel, &p, x, v);
    let two = num(&mut kernel, &p, 2);
    let nat_ty = kernel.const_(p.provable.heyting.nat.nat, vec![]);
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let eq_const = kernel.const_(logic.eq, vec![one_lvl]);
    let head_eq = apply(&mut kernel, eq_const, &[nat_ty, ev, two]);
    let tail_sat = {
        let sat_const = kernel.const_(p.sat, vec![]);
        apply(&mut kernel, sat_const, &[base, v])
    };
    let refl_const = kernel.const_(logic.eq_refl, vec![one_lvl]);
    let head_proof = apply(&mut kernel, refl_const, &[nat_ty, two]);
    let tail_proof = kernel.const_(logic.true_intro, vec![]);
    let and_intro = kernel.const_(logic.and_intro, vec![]);
    let value = apply(
        &mut kernel,
        and_intro,
        &[head_eq, tail_sat, head_proof, tail_proof],
    );

    let anon = kernel.anon();
    let name = kernel.name_str(anon, "ipc_sat_positive_control");
    kernel
        .add_declaration(crate::Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stated,
            value,
        })
        .expect("ipc_sat [var 0] (const 2) must be inhabited -- otherwise sat is unsatisfiable");
}

#[test]
fn sat_is_not_constantly_true() {
    // The discriminating half. `ipc_sat_not_vacuous` is a kernel Theorem
    // REFUTING `ipc_sat [var 0] (fun _ => 1)`: at that valuation the head
    // evaluates to 1, not the top 2. A constantly-true `sat` -- which would
    // make the soundness corollary vacuous -- could not be refuted at all,
    // so this cannot pass for a degenerate definition.
    let (kernel, p) = build();
    assert!(
        matches!(
            kernel.environment().get(p.sat_not_vacuous),
            Some(crate::Declaration::Theorem { .. })
        ),
        "ipc_sat_not_vacuous must be an admitted Theorem"
    );
}

// -- the countermodel arithmetic the final theorem rests on ------------------

#[test]
fn pem_evaluates_to_one_and_a_tautology_evaluates_to_top_at_the_same_valuation() {
    // This is the pair that makes the final theorem discriminating rather
    // than an artefact of an algebra where nothing reaches the top:
    //   eval (p or not p) (const 1) = join3 1 (himp3 1 0) = join3 1 0 = 1
    //   eval (p -> p)     (const 1) = himp3 1 1 = 2                    (top)
    // Same valuation, same evaluator, one refutable and one not.
    let (mut kernel, p) = build();
    let v = valuation_const(&mut kernel, &p, 1);

    let pem = pem_instance(&mut kernel, &p.provable.heyting);
    let pem_value = eval_at(&mut kernel, &p, pem, v);
    let one = num(&mut kernel, &p, 1);
    assert!(
        kernel.def_eq(pem_value, one).expect("def_eq must not error"),
        "eval (p or not p) (const 1) must be 1"
    );
    let two = num(&mut kernel, &p, 2);
    assert!(
        !kernel.def_eq(pem_value, two).expect("def_eq must not error"),
        "eval (p or not p) (const 1) must NOT be the top 2"
    );

    let x = var(&mut kernel, &p, 0);
    let self_imp = imp(&mut kernel, &p, x, x);
    let taut_value = eval_at(&mut kernel, &p, self_imp, v);
    let two = num(&mut kernel, &p, 2);
    assert!(
        kernel.def_eq(taut_value, two).expect("def_eq must not error"),
        "eval (p -> p) (const 1) must be the top 2 -- otherwise the algebra \
         refutes everything and the countermodel means nothing"
    );
}

#[test]
fn the_excluded_middle_is_not_intuitionistically_derivable() {
    // The fact. `ipc_excluded_middle_not_provable :
    //   Not (Provable FormulaList.nil (or_ (var 0) (imp (var 0) bot)))`
    // is admitted through the trusted gate, so the statement below is checked
    // by re-deriving the stated type rather than by trusting the name.
    let (mut kernel, p) = build();
    let pem = pem_instance(&mut kernel, &p.provable.heyting);
    let base = nil(&mut kernel, &p);
    let provable_const = kernel.const_(p.provable.provable, vec![]);
    let derivation = apply(&mut kernel, provable_const, &[base, pem]);
    let not_const = kernel.const_(p.provable.heyting.nat.logic.not, vec![]);
    let expected = kernel.app(not_const, derivation);

    let Some(crate::Declaration::Theorem { ty, .. }) =
        kernel.environment().get(p.pem_not_provable).cloned()
    else {
        panic!("ipc_excluded_middle_not_provable must be an admitted Theorem");
    };
    assert!(
        kernel.def_eq(ty, expected).expect("def_eq must not error"),
        "the admitted theorem's type must be Not (Provable nil (p or not p))"
    );
}

#[test]
fn the_relation_still_derives_what_intuitionistic_logic_does_derive() {
    // Same-kind positive control for the theorem above. `Provable nil (p -> p)`
    // is a landed Theorem from slice 2, in the SAME relation the slice-4
    // theorem says cannot derive `p or not p`. Without this, "nothing is
    // derivable" would explain the headline result just as well.
    let (kernel, p) = build();
    assert!(
        matches!(
            kernel.environment().get(p.provable.imp_self),
            Some(crate::Declaration::Theorem { .. })
        ),
        "Provable nil (imp p p) must still be derivable in the same relation"
    );
    assert!(
        matches!(
            kernel.environment().get(p.provable.and_elim1_example),
            Some(crate::Declaration::Theorem { .. })
        ),
        "Provable nil (imp (and_ p q) p) must still be derivable"
    );
}
