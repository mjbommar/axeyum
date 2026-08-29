//! The `Nat.bit` decode bridge: relating `landAux`/`lorAux`/`ldiffAux` at a
//! `Nat.bit`-constructed argument (`fuel = bit a m`, non-canonical) back to
//! the recursive step at the DECODED `(m, n)`.
//!
//! Two prior lanes (`docs/plan/status/237-nat-fuel-irrelevance.md`,
//! `docs/plan/status/239-nat-fuel-transport.md`) each independently named
//! this as the blocker for `land_bit`/`lor_bit`/`ldiff_bit` and stopped
//! short of attempting it. This file lands it for `Nat.land` in full and
//! documents exactly how far the `Nat.lor`/`Nat.ldiff` transport gets.
//!
//! # The construction, once
//!
//! `land m n := landAux m m n` uses `m` itself as fuel, and `bit a m` (for
//! symbolic `a`, `m`) is not syntactically `zero`/`succ`-shaped — it is
//! `add (mul 2 m) (cond a 1 0)`, stuck at symbolic `m`. So the canonical
//! fuel `bit a m` cannot be unfolded by a single `Nat.rec` step the way
//! `land_zero_left`/`land_zero_right` rely on.
//!
//! The fix does not touch the canonical fuel at all — it swaps it, via
//! [`Nat.land_aux_eq_land_of_le`](NatPrelude::land_aux_eq_land_of_le), for
//! an ARTIFICIALLY chosen fuel that IS syntactically `succ`-shaped
//! regardless of `a`/`m`:
//!
//! ```text
//! base  := mul 2 m                     -- = bit false m, by defn
//! k1    := succ base                   -- = bit true m, by defn
//! fuel  := succ k1
//! ```
//!
//! `Le (bit a m) fuel` holds unconditionally (case split on `a`: `a = true`
//! makes `bit a m` DEFEQ `k1` exactly, `a = false` makes it DEFEQ `base =
//! pred k1`; either way `≤ k1 ≤ fuel`), and `Le m k1` holds unconditionally
//! too (`m ≤ mul 2 m` via [`two_mul_eq_add_self`] + `le_add_right`, then
//! `≤ succ (mul 2 m) = k1`). Neither bound needs `m`'s shape exposed.
//!
//! Once `fuel` is `succ`-shaped, ONE `Nat.rec` step unfolds `landAux fuel
//! (bit a m) (bit b n)` to the shared `guarded` combinator
//! ([`rec_agreement`](super::rec_agreement)'s device, reproduced locally
//! here to avoid a cross-lane edit to that file) applied at the RAW
//! `div`/`mod` subterms. [`declare_bit_div_mod_two`] supplies the two facts
//! that decode them: `div (bit b n) 2 = n` and `mod (bit b n) 2 = cond b 1
//! 0`, both via one `div_mod_unique` call each against `Nat.div_mod_exec`
//! (the reconstruction equation is `bit`'s own definition, closed by
//! `refl`; the bound `cond b 1 0 < 2` is a two-leaf `Bool` split). After
//! that rewrite, the recursive occurrence is `landAux k1 m n`, itself
//! swapped back to the canonical `land m n` by
//! `land_aux_eq_land_of_le` again (this time `Le m k1`).
//!
//! What remains is a claim with NO fuel machinery left in it: `guarded (bit
//! a m) (bit b n) 0 0 (land m n) (mul (cond a 1 0) (cond b 1 0)) = bit (a
//! && b) (land m n)`. This still has two `beq _ 0` guards evaluated on
//! `bit a m`/`bit b n`, which are not defeq-resolved for fully symbolic
//! `a`, `m`, `b`, `n` — but resolving them needs no induction, only a
//! bounded case tree, and **the split is on the `Bool`s (`b`, then `a`),
//! NOT on the `Nat`s (`n`, `m`) an earlier (wrong) draft of this file
//! tried.** `bit test k := add (mul 2 k) (cond test 1 0)`, and `Nat.add`
//! recurses on its SECOND argument — `cond test 1 0` here — which is stuck
//! for symbolic `test` regardless of `k`'s shape. So `bit true k` is
//! `succ`-shaped for ANY `k`, even fully symbolic, and `beq (succ _) 0`
//! reduces to `false` by δι alone; only `test = false` needs the OTHER
//! operand's shape exposed (`bit false k = mul 2 k`, which recurses on `k`
//! and is genuinely stuck at symbolic `k`). Concretely: split `b` first
//! (the `n`-guard checks `bit b n`); at `b = true` the guard is false for
//! ANY `n`, no further split needed; at `b = false`, split `n` (`n = 0`
//! gives the guard true; `n = succ _` gives it false, unconditionally in
//! `a`/`m`). Then resolve the `m`-guard the same way via `a`, `m`. Land's
//! absorbing-zero guard rows (`land_zero_left`/`land_zero_right`, both
//! already proved) close the two degenerate leaves; the "both guards
//! false" leaf needs one more small fact, [`and_cond_mul_eq_cond`] (`mul
//! (cond a 1 0) (cond b 1 0) = cond (a && b) 1 0`, itself a two-leaf
//! `Bool` split on `a` alone using `one_mul`/`zero_mul`, since `Nat.mul`
//! recurses on its SECOND argument and `cond b 1 0` stays stuck at
//! symbolic `b`).
//!
//! **This flip cost a full debugging cycle and is worth stating plainly as
//! its own lesson.** The first draft assumed `bit test k` is `succ`-shaped
//! once `k` is `succ`-shaped (mirroring the `Nat.add`-recurses-on-its-
//! right-argument trap from a DIFFERENT angle), built the whole guard tree
//! around splitting `n`/`m`, and the kernel rejected `land_bit` with a
//! `TypeMismatch` naming two large opaque `ExprId`s. `Kernel::render_lean`
//! on both sides (via a throwaway `#[test]` catching the `Err` and
//! printing `k.render_lean(expected)`/`k.render_lean(got)`) showed the
//! `expected` side's guard was `beq (bit a (succ m_pred)) 0` — still stuck,
//! because `a` was the thing left symbolic, not `m`. The fix was cheap
//! once seen; finding it needed the rendered terms, not more staring at
//! the Rust.
//!
//! # What transports to `lor`/`ldiff`, and what does not (not attempted here)
//!
//! The fuel-swap machinery (`base`/`k1`/`fuel`, the two `Le` bounds, the
//! `div`/`mod` decode) is IDENTICAL for all three — it never inspects
//! `land`'s absorbing zero. What does NOT transport unchanged is the guard
//! tree's leaves: `lor`'s fuel-exhaustion row returns the OTHER full
//! operand (`bit a m` / `bit b n`), not the constant `0`, so its
//! degenerate leaves need `lor_zero_left`/`lor_zero_right` (both already
//! proved) instead, and its per-bit combine is `max` via `ble` +
//! `bool_select_nat`, needing a NEW `or`-flavoured analogue of
//! [`and_cond_mul_eq_cond`] that is NOT a two-leaf split the way the `and`
//! version is (`ble (cond a 1 0) (cond b 1 0)` does not resolve from a
//! split on `a` alone the way `and`'s iota-reduction does — it needs the
//! VALUE of `cond b 1 0` too in the `a = true` branch, i.e. a further
//! split on `b` there). `ldiff`'s hybrid guards and `beq`-based combine
//! need the analogous but distinct treatment. Landing the bridge
//! (`Nat.land_bit`) and documenting this precisely is this lane's scope;
//! `lor_bit`/`ldiff_bit` are left open for a follow-up lane.

use super::NatPrelude;
use super::bitwise::{and_fn, or_fn};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ, two_mul_eq_add_self};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// The shared shape of every `…Aux (succ k)` row in this bitwise family —
/// reproduced from `rec_agreement.rs` rather than imported (that file is a
/// concurrent-edit hotspot this lane was told to avoid touching). See that
/// file's own copy for the full rationale; this one must stay byte-for-byte
/// equivalent.
fn guarded(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    on_n_zero: ExprId,
    on_m_zero: ExprId,
    recursive: ExprId,
    bit: ExprId,
) -> ExprId {
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.mul(two, recursive);
    let stepped = d.add(doubled, bit);
    let m_is_zero = d.beq(m, zero);
    let inner = d.bool_select_nat(m_is_zero, on_m_zero, stepped);
    let n_is_zero = d.beq(n, zero);
    d.bool_select_nat(n_is_zero, on_n_zero, inner)
}

/// `Bool.rec` at a `Prop`-valued motive varying with the scrutinee: the
/// `Bool` case-split eliminator this file's proofs use throughout. Not
/// reused from `bitwise.rs`'s private `bool_select_bool` (`Nat`/`Bool`
/// codomain, not `Prop`) or `ops.rs`'s `cases_mod_two`/`cases_lt_bound`
/// (`Nat` scrutinee, not `Bool`).
pub(super) fn case_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_true: &dyn Fn(&mut NatDev<'_>) -> ExprId,
    at_false: &dyn Fn(&mut NatDev<'_>) -> ExprId,
) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let motive_lam = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive(d, x);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = at_true(d);
    let case_false = at_false(d);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive_lam, case_false, case_true, b])
}

/// The shared witness behind both [`NatPrelude::bit_div_two`] and
/// [`NatPrelude::bit_mod_two`]: `bit test n`'s own definition IS the
/// reconstruction equation (`add (mul 2 n) (cond test 1 0)`, closed by
/// `refl`), and `cond test 1 0 < 2` is a two-leaf `Bool` split — so
/// `div_mod_unique` against the executable projections (`div_mod_exec`)
/// gives both decoded components in one shot.
struct BitDivMod {
    div_bit: ExprId,
    mod_bit: ExprId,
    cond_test: ExprId,
    /// `And (Eq div_bit n) (Eq mod_bit cond_test)`.
    combined: ExprId,
}

fn bit_div_mod_witness(d: &mut NatDev<'_>, p: &NatPrelude, test: ExprId, n: ExprId) -> BitDivMod {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let divisor = d.succ(one);
    let bit_tn = d.const_app(p.bit, &[test, n]);
    let cond_test = d.bool_select_nat(test, one, zero);

    // Executable witness: divMod divisor bit_tn (div bit_tn divisor) (mod bit_tn divisor).
    let h1 = d.lemma(p.div_mod_exec, &[one, bit_tn]);

    // Hand-built witness: divMod divisor bit_tn n cond_test.
    let recon = {
        let prod = d.mul(divisor, n);
        d.add(prod, cond_test)
    };
    let eq_ty = d.eq(bit_tn, recon);
    let eq_proof = d.refl(bit_tn);
    let bound_ty = d.lt(cond_test, divisor);
    let bound_proof = case_bool(
        d,
        &p,
        test,
        &|d, x| {
            let one = d.num(1);
            let zero = d.zero();
            let divisor = d.succ(one);
            let c = d.bool_select_nat(x, one, zero);
            d.lt(c, divisor)
        },
        &|d| {
            let one = d.num(1);
            d.lemma(p.lt_succ_self, &[one])
        },
        &|d| {
            let one = d.num(1);
            d.zero_lt_succ(one)
        },
    );
    let h2 = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, eq_proof, bound_proof]);

    let div_bit = d.div(bit_tn, divisor);
    let mod_bit = d.modulo(bit_tn, divisor);
    let combined = d.lemma(
        p.div_mod_unique,
        &[divisor, bit_tn, div_bit, mod_bit, n, cond_test, h1, h2],
    );

    BitDivMod {
        div_bit,
        mod_bit,
        cond_test,
        combined,
    }
}

/// `Nat.bit_div_two : ∀ test n, Eq (div (bit test n) 2) n`.
fn declare_bit_div_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let test_fv = d.fresh_fvar();
    let test = d.kernel().fvar(test_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let w = bit_div_mod_witness(d, &p, test, n);
    let eq_ty = d.eq(w.div_bit, n);
    let mod_eq_ty = d.eq(w.mod_bit, w.cond_test);
    let proof = and_left(d, eq_ty, mod_eq_ty, w.combined);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, eq_ty);
        d.pi_fv(test_fv, bool_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(test_fv, bool_ty, inner)
    };
    d.declare_theorem(p.bit_div_two, ty, value)
}

/// `Nat.bit_mod_two : ∀ test n, Eq (mod (bit test n) 2) (bool_select_nat
/// test 1 0)`.
fn declare_bit_mod_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let test_fv = d.fresh_fvar();
    let test = d.kernel().fvar(test_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let w = bit_div_mod_witness(d, &p, test, n);
    let eq_ty = d.eq(w.div_bit, n);
    let mod_eq_ty = d.eq(w.mod_bit, w.cond_test);
    let proof = and_right(d, eq_ty, mod_eq_ty, w.combined);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, mod_eq_ty);
        d.pi_fv(test_fv, bool_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(test_fv, bool_ty, inner)
    };
    d.declare_theorem(p.bit_mod_two, ty, value)
}

/// `Eq (mul (cond a 1 0) (cond b 1 0)) (cond (and a b) 1 0)` — `land`'s
/// per-bit `mul` combine agrees with `cond` of the boolean AND. A two-leaf
/// split on `a` ALONE: `and a b` reduces via ι to `b` (at `a = true`) or
/// the literal `false` (at `a = false`) regardless of `b`'s shape, since
/// `Bool.rec`'s branch VALUE may be symbolic even though its scrutinee must
/// be literal. `Nat.mul` recurses on its SECOND argument, so `mul (cond a 1
/// 0) (cond b 1 0)` does not collapse by pure defeq even once `a` is
/// literal (`cond b 1 0` stays stuck at symbolic `b`) — closed instead by
/// `one_mul`/`zero_mul`.
fn and_cond_mul_eq_cond(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let cond_b = d.bool_select_nat(b, one, zero);
    case_bool(
        d,
        &p,
        a,
        &|d, x| {
            let one = d.num(1);
            let zero = d.zero();
            let cond_x = d.bool_select_nat(x, one, zero);
            let cond_b = d.bool_select_nat(b, one, zero);
            let lhs = d.mul(cond_x, cond_b);
            let and_fn_expr = and_fn(d);
            let xb = d.apply(and_fn_expr, &[x, b]);
            let rhs = d.bool_select_nat(xb, one, zero);
            d.eq(lhs, rhs)
        },
        &|d| d.lemma(p.one_mul, &[cond_b]),
        &|d| d.lemma(p.zero_mul, &[cond_b]),
    )
}

/// `Eq (guarded (bit a m) (bit b n) 0 0 (land m n) (mul (cond a 1 0) (cond b
/// 1 0))) (bit (and a b) (land m n))` — the guard-resolution half of the
/// bridge, once the fuel machinery has already rewritten the recursive
/// occurrence down to the canonical `land m n`. See the module doc.
fn land_guard_goal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let land_mn = d.const_app(p.land, &[m, n]);
    let bitval = d.mul(cond_a, cond_b);
    let lhs = guarded(d, bit_am, bit_bn, zero, zero, land_mn, bitval);
    let and_fn_expr = and_fn(d);
    let a_and_b = d.apply(and_fn_expr, &[a, b]);
    let rhs = d.const_app(p.bit, &[a_and_b, land_mn]);
    d.eq(lhs, rhs)
}

/// The "both guards false" leaf: proves [`land_guard_goal`] given that,
/// BY CONSTRUCTION at the call site, `bit a m`/`bit b n` are both positive
/// (so `guarded` reduces to `stepped` by pure defeq — the kernel checks
/// this automatically when the returned proof's type is compared against
/// the caller's unreduced statement).
fn land_guard_step_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let land_mn = d.const_app(p.land, &[m, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let bitval = d.mul(cond_a, cond_b);
    let combine_eq = and_cond_mul_eq_cond(d, &p, a, b);
    let and_fn_expr = and_fn(d);
    let a_and_b = d.apply(and_fn_expr, &[a, b]);
    let cond_ab = d.bool_select_nat(a_and_b, one, zero);
    d.congr(bitval, cond_ab, combine_eq, &|d, x| {
        let two = d.num(2);
        let doubled = d.mul(two, land_mn);
        d.add(doubled, x)
    })
}

/// The `m = 0, a = false` leaf: `guarded` selects the constant `0` (land's
/// absorbing-zero row), and the target reduces to `0` too (`and false b =
/// false` by ι, `land 0 n = 0` by defeq, `bit false 0 = 0` by defeq) — a
/// single `refl` closes it.
fn land_guard_on_m_zero_leaf(d: &mut NatDev<'_>) -> ExprId {
    let zero = d.zero();
    d.refl(zero)
}

/// Resolve the `m`-guard (`beq (bit a m) 0`), given that the `n`-guard is
/// already known false by construction at the call site.
///
/// **The split is on `a`, not `m`.** `bit a m := add (mul 2 m) (cond a 1
/// 0)`, and `Nat.add` recurses on its SECOND argument — here `cond a 1 0`,
/// which is stuck for symbolic `a` regardless of `m`'s shape. So `bit true m`
/// is `succ`-shaped (hence positive) for ANY `m`, even fully symbolic,
/// because `add x (succ zero)` reduces via the succ-row REGARDLESS of `x`'s
/// shape — the mirror image of the `n`-shape reasoning an earlier (wrong)
/// version of this tree used. Only `a = false` needs `m`'s shape exposed
/// (`bit false m = mul 2 m`, which recurses on `m` and is stuck at symbolic
/// `m`).
fn land_guard_inner(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| land_guard_goal(d, &p, cand_a, m, b, n),
        &|d| {
            let t = d.bool_true();
            land_guard_step_leaf(d, &p, t, m, b, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                m,
                &|d, cand_m| {
                    let false_ = d.bool_false();
                    land_guard_goal(d, &p, false_, cand_m, b, n)
                },
                &|d| land_guard_on_m_zero_leaf(d),
                &|d, m_pred| {
                    let succ_m = d.succ(m_pred);
                    let false_ = d.bool_false();
                    land_guard_step_leaf(d, &p, false_, succ_m, b, n)
                },
            )
        },
    )
}

/// The `n = 0, b = false` leaf: `guarded` selects `on_n_zero = 0`
/// regardless of `a`/`m`, and the target reduces to `0` too (`and a false =
/// false` needs `a` split — `and_fn`'s branches are `false`/`false` at
/// `y = false`, but the SCRUTINEE `a` is symbolic, so ι does not fire
/// without exposing `a`'s shape; `land m 0 = 0` needs the theorem
/// `land_zero_right`, not defeq, since `m`'s shape is unknown).
fn land_guard_on_n_zero_leaf(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| {
            let zero = d.zero();
            let false_ = d.bool_false();
            land_guard_goal(d, &p, cand_a, m, false_, zero)
        },
        &|d| {
            let t = d.bool_true();
            land_guard_on_n_zero_branch(d, &p, m, t)
        },
        &|d| {
            let f = d.bool_false();
            land_guard_on_n_zero_branch(d, &p, m, f)
        },
    )
}

/// One `a`-leaf of [`land_guard_on_n_zero_leaf`]: rewrite `land m 0` to `0`
/// via `land_zero_right`, then close by defeq (`bit (and a_lit false) 0`
/// reduces to `0` once `a_lit` is literal, since `and _ false`'s outer
/// scrutinee is now concrete).
fn land_guard_on_n_zero_branch(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    a_lit: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let false_ = d.bool_false();
    let land_m0 = d.const_app(p.land, &[m, zero]);
    let land_zero_right_m = d.lemma(p.land_zero_right, &[m]);
    let and_fn_expr = and_fn(d);
    let a_and_false = d.apply(and_fn_expr, &[a_lit, false_]);
    let target_before = d.const_app(p.bit, &[a_and_false, land_m0]);
    let target_after = d.const_app(p.bit, &[a_and_false, zero]);
    let congr_step = d.congr(land_m0, zero, land_zero_right_m, &|d, x| {
        d.const_app(p.bit, &[a_and_false, x])
    });
    let refl_after = d.refl(target_after);
    let (_final, chain_proof) = d.chain(
        target_before,
        &[(target_after, congr_step), (zero, refl_after)],
    );
    d.symm(target_before, zero, chain_proof)
}

/// The full guard-resolution case tree: split `b` (the `n`-guard checks
/// `beq (bit b n) 0`, which is `succ`-shaped-hence-false for ANY `n` once
/// `b = true` — see [`land_guard_inner`]'s doc for why the split is on the
/// `Bool`, not the `Nat`), then (when `b = false`) split `n`, then resolve
/// the `m`-guard the same way via [`land_guard_inner`].
fn resolve_land_guard(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        b,
        &|d, cand_b| land_guard_goal(d, &p, a, m, cand_b, n),
        &|d| {
            let t = d.bool_true();
            land_guard_inner(d, &p, a, m, t, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                n,
                &|d, cand_n| {
                    let false_ = d.bool_false();
                    land_guard_goal(d, &p, a, m, false_, cand_n)
                },
                &|d| land_guard_on_n_zero_leaf(d, &p, a, m),
                &|d, n_pred| {
                    let succ_n = d.succ(n_pred);
                    let false_ = d.bool_false();
                    land_guard_inner(d, &p, a, m, false_, succ_n)
                },
            )
        },
    )
}

/// `Nat.land_bit : ∀ a m b n, Eq (land (bit a m) (bit b n)) (bit (and a b)
/// (land m n))` — `F:ml430-nat-land-bit-b9ab7475`. See the module doc for
/// the full construction.
fn declare_land_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let two = d.num(2);
    let zero = d.zero();

    let base = d.mul(two, m);
    let k1 = d.succ(base);
    let fuel = d.succ(k1);

    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);

    // --- Le (bit a m) k1, via case split on a -------------------------------
    let m_le_k1 = case_bool(
        d,
        &p,
        a,
        &|d, x| {
            let bam = d.const_app(p.bit, &[x, m]);
            d.le(bam, k1)
        },
        &|d| d.lemma(p.le_refl, &[k1]),
        &|d| d.lemma(p.le_succ, &[base]),
    );
    let k1_le_fuel = d.lemma(p.le_succ, &[k1]);
    let m_le_fuel = d.lemma(p.le_trans, &[bit_am, k1, fuel, m_le_k1, k1_le_fuel]);

    // --- Le m k1 -------------------------------------------------------------
    let mm = d.add(m, m);
    let m_le_mm = d.lemma(p.le_add_right, &[m, m]);
    let two_mul_eq = two_mul_eq_add_self(d, &p, m); // Eq base mm
    let mm_eq_base = d.symm(base, mm, two_mul_eq);
    let motive_le = d.eq_motive(mm, &|d, x| d.le(m, x));
    let m_le_base = d.transport(mm, motive_le, m_le_mm, base, mm_eq_base);
    let base_le_k1 = d.lemma(p.le_succ, &[base]);
    let m_le_k1_bound = d.lemma(p.le_trans, &[m, base, k1, m_le_base, base_le_k1]);

    // --- land(bit a m)(bit b n) = landAux fuel (bit a m)(bit b n) -----------
    let fuel_eq = d.lemma(p.land_aux_eq_land_of_le, &[fuel, bit_am, bit_bn, m_le_fuel]);
    let landaux_fuel = d.const_app(p.land_aux, &[fuel, bit_am, bit_bn]);
    let land_ab = d.const_app(p.land, &[bit_am, bit_bn]);
    let step0 = d.symm(landaux_fuel, land_ab, fuel_eq);

    // --- refl-unfold to guarded(...) at the raw div/mod subterms ------------
    let half_am = d.div(bit_am, two);
    let half_bn = d.div(bit_bn, two);
    let mod_am = d.modulo(bit_am, two);
    let mod_bn = d.modulo(bit_bn, two);
    let rec0 = d.const_app(p.land_aux, &[k1, half_am, half_bn]);
    let bitval0 = d.mul(mod_am, mod_bn);
    let guarded0 = guarded(d, bit_am, bit_bn, zero, zero, rec0, bitval0);
    let step1 = d.refl(landaux_fuel);

    // --- rewrite half_am -> m, half_bn -> n, then land_aux k1 m n -> land m n
    let div_a = d.lemma(p.bit_div_two, &[a, m]);
    let div_b = d.lemma(p.bit_div_two, &[b, n]);
    let land_mn = d.const_app(p.land, &[m, n]);

    let rec1 = d.const_app(p.land_aux, &[k1, m, half_bn]);
    let rec0_to_rec1 = d.congr(half_am, m, div_a, &|d, x| {
        d.const_app(p.land_aux, &[k1, x, half_bn])
    });
    let rec2 = d.const_app(p.land_aux, &[k1, m, n]);
    let rec1_to_rec2 = d.congr(half_bn, n, div_b, &|d, x| {
        d.const_app(p.land_aux, &[k1, m, x])
    });
    let rec2_eq_land_mn = d.lemma(p.land_aux_eq_land_of_le, &[k1, m, n, m_le_k1_bound]);
    let (_rec_final, rec_chain) = d.chain(
        rec0,
        &[
            (rec1, rec0_to_rec1),
            (rec2, rec1_to_rec2),
            (land_mn, rec2_eq_land_mn),
        ],
    );

    // --- rewrite mod_am -> cond a, mod_bn -> cond b -------------------------
    let mod_a = d.lemma(p.bit_mod_two, &[a, m]);
    let mod_b = d.lemma(p.bit_mod_two, &[b, n]);
    let one = d.num(1);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let bitval1 = d.mul(cond_a, mod_bn);
    let bitval0_to_1 = d.congr(mod_am, cond_a, mod_a, &|d, x| d.mul(x, mod_bn));
    let bitval2 = d.mul(cond_a, cond_b);
    let bitval1_to_2 = d.congr(mod_bn, cond_b, mod_b, &|d, x| d.mul(cond_a, x));
    let (_bitval_final, bitval_chain) =
        d.chain(bitval0, &[(bitval1, bitval0_to_1), (bitval2, bitval1_to_2)]);

    let guarded_mid = guarded(d, bit_am, bit_bn, zero, zero, land_mn, bitval0);
    let guarded_final = guarded(d, bit_am, bit_bn, zero, zero, land_mn, bitval2);
    let step_rec = d.congr(rec0, land_mn, rec_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, zero, zero, hole, bitval0)
    });
    let step_bit = d.congr(bitval0, bitval2, bitval_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, zero, zero, land_mn, hole)
    });

    // --- resolve the two guards ----------------------------------------------
    let step_guard = resolve_land_guard(d, &p, a, m, b, n);

    let and_fn_expr = and_fn(d);
    let a_and_b = d.apply(and_fn_expr, &[a, b]);
    let target = d.const_app(p.bit, &[a_and_b, land_mn]);

    let (_final, proof) = d.chain(
        land_ab,
        &[
            (landaux_fuel, step0),
            (guarded0, step1),
            (guarded_mid, step_rec),
            (guarded_final, step_bit),
            (target, step_guard),
        ],
    );

    let stmt = d.eq(land_ab, target);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let inner = d.pi_fv(b_fv, bool_ty, inner);
        let inner = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(a_fv, bool_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let inner = d.lam_fv(b_fv, bool_ty, inner);
        let inner = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(a_fv, bool_ty, inner)
    };
    d.declare_theorem(p.land_bit, ty, value)
}

// ============================================================================
// `Nat.lor_bit` / `Nat.ldiff_bit`: the same fuel-swap bridge, each with its
// own guard-tree leaves and its own per-bit combine agreement. See the
// module doc's final section for what transports unchanged (the fuel-swap
// machinery: `base`/`k1`/`fuel`, both `Le` bounds, the `div`/`mod` decode)
// and what does not (the degenerate-guard values, and the combine lemma).
// ============================================================================

/// Local reproduction of `bitwise.rs`'s private `bool_select_bool` —
/// `Bool.rec` at a `Bool`-valued motive (`if condition then on_true else
/// on_false`, both minor premises themselves `Bool`s). Reproduced rather
/// than exported (avoiding a cross-lane edit to `bitwise.rs`), same
/// rationale as [`guarded`]'s local copy. Generic over `D: NatOps` (not the
/// concrete [`NatDev`]) so [`ldiff_fn`] can build the same term against the
/// test suite's own `Fixture`, matching `and_fn`/`or_fn`'s own genericity.
fn bool_select_bool_local<D: NatOps>(
    d: &mut D,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `fun a b => bool_select_bool a (bool_select_bool b false true) false` —
/// `Nat.ldiff`'s per-bit boolean combinator, `a && !b`. Mathlib v4.30
/// defines `Nat.ldiff` via `bitwise (fun a b => a && !b)`; reproduced here
/// (not imported — `bitwise.rs`/`ldiff.rs` are both off-limits for this
/// lane) purely to state `Nat.ldiff_bit`'s target. Generic over `D: NatOps`
/// for the same reason as [`bool_select_bool_local`].
pub(super) fn ldiff_fn<D: NatOps>(d: &mut D, p: &NatPrelude) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let not_b = bool_select_bool_local(d, &p, b, false_, true_);
    let body = bool_select_bool_local(d, &p, a, not_b, false_);
    let with_b = d.lam_fv(b_fv, bool_ty, body);
    d.lam_fv(a_fv, bool_ty, with_b)
}

// --- `lor`'s per-bit combine: `max` via `ble`, agrees with `cond (a || b)` -

/// `Eq (bool_select_nat (ble (cond a 1 0) (cond b 1 0)) (cond b 1 0) (cond a
/// 1 0)) (cond (or a b) 1 0)` at LITERAL `a`, `b` — every subterm on both
/// sides is then fully closed and reduces to a matching numeral, so `refl`
/// closes it directly (no case split needed at this point; the caller
/// supplies the literals).
fn or_cond_max_leaf(d: &mut NatDev<'_>, a_lit: ExprId, b_lit: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let cond_a = d.bool_select_nat(a_lit, one, zero);
    let cond_b = d.bool_select_nat(b_lit, one, zero);
    let a_le_b = d.ble(cond_a, cond_b);
    let lhs = d.bool_select_nat(a_le_b, cond_b, cond_a);
    d.refl(lhs)
}

/// The goal statement of [`or_cond_max_leaf`]/[`or_cond_max_eq_cond`], at
/// arbitrary (possibly symbolic) `a`, `b`.
fn or_cond_max_goal(d: &mut NatDev<'_>, _p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let a_le_b = d.ble(cond_a, cond_b);
    let lhs = d.bool_select_nat(a_le_b, cond_b, cond_a);
    let or_fn_expr = or_fn(d);
    let ab = d.apply(or_fn_expr, &[a, b]);
    let rhs = d.bool_select_nat(ab, one, zero);
    d.eq(lhs, rhs)
}

/// `Eq (bool_select_nat (ble (cond a 1 0) (cond b 1 0)) (cond b 1 0) (cond a
/// 1 0)) (cond (or a b) 1 0)` for ARBITRARY `a`, `b` — `lor`'s per-bit `max`
/// combine agrees with `cond` of the boolean OR. Unlike
/// [`and_cond_mul_eq_cond`]'s single split on `a` alone, `ble`'s recursion
/// needs BOTH operands' VALUE, not just `a`'s shape, in the `a = true`
/// branch (`ble 1 (cond b 1 0)` does not resolve until `cond b 1 0` is a
/// literal `0`/`1`) — so a further split on `b` is needed there. The `a =
/// false` branch needs no further split at all: `ble 0 y` reduces to the
/// literal `true` regardless of `y`'s shape (`Nat.ble`'s own zero-row), so
/// `bool_select_nat true cond_b cond_a` reduces straight to `cond_b`, which
/// is exactly `cond (or false b)` too (`or_fn(false, b)` ι-reduces to `b`
/// itself, literal scrutinee, regardless of `b`'s shape).
fn or_cond_max_eq_cond(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| or_cond_max_goal(d, &p, cand_a, b),
        &|d| {
            let t = d.bool_true();
            case_bool(
                d,
                &p,
                b,
                &|d, cand_b| or_cond_max_goal(d, &p, t, cand_b),
                &|d| {
                    let bt = d.bool_true();
                    or_cond_max_leaf(d, t, bt)
                },
                &|d| {
                    let bf = d.bool_false();
                    or_cond_max_leaf(d, t, bf)
                },
            )
        },
        &|d| {
            let one = d.num(1);
            let zero = d.zero();
            let cond_b = d.bool_select_nat(b, one, zero);
            d.refl(cond_b)
        },
    )
}

/// `Eq(guarded (bit a m) (bit b n) (bit a m) (bit b n) (lor m n) (max (cond a
/// 1 0) (cond b 1 0))) (bit (or a b) (lor m n))` — the guard-resolution half
/// of `lor`'s bridge. `lor`'s fuel-exhaustion rows PASS THROUGH the full
/// operand (`on_n_zero = bit a m`, `on_m_zero = bit b n`), not `land`'s
/// constant `0` — see the module doc and `lor.rs`'s own doc for why.
fn lor_guard_goal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let lor_mn = d.const_app(p.lor, &[m, n]);
    let a_le_b = d.ble(cond_a, cond_b);
    let bitval = d.bool_select_nat(a_le_b, cond_b, cond_a);
    let lhs = guarded(d, bit_am, bit_bn, bit_am, bit_bn, lor_mn, bitval);
    let or_fn_expr = or_fn(d);
    let a_or_b = d.apply(or_fn_expr, &[a, b]);
    let rhs = d.const_app(p.bit, &[a_or_b, lor_mn]);
    d.eq(lhs, rhs)
}

/// The "both operands positive" leaf: both zero-guards are false by
/// construction at the call site, so `guarded` reduces to `stepped` by pure
/// defeq — closed via [`or_cond_max_eq_cond`]'s combine agreement.
fn lor_guard_step_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let lor_mn = d.const_app(p.lor, &[m, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let a_le_b = d.ble(cond_a, cond_b);
    let bitval = d.bool_select_nat(a_le_b, cond_b, cond_a);
    let combine_eq = or_cond_max_eq_cond(d, &p, a, b);
    let or_fn_expr = or_fn(d);
    let a_or_b = d.apply(or_fn_expr, &[a, b]);
    let cond_ab = d.bool_select_nat(a_or_b, one, zero);
    d.congr(bitval, cond_ab, combine_eq, &|d, x| {
        let two = d.num(2);
        let doubled = d.mul(two, lor_mn);
        d.add(doubled, x)
    })
}

/// The `m = 0` leaf (with the `n`-guard already known false by construction):
/// `guarded` selects `on_m_zero = bit b n` (`lor`'s pass-through, not `0`),
/// and the target reduces to the SAME expression — `or_fn(false, b)`
/// ι-reduces straight to `b` (literal scrutinee, regardless of `b`'s shape)
/// and `lor(0, n)` is defeq `n` unconditionally (`lor_zero_left` is `refl`
/// for exactly this reason — see `lor.rs`'s module doc). So both sides are
/// syntactically `bit b n` once fully reduced: `d.refl` on the raw `bit_bn`
/// expression closes it, no further split needed (unlike `land`'s analogous
/// leaf, which needed none either, and unlike the `n = 0` leaf below, which
/// does).
fn lor_guard_on_m_zero_leaf(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let bit_bn = d.const_app(p.bit, &[b, n]);
    d.refl(bit_bn)
}

/// One `a`-leaf of [`lor_guard_on_n_zero_leaf`]: rewrite `lor m 0` to `m` via
/// `lor_zero_right`, then close by defeq (`or_fn(a_lit, false)` ι-reduces to
/// `a_lit` once `a_lit` is literal).
fn lor_guard_on_n_zero_branch(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    a_lit: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let false_ = d.bool_false();
    let lor_m0 = d.const_app(p.lor, &[m, zero]);
    let lor_zero_right_m = d.lemma(p.lor_zero_right, &[m]);
    let or_fn_expr = or_fn(d);
    let a_or_false = d.apply(or_fn_expr, &[a_lit, false_]);
    let target_before = d.const_app(p.bit, &[a_or_false, lor_m0]);
    let target_after = d.const_app(p.bit, &[a_or_false, m]);
    let congr_step = d.congr(lor_m0, m, lor_zero_right_m, &|d, x| {
        d.const_app(p.bit, &[a_or_false, x])
    });
    let bit_am_lit = d.const_app(p.bit, &[a_lit, m]);
    let refl_after = d.refl(target_after);
    let (_final, chain_proof) = d.chain(
        target_before,
        &[(target_after, congr_step), (bit_am_lit, refl_after)],
    );
    d.symm(target_before, bit_am_lit, chain_proof)
}

/// The `n = 0` leaf (with `b = false` already known from the outer split):
/// `guarded` selects `on_n_zero = bit a m` regardless of `a`/`m`, but the
/// target's `or_fn(a, false)` needs `a` LITERAL to ι-reduce — a further
/// split, unlike `land`'s analogous leaf (whose `and_fn(a, false)` collapses
/// to a constant regardless of `a`'s shape).
fn lor_guard_on_n_zero_leaf(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| {
            let zero = d.zero();
            let false_ = d.bool_false();
            lor_guard_goal(d, &p, cand_a, m, false_, zero)
        },
        &|d| {
            let t = d.bool_true();
            lor_guard_on_n_zero_branch(d, &p, m, t)
        },
        &|d| {
            let f = d.bool_false();
            lor_guard_on_n_zero_branch(d, &p, m, f)
        },
    )
}

/// Resolve the `m`-guard, given the `n`-guard already known false by
/// construction — same `a`-then-`m` split shape as [`land_guard_inner`],
/// swapping in `lor`'s pass-through `on_m_zero` leaf and combine.
fn lor_guard_inner(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| lor_guard_goal(d, &p, cand_a, m, b, n),
        &|d| {
            let t = d.bool_true();
            lor_guard_step_leaf(d, &p, t, m, b, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                m,
                &|d, cand_m| {
                    let false_ = d.bool_false();
                    lor_guard_goal(d, &p, false_, cand_m, b, n)
                },
                &|d| lor_guard_on_m_zero_leaf(d, &p, b, n),
                &|d, m_pred| {
                    let succ_m = d.succ(m_pred);
                    let false_ = d.bool_false();
                    lor_guard_step_leaf(d, &p, false_, succ_m, b, n)
                },
            )
        },
    )
}

/// The full guard-resolution case tree for `lor_bit`: split `b` (the
/// `n`-guard), then (when `b = false`) split `n`, then resolve the `m`-guard
/// via [`lor_guard_inner`].
fn resolve_lor_guard(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        b,
        &|d, cand_b| lor_guard_goal(d, &p, a, m, cand_b, n),
        &|d| {
            let t = d.bool_true();
            lor_guard_inner(d, &p, a, m, t, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                n,
                &|d, cand_n| {
                    let false_ = d.bool_false();
                    lor_guard_goal(d, &p, a, m, false_, cand_n)
                },
                &|d| lor_guard_on_n_zero_leaf(d, &p, a, m),
                &|d, n_pred| {
                    let succ_n = d.succ(n_pred);
                    let false_ = d.bool_false();
                    lor_guard_inner(d, &p, a, m, false_, succ_n)
                },
            )
        },
    )
}

/// `Nat.lor_bit : ∀ a m b n, Eq (lor (bit a m) (bit b n)) (bit (or a b) (lor
/// m n))` — `F:ml430-nat-lor-bit-a2f98c7c`. Same fuel-swap shape as
/// [`declare_land_bit`]; see that function and the module doc for the
/// shared machinery, and this section's leaves for what is new.
fn declare_lor_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let two = d.num(2);
    let zero = d.zero();

    let base = d.mul(two, m);
    let k1 = d.succ(base);
    let fuel = d.succ(k1);

    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);

    // --- Le (bit a m) k1, via case split on a -------------------------------
    let m_le_k1 = case_bool(
        d,
        &p,
        a,
        &|d, x| {
            let bam = d.const_app(p.bit, &[x, m]);
            d.le(bam, k1)
        },
        &|d| d.lemma(p.le_refl, &[k1]),
        &|d| d.lemma(p.le_succ, &[base]),
    );
    let k1_le_fuel = d.lemma(p.le_succ, &[k1]);
    let m_le_fuel = d.lemma(p.le_trans, &[bit_am, k1, fuel, m_le_k1, k1_le_fuel]);

    // --- Le m k1 -------------------------------------------------------------
    let mm = d.add(m, m);
    let m_le_mm = d.lemma(p.le_add_right, &[m, m]);
    let two_mul_eq = two_mul_eq_add_self(d, &p, m); // Eq base mm
    let mm_eq_base = d.symm(base, mm, two_mul_eq);
    let motive_le = d.eq_motive(mm, &|d, x| d.le(m, x));
    let m_le_base = d.transport(mm, motive_le, m_le_mm, base, mm_eq_base);
    let base_le_k1 = d.lemma(p.le_succ, &[base]);
    let m_le_k1_bound = d.lemma(p.le_trans, &[m, base, k1, m_le_base, base_le_k1]);

    // --- lor(bit a m)(bit b n) = lorAux fuel (bit a m)(bit b n) -------------
    let fuel_eq = d.lemma(p.lor_aux_eq_lor_of_le, &[fuel, bit_am, bit_bn, m_le_fuel]);
    let loraux_fuel = d.const_app(p.lor_aux, &[fuel, bit_am, bit_bn]);
    let lor_ab = d.const_app(p.lor, &[bit_am, bit_bn]);
    let step0 = d.symm(loraux_fuel, lor_ab, fuel_eq);

    // --- refl-unfold to guarded(...) at the raw div/mod subterms ------------
    let half_am = d.div(bit_am, two);
    let half_bn = d.div(bit_bn, two);
    let mod_am = d.modulo(bit_am, two);
    let mod_bn = d.modulo(bit_bn, two);
    let rec0 = d.const_app(p.lor_aux, &[k1, half_am, half_bn]);
    let mod_le0 = d.ble(mod_am, mod_bn);
    let bitval0 = d.bool_select_nat(mod_le0, mod_bn, mod_am);
    let guarded0 = guarded(d, bit_am, bit_bn, bit_am, bit_bn, rec0, bitval0);
    let step1 = d.refl(loraux_fuel);

    // --- rewrite half_am -> m, half_bn -> n, then lor_aux k1 m n -> lor m n
    let div_a = d.lemma(p.bit_div_two, &[a, m]);
    let div_b = d.lemma(p.bit_div_two, &[b, n]);
    let lor_mn = d.const_app(p.lor, &[m, n]);

    let rec1 = d.const_app(p.lor_aux, &[k1, m, half_bn]);
    let rec0_to_rec1 = d.congr(half_am, m, div_a, &|d, x| {
        d.const_app(p.lor_aux, &[k1, x, half_bn])
    });
    let rec2 = d.const_app(p.lor_aux, &[k1, m, n]);
    let rec1_to_rec2 = d.congr(half_bn, n, div_b, &|d, x| {
        d.const_app(p.lor_aux, &[k1, m, x])
    });
    let rec2_eq_lor_mn = d.lemma(p.lor_aux_eq_lor_of_le, &[k1, m, n, m_le_k1_bound]);
    let (_rec_final, rec_chain) = d.chain(
        rec0,
        &[
            (rec1, rec0_to_rec1),
            (rec2, rec1_to_rec2),
            (lor_mn, rec2_eq_lor_mn),
        ],
    );

    // --- rewrite mod_am -> cond a, mod_bn -> cond b (BOTH occurrences of
    // each, since they appear in `ble`'s condition AND as a branch value) --
    let mod_a = d.lemma(p.bit_mod_two, &[a, m]);
    let mod_b = d.lemma(p.bit_mod_two, &[b, n]);
    let one = d.num(1);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);

    let bitval1 = {
        let c = d.ble(cond_a, mod_bn);
        d.bool_select_nat(c, mod_bn, cond_a)
    };
    let bitval0_to_1 = d.congr(mod_am, cond_a, mod_a, &|d, x| {
        let c = d.ble(x, mod_bn);
        d.bool_select_nat(c, mod_bn, x)
    });
    let bitval2 = {
        let c = d.ble(cond_a, cond_b);
        d.bool_select_nat(c, cond_b, cond_a)
    };
    let bitval1_to_2 = d.congr(mod_bn, cond_b, mod_b, &|d, x| {
        let c = d.ble(cond_a, x);
        d.bool_select_nat(c, x, cond_a)
    });
    let (_bitval_final, bitval_chain) =
        d.chain(bitval0, &[(bitval1, bitval0_to_1), (bitval2, bitval1_to_2)]);

    let guarded_mid = guarded(d, bit_am, bit_bn, bit_am, bit_bn, lor_mn, bitval0);
    let guarded_final = guarded(d, bit_am, bit_bn, bit_am, bit_bn, lor_mn, bitval2);
    let step_rec = d.congr(rec0, lor_mn, rec_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, bit_am, bit_bn, hole, bitval0)
    });
    let step_bitv = d.congr(bitval0, bitval2, bitval_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, bit_am, bit_bn, lor_mn, hole)
    });

    // --- resolve the two guards ----------------------------------------------
    let step_guard = resolve_lor_guard(d, &p, a, m, b, n);

    let or_fn_expr = or_fn(d);
    let a_or_b = d.apply(or_fn_expr, &[a, b]);
    let target = d.const_app(p.bit, &[a_or_b, lor_mn]);

    let (_final, proof) = d.chain(
        lor_ab,
        &[
            (loraux_fuel, step0),
            (guarded0, step1),
            (guarded_mid, step_rec),
            (guarded_final, step_bitv),
            (target, step_guard),
        ],
    );

    let stmt = d.eq(lor_ab, target);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let inner = d.pi_fv(b_fv, bool_ty, inner);
        let inner = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(a_fv, bool_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let inner = d.lam_fv(b_fv, bool_ty, inner);
        let inner = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(a_fv, bool_ty, inner)
    };
    d.declare_theorem(p.lor_bit, ty, value)
}

// --- `ldiff`'s per-bit combine: `if n%2=0 then m%2 else 0`, agrees with
// `cond (a && !b)` ----------------------------------------------------------

/// `Eq (bool_select_nat (beq (cond b 1 0) 0) (cond a 1 0) 0) (cond (ldiff_fn
/// a b) 1 0)` at LITERAL `a`, `b` — fully closed once both are literal,
/// `refl` closes it.
fn ldiff_cond_leaf(d: &mut NatDev<'_>, a_lit: ExprId, b_lit: ExprId) -> ExprId {
    let one = d.num(1);
    let zero = d.zero();
    let cond_a = d.bool_select_nat(a_lit, one, zero);
    let cond_b = d.bool_select_nat(b_lit, one, zero);
    let b_is_zero = d.beq(cond_b, zero);
    let lhs = d.bool_select_nat(b_is_zero, cond_a, zero);
    d.refl(lhs)
}

/// The goal statement of [`ldiff_cond_leaf`]/[`ldiff_cond_eq_cond`].
fn ldiff_cond_goal(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let b_is_zero = d.beq(cond_b, zero);
    let lhs = d.bool_select_nat(b_is_zero, cond_a, zero);
    let ldiff_fn_expr = ldiff_fn(d, &p);
    let a_ldiff_b = d.apply(ldiff_fn_expr, &[a, b]);
    let rhs = d.bool_select_nat(a_ldiff_b, one, zero);
    d.eq(lhs, rhs)
}

/// `Eq (bool_select_nat (beq (cond b 1 0) 0) (cond a 1 0) 0) (cond (ldiff_fn
/// a b) 1 0)` for ARBITRARY `a`, `b`. `beq (cond b 1 0) 0` needs `b` literal
/// to ι-reduce (mirroring `land`/`lor`'s zero-guards), and — unlike `land`'s
/// single-split shortcut — the `b = true` branch's result (`0`) does not
/// come for free either: `ldiff_fn(a, true) = bool_select_bool(a, not_true,
/// false)` still has `a` as a symbolic Bool.rec scrutinee, so `a` needs its
/// own split too (both leaves reduce to `false`, matching the LHS's `0`).
fn ldiff_cond_eq_cond(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| ldiff_cond_goal(d, &p, cand_a, b),
        &|d| {
            let t = d.bool_true();
            case_bool(
                d,
                &p,
                b,
                &|d, cand_b| ldiff_cond_goal(d, &p, t, cand_b),
                &|d| {
                    let bt = d.bool_true();
                    ldiff_cond_leaf(d, t, bt)
                },
                &|d| {
                    let bf = d.bool_false();
                    ldiff_cond_leaf(d, t, bf)
                },
            )
        },
        &|d| {
            let f = d.bool_false();
            case_bool(
                d,
                &p,
                b,
                &|d, cand_b| ldiff_cond_goal(d, &p, f, cand_b),
                &|d| {
                    let bt = d.bool_true();
                    ldiff_cond_leaf(d, f, bt)
                },
                &|d| {
                    let bf = d.bool_false();
                    ldiff_cond_leaf(d, f, bf)
                },
            )
        },
    )
}

/// `Eq(guarded (bit a m) (bit b n) (bit a m) 0 (ldiff m n) (bitval)) (bit
/// (ldiff_fn a b) (ldiff m n))` — `ldiff`'s guard rows are the HYBRID
/// `land.rs`/`ldiff.rs` document: `on_n_zero = bit a m` (a `lor`-flavoured
/// pass-through — `ldiff m 0 = m`), `on_m_zero = 0` (a `land`-flavoured
/// absorbing constant — `ldiff 0 n = 0`).
fn ldiff_guard_goal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let ldiff_mn = d.const_app(p.ldiff, &[m, n]);
    let b_is_zero = d.beq(cond_b, zero);
    let bitval = d.bool_select_nat(b_is_zero, cond_a, zero);
    let lhs = guarded(d, bit_am, bit_bn, bit_am, zero, ldiff_mn, bitval);
    let ldiff_fn_expr = ldiff_fn(d, &p);
    let a_ldiff_b = d.apply(ldiff_fn_expr, &[a, b]);
    let rhs = d.const_app(p.bit, &[a_ldiff_b, ldiff_mn]);
    d.eq(lhs, rhs)
}

/// The "both operands positive" leaf, closed via [`ldiff_cond_eq_cond`].
fn ldiff_guard_step_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let ldiff_mn = d.const_app(p.ldiff, &[m, n]);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);
    let b_is_zero = d.beq(cond_b, zero);
    let bitval = d.bool_select_nat(b_is_zero, cond_a, zero);
    let combine_eq = ldiff_cond_eq_cond(d, &p, a, b);
    let ldiff_fn_expr = ldiff_fn(d, &p);
    let a_ldiff_b = d.apply(ldiff_fn_expr, &[a, b]);
    let cond_ab = d.bool_select_nat(a_ldiff_b, one, zero);
    d.congr(bitval, cond_ab, combine_eq, &|d, x| {
        let two = d.num(2);
        let doubled = d.mul(two, ldiff_mn);
        d.add(doubled, x)
    })
}

/// One `a`-leaf of [`ldiff_guard_on_n_zero_leaf`]: rewrite `ldiff m 0` to `m`
/// via `ldiff_zero_right`, then close by defeq — same shape as
/// [`lor_guard_on_n_zero_branch`], swapping `or_fn`/`lor_zero_right` for
/// `ldiff_fn`/`ldiff_zero_right`.
fn ldiff_guard_on_n_zero_branch(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    a_lit: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let false_ = d.bool_false();
    let ldiff_m0 = d.const_app(p.ldiff, &[m, zero]);
    let ldiff_zero_right_m = d.lemma(p.ldiff_zero_right, &[m]);
    let ldiff_fn_expr = ldiff_fn(d, &p);
    let a_ldiff_false = d.apply(ldiff_fn_expr, &[a_lit, false_]);
    let target_before = d.const_app(p.bit, &[a_ldiff_false, ldiff_m0]);
    let target_after = d.const_app(p.bit, &[a_ldiff_false, m]);
    let congr_step = d.congr(ldiff_m0, m, ldiff_zero_right_m, &|d, x| {
        d.const_app(p.bit, &[a_ldiff_false, x])
    });
    let bit_am_lit = d.const_app(p.bit, &[a_lit, m]);
    let refl_after = d.refl(target_after);
    let (_final, chain_proof) = d.chain(
        target_before,
        &[(target_after, congr_step), (bit_am_lit, refl_after)],
    );
    d.symm(target_before, bit_am_lit, chain_proof)
}

/// The `n = 0` leaf — same `a`-split shape as [`lor_guard_on_n_zero_leaf`]
/// (`ldiff`'s `on_n_zero` row is `lor`-flavoured pass-through too).
fn ldiff_guard_on_n_zero_leaf(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| {
            let zero = d.zero();
            let false_ = d.bool_false();
            ldiff_guard_goal(d, &p, cand_a, m, false_, zero)
        },
        &|d| {
            let t = d.bool_true();
            ldiff_guard_on_n_zero_branch(d, &p, m, t)
        },
        &|d| {
            let f = d.bool_false();
            ldiff_guard_on_n_zero_branch(d, &p, m, f)
        },
    )
}

/// Resolve the `m`-guard, given the `n`-guard already known false — the
/// `m = 0` leaf reuses [`land_guard_on_m_zero_leaf`] VERBATIM (`ldiff`'s
/// `on_m_zero` row is `land`-flavoured: constant `0`, closing by `refl`
/// with no further split, exactly as for `land`).
fn ldiff_guard_inner(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        a,
        &|d, cand_a| ldiff_guard_goal(d, &p, cand_a, m, b, n),
        &|d| {
            let t = d.bool_true();
            ldiff_guard_step_leaf(d, &p, t, m, b, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                m,
                &|d, cand_m| {
                    let false_ = d.bool_false();
                    ldiff_guard_goal(d, &p, false_, cand_m, b, n)
                },
                &|d| land_guard_on_m_zero_leaf(d),
                &|d, m_pred| {
                    let succ_m = d.succ(m_pred);
                    let false_ = d.bool_false();
                    ldiff_guard_step_leaf(d, &p, false_, succ_m, b, n)
                },
            )
        },
    )
}

/// The full guard-resolution case tree for `ldiff_bit`.
fn resolve_ldiff_guard(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    m: ExprId,
    b: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    case_bool(
        d,
        &p,
        b,
        &|d, cand_b| ldiff_guard_goal(d, &p, a, m, cand_b, n),
        &|d| {
            let t = d.bool_true();
            ldiff_guard_inner(d, &p, a, m, t, n)
        },
        &|d| {
            cases_zero_succ(
                d,
                n,
                &|d, cand_n| {
                    let false_ = d.bool_false();
                    ldiff_guard_goal(d, &p, a, m, false_, cand_n)
                },
                &|d| ldiff_guard_on_n_zero_leaf(d, &p, a, m),
                &|d, n_pred| {
                    let succ_n = d.succ(n_pred);
                    let false_ = d.bool_false();
                    ldiff_guard_inner(d, &p, a, m, false_, succ_n)
                },
            )
        },
    )
}

/// `Nat.ldiff_bit : ∀ a m b n, Eq (ldiff (bit a m) (bit b n)) (bit (a && !b)
/// (ldiff m n))` — `F:ml430-nat-ldiff-bit-6be49bb8`. Same fuel-swap shape as
/// [`declare_land_bit`]/[`declare_lor_bit`]; the guard tree is the hybrid
/// this section's docs describe.
fn declare_ldiff_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let two = d.num(2);
    let zero = d.zero();

    let base = d.mul(two, m);
    let k1 = d.succ(base);
    let fuel = d.succ(k1);

    let bit_am = d.const_app(p.bit, &[a, m]);
    let bit_bn = d.const_app(p.bit, &[b, n]);

    // --- Le (bit a m) k1, via case split on a -------------------------------
    let m_le_k1 = case_bool(
        d,
        &p,
        a,
        &|d, x| {
            let bam = d.const_app(p.bit, &[x, m]);
            d.le(bam, k1)
        },
        &|d| d.lemma(p.le_refl, &[k1]),
        &|d| d.lemma(p.le_succ, &[base]),
    );
    let k1_le_fuel = d.lemma(p.le_succ, &[k1]);
    let m_le_fuel = d.lemma(p.le_trans, &[bit_am, k1, fuel, m_le_k1, k1_le_fuel]);

    // --- Le m k1 -------------------------------------------------------------
    let mm = d.add(m, m);
    let m_le_mm = d.lemma(p.le_add_right, &[m, m]);
    let two_mul_eq = two_mul_eq_add_self(d, &p, m); // Eq base mm
    let mm_eq_base = d.symm(base, mm, two_mul_eq);
    let motive_le = d.eq_motive(mm, &|d, x| d.le(m, x));
    let m_le_base = d.transport(mm, motive_le, m_le_mm, base, mm_eq_base);
    let base_le_k1 = d.lemma(p.le_succ, &[base]);
    let m_le_k1_bound = d.lemma(p.le_trans, &[m, base, k1, m_le_base, base_le_k1]);

    // --- ldiff(bit a m)(bit b n) = ldiffAux fuel (bit a m)(bit b n) ---------
    let fuel_eq = d.lemma(
        p.ldiff_aux_eq_ldiff_of_le,
        &[fuel, bit_am, bit_bn, m_le_fuel],
    );
    let ldiffaux_fuel = d.const_app(p.ldiff_aux, &[fuel, bit_am, bit_bn]);
    let ldiff_ab = d.const_app(p.ldiff, &[bit_am, bit_bn]);
    let step0 = d.symm(ldiffaux_fuel, ldiff_ab, fuel_eq);

    // --- refl-unfold to guarded(...) at the raw div/mod subterms ------------
    let half_am = d.div(bit_am, two);
    let half_bn = d.div(bit_bn, two);
    let mod_am = d.modulo(bit_am, two);
    let mod_bn = d.modulo(bit_bn, two);
    let rec0 = d.const_app(p.ldiff_aux, &[k1, half_am, half_bn]);
    let mod_bn_is_zero0 = d.beq(mod_bn, zero);
    let bitval0 = d.bool_select_nat(mod_bn_is_zero0, mod_am, zero);
    let guarded0 = guarded(d, bit_am, bit_bn, bit_am, zero, rec0, bitval0);
    let step1 = d.refl(ldiffaux_fuel);

    // --- rewrite half_am -> m, half_bn -> n, then ldiff_aux k1 m n -> ldiff m n
    let div_a = d.lemma(p.bit_div_two, &[a, m]);
    let div_b = d.lemma(p.bit_div_two, &[b, n]);
    let ldiff_mn = d.const_app(p.ldiff, &[m, n]);

    let rec1 = d.const_app(p.ldiff_aux, &[k1, m, half_bn]);
    let rec0_to_rec1 = d.congr(half_am, m, div_a, &|d, x| {
        d.const_app(p.ldiff_aux, &[k1, x, half_bn])
    });
    let rec2 = d.const_app(p.ldiff_aux, &[k1, m, n]);
    let rec1_to_rec2 = d.congr(half_bn, n, div_b, &|d, x| {
        d.const_app(p.ldiff_aux, &[k1, m, x])
    });
    let rec2_eq_ldiff_mn = d.lemma(p.ldiff_aux_eq_ldiff_of_le, &[k1, m, n, m_le_k1_bound]);
    let (_rec_final, rec_chain) = d.chain(
        rec0,
        &[
            (rec1, rec0_to_rec1),
            (rec2, rec1_to_rec2),
            (ldiff_mn, rec2_eq_ldiff_mn),
        ],
    );

    // --- rewrite mod_am -> cond a, mod_bn -> cond b -------------------------
    let mod_a = d.lemma(p.bit_mod_two, &[a, m]);
    let mod_b = d.lemma(p.bit_mod_two, &[b, n]);
    let one = d.num(1);
    let cond_a = d.bool_select_nat(a, one, zero);
    let cond_b = d.bool_select_nat(b, one, zero);

    let bitval1 = {
        let c = d.beq(mod_bn, zero);
        d.bool_select_nat(c, cond_a, zero)
    };
    let bitval0_to_1 = d.congr(mod_am, cond_a, mod_a, &|d, x| {
        let c = d.beq(mod_bn, zero);
        d.bool_select_nat(c, x, zero)
    });
    let bitval2 = {
        let c = d.beq(cond_b, zero);
        d.bool_select_nat(c, cond_a, zero)
    };
    let bitval1_to_2 = d.congr(mod_bn, cond_b, mod_b, &|d, x| {
        let c = d.beq(x, zero);
        d.bool_select_nat(c, cond_a, zero)
    });
    let (_bitval_final, bitval_chain) =
        d.chain(bitval0, &[(bitval1, bitval0_to_1), (bitval2, bitval1_to_2)]);

    let guarded_mid = guarded(d, bit_am, bit_bn, bit_am, zero, ldiff_mn, bitval0);
    let guarded_final = guarded(d, bit_am, bit_bn, bit_am, zero, ldiff_mn, bitval2);
    let step_rec = d.congr(rec0, ldiff_mn, rec_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, bit_am, zero, hole, bitval0)
    });
    let step_bitv = d.congr(bitval0, bitval2, bitval_chain, &|d, hole| {
        guarded(d, bit_am, bit_bn, bit_am, zero, ldiff_mn, hole)
    });

    // --- resolve the two guards ----------------------------------------------
    let step_guard = resolve_ldiff_guard(d, &p, a, m, b, n);

    let ldiff_fn_expr = ldiff_fn(d, &p);
    let a_ldiff_b = d.apply(ldiff_fn_expr, &[a, b]);
    let target = d.const_app(p.bit, &[a_ldiff_b, ldiff_mn]);

    let (_final, proof) = d.chain(
        ldiff_ab,
        &[
            (ldiffaux_fuel, step0),
            (guarded0, step1),
            (guarded_mid, step_rec),
            (guarded_final, step_bitv),
            (target, step_guard),
        ],
    );

    let stmt = d.eq(ldiff_ab, target);

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let inner = d.pi_fv(b_fv, bool_ty, inner);
        let inner = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(a_fv, bool_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let inner = d.lam_fv(b_fv, bool_ty, inner);
        let inner = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(a_fv, bool_ty, inner)
    };
    d.declare_theorem(p.ldiff_bit, ty, value)
}

/// Declare the `Nat.bit` decode bridge helpers and `Nat.land_bit`/
/// `Nat.lor_bit`/`Nat.ldiff_bit`. See the module doc for the shared
/// fuel-swap machinery and each `declare_*_bit`'s own doc for what is new
/// per operator.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_bit_decode_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_bit_div_two(d, p)?;
    declare_bit_mod_two(d, p)?;
    declare_land_bit(d, p)?;
    declare_lor_bit(d, p)?;
    declare_ldiff_bit(d, p)?;
    Ok(())
}
