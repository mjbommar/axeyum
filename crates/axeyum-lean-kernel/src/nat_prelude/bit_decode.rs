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
//! bounded case tree (`cases_zero_succ` on `n`, then `m`, plus a `Bool`
//! split on `a`/`b` exactly where a guard's zero-ness genuinely depends on
//! it), because `bit test k` is `succ`-shaped for ANY `test` once `k` is
//! `succ`-shaped, and `beq (succ _) 0` reduces to `false` by δι alone
//! regardless of what is under the `succ`. Land's absorbing-zero guard
//! rows (`land_zero_left`/`land_zero_right`, both already proved) close
//! the two degenerate leaves; the "both guards false" leaf needs one more
//! small fact, [`and_cond_mul_eq_cond`] (`mul (cond a 1 0) (cond b 1 0) =
//! cond (a && b) 1 0`, itself a two-leaf `Bool` split on `a` alone using
//! `one_mul`/`zero_mul`, since `Nat.mul` recurses on its SECOND argument
//! and `cond b 1 0` stays stuck at symbolic `b`).
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
use super::bitwise::and_fn;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ, two_mul_eq_add_self};
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
fn case_bool(
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
    divisor: ExprId,
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
        divisor,
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
fn land_guard_goal(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId, b: ExprId, n: ExprId) -> ExprId {
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
fn land_guard_step_leaf(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId, b: ExprId, n: ExprId) -> ExprId {
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

/// Resolve the `m`-guard, given that the `n`-guard is already known false
/// (by construction at the call site: either `n` is literally `succ`-shaped,
/// or `n = 0` with `b = true`).
fn land_guard_inner(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    cases_zero_succ(
        d,
        m,
        &|d, cand_m| land_guard_goal(d, &p, a, cand_m, b, n),
        &|d| {
            let zero = d.zero();
            case_bool(
                d,
                &p,
                a,
                &|d, cand_a| land_guard_goal(d, &p, cand_a, zero, b, n),
                &|d| {
                    let t = d.bool_true();
                    let zero = d.zero();
                    land_guard_step_leaf(d, &p, t, zero, b, n)
                },
                &|d| land_guard_on_m_zero_leaf(d),
            )
        },
        &|d, m_pred| {
            let succ_m = d.succ(m_pred);
            land_guard_step_leaf(d, &p, a, succ_m, b, n)
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
fn land_guard_on_n_zero_branch(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, a_lit: ExprId) -> ExprId {
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
    let (_final, chain_proof) = d.chain(target_before, &[(target_after, congr_step), (zero, refl_after)]);
    d.symm(target_before, zero, chain_proof)
}

/// The full guard-resolution case tree: split `n`, then (when `n = 0`)
/// `b`, then (once positive) `m`, then (when `m = 0`) `a` — matching
/// exactly the guards `guarded` itself checks, `n` outermost.
fn resolve_land_guard(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, m: ExprId, b: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    cases_zero_succ(
        d,
        n,
        &|d, cand_n| land_guard_goal(d, &p, a, m, b, cand_n),
        &|d| {
            let zero = d.zero();
            case_bool(
                d,
                &p,
                b,
                &|d, cand_b| land_guard_goal(d, &p, a, m, cand_b, zero),
                &|d| {
                    let t = d.bool_true();
                    let zero = d.zero();
                    land_guard_inner(d, &p, a, m, t, zero)
                },
                &|d| land_guard_on_n_zero_leaf(d, &p, a, m),
            )
        },
        &|d, n_pred| {
            let succ_n = d.succ(n_pred);
            land_guard_inner(d, &p, a, m, b, succ_n)
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
    let rec0_to_rec1 = d.congr(half_am, m, div_a, &|d, x| d.const_app(p.land_aux, &[k1, x, half_bn]));
    let rec2 = d.const_app(p.land_aux, &[k1, m, n]);
    let rec1_to_rec2 = d.congr(half_bn, n, div_b, &|d, x| d.const_app(p.land_aux, &[k1, m, x]));
    let rec2_eq_land_mn = d.lemma(p.land_aux_eq_land_of_le, &[k1, m, n, m_le_k1_bound]);
    let (_rec_final, rec_chain) = d.chain(rec0, &[(rec1, rec0_to_rec1), (rec2, rec1_to_rec2), (land_mn, rec2_eq_land_mn)]);

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
    let (_bitval_final, bitval_chain) = d.chain(bitval0, &[(bitval1, bitval0_to_1), (bitval2, bitval1_to_2)]);

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

/// Declare the `Nat.bit` decode bridge helpers and `Nat.land_bit`. See the
/// module doc for what does and does not transport to `lor`/`ldiff`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_bit_decode_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_bit_div_two(d, p)?;
    declare_bit_mod_two(d, p)?;
    declare_land_bit(d, p)?;
    Ok(())
}
