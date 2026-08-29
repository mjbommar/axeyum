//! `Nat.xor_trichotomy` and `Nat.lt_xor_cases` — the composition step for
//! `F:ml430-nat-lt-xor-cases-c43a1e85`.
//!
//! All four blocking pieces landed earlier the same day
//! (`docs/plan/status/260-nat-lt-xor-cases.md`, `263`, `265`, `268`, `269`,
//! `270`, `271`):
//!
//! 1. `Nat.testBit_xor` (`testbit_bitwise.rs`)
//! 2. `Nat.exists_most_significant_bit` (`bit_order.rs`, via
//!    `Nat.msb_exists_of_le_fuel`)
//! 3. `Nat.lt_of_testBit` (`bit_order.rs`)
//! 4. `Nat.xor_assoc`, `Nat.xor_xor_cancel_left`/`_right`,
//!    `Nat.xor_ne_zero_iff` (`xor_algebra.rs`)
//!
//! This file is the composition: Mathlib's own route
//! (`Mathlib/Data/Nat/Bitwise.lean`, pinned commit
//! `c5ea00351c28e24afc9f0f84379aa41082b1188f`, read directly, not
//! paraphrased):
//!
//! ```text
//! theorem xor_trichotomy {a b c : ℕ} (h : a ^^^ b ^^^ c ≠ 0) :
//!     b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c := by
//!   set v := a ^^^ b ^^^ c with hv
//!   have hab : a ^^^ b = c ^^^ v := by rw [Nat.xor_comm c, Nat.xor_xor_cancel_right]
//!   have hbc : b ^^^ c = a ^^^ v := by rw [← Nat.xor_assoc, Nat.xor_xor_cancel_left]
//!   have hca : c ^^^ a = b ^^^ v := by
//!     rw [hv, Nat.xor_assoc, Nat.xor_comm a, ← Nat.xor_assoc, Nat.xor_xor_cancel_left]
//!   obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit h
//!   have : testBit a i ∨ testBit b i ∨ testBit c i := by
//!     contrapose! hi
//!     simp_rw [Bool.eq_false_eq_not_eq_true] at hi ⊢
//!     rw [testBit_xor, testBit_xor, hi.1, hi.2.1, hi.2.2]; rfl
//!   obtain h | h | h := this
//!   on_goal 1 => left; rw [hbc]
//!   on_goal 2 => right; left; rw [hca]
//!   on_goal 3 => right; right; rw [hab]
//!   all_goals
//!     refine lt_of_testBit i ?_ h fun j hj => ?_
//!     · rw [testBit_xor, h, hi]; rfl
//!     · simp only [testBit_xor, hi' _ hj, Bool.bne_false]
//!
//! theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c := by
//!   obtain ha | hb | hc := xor_trichotomy <| Nat.xor_assoc _ _ _ ▸ xor_ne_zero_iff.2 h.ne
//!   exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]
//! ```
//!
//! ## What changes in a `Nat`-valued (not `Bool`-valued) kernel
//!
//! This kernel's `testBit` is `Nat`-valued (`{0, 1}`, `binary.rs`), so the
//! `contrapose!`/`simp_rw [Bool.eq_false_eq_not_eq_true]` step above (which
//! only makes sense for `Bool`) is replaced by a direct forward case split:
//! `Nat.lt_two_cases` on each of `testBit a i`, `testBit b i`, `testBit c i`
//! (each `<= 1` via `Nat.testBit_le_one`), 8-way, with the one degenerate
//! branch (all three `= 0`) refuted directly against `hi : testBit v i = 1`
//! by computing `testBit v i = 0` from `Nat.testBit_xor` applied twice and
//! `Nat.succ_ne_zero`.
//!
//! `Nat.xor_xor_cancel_right` is not needed for `hab`/`hbc`/`hca` here:
//! `Nat.xor_assoc` alone gives `v = xor a (xor b c)` directly (`v`'s own
//! definition IS `xor_assoc`'s LHS), so `xor a v = xor a (xor a (xor b c))`
//! collapses to `xor b c` by ONE application of `xor_xor_cancel_left`, with
//! no separate `_right`-shaped step. The other two rotations use
//! `Nat.xor_comm` to reorder before applying the same `xor_assoc` +
//! `xor_xor_cancel_left` pattern once each.
//!
//! `Nat.lt_xor_cases` reuses `xor_trichotomy` with the SAME `(a, b, c)` it
//! was given (not a permutation): its hypothesis `Lt a (xor b c)` gives
//! `Not (Eq a (xor b c))` (via `Lt` irreflexivity/transitivity, since no
//! bare `ne_of_lt` lemma exists in this prelude — built inline from
//! `Nat.lt_irrefl` + a transport), then `Nat.xor_ne_zero_iff.mpr` and
//! `Nat.xor_assoc` route that into `Not (Eq (xor (xor a b) c) 0)`, exactly
//! `xor_trichotomy`'s hypothesis at THIS `(a, b, c)`. The `ha` branch is
//! refuted the same way (`Lt a (xor b c)` and `Lt (xor b c) a` cannot both
//! hold — via `Nat.le_succ`/`Nat.le_trans`/`Nat.lt_of_lt_of_le`/
//! `Nat.lt_irrefl`, since no bare `lt_asymm` lemma exists either).

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use super::testbit_bitwise::xor_bit;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Eq (xor_bit x 0) x`, given `Le x 1` — the same `{0, 1}` case-split shape
/// `xor_algebra.rs`'s private `round_trip_le_one` uses (not exposed
/// cross-file, so duplicated per the standing convention), applied to a
/// different target: `xor_bit(x, 0)` computes (at each concrete branch) to
/// `x` directly, since `beq(0, 1)` reduces to `false` and `xor_fn(_, false)`
/// selects its first argument at each LITERAL branch.
fn xor_bit_zero_right(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, h_le: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();

    let xb_of = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
        let zero = d.zero();
        xor_bit(d, v, zero)
    };
    let xb_x = xb_of(d, x);
    let target = d.eq(xb_x, x);

    let succ_x_le_succ_one = d.lemma(p.le_succ_succ, &[x, one, h_le]);
    let dichotomy = d.lemma(p.lt_two_cases, &[x, succ_x_le_succ_one]);

    let eq_x0_ty = d.eq(x, zero);
    let eq_x1_ty = d.eq(x, one);

    let minor_zero = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let xb0 = xb_of(d, zero);
        let step1 = d.congr(x, zero, h, &|d, w| xb_of(d, w));
        let step2 = d.refl(xb0); // xb0 computes to zero
        let to_zero = d.trans(xb_x, xb0, zero, step1, step2);
        let symm_h = d.symm(x, zero, h);
        let body = d.trans(xb_x, zero, x, to_zero, symm_h);
        d.lam_fv(h_fv, eq_x0_ty, body)
    };
    let minor_one = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let xb1 = xb_of(d, one);
        let step1 = d.congr(x, one, h, &|d, w| xb_of(d, w));
        let step2 = d.refl(xb1); // xb1 computes to one
        let to_one = d.trans(xb_x, xb1, one, step1, step2);
        let symm_h = d.symm(x, one, h);
        let body = d.trans(xb_x, one, x, to_one, symm_h);
        d.lam_fv(h_fv, eq_x1_ty, body)
    };

    let logic = d.prelude().logic;
    d.const_app(
        logic.or_elim,
        &[eq_x0_ty, eq_x1_ty, target, dichotomy, minor_zero, minor_one],
    )
}

/// `Or (Eq (testBit n i) 0) (Eq (testBit n i) 1)` — `Nat.testBit_le_one`
/// lifted through `Nat.le_succ_succ`/`Nat.lt_two_cases`, the same bridge
/// `xor_algebra.rs`'s `round_trip_le_one` uses for its own bound.
fn bit_dichotomy(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, i: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let tb = d.const_app(p.test_bit, &[n, i]);
    let h_le = d.lemma(p.test_bit_le_one, &[n, i]); // Le tb 1
    let succ_le = d.lemma(p.le_succ_succ, &[tb, one, h_le]); // Le (succ tb) (succ 1) ~ Lt tb 2
    d.lemma(p.lt_two_cases, &[tb, succ_le]) // Or (Eq tb 0) (Eq tb 1)
}

/// Given `Eq (testBit v j) 0`, produce `Eq (testBit (xor x v) j) (testBit x
/// j)` — `Nat.testBit_xor` with the second operand's bit substituted to `0`
/// and cancelled via [`xor_bit_zero_right`].
fn agree_above(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    v: ExprId,
    j: ExprId,
    h_zero: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let tb_x = d.const_app(p.test_bit, &[x, j]);
    let tb_v = d.const_app(p.test_bit, &[v, j]);
    let xor_xv = d.const_app(p.xor, &[x, v]);
    let tb_xor = d.const_app(p.test_bit, &[xor_xv, j]);

    let outer = d.lemma(p.test_bit_xor, &[x, v, j]); // Eq tb_xor (xor_bit tb_x tb_v)
    let xor_bit_tx_tv = xor_bit(d, tb_x, tb_v);
    let congr_h = d.congr(tb_v, zero, h_zero, &|d, w| {
        let tb_x2 = tb_x;
        xor_bit(d, tb_x2, w)
    });
    let xor_bit_tx_zero = xor_bit(d, tb_x, zero);
    let h_le = d.lemma(p.test_bit_le_one, &[x, j]); // Le tb_x 1
    let zero_right = xor_bit_zero_right(d, &p, tb_x, h_le); // Eq (xor_bit tb_x 0) tb_x

    d.chain(
        tb_xor,
        &[
            (xor_bit_tx_tv, outer),
            (xor_bit_tx_zero, congr_h),
            (tb_x, zero_right),
        ],
    )
    .1
}

/// Given `Eq (testBit x i) 1` and `Eq (testBit v i) 1`, produce `Eq (testBit
/// (xor x v) i) 0` — the two substituted bits cancel: `xor_bit 1 1`
/// computes to `0`.
fn cancel_at_msb(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    v: ExprId,
    i: ExprId,
    h_tx: ExprId,
    h_tv: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let tb_x = d.const_app(p.test_bit, &[x, i]);
    let tb_v = d.const_app(p.test_bit, &[v, i]);
    let xor_xv = d.const_app(p.xor, &[x, v]);
    let tb_xor = d.const_app(p.test_bit, &[xor_xv, i]);

    let outer = d.lemma(p.test_bit_xor, &[x, v, i]); // Eq tb_xor (xor_bit tb_x tb_v)
    let xor_bit_tx_tv = xor_bit(d, tb_x, tb_v);

    let congr_tx = d.congr(tb_x, one, h_tx, &|d, w| {
        let tb_v2 = tb_v;
        xor_bit(d, w, tb_v2)
    });
    let xor_bit_one_tv = xor_bit(d, one, tb_v);

    let congr_tv = d.congr(tb_v, one, h_tv, &|d, w| {
        let one2 = d.num(1);
        xor_bit(d, one2, w)
    });
    let xor_bit_one_one = xor_bit(d, one, one);
    let refl_step = d.refl(xor_bit_one_one); // computes to zero

    d.chain(
        tb_xor,
        &[
            (xor_bit_tx_tv, outer),
            (xor_bit_one_tv, congr_tx),
            (xor_bit_one_one, congr_tv),
            (zero, refl_step),
        ],
    )
    .1
}

/// Given `Eq (testBit a i) 0`, `Eq (testBit b i) 0`, `Eq (testBit c i) 0`,
/// produce `Eq (testBit (xor (xor a b) c) i) 0` — the degenerate branch of
/// the trichotomy's bit case-split, refuted against `hi : testBit v i = 1`.
#[allow(clippy::too_many_arguments)]
fn all_zero_gives_v_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    i: ExprId,
    h_ta0: ExprId,
    h_tb0: ExprId,
    h_tc0: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let xab = d.const_app(p.xor, &[a, b]);
    let v = d.const_app(p.xor, &[xab, c]);
    let tb_a = d.const_app(p.test_bit, &[a, i]);
    let tb_b = d.const_app(p.test_bit, &[b, i]);
    let tb_c = d.const_app(p.test_bit, &[c, i]);
    let tb_xab = d.const_app(p.test_bit, &[xab, i]);
    let tb_v = d.const_app(p.test_bit, &[v, i]);

    let outer = d.lemma(p.test_bit_xor, &[xab, c, i]); // Eq tb_v (xor_bit tb_xab tb_c)
    let node_outer = xor_bit(d, tb_xab, tb_c);

    let inner = d.lemma(p.test_bit_xor, &[a, b, i]); // Eq tb_xab (xor_bit tb_a tb_b)
    let xor_bit_ab = xor_bit(d, tb_a, tb_b);
    let step_inner = d.congr(tb_xab, xor_bit_ab, inner, &|d, w| {
        let tb_c2 = tb_c;
        xor_bit(d, w, tb_c2)
    });
    let node_inner_c = xor_bit(d, xor_bit_ab, tb_c);

    // xor_bit_ab -> 0
    let step_ta = d.congr(tb_a, zero, h_ta0, &|d, w| {
        let tb_b2 = tb_b;
        xor_bit(d, w, tb_b2)
    });
    let node_0_b = xor_bit(d, zero, tb_b);
    let step_tb = d.congr(tb_b, zero, h_tb0, &|d, w| {
        let zero2 = d.zero();
        xor_bit(d, zero2, w)
    });
    let node_0_0 = xor_bit(d, zero, zero);
    let refl_00 = d.refl(node_0_0);
    let ab_to_zero = d
        .chain(
            xor_bit_ab,
            &[(node_0_b, step_ta), (node_0_0, step_tb), (zero, refl_00)],
        )
        .1;

    let step_ab_zero = d.congr(xor_bit_ab, zero, ab_to_zero, &|d, w| {
        let tb_c2 = tb_c;
        xor_bit(d, w, tb_c2)
    });
    let node_0_c = xor_bit(d, zero, tb_c);
    let step_tc = d.congr(tb_c, zero, h_tc0, &|d, w| {
        let zero2 = d.zero();
        xor_bit(d, zero2, w)
    });
    let refl_00b = d.refl(node_0_0);

    d.chain(
        tb_v,
        &[
            (node_outer, outer),
            (node_inner_c, step_inner),
            (node_0_c, step_ab_zero),
            (node_0_0, step_tc),
            (zero, refl_00b),
        ],
    )
    .1
}

/// `fun i => And (Eq (testBit n i) 1) (∀ j, Lt i j → Eq (testBit n j) 0)` —
/// the `exists_most_significant_bit` predicate at `n`, duplicated from
/// `bit_order.rs`'s private `msb_predicate` (not exposed cross-file) since
/// [`exists_elim`] needs a term matching what
/// `Nat.exists_most_significant_bit`'s stored type actually carries.
fn msb_predicate(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let one = d.num(1);
    let zero = d.zero();
    let tb_i = d.const_app(p.test_bit, &[n, i]);
    let a = d.eq(tb_i, one);
    let b = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let lt_i_j = d.lt(i, j);
        let tb_j = d.const_app(p.test_bit, &[n, j]);
        let eq_j = d.eq(tb_j, zero);
        let body = d.arrow(lt_i_j, eq_j);
        d.pi_fv(j_fv, nat, body)
    };
    let and_ty = d.const_app(p.logic.and, &[a, b]);
    d.lam_fv(i_fv, nat, and_ty)
}

/// Non-dependent `Exists.rec` over `Nat`, duplicated from
/// `rec_agreement.rs`'s private `exists_elim` (not exposed cross-file).
fn exists_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    predicate: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level_one = d.level_one();
    let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
    let exists_ty = d.apply(exists_const, &[nat, predicate]);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, exists_ty, goal, BinderInfo::Default);
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, proof])
}

/// `False.rec (fun _ => target) false_proof : target`, duplicated from the
/// same pattern used throughout `bit_order.rs`/`order_more.rs` (not exposed
/// cross-file).
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let p = *p;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// Given `Eq (testBit x i) 1`, `Eq (testBit v i) 1`,
/// `∀ j, Lt i j → Eq (testBit v j) 0`, and a rotation identity
/// `Eq (xor x v) y`, produce `Lt y x` — `Nat.lt_of_testBit` at
/// `(xor x v, x, i)`, transported along the rotation.
#[allow(clippy::too_many_arguments)]
fn msb_gives_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    v: ExprId,
    i: ExprId,
    h_tx: ExprId,
    hi: ExprId,
    hi_prime: ExprId,
    y: ExprId,
    e_xv_y: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let xor_xv = d.const_app(p.xor, &[x, v]);

    let h0 = cancel_at_msb(d, &p, x, v, i, h_tx, hi); // Eq (testBit xor_xv i) 0

    let hagree = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let lt_i_j = d.lt(i, j);
        let h_zero_j = d.apply(hi_prime, &[j, hj]); // Eq (testBit v j) 0
        let agree = agree_above(d, &p, x, v, j, h_zero_j);
        let body = d.lam_fv(hj_fv, lt_i_j, agree);
        d.lam_fv(j_fv, nat, body)
    };

    let lt_proof = d.lemma(p.lt_of_test_bit, &[xor_xv, x, i, h0, h_tx, hagree]); // Lt xor_xv x

    let motive = d.eq_motive(xor_xv, &|d, w| {
        let x2 = x;
        d.lt(w, x2)
    });
    d.transport(xor_xv, motive, lt_proof, y, e_xv_y)
}

/// The three "rotation" identities Mathlib's `xor_trichotomy` proof needs,
/// each derived from `Nat.xor_assoc`/`Nat.xor_comm`/`Nat.xor_xor_cancel_left`
/// alone (`Nat.xor_xor_cancel_right` is NOT needed — see the module doc):
///
/// - `e_a : Eq (xor a v) (xor b c)`
/// - `e_b : Eq (xor b v) (xor c a)`
/// - `e_c : Eq (xor c v) (xor a b)`
///
/// where `v := xor (xor a b) c`.
fn build_rotations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = *p;
    let xab = d.const_app(p.xor, &[a, b]);
    let xbc = d.const_app(p.xor, &[b, c]);
    let xca = d.const_app(p.xor, &[c, a]);
    let v = d.const_app(p.xor, &[xab, c]);

    // e_a : Eq (xor a v) xbc -- v = xor a xbc directly by xor_assoc(a,b,c).
    let e_a = {
        let xassoc_abc = d.lemma(p.xor_assoc, &[a, b, c]); // Eq v (xor a xbc)
        let xor_a_xbc = d.const_app(p.xor, &[a, xbc]);
        let cancel_a = d.lemma(p.xor_xor_cancel_left, &[a, xbc]); // Eq (xor a (xor a xbc)) xbc
        let xor_a_axbc = d.const_app(p.xor, &[a, xor_a_xbc]);
        let congr_v = d.congr(v, xor_a_xbc, xassoc_abc, &|d, w| {
            let a2 = a;
            d.const_app(p.xor, &[a2, w])
        });
        let xor_a_v = d.const_app(p.xor, &[a, v]);
        d.chain(xor_a_v, &[(xor_a_axbc, congr_v), (xbc, cancel_a)])
            .1
    };

    // e_b : Eq (xor b v) xca -- via xor_comm(a,b), xor_assoc(b,a,c),
    // xor_xor_cancel_left(b, xac), then xor_comm(c,a).
    let e_b = {
        let xor_b_a = d.const_app(p.xor, &[b, a]);
        let comm_ab = d.lemma(p.xor_comm, &[a, b]); // Eq xab xor_b_a
        let congr1 = d.congr(xab, xor_b_a, comm_ab, &|d, w| {
            let c2 = c;
            d.const_app(p.xor, &[w, c2])
        }); // Eq v (xor xor_b_a c)
        let xor_ba_c = d.const_app(p.xor, &[xor_b_a, c]);
        let xassoc_bac = d.lemma(p.xor_assoc, &[b, a, c]); // Eq xor_ba_c (xor b (xor a c))
        let xac = d.const_app(p.xor, &[a, c]);
        let xor_b_xac = d.const_app(p.xor, &[b, xac]);
        let v_eq_b_xac = d.chain(v, &[(xor_ba_c, congr1), (xor_b_xac, xassoc_bac)]).1; // Eq v xor_b_xac

        let cancel_b = d.lemma(p.xor_xor_cancel_left, &[b, xac]); // Eq (xor b (xor b xac)) xac
        let xor_b_bxac = d.const_app(p.xor, &[b, xor_b_xac]);
        let congr_vb = d.congr(v, xor_b_xac, v_eq_b_xac, &|d, w| {
            let b2 = b;
            d.const_app(p.xor, &[b2, w])
        }); // Eq (xor b v) xor_b_bxac
        let xor_b_v = d.const_app(p.xor, &[b, v]);
        let xor_bv_eq_xac = d
            .chain(xor_b_v, &[(xor_b_bxac, congr_vb), (xac, cancel_b)])
            .1; // Eq (xor b v) xac

        let comm_ca = d.lemma(p.xor_comm, &[c, a]); // Eq xca xac
        let symm_xac = d.symm(xor_b_v, xac, xor_bv_eq_xac); // Eq xac (xor b v)
        let e_b_rev = d.chain(xca, &[(xac, comm_ca), (xor_b_v, symm_xac)]).1; // Eq xca (xor b v)
        d.symm(xca, xor_b_v, e_b_rev) // Eq (xor b v) xca
    };

    // e_c : Eq (xor c v) xab -- v = xor c xab directly by xor_comm(xab,c),
    // then xor_xor_cancel_left(c, xab).
    let e_c = {
        let xor_c_xab = d.const_app(p.xor, &[c, xab]);
        let comm_xabc = d.lemma(p.xor_comm, &[xab, c]); // Eq v xor_c_xab
        let cancel_c = d.lemma(p.xor_xor_cancel_left, &[c, xab]); // Eq (xor c (xor c xab)) xab
        let xor_c_cxab = d.const_app(p.xor, &[c, xor_c_xab]);
        let congr_vc = d.congr(v, xor_c_xab, comm_xabc, &|d, w| {
            let c2 = c;
            d.const_app(p.xor, &[c2, w])
        });
        let xor_c_v = d.const_app(p.xor, &[c, v]);
        d.chain(xor_c_v, &[(xor_c_cxab, congr_vc), (xab, cancel_c)])
            .1
    };

    (e_a, e_b, e_c)
}

/// `Nat.xor_trichotomy : ∀ a b c, Not (Eq (xor (xor a b) c) 0) → Or (Lt (xor
/// b c) a) (Or (Lt (xor c a) b) (Lt (xor a b) c))`. See the module doc for
/// the full route.
fn declare_xor_trichotomy(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.xor_trichotomy, 3, &|d, vals| {
        let (a, b, c) = (vals[0], vals[1], vals[2]);
        let zero = d.zero();
        let one = d.num(1);

        let xab = d.const_app(p.xor, &[a, b]);
        let xbc = d.const_app(p.xor, &[b, c]);
        let xca = d.const_app(p.xor, &[c, a]);
        let v = d.const_app(p.xor, &[xab, c]);

        let eq_v0_ty = d.eq(v, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_v0_ty, false_ty);
        let ne_fv = d.fresh_fvar();
        let h_ne = d.kernel().fvar(ne_fv);

        let lt_bc_a = d.lt(xbc, a);
        let lt_ca_b = d.lt(xca, b);
        let lt_ab_c = d.lt(xab, c);
        let inner_or = d.const_app(p.logic.or, &[lt_ca_b, lt_ab_c]);
        let goal = d.const_app(p.logic.or, &[lt_bc_a, inner_or]);

        let (e_a, e_b, e_c) = build_rotations(d, &p, a, b, c);

        let msb_v = d.lemma(p.exists_most_significant_bit, &[v, h_ne]); // Exists Nat (msb_predicate v)
        let predicate = msb_predicate(d, &p, v);

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let tb_v_i = d.const_app(p.test_bit, &[v, i]);
            let eq1 = d.eq(tb_v_i, one);
            let upper_ty = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let lt_i_j = d.lt(i, j);
                let tb_v_j = d.const_app(p.test_bit, &[v, j]);
                let eq0 = d.eq(tb_v_j, zero);
                let body = d.arrow(lt_i_j, eq0);
                d.pi_fv(j_fv, nat, body)
            };
            let and_ty = d.const_app(p.logic.and, &[eq1, upper_ty]);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hi = and_left(d, eq1, upper_ty, h);
            let hi_prime = and_right(d, eq1, upper_ty, h);

            let ta = d.const_app(p.test_bit, &[a, i]);
            let tb_ = d.const_app(p.test_bit, &[b, i]);
            let tc_ = d.const_app(p.test_bit, &[c, i]);
            let eq_ta0 = d.eq(ta, zero);
            let eq_ta1 = d.eq(ta, one);
            let eq_tb0 = d.eq(tb_, zero);
            let eq_tb1 = d.eq(tb_, one);
            let eq_tc0 = d.eq(tc_, zero);
            let eq_tc1 = d.eq(tc_, one);

            let branch_ta1 = {
                let hf = d.fresh_fvar();
                let h_ta = d.kernel().fvar(hf);
                let lt_proof = msb_gives_lt(d, &p, a, v, i, h_ta, hi, hi_prime, xbc, e_a);
                let wrapped = d.const_app(p.logic.or_inl, &[lt_bc_a, inner_or, lt_proof]);
                d.lam_fv(hf, eq_ta1, wrapped)
            };

            let branch_ta0 = {
                let hf0 = d.fresh_fvar();
                let h_ta0 = d.kernel().fvar(hf0);

                let branch_tb1 = {
                    let hf = d.fresh_fvar();
                    let h_tb = d.kernel().fvar(hf);
                    let lt_proof = msb_gives_lt(d, &p, b, v, i, h_tb, hi, hi_prime, xca, e_b);
                    let inner_w = d.const_app(p.logic.or_inl, &[lt_ca_b, lt_ab_c, lt_proof]);
                    let wrapped = d.const_app(p.logic.or_inr, &[lt_bc_a, inner_or, inner_w]);
                    d.lam_fv(hf, eq_tb1, wrapped)
                };

                let branch_tb0 = {
                    let hf0b = d.fresh_fvar();
                    let h_tb0 = d.kernel().fvar(hf0b);

                    let branch_tc1 = {
                        let hf = d.fresh_fvar();
                        let h_tc = d.kernel().fvar(hf);
                        let lt_proof = msb_gives_lt(d, &p, c, v, i, h_tc, hi, hi_prime, xab, e_c);
                        let inner_w = d.const_app(p.logic.or_inr, &[lt_ca_b, lt_ab_c, lt_proof]);
                        let wrapped = d.const_app(p.logic.or_inr, &[lt_bc_a, inner_or, inner_w]);
                        d.lam_fv(hf, eq_tc1, wrapped)
                    };

                    let branch_tc0 = {
                        let hf0c = d.fresh_fvar();
                        let h_tc0 = d.kernel().fvar(hf0c);
                        let v_zero = all_zero_gives_v_zero(d, &p, a, b, c, i, h_ta0, h_tb0, h_tc0);
                        let hi_symm = d.symm(tb_v_i, one, hi); // Eq one tb_v_i
                        let one_eq_zero = d.trans(one, tb_v_i, zero, hi_symm, v_zero); // Eq one zero
                        let false_proof = d.lemma(p.succ_ne_zero, &[zero, one_eq_zero]);
                        let goal_proof = ex_falso(d, &p, goal, false_proof);
                        d.lam_fv(hf0c, eq_tc0, goal_proof)
                    };

                    let dichot_c = bit_dichotomy(d, &p, c, i);
                    let body = d.const_app(
                        p.logic.or_elim,
                        &[eq_tc0, eq_tc1, goal, dichot_c, branch_tc0, branch_tc1],
                    );
                    d.lam_fv(hf0b, eq_tb0, body)
                };

                let dichot_b = bit_dichotomy(d, &p, b, i);
                let body = d.const_app(
                    p.logic.or_elim,
                    &[eq_tb0, eq_tb1, goal, dichot_b, branch_tb0, branch_tb1],
                );
                d.lam_fv(hf0, eq_ta0, body)
            };

            let dichot_a = bit_dichotomy(d, &p, a, i);
            let case_result = d.const_app(
                p.logic.or_elim,
                &[eq_ta0, eq_ta1, goal, dichot_a, branch_ta0, branch_ta1],
            );

            let body = d.lam_fv(h_fv, and_ty, case_result);
            d.lam_fv(i_fv, nat, body)
        };

        let proof = exists_elim(d, &p, predicate, goal, minor, msb_v);
        let stmt = d.arrow(ne_ty, goal);
        let full_proof = d.lam_fv(ne_fv, ne_ty, proof);
        (stmt, full_proof)
    })?;
    Ok(())
}

/// `Nat.lt_xor_cases : ∀ a b c, Lt a (xor b c) → Or (Lt (xor a c) b) (Lt
/// (xor a b) c)` — `F:ml430-nat-lt-xor-cases-c43a1e85`. See the module doc
/// for the full route.
fn declare_lt_xor_cases(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lt_xor_cases, 3, &|d, vals| {
        let (a, b, c) = (vals[0], vals[1], vals[2]);
        let zero = d.zero();
        let xbc = d.const_app(p.xor, &[b, c]);
        let xab = d.const_app(p.xor, &[a, b]);
        let xac = d.const_app(p.xor, &[a, c]);
        let xca = d.const_app(p.xor, &[c, a]);

        let h_ty = d.lt(a, xbc);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let lt_ac_b = d.lt(xac, b);
        let lt_ab_c = d.lt(xab, c);
        let goal = d.const_app(p.logic.or, &[lt_ac_b, lt_ab_c]);

        // h_ne_a_xbc : Not (Eq a xbc) -- from h : Lt a xbc via lt_irrefl.
        let heq_ty = d.eq(a, xbc);
        let h_ne_a_xbc = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let motive = d.eq_motive(a, &|d, w| {
                let xbc2 = xbc;
                d.lt(w, xbc2)
            });
            let transported = d.transport(a, motive, h, xbc, heq); // Lt xbc xbc
            let false_proof = d.lemma(p.lt_irrefl, &[xbc, transported]);
            d.lam_fv(heq_fv, heq_ty, false_proof)
        };

        // not_eq_axbc0 : Not (Eq (xor a xbc) 0) -- xor_ne_zero_iff.mpr.
        let xor_a_xbc = d.const_app(p.xor, &[a, xbc]);
        let iff_inst = d.lemma(p.xor_ne_zero_iff, &[a, xbc]);
        let eq_xor_a_xbc_0 = d.eq(xor_a_xbc, zero);
        let a_prop = d.const_app(p.logic.not, &[eq_xor_a_xbc_0]);
        let b_prop = d.const_app(p.logic.not, &[heq_ty]);
        let not_eq_axbc0 = d.const_app(p.logic.iff_mpr, &[a_prop, b_prop, iff_inst, h_ne_a_xbc]);

        // not_eq_v0 : Not (Eq (xor (xor a b) c) 0) -- transported along xor_assoc.
        let big_v = d.const_app(p.xor, &[xab, c]);
        let xassoc = d.lemma(p.xor_assoc, &[a, b, c]); // Eq big_v xor_a_xbc
        let not_eq_v0 = {
            let hv0_fv = d.fresh_fvar();
            let hv0 = d.kernel().fvar(hv0_fv);
            let eq_v0_ty = d.eq(big_v, zero);
            let motive = d.eq_motive(big_v, &|d, w| d.eq(w, zero));
            let eq_x0 = d.transport(big_v, motive, hv0, xor_a_xbc, xassoc); // Eq xor_a_xbc 0
            let false_proof = d.apply(not_eq_axbc0, &[eq_x0]);
            d.lam_fv(hv0_fv, eq_v0_ty, false_proof)
        };

        let tri = d.lemma(p.xor_trichotomy, &[a, b, c, not_eq_v0]);
        // tri : Or (Lt xbc a) (Or (Lt xca b) (Lt xab c))

        let lt_xbc_a_ty = d.lt(xbc, a);
        let lt_xca_b_ty = d.lt(xca, b);
        let lt_xab_c_ty = d.lt(xab, c);
        let inner_or_ty = d.const_app(p.logic.or, &[lt_xca_b_ty, lt_xab_c_ty]);

        let branch_ha = {
            let ha_fv = d.fresh_fvar();
            let h_ha = d.kernel().fvar(ha_fv); // Lt xbc a
            let succ_xbc = d.succ(xbc);
            let le_succ_xbc = d.lemma(p.le_succ, &[xbc]); // Le xbc (succ xbc)
            let le_xbc_a = d.lemma(p.le_trans, &[xbc, succ_xbc, a, le_succ_xbc, h_ha]); // Le xbc a
            let lt_a_a = d.lemma(p.lt_of_lt_of_le, &[a, xbc, a, h, le_xbc_a]); // Lt a a
            let false_proof = d.lemma(p.lt_irrefl, &[a, lt_a_a]);
            let goal_proof = ex_falso(d, &p, goal, false_proof);
            d.lam_fv(ha_fv, lt_xbc_a_ty, goal_proof)
        };

        let branch_rest = {
            let hr_fv = d.fresh_fvar();
            let h_rest = d.kernel().fvar(hr_fv);

            let branch_hb = {
                let hb_fv = d.fresh_fvar();
                let h_hb = d.kernel().fvar(hb_fv); // Lt xca b
                let comm_ca = d.lemma(p.xor_comm, &[c, a]); // Eq xca xac
                let motive = d.eq_motive(xca, &|d, w| {
                    let b2 = b;
                    d.lt(w, b2)
                });
                let transported = d.transport(xca, motive, h_hb, xac, comm_ca); // Lt xac b
                let wrapped = d.const_app(p.logic.or_inl, &[lt_ac_b, lt_ab_c, transported]);
                d.lam_fv(hb_fv, lt_xca_b_ty, wrapped)
            };
            let branch_hc = {
                let hc_fv = d.fresh_fvar();
                let h_hc = d.kernel().fvar(hc_fv); // Lt xab c
                let wrapped = d.const_app(p.logic.or_inr, &[lt_ac_b, lt_ab_c, h_hc]);
                d.lam_fv(hc_fv, lt_xab_c_ty, wrapped)
            };
            let body = d.const_app(
                p.logic.or_elim,
                &[lt_xca_b_ty, lt_xab_c_ty, goal, h_rest, branch_hb, branch_hc],
            );
            d.lam_fv(hr_fv, inner_or_ty, body)
        };

        let case_result = d.const_app(
            p.logic.or_elim,
            &[lt_xbc_a_ty, inner_or_ty, goal, tri, branch_ha, branch_rest],
        );

        let stmt = d.arrow(h_ty, goal);
        let proof = d.lam_fv(h_fv, h_ty, case_result);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order: `xor_trichotomy`
/// needs nothing from `lt_xor_cases`, but `lt_xor_cases` needs
/// `xor_trichotomy`.
pub(super) fn declare_xor_trichotomy_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_xor_trichotomy(d, p)?;
    declare_lt_xor_cases(d, p)?;
    Ok(())
}
