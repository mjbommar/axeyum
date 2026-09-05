//! `Nat.Finset` subset search — the TWO-dimensional analogue of
//! `Nat.Finset.allBelow_false_witness` (ADR-1614).
//!
//! # The obstruction this removes
//!
//! ADR-1608 landed Hall's marriage theorem in its *necessity* direction only
//! and named the blocker precisely: the sufficiency direction splits on whether
//! some proper non-empty `t ⊆ s` is **critical**
//! (`card t = card (unionOver nb t)`), and with no classical choice that `t`
//! must be **computed** — a bounded search over the `2^(bound s)` subsets of a
//! `Nat.Finset`, together with a reflection lemma that reads the search's
//! verdict back into the kernel. Nothing of that shape existed:
//! `Nat.Finset.allBelow_false_witness` searches over *indices* (one
//! dimension); nothing searched over *subsets*.
//!
//! A `shape_search` sweep at 2,832 declarations (positive control
//! `Nat.Rado.IsRadoNumber`, FOUND) returns ABSENT for `decode`, `encode`,
//! `subsets`, `powerset` and `enumerate`. It does **not** return absent for
//! `testBit`: `Nat.testBit : Nat → Nat → Nat` and its laws already exist in
//! `binary.rs`/`bit_order.rs`, and they are the whole reason this module is
//! short. Searching for the STEP rather than the NAME saved rebuilding the bit
//! decoder.
//!
//! # What is here
//!
//! ```text
//! Nat.Finset.bitB k i        := beq (Nat.testBit k i) 1     -- the Bool view
//! Nat.Finset.decode n k      := Nat.Finset.mk (bitB k) n    -- the k-th subset of [0,n)
//! Nat.Finset.encodeFrom f n j                               -- recursion on the WIDTH n
//!   | f 0       j = 0
//!   | f (succ m) j = Nat.bit (f j) (encodeFrom f m (succ j))
//! Nat.Finset.encode t n      := encodeFrom (Nat.Finset.memB t) n 0
//! Nat.Finset.anySubset P n   := notB (allBelow (fun k => notB (P (decode n k))) (pow 2 n))
//! ```
//!
//! and the four laws:
//!
//! * `bitB_encodeFrom` — the decoder inverts the encoder pointwise below the
//!   width;
//! * `encodeFrom_lt_pow` — every code is below `2^n`, so the search range is
//!   right;
//! * `memB_decode_encode` — **exhaustiveness**: every `Nat.Finset` whose bound
//!   is at most `n` has the same membership as `decode n (encode t n)`, at
//!   EVERY index, not only below `n` (above the bound both sides are `false`
//!   because `memB` truncates inside its own definition, ADR-1577);
//! * `existsSubset_of_search` / `forallSubset_of_search` — **the reflection
//!   lemma, in both polarities**. This is the reusable primitive, and it is the
//!   deliverable: it is to subsets what `allBelow_false_witness` and
//!   `allBelow_true_at` are to indices.
//!
//! # Two things worth recording
//!
//! **The width bound is `Nat.pow 2 n`, and it is never formed.** Every numeral
//! in this prelude is unary, so `2^n` cannot be *computed* for interesting `n`
//! — but a `Prop` that merely mentions it never reduces it. Every statement
//! below is therefore over a variable `n`; only the evaluation tests
//! instantiate, and they stay at `n ≤ 3`.
//!
//! **`forallSubset_of_search` carries an explicit congruence premise.** Two
//! `Nat.Finset`s with the same members are not `Eq` at type `Nat.Finset` (the
//! carrier stores a raw predicate and a bound; `finset.rs`'s module note says
//! so), so a search over `decode`d sets can only conclude about a set the
//! caller supplies if the searched predicate respects membership. Making that
//! obligation a hypothesis rather than hiding it is the honest form: the
//! consumer discharges it once, at its own `P`, and `memB_decode_encode` is
//! exactly the fact the discharge consumes.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::not_b;
use super::helpers::and_right;
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_lt_or_ge, cases_zero_succ};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// The predicate type `Nat → Bool`.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// The searched-property type `Nat.Finset → Bool`.
fn prop_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let fs = finset_ty(d, p);
    let bool_ty = d.bool_ty();
    d.arrow(fs, bool_ty)
}

/// `Nat.Finset.memB s i`.
fn mem_b(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Nat.Finset.memB s` — the membership predicate as a function.
fn mem_b_fn(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s])
}

/// `Nat.Finset.bound s`.
fn fs_bound(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_bound, &[s])
}

/// `Nat.Finset.bitB k i`.
fn bit_b(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_bit_b, &[k, i])
}

/// `Nat.Finset.decode n k`.
fn decode(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.finset_decode, &[n, k])
}

/// `Nat.Finset.encodeFrom f n j`.
fn encode_from(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.finset_encode_from, &[f, n, j])
}

/// `Nat.Finset.encode t n`.
fn encode(d: &mut NatDev<'_>, p: &NatPrelude, t: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.finset_encode, &[t, n])
}

/// `Nat.bit b m`.
fn nat_bit(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.bit, &[b, m])
}

/// `Nat.Finset.allBelow f n`.
fn all_below(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.finset_all_below, &[f, n])
}

/// `pow 2 n` — the number of subsets of `[0, n)`. Never reduced: every
/// statement here is over a variable `n`.
fn two_pow(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    d.pow(two, n)
}

/// `Bool.rec (fun _ => Bool) on_false on_true condition` — `if condition then
/// on_true else on_false` at `Bool`. Per this prelude's per-file convention,
/// each module carries its own copy.
fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `heq : Eq Bool cond true ⊢ Eq Bool (bool_select_bool cond a b) a`.
fn select_bool_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let true_val = d.bool_true();
    let back = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, back)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bool_select_bool cond a b) b`.
fn select_bool_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let back = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, back)
}

/// Congruence from a `Nat` equation into a `Bool`-valued one-hole context:
/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)`. `NatOps::congr` is `Nat`-valued in
/// its conclusion and `graph::bool_congr` takes a `Bool` equation, so neither
/// applies; every bridge in this module (`bit_div_two`, `bit_mod_two`,
/// `succ_add`, `zero_add`) is a `Nat` equation read inside a `Bool` term.
fn nat_to_bool_congr(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// Non-dependent `Or.rec` into a `Prop` goal.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `h : Eq Bool (notB x) true ⊢ Eq Bool x false`.
fn not_b_true_elim(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let tv = d.bool_true();
    let fv = d.bool_false();
    let goal = d.bool_eq(x, fv);
    let is_true = d.bool_eq(x, tv);
    let is_false = d.bool_eq(x, fv);
    let decided = bool_true_or_false(d, &p, x);

    let on_true = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        // `notB x` IS `if x then false else true`, so `x = true` makes it
        // `false`, which contradicts the hypothesis.
        let nb = not_b(d, &p, x);
        let nb_false = select_bool_true(d, &p, x, fv, tv, hx);
        let back = d.bool_symm(nb, fv, nb_false);
        let impossible = d.bool_trans(fv, nb, tv, back, h);
        let absurd = d.false_true_elim(goal, impossible);
        d.lam_fv(hx_fv, is_true, absurd)
    };
    let on_false = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        d.lam_fv(hx_fv, is_false, hx)
    };
    or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided)
}

/// `h : Eq Bool (notB x) false ⊢ Eq Bool x true`.
fn not_b_false_elim(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let tv = d.bool_true();
    let fv = d.bool_false();
    let goal = d.bool_eq(x, tv);
    let is_true = d.bool_eq(x, tv);
    let is_false = d.bool_eq(x, fv);
    let decided = bool_true_or_false(d, &p, x);

    let on_true = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        d.lam_fv(hx_fv, is_true, hx)
    };
    let on_false = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        // `x = false` makes `notB x` be `true`, contradicting `notB x = false`.
        let nb = not_b(d, &p, x);
        let nb_true = select_bool_false(d, &p, x, fv, tv, hx);
        let back = d.bool_symm(nb, fv, h);
        let impossible = d.bool_trans(fv, nb, tv, back, nb_true);
        let absurd = d.false_true_elim(goal, impossible);
        d.lam_fv(hx_fv, is_false, absurd)
    };
    or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided)
}

/// `Exists.{1} Nat.Finset pred`.
fn exists_finset(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let fs = finset_ty(d, p);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[fs, pred])
}

/// `Exists.intro.{1} Nat.Finset pred w h`.
fn exists_intro_finset(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let fs = finset_ty(d, p);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[fs, pred, w, h])
}

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.rec.{1}` over `Nat` into a `Prop` goal.
fn exists_elim_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex_ty = exists_nat(d, p, pred);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, proof])
}

/// `fun i => And (Lt i n) (Eq Bool (f i) false)` — the shape
/// `Nat.Finset.allBelow_false_witness` produces a witness for. Rebuilt here so
/// the `And` component types offered to `and_left`/`and_right` are the ones the
/// existential's own predicate names.
fn below_witness_pred(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let lt = d.lt(i, n);
    let fi = d.apply(f, &[i]);
    let fal = d.bool_false();
    let is_false = d.bool_eq(fi, fal);
    let body = d.const_app(p.logic.and, &[lt, is_false]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun k => notB (P (decode n k))` — the loop body `anySubset` folds.
fn search_body(d: &mut NatDev<'_>, p: &NatPrelude, big_p: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sub = decode(d, &p, n, k);
    let at_sub = d.apply(big_p, &[sub]);
    let body = not_b(d, &p, at_sub);
    d.lam_fv(k_fv, nat, body)
}

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

/// `bitB`, `decode`, `encodeFrom`, `encode` and `anySubset`.
fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fs = finset_ty(d, &p);
    let pty = pred_ty(d);
    let anon = d.anon_name();
    let one = d.level_one();

    // bitB : Nat -> Nat -> Bool := fun k i => beq (testBit k i) 1
    {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tb = d.const_app(p.test_bit, &[k, i]);
        let one_lit = d.num(1);
        let body = d.beq(tb, one_lit);
        let value = {
            let inner = d.lam_fv(i_fv, nat, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_bit_b,
            uparams: vec![],
            ty,
            value,
            // Strictly above `Nat.testBit` (5).
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    // decode : Nat -> Nat -> Nat.Finset := fun n k => Nat.Finset.mk (bitB k) n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pred = d.const_app(p.finset_bit_b, &[k]);
        let body = d.const_app(p.finset_mk, &[pred, n]);
        let value = {
            let inner = d.lam_fv(k_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };
        let ty = {
            let inner = d.arrow(nat, fs);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_decode,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(8),
        })?;
    }

    // encodeFrom : (Nat -> Bool) -> Nat -> Nat -> Nat
    //   := fun f n => Nat.rec.{1} (fun _ => Nat -> Nat)
    //                   (fun _ => 0)
    //                   (fun _ ih => fun j => bit (f j) (ih (succ j)))
    //                   n
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let nat_to_nat = d.arrow(nat, nat);
        let motive = d
            .kernel()
            .lam(anon, nat, nat_to_nat, BinderInfo::Default);
        let base = {
            let zero = d.zero();
            d.kernel().lam(anon, nat, zero, BinderInfo::Default)
        };
        let step = {
            let m_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let tail = d.apply(ih, &[sj]);
            let fj = d.apply(f, &[j]);
            let body = nat_bit(d, &p, fj, tail);
            let with_j = d.lam_fv(j_fv, nat, body);
            let with_ih = d.lam_fv(ih_fv, nat_to_nat, with_j);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let looped = d.apply(rec, &[motive, base, step, n]);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = d.apply(looped, &[j]);
        let value = {
            let with_j = d.lam_fv(j_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_j);
            d.lam_fv(f_fv, pty, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            let with_n = d.arrow(nat, inner);
            d.arrow(pty, with_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_encode_from,
            uparams: vec![],
            ty,
            value,
            // Strictly above `Nat.bit` (3).
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // encode : Nat.Finset -> Nat -> Nat := fun t n => encodeFrom (memB t) n 0
    {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f = mem_b_fn(d, &p, t);
        let zero = d.zero();
        let body = encode_from(d, &p, f, n, zero);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(t_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_encode,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // anySubset : (Nat.Finset -> Bool) -> Nat -> Bool
    //   := fun P n => notB (allBelow (fun k => notB (P (decode n k))) (pow 2 n))
    {
        let big_p_ty = prop_ty(d, &p);
        let big_p_fv = d.fresh_fvar();
        let big_p = d.kernel().fvar(big_p_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let g = search_body(d, &p, big_p, n);
        let range = two_pow(d, n);
        let loop_ = all_below(d, &p, g, range);
        let body = not_b(d, &p, loop_);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(big_p_fv, big_p_ty, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(big_p_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_any_subset,
            uparams: vec![],
            ty,
            value,
            // Above `decode` (8) and `allBelow` (3).
            hint: ReducibilityHint::Regular(10),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The decoder inverts the encoder.
// ---------------------------------------------------------------------------

/// `Eq Bool (bitB (bit b m) 0) b` — the bottom bit of a `Nat.bit` is the bit.
///
/// `bitB k 0` is `beq (testBit k 0) 1`, and `testBit k 0` is `mod k 2` by
/// `refl`, so this is `Nat.bit_mod_two` read through `beq · 1` and then a
/// two-case split on `b` where both leaves are literal `beq` computations.
fn bit_b_at_zero(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    let one_lit = d.num(1);
    let zero = d.zero();
    let bitted = nat_bit(d, &p, b, m);
    let two = d.num(2);
    let modded = d.modulo(bitted, two);
    let selected = d.bool_select_nat(b, one_lit, zero);

    // `mod (bit b m) 2 = bool_select_nat b 1 0`, read inside `beq · 1`.
    let h_mod = d.lemma(p.bit_mod_two, &[b, m]);
    let s1 = nat_to_bool_congr(d, modded, selected, h_mod, &|d, x| {
        let one_lit = d.num(1);
        d.beq(x, one_lit)
    });

    // `beq (bool_select_nat b 1 0) 1 = b`, by cases on `b`.
    let goal2 = {
        let lhs = {
            let one_lit = d.num(1);
            d.beq(selected, one_lit)
        };
        d.bool_eq(lhs, b)
    };
    let tv = d.bool_true();
    let fal = d.bool_false();
    let is_true = d.bool_eq(b, tv);
    let is_false = d.bool_eq(b, fal);
    let decided = bool_true_or_false(d, &p, b);
    let branch = |d: &mut NatDev<'_>, literal: ExprId, hyp_ty: ExprId| -> ExprId {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let back = d.bool_symm(b, literal, h);
        let motive = d.bool_eq_motive(literal, &|d, v| {
            let one_lit = d.num(1);
            let zero = d.zero();
            let sel = d.bool_select_nat(v, one_lit, zero);
            let lhs = {
                let one_lit = d.num(1);
                d.beq(sel, one_lit)
            };
            d.bool_eq(lhs, v)
        });
        let refl_case = d.bool_refl(literal);
        let body = d.bool_transport(literal, motive, refl_case, b, back);
        d.lam_fv(h_fv, hyp_ty, body)
    };
    let on_true = branch(d, tv, is_true);
    let on_false = branch(d, fal, is_false);
    let s2 = or_elim(
        d, &p, is_true, is_false, goal2, on_true, on_false, decided,
    );

    let lhs_mid = {
        let one_lit = d.num(1);
        d.beq(modded, one_lit)
    };
    let rhs_mid = {
        let one_lit = d.num(1);
        d.beq(selected, one_lit)
    };
    d.bool_trans(lhs_mid, rhs_mid, b, s1, s2)
}

/// `Nat.Finset.bitB_encodeFrom : ∀ f n j i, Lt i n →
/// Eq Bool (bitB (encodeFrom f n j) i) (f (add j i))`.
///
/// The exhaustiveness half, at the level of raw predicates: the code
/// `encodeFrom f n j` stores `f j, f (j+1), …, f (j+n-1)` in bits `0 … n-1`.
/// Induction on the WIDTH `n` with the start index `j` and the queried bit `i`
/// both generalised inside the motive — `j` has to vary because the recursion
/// walks it upward, and `i` has to vary because the step splits on whether the
/// queried bit is the one just written.
fn declare_bit_b_encode_from(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    // `∀ j i, Lt i n → bitB (encodeFrom f n j) i = f (j + i)`, at a bound `n`.
    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, n);
        let code = encode_from(d, &p, f, n, j);
        let lhs = bit_b(d, &p, code, i);
        let shifted = d.add(j, i);
        let rhs = d.apply(f, &[shifted]);
        let concl = d.bool_eq(lhs, rhs);
        let with_hi = d.arrow(hi_ty, concl);
        let with_i = d.pi_fv(i_fv, nat, with_hi);
        d.pi_fv(j_fv, nat, with_i)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // Nothing is below `0`, so every index is refuted.
            let zero = d.zero();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = d.lt(i, zero);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let refuted = d.lemma(p.not_lt_zero, &[i, hi]);
            let goal = {
                let code = encode_from(d, &p, f, zero, j);
                let lhs = bit_b(d, &p, code, i);
                let shifted = d.add(j, i);
                let rhs = d.apply(f, &[shifted]);
                d.bool_eq(lhs, rhs)
            };
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let anon = d.anon_name();
            let false_motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let level_zero = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let absurd = d.apply(rec, &[false_motive, refuted]);
            let with_hi = d.lam_fv(hi_fv, hi_ty, absurd);
            let with_i = d.lam_fv(i_fv, nat, with_hi);
            d.lam_fv(j_fv, nat, with_i)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);

            // The code at width `succ m` IS `bit (f j) (encodeFrom f m (succ j))`.
            let sj = d.succ(j);
            let tail = encode_from(d, &p, f, m, sj);
            let fj = d.apply(f, &[j]);

            let motive_i = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
                let hi_ty = d.lt(i, sm);
                let code = encode_from(d, &p, f, sm, j);
                let lhs = bit_b(d, &p, code, i);
                let shifted = d.add(j, i);
                let rhs = d.apply(f, &[shifted]);
                let concl = d.bool_eq(lhs, rhs);
                d.arrow(hi_ty, concl)
            };

            let at_zero = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let hi_ty = d.lt(zero, sm);
                let hi_fv = d.fresh_fvar();
                // `add j 0` IS `j` (`Nat.add` recurses on the right), so the
                // bottom-bit law closes this leaf outright.
                let proof = bit_b_at_zero(d, &p, fj, tail);
                d.lam_fv(hi_fv, hi_ty, proof)
            };

            let at_succ = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
                let si = d.succ(i);
                let hi_ty = d.lt(si, sm);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);

                // `Lt (succ i) (succ m)` IS `Le (succ (succ i)) (succ m)`.
                let shorter = d.lemma(p.le_of_succ_le_succ, &[si, m, hi]);

                // Step A: peel the written bit.
                // `bitB (bit b M) (succ i)` IS `beq (testBit (div (bit b M) 2) i) 1`.
                let bitted = nat_bit(d, &p, fj, tail);
                let two = d.num(2);
                let halved = d.div(bitted, two);
                let h_div = d.lemma(p.bit_div_two, &[fj, tail]);
                let step_a = nat_to_bool_congr(d, halved, tail, h_div, &|d, x| {
                    let tb = d.const_app(p.test_bit, &[x, i]);
                    let one_lit = d.num(1);
                    d.beq(tb, one_lit)
                });

                // Step B: the induction hypothesis, at the shifted start.
                let step_b = d.apply(ih, &[sj, i, shorter]);

                // Step C: `f (succ j + i) = f (j + succ i)`; the right side is
                // `f (succ (j + i))` by iota, and `succ_add` supplies the left.
                let lhs_arg = d.add(sj, i);
                let rhs_arg = {
                    let inner = d.add(j, i);
                    d.succ(inner)
                };
                let h_succ_add = d.lemma(p.succ_add, &[j, i]);
                let step_c = nat_to_bool_congr(d, lhs_arg, rhs_arg, h_succ_add, &|d, x| {
                    d.apply(f, &[x])
                });

                let a_lhs = bit_b(d, &p, bitted, si);
                let a_rhs = bit_b(d, &p, tail, i);
                let b_rhs = d.apply(f, &[lhs_arg]);
                let c_rhs = d.apply(f, &[rhs_arg]);
                let ab = d.bool_trans(a_lhs, a_rhs, b_rhs, step_a, step_b);
                let proof = d.bool_trans(a_lhs, b_rhs, c_rhs, ab, step_c);
                d.lam_fv(hi_fv, hi_ty, proof)
            };

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let cased = cases_zero_succ(d, i, &motive_i, &at_zero, &at_succ);
            let with_i = d.lam_fv(i_fv, nat, cased);
            d.lam_fv(j_fv, nat, with_i)
        },
        n,
    );

    let ty = {
        let concl = motive_at(d, n);
        let with_n = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(f_fv, pty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, pty, with_n)
    };
    d.declare_theorem(p.finset_bit_b_encode_from, ty, value)
}

/// `Nat.Finset.encodeFrom_lt_pow : ∀ f n j, Lt (encodeFrom f n j) (pow 2 n)`.
///
/// The search range is right. Induction on the width: at `0` the code is `0`
/// and `pow 2 0` is `1`; at `succ m` the code is `bit (f j) M` with
/// `M < pow 2 m`, and `Nat.bit_lt_bit` is stated for arbitrary bits on both
/// sides, so `bit (f j) M < bit false (pow 2 m) = 2 * pow 2 m = pow 2 (succ m)`
/// with no case split on `f j` at all.
fn declare_encode_from_lt_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let code = encode_from(d, &p, f, n, j);
        let range = two_pow(d, n);
        let concl = d.lt(code, range);
        d.pi_fv(j_fv, nat, concl)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let zero = d.zero();
            let j_fv = d.fresh_fvar();
            let one_lit = d.num(1);
            let base = d.zero_lt_succ(zero);
            let two = d.num(2);
            let h_pow = d.lemma(p.pow_zero, &[two]);
            let range = two_pow(d, zero);
            let back = d.symm(range, one_lit, h_pow);
            let motive = d.eq_motive(one_lit, &|d, x| {
                let zero = d.zero();
                d.lt(zero, x)
            });
            let proof = d.transport(one_lit, motive, base, range, back);
            d.lam_fv(j_fv, nat, proof)
        },
        &|d, m, ih| {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let sj = d.succ(j);
            let tail = encode_from(d, &p, f, m, sj);
            let fj = d.apply(f, &[j]);
            let smaller = d.apply(ih, &[sj]);

            let range_m = two_pow(d, m);
            let fal = d.bool_false();
            let strict = d.lemma(p.bit_lt_bit, &[tail, range_m, fj, fal, smaller]);

            // `bit false (pow 2 m) = 2 * pow 2 m = pow 2 (succ m)`.
            let doubled = {
                let two = d.num(2);
                d.mul(two, range_m)
            };
            let h_bit_false = d.lemma(p.bit_false, &[range_m]);
            let sm = d.succ(m);
            let range_sm = two_pow(d, sm);
            let two = d.num(2);
            let h_pow_succ = d.lemma(p.pow_succ, &[two, m]);
            let swapped = d.mul(range_m, two);
            let h_comm = d.lemma(p.mul_comm, &[range_m, two]);
            let h_forward = d.trans(range_sm, swapped, doubled, h_pow_succ, h_comm);
            let h_back = d.symm(range_sm, doubled, h_forward);
            let bitted_range = nat_bit(d, &p, fal, range_m);
            let h_chain = d.trans(bitted_range, doubled, range_sm, h_bit_false, h_back);

            let bitted = nat_bit(d, &p, fj, tail);
            let motive = d.eq_motive(bitted_range, &|d, x| d.lt(bitted, x));
            let proof = d.transport(bitted_range, motive, strict, range_sm, h_chain);
            d.lam_fv(j_fv, nat, proof)
        },
        n,
    );

    let ty = {
        let concl = motive_at(d, n);
        let with_n = d.pi_fv(n_fv, nat, concl);
        d.pi_fv(f_fv, pty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, pty, with_n)
    };
    d.declare_theorem(p.finset_encode_from_lt_pow, ty, value)
}

/// `Nat.Finset.memB_decode_encode : ∀ t n i, Le (bound t) n →
/// Eq Bool (memB (decode n (encode t n)) i) (memB t i)`.
///
/// **Exhaustiveness**, and the lemma the reflection lemma's `false` branch
/// consumes. Stated at EVERY index rather than only below `n`: above the bound
/// both sides are `false`, because `memB` truncates inside its own definition
/// (ADR-1577), so the two sets agree extensionally and not merely on the
/// searched window. That is what lets `forallSubset_of_search` discharge a
/// caller's congruence premise with no side condition on the index.
fn declare_mem_b_decode_encode(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let bound_t = fs_bound(d, &p, t);
    let hb_ty = d.le(bound_t, n);

    let code = encode(d, &p, t, n);
    let sub = decode(d, &p, n, code);

    let motive = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
        let lhs = mem_b(d, &p, sub, i);
        let rhs = mem_b(d, &p, t, i);
        d.bool_eq(lhs, rhs)
    };

    let small = |d: &mut NatDev<'_>, i: ExprId, hlt: ExprId| -> ExprId {
        // `bound (decode n k)` IS `n`, so `hlt : Lt i n` is already the premise
        // `memB_of_lt` wants, and `pred (decode n k)` IS `bitB k`.
        let unfolded = d.lemma(p.finset_mem_b_of_lt, &[sub, i, hlt]);
        let lhs = mem_b(d, &p, sub, i);
        let mid = bit_b(d, &p, code, i);

        // `bitB (encodeFrom (memB t) n 0) i = memB t (0 + i)`.
        let f = mem_b_fn(d, &p, t);
        let zero = d.zero();
        let decoded = d.lemma(p.finset_bit_b_encode_from, &[f, n, zero, i, hlt]);
        let shifted = d.add(zero, i);
        let rhs_shifted = mem_b(d, &p, t, shifted);
        let h_zero_add = d.lemma(p.zero_add, &[i]);
        let fixed = nat_to_bool_congr(d, shifted, i, h_zero_add, &|d, x| mem_b(d, &p, t, x));
        let rhs = mem_b(d, &p, t, i);
        let half = d.bool_trans(mid, rhs_shifted, rhs, decoded, fixed);
        d.bool_trans(lhs, mid, rhs, unfolded, half)
    };

    let big = |d: &mut NatDev<'_>, i: ExprId, hge: ExprId| -> ExprId {
        // `bound (decode n k)` IS `n`, so `hge : Le n i` applies directly.
        let left_false = d.lemma(p.finset_mem_b_of_bound_le, &[sub, i, hge]);
        let widened = d.lemma(p.le_trans, &[bound_t, n, i, hb, hge]);
        let right_false = d.lemma(p.finset_mem_b_of_bound_le, &[t, i, widened]);
        let lhs = mem_b(d, &p, sub, i);
        let rhs = mem_b(d, &p, t, i);
        let fal = d.bool_false();
        let back = d.bool_symm(rhs, fal, right_false);
        d.bool_trans(lhs, fal, rhs, left_false, back)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let cased = cases_lt_or_ge(d, &p, i, n, &motive, &small, &big);

    let ty = {
        let concl = motive(d, i);
        let with_hb = d.arrow(hb_ty, concl);
        let with_i = d.pi_fv(i_fv, nat, with_hb);
        let with_n = d.pi_fv(n_fv, nat, with_i);
        d.pi_fv(t_fv, fs, with_n)
    };
    let value = {
        let with_hb = d.lam_fv(hb_fv, hb_ty, cased);
        let with_i = d.lam_fv(i_fv, nat, with_hb);
        let with_n = d.lam_fv(n_fv, nat, with_i);
        d.lam_fv(t_fv, fs, with_n)
    };
    d.declare_theorem(p.finset_mem_b_decode_encode, ty, value)
}

// ---------------------------------------------------------------------------
// The reflection lemma, in both polarities.
// ---------------------------------------------------------------------------

/// `Nat.Finset.existsSubset_of_search : ∀ P n, Eq Bool (anySubset P n) true →
/// Exists (fun t => And (Eq Nat (bound t) n) (Eq Bool (P t) true))`.
///
/// The SEARCH direction. A `true` verdict is a `false` `allBelow`, and
/// `Nat.Finset.allBelow_false_witness` turns that into a code `k`; `decode n k`
/// is the subset, and its bound is `n` by `refl` because `decode` builds it.
/// Nothing about the search is trusted: the kernel recomputes `P` at the
/// decoded set.
fn declare_exists_subset(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let big_p_ty = prop_ty(d, &p);

    let big_p_fv = d.fresh_fvar();
    let big_p = d.kernel().fvar(big_p_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // The existential's predicate over `Nat.Finset`.
    let result_pred = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let bound_t = fs_bound(d, &p, t);
        let bound_eq = d.eq(bound_t, n);
        let at_t = d.apply(big_p, &[t]);
        let tv = d.bool_true();
        let val_eq = d.bool_eq(at_t, tv);
        let body = d.const_app(p.logic.and, &[bound_eq, val_eq]);
        d.lam_fv(t_fv, fs, body)
    };
    let goal = exists_finset(d, &p, result_pred);

    let search = d.const_app(p.finset_any_subset, &[big_p, n]);
    let tv = d.bool_true();
    let hyp_ty = d.bool_eq(search, tv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let g = search_body(d, &p, big_p, n);
    let range = two_pow(d, n);
    let loop_ = all_below(d, &p, g, range);
    let loop_false = not_b_true_elim(d, &p, loop_, h);
    let found = d.lemma(p.finset_all_below_false_witness, &[g, range, loop_false]);

    let witness_pred = below_witness_pred(d, &p, g, range);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_ty = d.lt(k, range);
        let gk = d.apply(g, &[k]);
        let fal = d.bool_false();
        let gk_false = d.bool_eq(gk, fal);
        let hw_ty = d.const_app(p.logic.and, &[lt_ty, gk_false]);
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let negated = and_right(d, lt_ty, gk_false, hw);
        let sub = decode(d, &p, n, k);
        let at_sub = d.apply(big_p, &[sub]);
        // `g k` beta-reduces to `notB (P (decode n k))`; the kernel identifies
        // the two, so the elimination applies at the reduced form.
        let holds = not_b_false_elim(d, &p, at_sub, negated);

        let bound_sub = fs_bound(d, &p, sub);
        let bound_eq = d.eq(bound_sub, n);
        let bound_pf = d.refl(n);
        let tv2 = d.bool_true();
        let val_eq = d.bool_eq(at_sub, tv2);
        let pair = d.const_app(p.logic.and_intro, &[bound_eq, val_eq, bound_pf, holds]);
        let intro = exists_intro_finset(d, &p, result_pred, sub, pair);
        let with_hw = d.lam_fv(hw_fv, hw_ty, intro);
        d.lam_fv(k_fv, nat, with_hw)
    };
    let proof = exists_elim_nat(d, &p, witness_pred, goal, minor, found);

    let ty = {
        let with_h = d.arrow(hyp_ty, goal);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(big_p_fv, big_p_ty, with_n)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(big_p_fv, big_p_ty, with_n)
    };
    d.declare_theorem(p.finset_exists_subset_of_search, ty, value)
}

/// `Nat.Finset.forallSubset_of_search : ∀ P n,
/// (∀ u v, (∀ i, Eq Bool (memB u i) (memB v i)) → Eq Bool (P u) (P v)) →
/// Eq Bool (anySubset P n) false → ∀ t, Le (bound t) n → Eq Bool (P t) false`.
///
/// The REFUTATION direction, and the one Hall's sufficiency actually consumes:
/// an exhausted search is a proof that NO subset of the searched width has the
/// property. The congruence premise is what carries the verdict from the
/// enumerated representative `decode n (encode t n)` to the caller's own `t`;
/// see the module note for why it cannot be dropped.
fn declare_forall_subset(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let big_p_ty = prop_ty(d, &p);

    let big_p_fv = d.fresh_fvar();
    let big_p = d.kernel().fvar(big_p_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `∀ u v, (∀ i, memB u i = memB v i) → P u = P v`.
    let cong_ty = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let agree = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lhs = mem_b(d, &p, u, i);
            let rhs = mem_b(d, &p, v, i);
            let body = d.bool_eq(lhs, rhs);
            d.pi_fv(i_fv, nat, body)
        };
        let at_u = d.apply(big_p, &[u]);
        let at_v = d.apply(big_p, &[v]);
        let concl = d.bool_eq(at_u, at_v);
        let with_agree = d.arrow(agree, concl);
        let with_v = d.pi_fv(v_fv, fs, with_agree);
        d.pi_fv(u_fv, fs, with_v)
    };
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let search = d.const_app(p.finset_any_subset, &[big_p, n]);
    let fal = d.bool_false();
    let hyp_ty = d.bool_eq(search, fal);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let bound_t = fs_bound(d, &p, t);
    let hb_ty = d.le(bound_t, n);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let g = search_body(d, &p, big_p, n);
    let range = two_pow(d, n);
    let loop_ = all_below(d, &p, g, range);
    let loop_true = not_b_false_elim(d, &p, loop_, h);
    let pointwise = d.lemma(p.finset_all_below_true_at, &[g, range, loop_true]);

    let f = mem_b_fn(d, &p, t);
    let zero = d.zero();
    let code = encode(d, &p, t, n);
    // `encode t n` IS `encodeFrom (memB t) n 0`, so the bound applies directly.
    let in_range = d.lemma(p.finset_encode_from_lt_pow, &[f, n, zero]);
    let at_code = d.apply(pointwise, &[code, in_range]);

    let sub = decode(d, &p, n, code);
    let at_sub = d.apply(big_p, &[sub]);
    let sub_false = not_b_true_elim(d, &p, at_sub, at_code);

    let agree = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = d.lemma(p.finset_mem_b_decode_encode, &[t, n, i, hb]);
        d.lam_fv(i_fv, nat, body)
    };
    let bridge = d.apply(hc, &[sub, t, agree]);
    let at_t = d.apply(big_p, &[t]);
    let back = d.bool_symm(at_sub, at_t, bridge);
    let proof = d.bool_trans(at_t, at_sub, fal, back, sub_false);

    let concl = d.bool_eq(at_t, fal);
    let ty = {
        let with_hb = d.arrow(hb_ty, concl);
        let with_t = d.pi_fv(t_fv, fs, with_hb);
        let with_h = d.arrow(hyp_ty, with_t);
        let with_hc = d.arrow(cong_ty, with_h);
        let with_n = d.pi_fv(n_fv, nat, with_hc);
        d.pi_fv(big_p_fv, big_p_ty, with_n)
    };
    let value = {
        let with_hb = d.lam_fv(hb_fv, hb_ty, proof);
        let with_t = d.lam_fv(t_fv, fs, with_hb);
        let with_h = d.lam_fv(h_fv, hyp_ty, with_t);
        let with_hc = d.lam_fv(hc_fv, cong_ty, with_h);
        let with_n = d.lam_fv(n_fv, nat, with_hc);
        d.lam_fv(big_p_fv, big_p_ty, with_n)
    };
    d.declare_theorem(p.finset_forall_subset_of_search, ty, value)
}

/// Declare the subset-search primitive.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_subset_search_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_definitions(d, p)?;
    declare_bit_b_encode_from(d, p)?;
    declare_encode_from_lt_pow(d, p)?;
    declare_mem_b_decode_encode(d, p)?;
    declare_exists_subset(d, p)?;
    declare_forall_subset(d, p)?;
    Ok(())
}
