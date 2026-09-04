//! `Nat.Rado` — Rado numbers as a *defined object*, and the search-to-kernel
//! route demonstrated end to end on one instance (ADR-1596).
//!
//! # What was missing
//!
//! The fact ledger holds two four-colour Rado numbers with
//! `epistemic_status: computed` — `R_4(5(x-y) = 3z) = 625`
//! (`artifacts/facts/F-rado-r4-a5-b3.json`) and `R_4(5(x-y) = 4z) = 741`
//! (`F-rado-r4-a5-b4.json`). Both carry search certificates that this
//! repository's own DRAT checker re-derived. Neither is a theorem *about*
//! anything, because until this module nothing in the kernel said what a Rado
//! number **is**: the values were numbers with certificates.
//!
//! This module states the object. Everything below is parameterized over the
//! bound `n`; see "The unary-numeral constraint" for why that is not a
//! stylistic choice.
//!
//! ```text
//! Nat.Rado.Sol a b x y z        := a * x = a * y + b * z   -- a(x-y) = bz, subtraction-free
//! Nat.Rado.IsColouring k n c    := ∀ i, 1 <= i <= n → c i < k
//! Nat.Rado.MonoSol a b n c      := ∃ x y z, all in [1,n] ∧ Sol a b x y z ∧ c x = c y ∧ c y = c z
//! Nat.Rado.Arrows a b k n       := ∀ c, IsColouring k n c → MonoSol a b n c
//! Nat.Rado.IsRadoNumber a b k n := Arrows a b k n ∧ ∀ m < n, ¬ Arrows a b k m
//! ```
//!
//! `Sol` is stated **subtraction-free**, `a * x = a * y + b * z`, not
//! `a * (x - y) = b * z`. `Nat` subtraction truncates, so the second form is
//! true for every `x <= y` with `z = 0` and would silently admit degenerate
//! "solutions"; the first is the equation Chang-De Loera-Wesley actually study
//! over the positive integers, and it is the same shape
//! `tests/rado_sharp_factorization.rs` already uses for the paper's `thm:sharp`.
//!
//! # The unary-numeral constraint, and how the statements work with it
//!
//! Every `Nat` numeral in this kernel is unary: `625` is `succ` applied 625
//! times to `zero`, and cost is superlinear in the largest magnitude *formed*
//! (`docs/contributor-guide/prelude-build-cost.md`; `decide`'s own
//! `MAX_MAGNITUDE` is 30). So the sentence "the four-colour Rado number of
//! 5(x-y) = 3z is 625" cannot be *written* as a kernel statement at the cost
//! this repository is willing to pay — not because the logic is too weak, but
//! because the numeral is too big.
//!
//! Every declaration here is therefore stated with `n` (and `a`, `b`, `k`) as
//! **variables**. `Nat.Rado.isRadoNumber_of_succ` is the load-bearing one: it
//! takes the two halves a search actually produces — an upper bound at `succ m`
//! and a refutation at `m` — and returns the leastness statement, for *any*
//! `m`. A certificate for `a = 5, b = 3, k = 4, m = 624` would instantiate it
//! without any lemma here being restated; what it could not do is *form*
//! `succ^625 zero`. That residue is the finding, and ADR-1596 states it
//! precisely.
//!
//! # `Nat.Finset` is where the colouring certificate lives
//!
//! A `k = 2` colouring of `[1,n]` **is** a finite set: the class of colour 1.
//! `Nat.Rado.ofFinset s` is the indicator of `Nat.Finset.memB s`, and
//! `Nat.Rado.isColouring_ofFinset` says every `Nat.Finset` is a valid
//! 2-colouring of every range, with no side condition. So the lower-bound
//! certificate a search emits (a subset of `[1,n]`) is transcribed into the
//! kernel as a `Nat.Finset` and needs no well-formedness proof of its own.
//!
//! # The instance that closes the loop
//!
//! `R_2(x = y + z) = 5` — the two-colour Schur number in Rado form, `a = b = 1`.
//! Both halves are discharged in-kernel and both are *reconstructed from a
//! search*, not hand-written:
//!
//! * **Upper bound** ([`declare_schur_upper`]): [`search_witness`] enumerates
//!   the `2^5` colour assignments to `[1,5]` and, for each, finds the
//!   monochromatic triple. The proof term is the matching decision tree over
//!   `Nat.lt_two_cases`, one `Or.elim` per index, with that triple at the leaf.
//!   If any assignment had no triple the builder returns `None` and the
//!   declaration is never attempted — the exit status depends on the finding.
//! * **Lower bound** ([`declare_schur_lower`]): [`search_avoiding_set`]
//!   enumerates the `2^4` subsets of `[1,4]` and returns one whose induced
//!   2-colouring has no monochromatic solution — `{2,3}`, i.e. `{1,4}/{2,3}`,
//!   which is the unique such partition up to swapping the colours. The
//!   refutation is by *reflection*: a `Bool` triple loop over
//!   `Nat.Finset.allBelow` is reduced to `true` by the kernel itself, and
//!   `Nat.Finset.allBelow_true_at` reads it back at the three existential
//!   witnesses. That is this project's thesis in one proof term — untrusted
//!   search picks the set, trusted computation checks it.
//!
//! `Nat.Rado.schur_two : IsRadoNumber 1 1 2 5` is the two halves joined by
//! `isRadoNumber_of_succ`, and it is the first Rado number in this repository
//! that is a theorem rather than a certificate.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// The instance this module closes: `a`, `b`, the colour count, and the bound.
/// `a = b = 1` is `x = y + z`, the two-colour Schur equation in Rado form.
const SCHUR_A: u32 = 1;
const SCHUR_B: u32 = 1;
const SCHUR_N: u32 = 5;

// ---------------------------------------------------------------------------
// The untrusted half: search.
//
// Nothing below is trusted. Each routine returns a certificate that the kernel
// then re-checks; a `None` means the builder declares nothing at all.
// ---------------------------------------------------------------------------

/// Does `(x, y, z)` solve `a * x = a * y + b * z`?
pub(super) fn is_solution(a: u32, b: u32, x: u32, y: u32, z: u32) -> bool {
    a * x == a * y + b * z
}

/// The monochromatic triple in `[1, n]` for the colour assignment
/// `colours[i - 1]`, or `None` if this assignment avoids one.
///
/// Enumerated in a fixed order so the emitted proof term is deterministic.
pub(super) fn search_witness(a: u32, b: u32, n: u32, colours: &[u32]) -> Option<(u32, u32, u32)> {
    for x in 1..=n {
        for y in 1..=n {
            for z in 1..=n {
                if is_solution(a, b, x, y, z)
                    && colours[(x - 1) as usize] == colours[(y - 1) as usize]
                    && colours[(y - 1) as usize] == colours[(z - 1) as usize]
                {
                    return Some((x, y, z));
                }
            }
        }
    }
    None
}

/// Every `k = 2` colour assignment to `[1, n]`, as a bit pattern.
fn assignment(n: u32, bits: u32) -> Vec<u32> {
    (0..n).map(|i| (bits >> i) & 1).collect()
}

/// A subset of `[1, n]` whose indicator 2-colouring has no monochromatic
/// solution, or `None` if every subset admits one (which is exactly the
/// statement that `n` is at or above the Rado number).
///
/// Returned as the sorted member list, which is what the `Nat.Finset`
/// transcription needs.
pub(super) fn search_avoiding_set(a: u32, b: u32, n: u32) -> Option<Vec<u32>> {
    for bits in 0..(1u32 << n) {
        let colours = assignment(n, bits);
        if search_witness(a, b, n, &colours).is_none() {
            return Some(
                (1..=n)
                    .filter(|&i| colours[(i - 1) as usize] == 1)
                    .collect(),
            );
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Prop`.
fn prop(d: &mut NatDev<'_>) -> ExprId {
    d.kernel().sort_zero()
}

/// The colouring carrier `Nat -> Nat`.
fn colour_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// `Bool.rec.{1} (fun _ => Bool) on_false on_true condition` — a `Bool`-valued
/// `if`.
fn select_bool(
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

/// `Nat.le lo hi` at two concrete magnitudes: `le.step` applied `hi - lo` times
/// to `le.refl lo`. Panics on `lo > hi`, which is a builder bug rather than a
/// kernel rejection.
fn le_proof(d: &mut NatDev<'_>, p: &NatPrelude, lo: u32, hi: u32) -> ExprId {
    assert!(lo <= hi, "le_proof: {lo} > {hi}");
    let lo_e = d.num(lo);
    let mut proof = d.const_app(p.le_refl, &[lo_e]);
    for step in lo..hi {
        let from = d.num(step);
        proof = d.const_app(p.le_step, &[lo_e, from, proof]);
    }
    proof
}

/// `Nat.lt lo hi` at concrete magnitudes — `Lt a b` is `Le (succ a) b`.
fn lt_proof(d: &mut NatDev<'_>, p: &NatPrelude, lo: u32, hi: u32) -> ExprId {
    le_proof(d, p, lo + 1, hi)
}

/// `Nat.inClosedInterval 1 n i` — membership in `[1, n]`, the range every
/// statement here quantifies over.
fn in_range(d: &mut NatDev<'_>, n: ExprId, i: ExprId) -> ExprId {
    let one = d.num(1);
    d.in_closed_interval(one, n, i)
}

/// `And.intro` of the two halves of `in_range` at concrete magnitudes.
fn in_range_proof(d: &mut NatDev<'_>, p: &NatPrelude, n: u32, i: u32) -> ExprId {
    let one = d.num(1);
    let i_e = d.num(i);
    let n_e = d.num(n);
    let lower_ty = d.le(one, i_e);
    let upper_ty = d.le(i_e, n_e);
    let lower = le_proof(d, p, 1, i);
    let upper = le_proof(d, p, i, n);
    d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper])
}

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.intro.{1} Nat pred w h`.
fn exists_intro_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, w, h])
}

/// `Exists.rec.{1}` into a `Prop` goal.
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

/// The right-nested `And` chain a `MonoSol` witness carries, at the three
/// witnesses.
fn mono_body(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let rx = in_range(d, n, x);
    let ry = in_range(d, n, y);
    let rz = in_range(d, n, z);
    let sol = d.const_app(p.rado_sol, &[a, b, x, y, z]);
    let cx = d.apply(c, &[x]);
    let cy = d.apply(c, &[y]);
    let cz = d.apply(c, &[z]);
    let exy = d.eq(cx, cy);
    let eyz = d.eq(cy, cz);
    let tail = d.const_app(p.logic.and, &[exy, eyz]);
    let with_sol = d.const_app(p.logic.and, &[sol, tail]);
    let with_z = d.const_app(p.logic.and, &[rz, with_sol]);
    let with_y = d.const_app(p.logic.and, &[ry, with_z]);
    d.const_app(p.logic.and, &[rx, with_y])
}

/// `fun z => <mono_body at x y z>`.
fn mono_pred_z(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let body = mono_body(d, p, a, b, n, c, x, y, z);
    d.lam_fv(z_fv, nat, body)
}

/// `fun y => Exists (mono_pred_z …)`.
fn mono_pred_y(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let inner = mono_pred_z(d, p, a, b, n, c, x, y);
    let body = exists_nat(d, p, inner);
    d.lam_fv(y_fv, nat, body)
}

/// `fun x => Exists (mono_pred_y …)`.
fn mono_pred_x(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let inner = mono_pred_y(d, p, a, b, n, c, x);
    let body = exists_nat(d, p, inner);
    d.lam_fv(x_fv, nat, body)
}

/// The unfolded `MonoSol a b n c`.
fn mono_sol_unfolded(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
) -> ExprId {
    let pred = mono_pred_x(d, p, a, b, n, c);
    exists_nat(d, p, pred)
}

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop_ty = prop(d);
    let cty = colour_ty(d);

    // Sol a b x y z := a * x = a * y + b * z
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let lhs = d.mul(a, x);
        let ay = d.mul(a, y);
        let bz = d.mul(b, z);
        let rhs = d.add(ay, bz);
        let body = d.eq(lhs, rhs);
        let value = {
            let l5 = d.lam_fv(z_fv, nat, body);
            let l4 = d.lam_fv(y_fv, nat, l5);
            let l3 = d.lam_fv(x_fv, nat, l4);
            let l2 = d.lam_fv(b_fv, nat, l3);
            d.lam_fv(a_fv, nat, l2)
        };
        let ty = {
            let t5 = d.arrow(nat, prop_ty);
            let t4 = d.arrow(nat, t5);
            let t3 = d.arrow(nat, t4);
            let t2 = d.arrow(nat, t3);
            d.arrow(nat, t2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_sol,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // IsColouring k n c := ∀ i, inClosedInterval 1 n i → c i < k
    {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let concl = d.lt(ci, k);
        let hyp = in_range(d, n, i);
        let step = d.arrow(hyp, concl);
        let body = d.pi_fv(i_fv, nat, step);
        let value = {
            let l3 = d.lam_fv(c_fv, cty, body);
            let l2 = d.lam_fv(n_fv, nat, l3);
            d.lam_fv(k_fv, nat, l2)
        };
        let ty = {
            let t3 = d.arrow(cty, prop_ty);
            let t2 = d.arrow(nat, t3);
            d.arrow(nat, t2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_is_colouring,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // MonoSol a b n c := ∃ x y z, …
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = mono_sol_unfolded(d, &p, a, b, n, c);
        let value = {
            let l4 = d.lam_fv(c_fv, cty, body);
            let l3 = d.lam_fv(n_fv, nat, l4);
            let l2 = d.lam_fv(b_fv, nat, l3);
            d.lam_fv(a_fv, nat, l2)
        };
        let ty = {
            let t4 = d.arrow(cty, prop_ty);
            let t3 = d.arrow(nat, t4);
            let t2 = d.arrow(nat, t3);
            d.arrow(nat, t2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_mono_sol,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // Arrows a b k n := ∀ c, IsColouring k n c → MonoSol a b n c
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hyp = d.const_app(p.rado_is_colouring, &[k, n, c]);
        let concl = d.const_app(p.rado_mono_sol, &[a, b, n, c]);
        let step = d.arrow(hyp, concl);
        let body = d.pi_fv(c_fv, cty, step);
        let value = {
            let l4 = d.lam_fv(n_fv, nat, body);
            let l3 = d.lam_fv(k_fv, nat, l4);
            let l2 = d.lam_fv(b_fv, nat, l3);
            d.lam_fv(a_fv, nat, l2)
        };
        let ty = {
            let t4 = d.arrow(nat, prop_ty);
            let t3 = d.arrow(nat, t4);
            let t2 = d.arrow(nat, t3);
            d.arrow(nat, t2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_arrows,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // IsRadoNumber a b k n := Arrows a b k n ∧ ∀ m, m < n → Arrows a b k m → False
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let upper = d.const_app(p.rado_arrows, &[a, b, k, n]);
        let least = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let arrows_m = d.const_app(p.rado_arrows, &[a, b, k, m]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let inner = d.arrow(arrows_m, false_ty);
            let lt = d.lt(m, n);
            let step = d.arrow(lt, inner);
            d.pi_fv(m_fv, nat, step)
        };
        let body = d.const_app(p.logic.and, &[upper, least]);
        let value = {
            let l4 = d.lam_fv(n_fv, nat, body);
            let l3 = d.lam_fv(k_fv, nat, l4);
            let l2 = d.lam_fv(b_fv, nat, l3);
            d.lam_fv(a_fv, nat, l2)
        };
        let ty = {
            let t4 = d.arrow(nat, prop_ty);
            let t3 = d.arrow(nat, t4);
            let t2 = d.arrow(nat, t3);
            d.arrow(nat, t2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_is_rado_number,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `ofFinset` — a finite set IS a two-colouring.
// ---------------------------------------------------------------------------

/// `Nat.Rado.ofFinset s i` — `1` when `i` is a member of `s`, `0` otherwise.
fn of_finset_at(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    let mem = d.const_app(p.finset_mem_b, &[s, i]);
    let one = d.num(1);
    let zero = d.num(0);
    d.bool_select_nat(mem, one, zero)
}

fn declare_of_finset(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    // ofFinset : Nat.Finset -> Nat -> Nat
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let body = of_finset_at(d, &p, s, i);
        let value = {
            let inner = d.lam_fv(i_fv, nat, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.rado_of_finset,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    // Nat.boolSelect_lt : ∀ (t f k : Nat) (b : Bool), t < k → f < k →
    //                     Bool.rec (fun _ => Nat) f t b < k
    {
        let bool_ty = d.bool_ty();
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ht_ty = d.lt(t, k);
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let hf_ty = d.lt(f, k);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);

        let selected = d.bool_select_nat(b, t, f);
        let concl = d.lt(selected, k);

        let motive = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let at_v = d.bool_select_nat(v, t, f);
            let body = d.lt(at_v, k);
            d.lam_fv(v_fv, bool_ty, body)
        };
        let zero_level = d.kernel().level_zero();
        let rec = d.kernel().const_(p.logic.bool_rec, vec![zero_level]);
        let body = d.apply(rec, &[motive, hf, ht, b]);

        let ty = {
            let s6 = d.arrow(hf_ty, concl);
            let s5 = d.arrow(ht_ty, s6);
            let s4 = d.pi_fv(b_fv, bool_ty, s5);
            let s3 = d.pi_fv(k_fv, nat, s4);
            let s2 = d.pi_fv(f_fv, nat, s3);
            d.pi_fv(t_fv, nat, s2)
        };
        let value = {
            let s6 = d.lam_fv(hf_fv, hf_ty, body);
            let s5 = d.lam_fv(ht_fv, ht_ty, s6);
            let s4 = d.lam_fv(b_fv, bool_ty, s5);
            let s3 = d.lam_fv(k_fv, nat, s4);
            let s2 = d.lam_fv(f_fv, nat, s3);
            d.lam_fv(t_fv, nat, s2)
        };
        d.declare_theorem(p.bool_select_lt, ty, value)?;
    }

    // Nat.Rado.isColouring_ofFinset : ∀ n s, IsColouring 2 n (ofFinset s)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let two = d.num(2);
        let col = d.const_app(p.rado_of_finset, &[s]);
        let stmt = d.const_app(p.rado_is_colouring, &[two, n, col]);

        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp = in_range(d, n, i);
            let hyp_fv = d.fresh_fvar();
            let one = d.num(1);
            let zero = d.num(0);
            let mem = d.const_app(p.finset_mem_b, &[s, i]);
            let ht = lt_proof(d, &p, 1, 2);
            let hf = lt_proof(d, &p, 0, 2);
            let step = d.const_app(p.bool_select_lt, &[one, zero, two, mem, ht, hf]);
            let with_hyp = d.lam_fv(hyp_fv, hyp, step);
            let nat_ty = d.nat_ty();
            d.lam_fv(i_fv, nat_ty, with_hyp)
        };

        let ty = {
            let inner = d.pi_fv(s_fv, fs, stmt);
            d.pi_fv(n_fv, nat, inner)
        };
        let value = {
            let inner = d.lam_fv(s_fv, fs, body);
            d.lam_fv(n_fv, nat, inner)
        };
        d.declare_theorem(p.rado_is_colouring_of_finset, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Monotonicity, and the reduction a certificate actually needs.
// ---------------------------------------------------------------------------

fn declare_reductions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let cty = colour_ty(d);

    // inRange_of_le : ∀ m n i, Le m n → inRange m i → inRange n i
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hmn_ty = d.le(m, n);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);
        let hyp_ty = in_range(d, m, i);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let concl = in_range(d, n, i);

        let one = d.num(1);
        let lower_ty = d.le(one, i);
        let upper_m = d.le(i, m);
        let lower = and_left(d, lower_ty, upper_m, hyp);
        let upper_old = and_right(d, lower_ty, upper_m, hyp);
        let upper = d.const_app(p.le_trans, &[i, m, n, upper_old, hmn]);
        let upper_ty = d.le(i, n);
        let body = d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper]);

        let ty = {
            let s5 = d.arrow(hyp_ty, concl);
            let s4 = d.arrow(hmn_ty, s5);
            let s3 = d.pi_fv(i_fv, nat, s4);
            let s2 = d.pi_fv(n_fv, nat, s3);
            d.pi_fv(m_fv, nat, s2)
        };
        let value = {
            let s5 = d.lam_fv(hyp_fv, hyp_ty, body);
            let s4 = d.lam_fv(hmn_fv, hmn_ty, s5);
            let s3 = d.lam_fv(i_fv, nat, s4);
            let s2 = d.lam_fv(n_fv, nat, s3);
            d.lam_fv(m_fv, nat, s2)
        };
        d.declare_theorem(p.rado_in_range_of_le, ty, value)?;
    }

    // isColouring_of_le : ∀ k m n c, Le m n → IsColouring k n c → IsColouring k m c
    {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hmn_ty = d.le(m, n);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);
        let hc_ty = d.const_app(p.rado_is_colouring, &[k, n, c]);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let concl = d.const_app(p.rado_is_colouring, &[k, m, c]);

        let body = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = in_range(d, m, i);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let widened = d.const_app(p.rado_in_range_of_le, &[m, n, i, hmn, hyp]);
            let step = d.apply(hc, &[i, widened]);
            let with_hyp = d.lam_fv(hyp_fv, hyp_ty, step);
            d.lam_fv(i_fv, nat, with_hyp)
        };

        let ty = {
            let s6 = d.arrow(hc_ty, concl);
            let s5 = d.arrow(hmn_ty, s6);
            let s4 = d.pi_fv(c_fv, cty, s5);
            let s3 = d.pi_fv(n_fv, nat, s4);
            let s2 = d.pi_fv(m_fv, nat, s3);
            d.pi_fv(k_fv, nat, s2)
        };
        let value = {
            let s6 = d.lam_fv(hc_fv, hc_ty, body);
            let s5 = d.lam_fv(hmn_fv, hmn_ty, s6);
            let s4 = d.lam_fv(c_fv, cty, s5);
            let s3 = d.lam_fv(n_fv, nat, s4);
            let s2 = d.lam_fv(m_fv, nat, s3);
            d.lam_fv(k_fv, nat, s2)
        };
        d.declare_theorem(p.rado_is_colouring_of_le, ty, value)?;
    }

    // monoSol_of_le : ∀ a b m n c, Le m n → MonoSol a b m c → MonoSol a b n c
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hmn_ty = d.le(m, n);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);
        let hm_ty = d.const_app(p.rado_mono_sol, &[a, b, m, c]);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let goal = d.const_app(p.rado_mono_sol, &[a, b, n, c]);
        let goal_unfolded = mono_sol_unfolded(d, &p, a, b, n, c);

        // fun x hx => Exists.rec … (fun y hy => Exists.rec … (fun z hz => …))
        let inner_minor = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let pred_y_at_x = mono_pred_y(d, &p, a, b, m, c, x);
            let hx_ty = exists_nat(d, &p, pred_y_at_x);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);

            let minor_y = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let pred_z_at_xy = mono_pred_z(d, &p, a, b, m, c, x, y);
                let hy_ty = exists_nat(d, &p, pred_z_at_xy);
                let hy_fv = d.fresh_fvar();
                let hy = d.kernel().fvar(hy_fv);

                let minor_z = {
                    let z_fv = d.fresh_fvar();
                    let z = d.kernel().fvar(z_fv);
                    let hz_ty = mono_body(d, &p, a, b, m, c, x, y, z);
                    let hz_fv = d.fresh_fvar();
                    let hz = d.kernel().fvar(hz_fv);

                    // Take the chain apart at `m` and put it back at `n`.
                    let rx_m = in_range(d, m, x);
                    let ry_m = in_range(d, m, y);
                    let rz_m = in_range(d, m, z);
                    let sol = d.const_app(p.rado_sol, &[a, b, x, y, z]);
                    let cx = d.apply(c, &[x]);
                    let cy = d.apply(c, &[y]);
                    let cz = d.apply(c, &[z]);
                    let exy = d.eq(cx, cy);
                    let eyz = d.eq(cy, cz);
                    let tail_ty = d.const_app(p.logic.and, &[exy, eyz]);
                    let with_sol_ty = d.const_app(p.logic.and, &[sol, tail_ty]);
                    let with_z_ty = d.const_app(p.logic.and, &[rz_m, with_sol_ty]);
                    let with_y_ty = d.const_app(p.logic.and, &[ry_m, with_z_ty]);

                    let hrx = and_left(d, rx_m, with_y_ty, hz);
                    let rest_y = and_right(d, rx_m, with_y_ty, hz);
                    let hry = and_left(d, ry_m, with_z_ty, rest_y);
                    let rest_z = and_right(d, ry_m, with_z_ty, rest_y);
                    let hrz = and_left(d, rz_m, with_sol_ty, rest_z);
                    let rest_sol = and_right(d, rz_m, with_sol_ty, rest_z);

                    let hrx_n = d.const_app(p.rado_in_range_of_le, &[m, n, x, hmn, hrx]);
                    let hry_n = d.const_app(p.rado_in_range_of_le, &[m, n, y, hmn, hry]);
                    let hrz_n = d.const_app(p.rado_in_range_of_le, &[m, n, z, hmn, hrz]);

                    let rx_n = in_range(d, n, x);
                    let ry_n = in_range(d, n, y);
                    let rz_n = in_range(d, n, z);
                    let with_z_n = d.const_app(p.logic.and, &[rz_n, with_sol_ty]);
                    let with_y_n = d.const_app(p.logic.and, &[ry_n, with_z_n]);

                    let packed_z =
                        d.const_app(p.logic.and_intro, &[rz_n, with_sol_ty, hrz_n, rest_sol]);
                    let packed_y =
                        d.const_app(p.logic.and_intro, &[ry_n, with_z_n, hry_n, packed_z]);
                    let packed_x =
                        d.const_app(p.logic.and_intro, &[rx_n, with_y_n, hrx_n, packed_y]);

                    let pred_z_n = mono_pred_z(d, &p, a, b, n, c, x, y);
                    let ez = exists_intro_nat(d, &p, pred_z_n, z, packed_x);
                    let pred_y_n = mono_pred_y(d, &p, a, b, n, c, x);
                    let ey = exists_intro_nat(d, &p, pred_y_n, y, ez);
                    let pred_x_n = mono_pred_x(d, &p, a, b, n, c);
                    let ex = exists_intro_nat(d, &p, pred_x_n, x, ey);

                    let with_hz = d.lam_fv(hz_fv, hz_ty, ex);
                    d.lam_fv(z_fv, nat, with_hz)
                };

                let elim_z = exists_elim_nat(d, &p, pred_z_at_xy, goal_unfolded, minor_z, hy);
                let with_hy = d.lam_fv(hy_fv, hy_ty, elim_z);
                d.lam_fv(y_fv, nat, with_hy)
            };

            let elim_y = exists_elim_nat(d, &p, pred_y_at_x, goal_unfolded, minor_y, hx);
            let with_hx = d.lam_fv(hx_fv, hx_ty, elim_y);
            d.lam_fv(x_fv, nat, with_hx)
        };

        let pred_x_m = mono_pred_x(d, &p, a, b, m, c);
        let body = exists_elim_nat(d, &p, pred_x_m, goal_unfolded, inner_minor, hm);

        let ty = {
            let s7 = d.arrow(hm_ty, goal);
            let s6 = d.arrow(hmn_ty, s7);
            let s5 = d.pi_fv(c_fv, cty, s6);
            let s4 = d.pi_fv(n_fv, nat, s5);
            let s3 = d.pi_fv(m_fv, nat, s4);
            let s2 = d.pi_fv(b_fv, nat, s3);
            d.pi_fv(a_fv, nat, s2)
        };
        let value = {
            let s7 = d.lam_fv(hm_fv, hm_ty, body);
            let s6 = d.lam_fv(hmn_fv, hmn_ty, s7);
            let s5 = d.lam_fv(c_fv, cty, s6);
            let s4 = d.lam_fv(n_fv, nat, s5);
            let s3 = d.lam_fv(m_fv, nat, s4);
            let s2 = d.lam_fv(b_fv, nat, s3);
            d.lam_fv(a_fv, nat, s2)
        };
        d.declare_theorem(p.rado_mono_sol_of_le, ty, value)?;
    }

    // arrows_of_le : ∀ a b k m n, Le m n → Arrows a b k m → Arrows a b k n
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hmn_ty = d.le(m, n);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);
        let ha_ty = d.const_app(p.rado_arrows, &[a, b, k, m]);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let concl = d.const_app(p.rado_arrows, &[a, b, k, n]);

        let body = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let hc_ty = d.const_app(p.rado_is_colouring, &[k, n, c]);
            let hc_fv = d.fresh_fvar();
            let hc = d.kernel().fvar(hc_fv);
            let restricted = d.const_app(p.rado_is_colouring_of_le, &[k, m, n, c, hmn, hc]);
            let at_m = d.apply(ha, &[c, restricted]);
            let widened = d.const_app(p.rado_mono_sol_of_le, &[a, b, m, n, c, hmn, at_m]);
            let with_hc = d.lam_fv(hc_fv, hc_ty, widened);
            d.lam_fv(c_fv, cty, with_hc)
        };

        let ty = {
            let s7 = d.arrow(ha_ty, concl);
            let s6 = d.arrow(hmn_ty, s7);
            let s5 = d.pi_fv(n_fv, nat, s6);
            let s4 = d.pi_fv(m_fv, nat, s5);
            let s3 = d.pi_fv(k_fv, nat, s4);
            let s2 = d.pi_fv(b_fv, nat, s3);
            d.pi_fv(a_fv, nat, s2)
        };
        let value = {
            let s7 = d.lam_fv(ha_fv, ha_ty, body);
            let s6 = d.lam_fv(hmn_fv, hmn_ty, s7);
            let s5 = d.lam_fv(n_fv, nat, s6);
            let s4 = d.lam_fv(m_fv, nat, s5);
            let s3 = d.lam_fv(k_fv, nat, s4);
            let s2 = d.lam_fv(b_fv, nat, s3);
            d.lam_fv(a_fv, nat, s2)
        };
        d.declare_theorem(p.rado_arrows_of_le, ty, value)?;
    }

    // isRadoNumber_of_succ : ∀ a b k m,
    //     Arrows a b k (succ m) → (Arrows a b k m → False) → IsRadoNumber a b k (succ m)
    //
    // THE reduction a certificate needs: the two halves a search produces,
    // joined into leastness, with `m` a variable throughout.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sm = d.succ(m);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        let hup_ty = d.const_app(p.rado_arrows, &[a, b, k, sm]);
        let hup_fv = d.fresh_fvar();
        let hup = d.kernel().fvar(hup_fv);
        let arrows_m = d.const_app(p.rado_arrows, &[a, b, k, m]);
        let hlow_ty = d.arrow(arrows_m, false_ty);
        let hlow_fv = d.fresh_fvar();
        let hlow = d.kernel().fvar(hlow_fv);
        let concl = d.const_app(p.rado_is_rado_number, &[a, b, k, sm]);

        let least = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, sm);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);
            let arrows_j = d.const_app(p.rado_arrows, &[a, b, k, j]);
            let haj_fv = d.fresh_fvar();
            let haj = d.kernel().fvar(haj_fv);
            let jle = d.const_app(p.le_of_lt_succ, &[j, m, hj]);
            let at_m = d.const_app(p.rado_arrows_of_le, &[a, b, k, j, m, jle, haj]);
            let absurd = d.apply(hlow, &[at_m]);
            let with_haj = d.lam_fv(haj_fv, arrows_j, absurd);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_haj);
            d.lam_fv(j_fv, nat, with_hj)
        };
        let least_ty = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let arrows_j = d.const_app(p.rado_arrows, &[a, b, k, j]);
            let inner = d.arrow(arrows_j, false_ty);
            let hj_ty = d.lt(j, sm);
            let step = d.arrow(hj_ty, inner);
            d.pi_fv(j_fv, nat, step)
        };
        let body = d.const_app(p.logic.and_intro, &[hup_ty, least_ty, hup, least]);

        let ty = {
            let s6 = d.arrow(hlow_ty, concl);
            let s5 = d.arrow(hup_ty, s6);
            let s4 = d.pi_fv(m_fv, nat, s5);
            let s3 = d.pi_fv(k_fv, nat, s4);
            let s2 = d.pi_fv(b_fv, nat, s3);
            d.pi_fv(a_fv, nat, s2)
        };
        let value = {
            let s6 = d.lam_fv(hlow_fv, hlow_ty, body);
            let s5 = d.lam_fv(hup_fv, hup_ty, s6);
            let s4 = d.lam_fv(m_fv, nat, s5);
            let s3 = d.lam_fv(k_fv, nat, s4);
            let s2 = d.lam_fv(b_fv, nat, s3);
            d.lam_fv(a_fv, nat, s2)
        };
        d.declare_theorem(p.rado_is_rado_number_of_succ, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The instance: R_2(x = y + z) = 5, both halves reconstructed from search.
// ---------------------------------------------------------------------------

/// The upper bound `Arrows 1 1 2 5`, as the decision tree over
/// `Nat.lt_two_cases` that [`search_witness`] fills in leaf by leaf.
///
/// Returns `Err` only from the kernel. If the SEARCH fails at any leaf the
/// function returns `Ok(false)` and declares nothing — a colour assignment
/// with no monochromatic triple would mean the theorem is false, and this
/// builder must not paper over that by declaring something weaker.
fn declare_schur_upper(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<bool, KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let cty = colour_ty(d);
    let a = d.num(SCHUR_A);
    let b = d.num(SCHUR_B);
    let n = d.num(SCHUR_N);
    let two = d.num(2);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hc_ty = d.const_app(p.rado_is_colouring, &[two, n, c]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let goal = d.const_app(p.rado_mono_sol, &[a, b, n, c]);

    // The tree, built bottom-up over the 2^SCHUR_N assignments.
    //
    // `frame[i]` is the proof of `Eq (c (i+1)) colours[i]` live at this leaf.
    fn leaf(
        d: &mut NatDev<'_>,
        p: &NatPrelude,
        c: ExprId,
        colours: &[u32],
        frame: &[ExprId],
    ) -> Option<ExprId> {
        let (x, y, z) = search_witness(SCHUR_A, SCHUR_B, SCHUR_N, colours)?;
        let a = d.num(SCHUR_A);
        let b = d.num(SCHUR_B);
        let n = d.num(SCHUR_N);
        let x_e = d.num(x);
        let y_e = d.num(y);
        let z_e = d.num(z);

        let cx = d.apply(c, &[x_e]);
        let cy = d.apply(c, &[y_e]);
        let cz = d.apply(c, &[z_e]);
        let vx = d.num(colours[(x - 1) as usize]);
        let vy = d.num(colours[(y - 1) as usize]);
        let vz = d.num(colours[(z - 1) as usize]);
        let hx_col = frame[(x - 1) as usize];
        let hy_col = frame[(y - 1) as usize];
        let hz_col = frame[(z - 1) as usize];

        let hxy = {
            let back = d.symm(cy, vy, hy_col);
            d.trans(cx, vx, cy, hx_col, back)
        };
        let hyz = {
            let back = d.symm(cz, vz, hz_col);
            d.trans(cy, vy, cz, hy_col, back)
        };

        let rx = in_range_proof(d, p, SCHUR_N, x);
        let ry = in_range_proof(d, p, SCHUR_N, y);
        let rz = in_range_proof(d, p, SCHUR_N, z);
        let sol_lhs = d.mul(a, x_e);
        let hsol = d.refl(sol_lhs);

        // Types for the `And.intro` chain, in the same right-nested shape
        // `mono_body` builds.
        let rx_ty = in_range(d, n, x_e);
        let ry_ty = in_range(d, n, y_e);
        let rz_ty = in_range(d, n, z_e);
        let sol_ty = d.const_app(p.rado_sol, &[a, b, x_e, y_e, z_e]);
        let exy = d.eq(cx, cy);
        let eyz = d.eq(cy, cz);
        let tail_ty = d.const_app(p.logic.and, &[exy, eyz]);
        let with_sol_ty = d.const_app(p.logic.and, &[sol_ty, tail_ty]);
        let with_z_ty = d.const_app(p.logic.and, &[rz_ty, with_sol_ty]);
        let with_y_ty = d.const_app(p.logic.and, &[ry_ty, with_z_ty]);

        let tail = d.const_app(p.logic.and_intro, &[exy, eyz, hxy, hyz]);
        let with_sol = d.const_app(p.logic.and_intro, &[sol_ty, tail_ty, hsol, tail]);
        let with_z = d.const_app(p.logic.and_intro, &[rz_ty, with_sol_ty, rz, with_sol]);
        let with_y = d.const_app(p.logic.and_intro, &[ry_ty, with_z_ty, ry, with_z]);
        let packed = d.const_app(p.logic.and_intro, &[rx_ty, with_y_ty, rx, with_y]);

        let pred_z = mono_pred_z(d, p, a, b, n, c, x_e, y_e);
        let ez = exists_intro_nat(d, p, pred_z, z_e, packed);
        let pred_y = mono_pred_y(d, p, a, b, n, c, x_e);
        let ey = exists_intro_nat(d, p, pred_y, y_e, ez);
        let pred_x = mono_pred_x(d, p, a, b, n, c);
        Some(exists_intro_nat(d, p, pred_x, x_e, ey))
    }

    #[allow(clippy::too_many_arguments)]
    fn tree(
        d: &mut NatDev<'_>,
        p: &NatPrelude,
        c: ExprId,
        hc: ExprId,
        goal: ExprId,
        index: u32,
        colours: &mut Vec<u32>,
        frame: &mut Vec<ExprId>,
    ) -> Option<ExprId> {
        if index > SCHUR_N {
            return leaf(d, p, c, colours, frame);
        }
        let i_e = d.num(index);
        let ci = d.apply(c, &[i_e]);
        let range = in_range_proof(d, p, SCHUR_N, index);
        let bound = d.apply(hc, &[i_e, range]);
        let cases = d.const_app(p.lt_two_cases, &[ci, bound]);
        let zero = d.num(0);
        let one = d.num(1);
        let left_ty = d.eq(ci, zero);
        let right_ty = d.eq(ci, one);

        let mut branch = |d: &mut NatDev<'_>, value: u32, hyp_ty: ExprId| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            colours.push(value);
            frame.push(h);
            let sub = tree(d, p, c, hc, goal, index + 1, colours, frame);
            frame.pop();
            colours.pop();
            sub.map(|body| d.lam_fv(h_fv, hyp_ty, body))
        };

        let left = branch(d, 0, left_ty)?;
        let right = branch(d, 1, right_ty)?;
        Some(d.const_app(
            p.logic.or_elim,
            &[left_ty, right_ty, goal, cases, left, right],
        ))
    }

    let mut colours: Vec<u32> = Vec::new();
    let mut frame: Vec<ExprId> = Vec::new();
    let Some(body) = tree(d, &p, c, hc, goal, 1, &mut colours, &mut frame) else {
        return Ok(false);
    };

    let ty = d.const_app(p.rado_arrows, &[a, b, two, n]);
    let value = {
        let inner = d.lam_fv(hc_fv, hc_ty, body);
        d.lam_fv(c_fv, cty, inner)
    };
    let _ = nat;
    d.declare_theorem(p.rado_schur_arrows_five, ty, value)?;
    Ok(true)
}

/// `Nat.Rado.schurSet` — the lower-bound certificate, transcribed from
/// [`search_avoiding_set`] as a `Nat.Finset` whose stored predicate is a chain
/// of `Nat.beq` tests against the found members.
///
/// The bound is `SCHUR_N` (one past the range `[1, SCHUR_N - 1]` the set
/// colours), so `Nat.Finset.memB` never truncates a member away.
fn declare_schur_set(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    members: &[u32],
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let mut body = d.bool_false();
    for &m in members.iter().rev() {
        let m_e = d.num(m);
        let hit = d.beq(i, m_e);
        let yes = d.bool_true();
        body = select_bool(d, &p, hit, yes, body);
    }
    let pred = d.lam_fv(i_fv, nat, body);
    let bound = d.num(SCHUR_N);
    let value = d.const_app(p.finset_mk, &[pred, bound]);
    let ty = finset_ty(d, &p);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rado_schur_set,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// The lower bound `Arrows 1 1 2 4 → False`, by reflection.
///
/// The `Bool` triple loop `allBelow (fun i => allBelow (fun j => allBelow
/// (fun l => g i j l) 5) 5) 5` is reduced to `true` by the kernel's own
/// conversion check — nothing here asserts that it is true, the kernel
/// computes it — and `Nat.Finset.allBelow_true_at` then reads it back at the
/// three existential witnesses the hypothesis hands over.
fn declare_schur_lower(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let a = d.num(SCHUR_A);
    let b = d.num(SCHUR_B);
    let four = d.num(SCHUR_N - 1);
    let five = d.num(SCHUR_N);
    let two = d.num(2);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);

    let set = d.kernel().const_(p.rado_schur_set, vec![]);
    let col = d.const_app(p.rado_of_finset, &[set]);
    let hcol = d.const_app(p.rado_is_colouring_of_finset, &[four, set]);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.const_app(p.rado_arrows, &[a, b, two, four]);
    let mono = d.apply(h, &[col, hcol]);

    // `g i j l` — `true` unless `(i, j, l)` is a monochromatic solution
    // inside `[1, 4]`.
    fn guard(d: &mut NatDev<'_>, col: ExprId, i: ExprId, j: ExprId, l: ExprId) -> Vec<ExprId> {
        let one = d.num(1);
        let a = d.num(SCHUR_A);
        let b = d.num(SCHUR_B);
        let c1 = d.ble(one, i);
        let c2 = d.ble(one, j);
        let c3 = d.ble(one, l);
        let lhs = d.mul(a, i);
        let aj = d.mul(a, j);
        let bl = d.mul(b, l);
        let rhs = d.add(aj, bl);
        let c4 = d.beq(lhs, rhs);
        let ci = d.apply(col, &[i]);
        let cj = d.apply(col, &[j]);
        let cl = d.apply(col, &[l]);
        let c5 = d.beq(ci, cj);
        let c6 = d.beq(cj, cl);
        vec![c1, c2, c3, c4, c5, c6]
    }

    /// The `E_k` chain: `E[6]` is `Bool.false`, `E[k-1] = if c_k then E[k] else true`.
    fn chain(d: &mut NatDev<'_>, p: &NatPrelude, conds: &[ExprId]) -> Vec<ExprId> {
        let mut out = vec![d.bool_false()];
        for &cond in conds.iter().rev() {
            let inner = *out.last().expect("non-empty");
            let yes = d.bool_true();
            let next = select_bool(d, p, cond, inner, yes);
            out.push(next);
        }
        out.reverse();
        out
    }

    fn g_at(
        d: &mut NatDev<'_>,
        p: &NatPrelude,
        col: ExprId,
        i: ExprId,
        j: ExprId,
        l: ExprId,
    ) -> ExprId {
        let conds = guard(d, col, i, j, l);
        let ch = chain(d, p, &conds);
        ch[0]
    }

    // The three nested loops, as the exact lambdas `allBelow_true_at` needs.
    let inner_lam = |d: &mut NatDev<'_>, i: ExprId, j: ExprId| {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let body = g_at(d, &p, col, i, j, l);
        d.lam_fv(l_fv, nat, body)
    };
    let mid_lam = |d: &mut NatDev<'_>, i: ExprId| {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let inner = inner_lam(d, i, j);
        let body = d.const_app(p.finset_all_below, &[inner, five]);
        d.lam_fv(j_fv, nat, body)
    };
    let outer_lam = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let mid = mid_lam(d, i);
        let body = d.const_app(p.finset_all_below, &[mid, five]);
        d.lam_fv(i_fv, nat, body)
    };

    // `Eq.refl Bool Bool.true` against `Eq Bool (allBelow …) Bool.true`: the
    // kernel's conversion check IS the certificate check.
    let bool_true = d.bool_true();
    let loop_proof = d.bool_refl(bool_true);

    let refute = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let pred_y_at_x = mono_pred_y(d, &p, a, b, four, col, x);
        let hx_ty = exists_nat(d, &p, pred_y_at_x);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);

        let minor_y = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let pred_z_at_xy = mono_pred_z(d, &p, a, b, four, col, x, y);
            let hy_ty = exists_nat(d, &p, pred_z_at_xy);
            let hy_fv = d.fresh_fvar();
            let hy = d.kernel().fvar(hy_fv);

            let minor_z = {
                let z_fv = d.fresh_fvar();
                let z = d.kernel().fvar(z_fv);
                let hz_ty = mono_body(d, &p, a, b, four, col, x, y, z);
                let hz_fv = d.fresh_fvar();
                let hz = d.kernel().fvar(hz_fv);

                // Unpack the witness.
                let rx_ty = in_range(d, four, x);
                let ry_ty = in_range(d, four, y);
                let rz_ty = in_range(d, four, z);
                let sol_ty = d.const_app(p.rado_sol, &[a, b, x, y, z]);
                let cx = d.apply(col, &[x]);
                let cy = d.apply(col, &[y]);
                let cz = d.apply(col, &[z]);
                let exy = d.eq(cx, cy);
                let eyz = d.eq(cy, cz);
                let tail_ty = d.const_app(p.logic.and, &[exy, eyz]);
                let with_sol_ty = d.const_app(p.logic.and, &[sol_ty, tail_ty]);
                let with_z_ty = d.const_app(p.logic.and, &[rz_ty, with_sol_ty]);
                let with_y_ty = d.const_app(p.logic.and, &[ry_ty, with_z_ty]);

                let hrx = and_left(d, rx_ty, with_y_ty, hz);
                let rest_y = and_right(d, rx_ty, with_y_ty, hz);
                let hry = and_left(d, ry_ty, with_z_ty, rest_y);
                let rest_z = and_right(d, ry_ty, with_z_ty, rest_y);
                let hrz = and_left(d, rz_ty, with_sol_ty, rest_z);
                let rest_sol = and_right(d, rz_ty, with_sol_ty, rest_z);
                let hsol = and_left(d, sol_ty, tail_ty, rest_sol);
                let rest_col = and_right(d, sol_ty, tail_ty, rest_sol);
                let hxy = and_left(d, exy, eyz, rest_col);
                let hyz = and_right(d, exy, eyz, rest_col);

                let one = d.num(1);
                let x_lo = d.le(one, x);
                let x_hi = d.le(x, four);
                let y_lo = d.le(one, y);
                let y_hi = d.le(y, four);
                let z_lo = d.le(one, z);
                let z_hi = d.le(z, four);
                let hx_pos = and_left(d, x_lo, x_hi, hrx);
                let hx_le = and_right(d, x_lo, x_hi, hrx);
                let hy_pos = and_left(d, y_lo, y_hi, hry);
                let hy_le = and_right(d, y_lo, y_hi, hry);
                let hz_pos = and_left(d, z_lo, z_hi, hrz);
                let hz_le = and_right(d, z_lo, z_hi, hrz);

                let hx5 = d.const_app(p.lt_succ_of_le, &[x, four, hx_le]);
                let hy5 = d.const_app(p.lt_succ_of_le, &[y, four, hy_le]);
                let hz5 = d.const_app(p.lt_succ_of_le, &[z, four, hz_le]);

                // Reflection: read the loop back at x, then y, then z.
                let mid_at_x = mid_lam(d, x);
                let step_x = d.const_app(
                    p.finset_all_below_true_at,
                    &[outer_lam, five, loop_proof, x, hx5],
                );
                let inner_at_xy = inner_lam(d, x, y);
                let step_y = d.const_app(
                    p.finset_all_below_true_at,
                    &[mid_at_x, five, step_x, y, hy5],
                );
                let step_z = d.const_app(
                    p.finset_all_below_true_at,
                    &[inner_at_xy, five, step_y, z, hz5],
                );

                // Force each condition to `true`, six transports, and land on
                // `Bool.false = Bool.true`.
                let conds = guard(d, col, x, y, z);
                let ch = chain(d, &p, &conds);
                let lhs = d.mul(a, x);
                let ay = d.mul(a, y);
                let bz = d.mul(b, z);
                let rhs = d.add(ay, bz);
                let evidence = vec![
                    d.const_app(p.ble_eq_true_of_le, &[one, x, hx_pos]),
                    d.const_app(p.ble_eq_true_of_le, &[one, y, hy_pos]),
                    d.const_app(p.ble_eq_true_of_le, &[one, z, hz_pos]),
                    d.const_app(p.beq_eq_true_of_eq, &[lhs, rhs, hsol]),
                    d.const_app(p.beq_eq_true_of_eq, &[cx, cy, hxy]),
                    d.const_app(p.beq_eq_true_of_eq, &[cy, cz, hyz]),
                ];

                let mut current = step_z;
                for (k, &cond) in conds.iter().enumerate() {
                    let rest = ch[k + 1];
                    let motive = d.bool_eq_motive(cond, &|d, v| {
                        let yes = d.bool_true();
                        let selected = select_bool(d, &p, v, rest, yes);
                        let t = d.bool_true();
                        d.bool_eq(selected, t)
                    });
                    let t = d.bool_true();
                    current = d.bool_transport(cond, motive, current, t, evidence[k]);
                }
                let absurd = d.const_app(p.logic.bool_false_ne_true, &[current]);

                let _ = (hz_pos, bool_ty);
                let with_hz = d.lam_fv(hz_fv, hz_ty, absurd);
                d.lam_fv(z_fv, nat, with_hz)
            };

            let elim_z = exists_elim_nat(d, &p, pred_z_at_xy, false_ty, minor_z, hy);
            let with_hy = d.lam_fv(hy_fv, hy_ty, elim_z);
            d.lam_fv(y_fv, nat, with_hy)
        };

        let elim_y = exists_elim_nat(d, &p, pred_y_at_x, false_ty, minor_y, hx);
        let with_hx = d.lam_fv(hx_fv, hx_ty, elim_y);
        d.lam_fv(x_fv, nat, with_hx)
    };

    let pred_x = mono_pred_x(d, &p, a, b, four, col);
    let body = exists_elim_nat(d, &p, pred_x, false_ty, refute, mono);

    let ty = d.arrow(h_ty, false_ty);
    let value = d.lam_fv(h_fv, h_ty, body);
    d.declare_theorem(p.rado_schur_not_arrows_four, ty, value)
}

/// `Nat.Rado.schur_two : IsRadoNumber 1 1 2 5` — the two halves joined by
/// `isRadoNumber_of_succ`, at `m := 4`.
fn declare_schur_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let a = d.num(SCHUR_A);
    let b = d.num(SCHUR_B);
    let two = d.num(2);
    let four = d.num(SCHUR_N - 1);
    let five = d.num(SCHUR_N);
    let upper = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
    let lower = d.kernel().const_(p.rado_schur_not_arrows_four, vec![]);
    let value = d.const_app(
        p.rado_is_rado_number_of_succ,
        &[a, b, two, four, upper, lower],
    );
    let ty = d.const_app(p.rado_is_rado_number, &[a, b, two, five]);
    d.declare_theorem(p.rado_schur_two, ty, value)
}

pub(super) fn declare_rado_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_definitions(d, p)?;
    declare_of_finset(d, p)?;
    declare_reductions(d, p)?;

    // The search runs first; nothing is declared unless it produced both
    // certificates. `expect` here is a builder invariant, not a kernel one:
    // for `a = b = 1, k = 2` the two searches are total by construction and a
    // `None` would mean the enumeration itself is broken.
    let members = search_avoiding_set(SCHUR_A, SCHUR_B, SCHUR_N - 1)
        .expect("the 2-colour Schur lower bound has an avoiding subset of [1,4]");
    declare_schur_set(d, p, &members)?;
    let upper = declare_schur_upper(d, p)?;
    assert!(
        upper,
        "the 2-colour Schur upper bound search left an assignment with no monochromatic triple"
    );
    declare_schur_lower(d, p)?;
    declare_schur_two(d, p)?;
    Ok(())
}
