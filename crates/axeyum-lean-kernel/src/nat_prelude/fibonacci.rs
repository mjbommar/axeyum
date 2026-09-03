//! The Fibonacci numbers `Nat.fib`, and the sum identity `Nat.sum_fib`.
//!
//! # Two-step recursion, without a tuple type
//!
//! `Nat.fib`'s recurrence (`fib (n+2) = fib (n+1) + fib n`) needs the PREVIOUS
//! TWO values at every step, but `Nat.rec` only ever hands a step its
//! predecessor's single value. The textbook fix recurses on a PAIR `(fib n,
//! fib (n+1))` and projects — but this kernel has no tuple type (confirmed
//! today when a sibling lane could not reify a 2×2 adjugate), so that fix is
//! not literally available. `binary.rs`'s `testBitAux` already recurses with a
//! `Nat → Nat`-valued motive (fuel `i` drives the recursion, an ordinary
//! `Nat` parameter `n` is threaded through unchanged); this file generalizes
//! that ONE step further: the motive is `Nat → Nat → Nat` (curried, not a
//! tuple), threading TWO ordinary parameters `a b` — the accumulator pair —
//! through, updated at every step. No tuple is needed because currying
//! already gives two independent slots.
//!
//! `Nat.fibAux i a b` computes the generalized Fibonacci sequence seeded at
//! `(a, b)`, `i` steps in: `fibAux 0 a b ≡ a`, `fibAux (succ i) a b ≡ fibAux i
//! b (add a b)`. `Nat.fib n := fibAux n 0 1`.
//!
//! Hand check: `fibAux 0 a b = a`. `fibAux 1 a b = fibAux 0 b (a+b) = b`.
//! `fibAux 2 a b = fibAux 1 b (a+b) = (a+b)` (apply the `fibAux 1 x y = y`
//! pattern at `x=b, y=a+b`). So `fib 0 = 0`, `fib 1 = 1`, `fib 2 = 0+1 = 1`,
//! matching the standard sequence. All three facts above are pure `δ`/`ι`
//! unfolding — no theorem is needed to state or use them.
//!
//! The alternative the brief offered — proving `And (P n) (P (succ n))`
//! together by ordinary `Nat.rec`, the device `Wilson`'s pairing collapse uses
//! — proves a PROPOSITION about two indices at once; it does not by itself
//! give a way to *define* a `Nat`-valued function, which is what `fib` is.
//! The curried-accumulator route above is the one actually used here.
//!
//! # `fib_add_two`: true, but not by `δ`/`ι` alone
//!
//! `fib (n+2) = fib (n+1) + fib n` is NOT a bare reduction fact, even though
//! `fib`'s own defining recursion is: `fib`'s seed `(0, 1)` is FIXED, but the
//! recursive step changes the accumulator PAIR at every call
//! (`fibAux (succ i) a b ≡ fibAux i b (a+b)`), so relating `fibAux (n+2) 0 1`
//! to `fibAux (n+1) 0 1` and `fibAux n 0 1` needs the identity to hold for
//! EVERY seed the recursion passes through, not just `(0,1)`. So the proof
//! goes through a STRONGER internal fact, generalized over the seed
//! (`fib_aux_add_two_gen`, never exposed as a prelude name):
//!
//! `∀ i a b, fibAux (succ (succ i)) a b = add (fibAux (succ i) a b) (fibAux i a b)`
//!
//! by induction on `i`, with `a` and `b` BOTH generalized inside the motive
//! (mirroring `vandermonde.rs`'s `n`/`k` generalization inside its own outer
//! induction, for the same reason: the induction hypothesis is needed at a
//! DIFFERENT seed than the one the goal states).
//!
//! * **Base case (`i = 0`).** `fibAux 2 a b` reduces (two unfoldings) to `add
//!   a b`; the right-hand side's `fibAux 1 a b + fibAux 0 a b` reduces to
//!   `add b a`. The two accumulator slots land in the OPPOSITE order after one
//!   shift, so this genuinely needs `add_comm` — the one non-defeq step in
//!   the whole lemma.
//! * **Successor case (`i = succ j`).** Needs NO explicit rewriting at all.
//!   Unfolding `fibAux (succ ·) a b ≡ fibAux · b (a+b)` once on the goal's
//!   LHS and once on each summand of its RHS lands EXACTLY on the induction
//!   hypothesis applied at the shifted seed `(b, add a b)` — so
//!   `fun a b => ih b (add a b)` already has the goal's type up to `δ`/`ι`,
//!   and the kernel's own defeq check accepts it as the entire step proof
//!   (the same trick `binary.rs`'s `testBit_le_one` step uses at one seed
//!   slot; here it closes at two).
//!
//! `fib_add_two` (the exposed name, stated over `fib` rather than `fibAux`)
//! is the `i := n, a := 0, b := 1` instance of the general fact, converted by
//! the same defeq (`fib x` unfolds to `fibAux x 0 1` by one `δ` step) that
//! makes the whole file work.
//!
//! # Cassini's identity: needs ℤ, not attempted here
//!
//! `fib(n+1)·fib(n-1) - fib(n)^2 = (-1)^n` alternates sign, so it is not a ℕ
//! statement as written. The ℕ-only two-case form keeps both orientations
//! non-negative: for `n` even, `fib(n+1)*fib(n-1) = fib(n)^2 + 1`; for `n`
//! odd, `fib(n)^2 = fib(n+1)*fib(n-1) + 1`. Hand check at three points: `n=1`
//! is odd and `fib(1)^2 = 1` while `fib(2)*fib(0) + 1 = 0 + 1 = 1`; `n=2` is
//! even and `fib(3)*fib(1) = 2` while `fib(2)^2 + 1 = 1 + 1 = 2`; `n=3` is odd
//! and `fib(3)^2 = 4` while `fib(4)*fib(2) + 1 = 3 + 1 = 4`. All three match.
//!
//! The parity case-split checks out by hand, but is NOT attempted in this
//! file: it is adjacent to `int_prelude/` in spirit (a signed alternation
//! reduced to two unsigned cases), and more importantly the case-split itself
//! is substantial new machinery on top of what is here — decidable parity,
//! plus an induction that carries the Cassini invariant two steps at a time —
//! that this slice's budget does not cover. Reported per the brief's explicit
//! "both are acceptable" option: this file stops short of Cassini.
//!
//! # `fib_add` and `coprime_fib_succ`: two more pieces, `gcd_fib` still not
//! started
//!
//! `fib_add` (the addition formula, `succ`-shaped so no `Nat.sub` appears:
//! `fib (m+n+1) = fib m * fib n + fib (m+1) * fib (n+1)`) and
//! `coprime_fib_succ` (`gcd (fib n) (fib (succ n)) = 1`, consecutive
//! Fibonacci numbers are coprime) are now both declared and kernel-confirmed
//! axiom-free, below.
//!
//! `gcd (fib m) (fib n) = fib (gcd m n)` itself is still NOT attempted.
//! `Nat.gcd` is a checked `WellFounded.fix` over `lt`, recursing on the
//! FIRST argument via the executable remainder (`gcd.rs`'s module doc), so
//! mirroring the Euclidean descent means an induction along that SAME
//! well-founded order — strong induction, not the ordinary structural
//! induction `fib_add` and `coprime_fib_succ` both get away with — and needs
//! `well_founded_fix_eq` (the device `gcd_succ`/`gcd_zero_left` in `gcd.rs`
//! already use) to unfold `gcd` at each step. That descent is its own slice.

use super::NatPrelude;
use super::finite::{pos_implies_succ_pred, zero_lt_via_c};
use super::helpers::{and_left, and_right, iff_reverse};
use super::ops::{NatDev, NatOps, cases_lt_bound, cases_lt_or_ge};
use super::steps::absurd;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.fibAux`: it calls only `Nat.add` (height 1), so any
/// height `> 1` is sound; picked clear of every height used elsewhere in this
/// prelude (max in use before this file: `13`, `totient.rs`).
const FIB_AUX_HEIGHT: u16 = 14;
/// Delta height for `Nat.fib`: it calls `Nat.fibAux`, so this must exceed
/// [`FIB_AUX_HEIGHT`].
const FIB_HEIGHT: u16 = 15;

// ============================================================================
// `Nat.fibAux` and `Nat.fib`.
// ============================================================================

/// `Nat.fibAux : Nat → Nat → Nat → Nat` and `Nat.fib : Nat → Nat`. See the
/// module doc for the accumulator-pair recursion shape.
fn declare_fib_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fn_ty2 = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };

    // fibAux 0 a b ≡ a ; fibAux (succ i) a b ≡ fibAux i b (add a b)
    {
        let base_term = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, nat, a);
            d.lam_fv(a_fv, nat, inner)
        };
        let step_term = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.add(a, b);
            let applied = d.apply(ih, &[b, ab]);
            let inner_b = d.lam_fv(b_fv, nat, applied);
            let inner_a = d.lam_fv(a_fv, nat, inner_b);
            let with_ih = d.lam_fv(ih_fv, fn_ty2, inner_a);
            d.lam_fv(j_fv, nat, with_ih)
        };
        let motive = d.kernel().lam(anon, nat, fn_ty2, BinderInfo::Default);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let one = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base_term, step_term, i]);
        let value = d.lam_fv(i_fv, nat, body);
        let ty = d.arrow(nat, fn_ty2);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.fib_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(FIB_AUX_HEIGHT),
        })?;
    }

    // fib n := fibAux n 0 1
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let one_lit = d.num(1);
        let applied = d.const_app(p.fib_aux, &[n, zero, one_lit]);
        let value = d.lam_fv(n_fv, nat, applied);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.fib,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(FIB_HEIGHT),
        })?;
    }
    Ok(())
}

// ============================================================================
// `fib_add_two`.
// ============================================================================

/// `∀ i a b, fibAux (succ (succ i)) a b = add (fibAux (succ i) a b) (fibAux i
/// a b)` — the seed-generalized fact `fib_add_two` specializes. See the
/// module doc for why the seed must be generalized and why the successor case
/// needs no rewriting at all.
fn fib_aux_add_two_gen(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let si = d.succ(i);
        let sii = d.succ(si);
        let lhs = d.const_app(p.fib_aux, &[sii, a, b]);
        let fa1 = d.const_app(p.fib_aux, &[si, a, b]);
        let fa0 = d.const_app(p.fib_aux, &[i, a, b]);
        let rhs = d.add(fa1, fa0);
        let eqn = d.eq(lhs, rhs);
        let inner = d.pi_fv(b_fv, nat, eqn);
        d.pi_fv(a_fv, nat, inner)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof = d.induct(
        &stmt_at,
        &|d| {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let h_comm = d.lemma(p.add_comm, &[a, b]); // add a b = add b a
            let with_b = d.lam_fv(b_fv, nat, h_comm);
            d.lam_fv(a_fv, nat, with_b)
        },
        &|d, _j, ih| {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let ab = d.add(a, b);
            let applied = d.apply(ih, &[b, ab]);
            let with_b = d.lam_fv(b_fv, nat, applied);
            d.lam_fv(a_fv, nat, with_b)
        },
        i,
    );
    d.lam_fv(i_fv, nat, proof)
}

/// `Nat.fib_add_two : ∀ n, fib (succ (succ n)) = add (fib (succ n)) (fib n)`.
fn declare_fib_add_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let general = fib_aux_add_two_gen(d, &p);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let one = d.num(1);
    let proof_at_n = d.apply(general, &[n, zero, one]);

    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let lhs = d.const_app(p.fib, &[ssn]);
    let fib_sn = d.const_app(p.fib, &[sn]);
    let fib_n = d.const_app(p.fib, &[n]);
    let rhs = d.add(fib_sn, fib_n);
    let stmt = d.eq(lhs, rhs);

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof_at_n);
    d.declare_theorem(p.fib_add_two, ty, value)
}

// ============================================================================
// `fib_le_succ` and `fib_pos_of_pos`.
// ============================================================================

/// `Nat.fib_le_succ : ∀ n, Le (fib n) (fib (succ n))`. Induction on `n`; the
/// step needs no induction hypothesis — `fib_add_two` plus `le_add_right`
/// gives it unconditionally at every `n`.
fn declare_fib_le_succ(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let motive = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
        let fi = d.const_app(p.fib, &[i]);
        let si = d.succ(i);
        let fsi = d.const_app(p.fib, &[si]);
        d.le(fi, fsi)
    };
    let base = |d: &mut NatDev<'_>| -> ExprId {
        let one = d.num(1);
        d.lemma(p.zero_le, &[one]) // Le 0 1, defeq to Le (fib 0) (fib 1)
    };
    let step = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
        let sj = d.succ(j);
        let ssj = d.succ(sj);
        let fib_sj = d.const_app(p.fib, &[sj]);
        let fib_j = d.const_app(p.fib, &[j]);
        let fib_ssj = d.const_app(p.fib, &[ssj]);

        let h_add2 = d.lemma(p.fib_add_two, &[j]); // fib_ssj = add fib_sj fib_j
        let sum = d.add(fib_sj, fib_j);
        let h_le = d.lemma(p.le_add_right, &[fib_sj, fib_j]); // Le fib_sj sum

        let rev = d.symm(fib_ssj, sum, h_add2); // sum = fib_ssj
        let motive = d.eq_motive(sum, &|d, x| d.le(fib_sj, x));
        d.transport(sum, motive, h_le, fib_ssj, rev)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.induct(&motive, &base, &step, n);
    let stmt = motive(d, n);

    let nat = d.nat_ty();
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.fib_le_succ, ty, value)
}

/// `Nat.fib_mono : ∀ a b, Le a b → Le (fib a) (fib b)`.
///
/// This is deliberately a composition theorem rather than another recurrence
/// proof: specialize the reusable adjacent-step monotonicity combinator to
/// `fib` and its already checked `fib_le_succ` theorem.
fn declare_fib_mono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(a, b);
    let fib = d.kernel().const_(p.fib, vec![]);
    let adjacent = d.kernel().const_(p.fib_le_succ, vec![]);
    let proof = d.const_app(p.monotone_of_le_succ, &[fib, adjacent, a, b, h]);
    let fib_a = d.const_app(p.fib, &[a]);
    let fib_b = d.const_app(p.fib, &[b]);
    let conclusion = d.le(fib_a, fib_b);
    let ty = {
        let arrow = d.kernel().pi(anon, h_ty, conclusion, BinderInfo::Default);
        let over_b = d.pi_fv(b_fv, nat, arrow);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, h_ty, proof);
        let over_b = d.lam_fv(b_fv, nat, over_h);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.declare_theorem(p.fib_mono, ty, value)
}

/// `∀ i, Lt zero (fib (succ i))` — every `fib` value past the zeroth is
/// positive, unconditionally (no hypothesis to discharge here; that is
/// [`declare_fib_pos_of_pos`]'s job). Induction on `i`; base is `le_refl 1`
/// (`Lt 0 1 ≡ Le 1 1`), step chains `fib_le_succ` through `lt_of_lt_of_le`.
fn fib_succ_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, i: ExprId| -> ExprId {
        let zero = d.zero();
        let si = d.succ(i);
        let fsi = d.const_app(p.fib, &[si]);
        d.lt(zero, fsi)
    };
    let base = |d: &mut NatDev<'_>| -> ExprId {
        let one = d.num(1);
        d.lemma(p.le_refl, &[one]) // Le 1 1, defeq to Lt 0 (fib 1)
    };
    let step = |d: &mut NatDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
        let sm = d.succ(m);
        let ssm = d.succ(sm);
        let fib_sm = d.const_app(p.fib, &[sm]);
        let fib_ssm = d.const_app(p.fib, &[ssm]);
        let h_le = d.lemma(p.fib_le_succ, &[sm]); // Le fib_sm fib_ssm
        let zero = d.zero();
        d.lemma(p.lt_of_lt_of_le, &[zero, fib_sm, fib_ssm, ih, h_le])
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof = d.induct(&motive, &base, &step, i);
    d.lam_fv(i_fv, nat, proof)
}

/// `Nat.fib_pos_of_pos : ∀ n, Lt zero n → Lt zero (fib n)`. From
/// [`fib_succ_pos`], transported along `pos_implies_succ_pred` (`n = succ
/// (pred n)` for `0 < n`).
fn declare_fib_pos_of_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let succ_pos = fib_succ_pos(d, &p);

    d.theorem(p.fib_pos_of_pos, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let hyp_ty = d.lt(zero, n);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let succ_pred_fn = pos_implies_succ_pred(d, &p, n);
        let eq_n_spn = d.apply(succ_pred_fn, &[hyp]); // n = succ (pred n)

        let pn = d.pred(n);
        let at_pred = d.apply(succ_pos, &[pn]); // Lt 0 (fib (succ pn))
        let spn = d.succ(pn);
        let rev = d.symm(n, spn, eq_n_spn); // spn = n

        let motive = d.eq_motive(spn, &|d, x| {
            let fx = d.const_app(p.fib, &[x]);
            let z = d.zero();
            d.lt(z, fx)
        });
        let result = d.transport(spn, motive, at_pred, n, rev);

        let fib_n = d.const_app(p.fib, &[n]);
        let concl = d.lt(zero, fib_n);
        let stmt = d.arrow(hyp_ty, concl);
        let body = d.lam_fv(hyp_fv, hyp_ty, result);
        (stmt, body)
    })?;
    Ok(())
}

// ============================================================================
// `sum_fib`.
// ============================================================================

/// `∀ n, add (sumRange fib n) 1 = fib (succ n)` — the subtraction-FREE form
/// of the sum identity, straight induction. `Nat.sub` never drives an
/// induction step in this file; only [`declare_sum_fib`]'s final conversion
/// touches it, once, unconditionally.
fn sum_fib_add_one_gen(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fib_const = d.kernel().const_(p.fib, vec![]);

    let stmt_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let sr = d.sum_range(fib_const, n);
        let one = d.num(1);
        let lhs = d.add(sr, one);
        let sn = d.succ(n);
        let rhs = d.const_app(p.fib, &[sn]);
        d.eq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.induct(
        &stmt_at,
        &|d| {
            let one = d.num(1);
            d.refl(one)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let ssm = d.succ(sm);
            let fib_m = d.const_app(p.fib, &[m]);
            let fib_sm = d.const_app(p.fib, &[sm]);
            let fib_ssm = d.const_app(p.fib, &[ssm]);
            let sr_m = d.sum_range(fib_const, m);
            let one = d.num(1);

            let lhs_start = {
                let inner = d.add(sr_m, fib_m);
                d.add(inner, one)
            };

            let h_rc = d.lemma(p.add_right_comm, &[sr_m, fib_m, one]);
            // h_rc : add (add sr_m fib_m) 1 = add (add sr_m 1) fib_m
            let stage1 = {
                let inner = d.add(sr_m, one);
                d.add(inner, fib_m)
            };

            let sr_m_1 = d.add(sr_m, one);
            let h_ih_congr = d.congr(sr_m_1, fib_sm, ih, &|d, x| d.add(x, fib_m));
            let stage2 = d.add(fib_sm, fib_m);

            let h_add2 = d.lemma(p.fib_add_two, &[m]); // fib_ssm = stage2
            let h_add2_rev = d.symm(fib_ssm, stage2, h_add2); // stage2 = fib_ssm

            let (_e, proof) = d.chain(
                lhs_start,
                &[(stage1, h_rc), (stage2, h_ih_congr), (fib_ssm, h_add2_rev)],
            );
            proof
        },
        n,
    );
    d.lam_fv(n_fv, nat, proof)
}

/// `Nat.sum_fib : ∀ n, sumRange fib n = sub (fib (succ n)) one`.
fn declare_sum_fib(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let general = sum_fib_add_one_gen(d, &p);

    d.theorem(p.sum_fib, 1, &|d, v| {
        let n = v[0];
        let fib_const = d.kernel().const_(p.fib, vec![]);
        let sr_n = d.sum_range(fib_const, n);
        let sn = d.succ(n);
        let fib_sn = d.const_app(p.fib, &[sn]);
        let one = d.num(1);

        let h1 = d.apply(general, &[n]); // add sr_n 1 = fib_sn
        let add_srn_1 = d.add(sr_n, one);

        let h2 = d.lemma(p.add_comm, &[sr_n, one]); // add sr_n 1 = add 1 sr_n
        let add_1_srn = d.add(one, sr_n);

        let rev_h1 = d.symm(add_srn_1, fib_sn, h1); // fib_sn = add_srn_1
        let (_e, h3) = d.chain(fib_sn, &[(add_srn_1, rev_h1), (add_1_srn, h2)]);
        // h3 : fib_sn = add_1_srn

        let h4 = d.congr(fib_sn, add_1_srn, h3, &|d, x| d.sub(x, one));
        let sub_fib_sn_1 = d.sub(fib_sn, one);
        let sub_add1srn_1 = d.sub(add_1_srn, one);

        let h5 = d.lemma(p.add_sub_cancel_left, &[one, sr_n]); // sub add_1_srn 1 = sr_n

        let (_e2, h6) = d.chain(sub_fib_sn_1, &[(sub_add1srn_1, h4), (sr_n, h5)]);
        // h6 : sub_fib_sn_1 = sr_n

        let final_proof = d.symm(sub_fib_sn_1, sr_n, h6); // sr_n = sub_fib_sn_1
        let stmt = d.eq(sr_n, sub_fib_sn_1);
        (stmt, final_proof)
    })?;
    Ok(())
}

// ============================================================================
// `add_regroup_four`: a private 4-term commutative regroup.
// ============================================================================

/// `Eq Nat (add (add a b) (add c e)) (add (add a c) (add b e))`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`binomial.rs`, `div_mod_lemmas.rs`,
/// `finite_set.rs`, `subset_sum.rs`, `rec_agreement.rs`,
/// `count_range_reversal.rs`, `eisenstein_lemma.rs`). Needed once, in
/// [`declare_fib_add`]'s step case, to reconcile the two different pairings
/// `fib_add_two` applied at two different indices produces.
fn add_regroup_four(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    // Generic-then-apply (`prove_eq_at`): a caller may pass compound
    // arguments outside the ring fragment; `prove_eq` on the literal terms
    // would (correctly) decline `NonRing` on those.
    crate::ring::nat::prove_eq_at(d, p, &[a, b, c, e], &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let ce = d.add(c, e);
        let lhs = d.add(ab, ce);
        let ac = d.add(a, c);
        let be = d.add(b, e);
        let rhs = d.add(ac, be);
        (lhs, rhs)
    })
    .unwrap_or_else(|err| panic!("ring declined add_regroup_four: {err:?}"))
}

// ============================================================================
// `fib_add`: the addition formula.
// ============================================================================

/// `Nat.fib_add : ∀ m n, fib (succ (add m n)) =
/// add (mul (fib m) (fib n)) (mul (fib (succ m)) (fib (succ n)))` — the
/// Fibonacci addition formula, in `succ`-shaped form (no `Nat.sub` anywhere).
///
/// Hand-checked (`fib = 0,1,1,2,3,5,8,13,…`): `m=0,n=0`: `fib 1 = 1` vs
/// `fib0*fib0+fib1*fib1 = 0+1 = 1`. `m=1,n=0`: `fib 2 = 1` vs
/// `fib1*fib0+fib2*fib1 = 0+1 = 1`. `m=1,n=1`: `fib 3 = 2` vs
/// `fib1*fib1+fib2*fib2 = 1+1 = 2`. `m=2,n=1`: `fib 4 = 3` vs
/// `fib2*fib1+fib3*fib2 = 1+2 = 3`. `m=2,n=2`: `fib 5 = 5` vs
/// `fib2*fib2+fib3*fib3 = 1+4 = 5`. `m=3,n=2`: `fib 6 = 8` vs
/// `fib3*fib2+fib4*fib3 = 2+6 = 8`. `m=3,n=3`: `fib 7 = 13` vs
/// `fib3^2+fib4^2 = 4+9 = 13`. All match.
///
/// Proved by pairing two statements per index and inducting ORDINARILY on
/// `n` (`m` fixed, captured from the outer closure) — the "prove `P n ∧ P
/// (succ n)` together by ordinary `Nat.rec`" device this file's own module
/// doc already names for PROVING a proposition, as opposed to DEFINING a
/// function (which is what ruled it out for `fib` itself). `R(n) := And
/// (stmt_at n) (stmt_at (succ n))`, where `stmt_at k` is the statement at
/// index `k`. The successor step reads `stmt_at (succ j)` off the induction
/// hypothesis's second half for free (no work), and derives the NEW second
/// half, `stmt_at (succ (succ j))`, from `fib_add_two` applied at TWO
/// different indices (`succ k` to split the goal, then `j` and `succ j` to
/// fold the two products each back into one), `left_distrib`, and
/// [`add_regroup_four`] to reconcile the two different groupings those two
/// substitutions produce.
fn declare_fib_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.fib_add, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let succ_m = d.succ(m);
        let fm = d.const_app(p.fib, &[m]);
        let fm1 = d.const_app(p.fib, &[succ_m]);

        // `fib (succ (add m k)) = add (mul fm (fib k)) (mul fm1 (fib (succ k)))`
        let stmt_at = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let mk = d.add(m, k);
            let idx = d.succ(mk);
            let lhs = d.const_app(p.fib, &[idx]);
            let fk = d.const_app(p.fib, &[k]);
            let succ_k = d.succ(k);
            let fk1 = d.const_app(p.fib, &[succ_k]);
            let fm_fk = d.mul(fm, fk);
            let fm1_fk1 = d.mul(fm1, fk1);
            let rhs = d.add(fm_fk, fm1_fk1);
            d.eq(lhs, rhs)
        };

        let pair_motive = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let a = stmt_at(d, k);
            let succ_k = d.succ(k);
            let b = stmt_at(d, succ_k);
            d.const_app(p.logic.and, &[a, b])
        };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let one = d.num(1);
            let a_ty = stmt_at(d, zero);
            let b_ty = stmt_at(d, one);

            // A(0): fib (succ (add m 0)) = add (mul fm (fib 0)) (mul fm1 (fib 1))
            //   `fib (succ (add m 0))` is defeq `fm1`.
            let a_proof = {
                let fm_zero = d.mul(fm, zero);
                let fm1_one = d.mul(fm1, one);
                let term0 = d.add(fm_zero, fm1_one);
                let term1 = d.add(zero, fm1_one);
                let term2 = d.add(zero, fm1);
                let h1 = {
                    let h = d.lemma(p.mul_zero, &[fm]); // mul fm 0 = 0
                    d.congr(fm_zero, zero, h, &|d, x| {
                        let fm1_one = d.mul(fm1, one);
                        d.add(x, fm1_one)
                    })
                };
                let h2 = {
                    let h = d.lemma(p.mul_one, &[fm1]); // mul fm1 1 = fm1
                    d.congr(fm1_one, fm1, h, &|d, x| d.add(zero, x))
                };
                let h3 = d.lemma(p.zero_add, &[fm1]); // add 0 fm1 = fm1
                let (_e, chained) = d.chain(term0, &[(term1, h1), (term2, h2), (fm1, h3)]);
                d.symm(term0, fm1, chained) // fm1 = term0
            };

            // B(0) = stmt_at(1): fib (succ (add m 1)) =
            //   add (mul fm (fib 1)) (mul fm1 (fib 2))
            //   `fib (succ (add m 1))` is defeq `fib (succ (succ m))`, related
            //   to `fm, fm1` by `fib_add_two m`.
            let b_proof = {
                let succ_succ_m = d.succ(succ_m);
                let start = d.const_app(p.fib, &[succ_succ_m]);
                let sum = d.add(fm1, fm);
                let h_add2 = d.lemma(p.fib_add_two, &[m]); // fib (succ succ m) = add fm1 fm
                let swapped = d.add(fm, fm1);
                let h_comm = d.lemma(p.add_comm, &[fm1, fm]); // add fm1 fm = add fm fm1
                let fm_one = d.mul(fm, one);
                let mid = d.add(fm_one, fm1);
                let h3 = {
                    let mul_one_fm = d.lemma(p.mul_one, &[fm]); // mul fm 1 = fm
                    let h = d.symm(fm_one, fm, mul_one_fm); // fm = mul fm 1
                    d.congr(fm, fm_one, h, &|d, x| d.add(x, fm1))
                };
                let fm1_one = d.mul(fm1, one);
                let target = d.add(fm_one, fm1_one);
                let h4 = {
                    let mul_one_fm1 = d.lemma(p.mul_one, &[fm1]); // mul fm1 1 = fm1
                    let h = d.symm(fm1_one, fm1, mul_one_fm1); // fm1 = mul fm1 1
                    d.congr(fm1, fm1_one, h, &|d, x| {
                        let fm_one = d.mul(fm, one);
                        d.add(fm_one, x)
                    })
                };
                let (_e, proof) = d.chain(
                    start,
                    &[(sum, h_add2), (swapped, h_comm), (mid, h3), (target, h4)],
                );
                proof
            };

            d.const_app(p.logic.and_intro, &[a_ty, b_ty, a_proof, b_proof])
        };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let a_ty = stmt_at(d, j);
            let succ_j = d.succ(j);
            let b_ty = stmt_at(d, succ_j);
            let ih_a = and_left(d, a_ty, b_ty, ih); // stmt_at(j)
            let ih_b = and_right(d, a_ty, b_ty, ih); // stmt_at(succ j)

            let new_first = ih_b;

            let succ_succ_j = d.succ(succ_j);
            let succ_succ_succ_j = d.succ(succ_succ_j);
            let k = d.add(m, j);
            let succ_k = d.succ(k);
            let succ_succ_k = d.succ(succ_k);
            let succ_succ_succ_k = d.succ(succ_succ_k);

            let fj = d.const_app(p.fib, &[j]);
            let fj1 = d.const_app(p.fib, &[succ_j]);
            let fj2 = d.const_app(p.fib, &[succ_succ_j]);
            let fj3 = d.const_app(p.fib, &[succ_succ_succ_j]);
            let fib_succ_k = d.const_app(p.fib, &[succ_k]);
            let fib_succ_succ_k = d.const_app(p.fib, &[succ_succ_k]);

            let a_term = d.mul(fm, fj1);
            let b_term = d.mul(fm1, fj2);
            let c_term = d.mul(fm, fj);
            let e_term = d.mul(fm1, fj1);

            let start = d.const_app(p.fib, &[succ_succ_succ_k]);

            // Step 1: `fib_add_two` at `succ k`, splitting the goal in two.
            let next1 = d.add(fib_succ_succ_k, fib_succ_k);
            let h1 = d.lemma(p.fib_add_two, &[succ_k]);

            // Step 2: substitute `fib_succ_succ_k` via `ih_b` (= stmt_at(succ j)).
            let ab_term = d.add(a_term, b_term);
            let next2 = d.add(ab_term, fib_succ_k);
            let h2 = d.congr(fib_succ_succ_k, ab_term, ih_b, &|d, x| d.add(x, fib_succ_k));

            // Step 3: substitute `fib_succ_k` via `ih_a` (= stmt_at(j)).
            let ce_term = d.add(c_term, e_term);
            let next3 = d.add(ab_term, ce_term);
            let h3 = d.congr(fib_succ_k, ce_term, ih_a, &|d, x| {
                let ab_term = d.add(a_term, b_term);
                d.add(ab_term, x)
            });

            // Step 4: the 4-term regroup, `(A+B)+(C+E) = (A+C)+(B+E)`.
            let ac_term = d.add(a_term, c_term);
            let be_term = d.add(b_term, e_term);
            let next4 = d.add(ac_term, be_term);
            let h4 = add_regroup_four(d, &p, a_term, b_term, c_term, e_term);

            // Step 5: fold each pair back into one `mul`, via `left_distrib`
            // reversed and `fib_add_two` reversed (at `j`, then at `succ j`).
            let fm_fj2 = d.mul(fm, fj2);
            let ac_to_fm_fj2 = {
                let fj1_fj = d.add(fj1, fj);
                let folded = d.mul(fm, fj1_fj);
                let left_distrib_h = d.lemma(p.left_distrib, &[fm, fj1, fj]);
                let h_ld = d.symm(folded, ac_term, left_distrib_h);
                let h_fib = {
                    let h = d.lemma(p.fib_add_two, &[j]); // fj2 = add fj1 fj
                    d.symm(fj2, fj1_fj, h) // add fj1 fj = fj2
                };
                let h_fold = d.congr(fj1_fj, fj2, h_fib, &|d, x| d.mul(fm, x));
                d.trans(ac_term, folded, fm_fj2, h_ld, h_fold)
            };
            let fm1_fj3 = d.mul(fm1, fj3);
            let be_to_fm1_fj3 = {
                let fj2_fj1 = d.add(fj2, fj1);
                let folded = d.mul(fm1, fj2_fj1);
                let left_distrib_h = d.lemma(p.left_distrib, &[fm1, fj2, fj1]);
                let h_ld = d.symm(folded, be_term, left_distrib_h);
                let h_fib = {
                    let h = d.lemma(p.fib_add_two, &[succ_j]); // fj3 = add fj2 fj1
                    d.symm(fj3, fj2_fj1, h) // add fj2 fj1 = fj3
                };
                let h_fold = d.congr(fj2_fj1, fj3, h_fib, &|d, x| d.mul(fm1, x));
                d.trans(be_term, folded, fm1_fj3, h_ld, h_fold)
            };

            let next5 = d.add(fm_fj2, be_term);
            let h5 = d.congr(ac_term, fm_fj2, ac_to_fm_fj2, &|d, x| {
                let be_term = d.add(b_term, e_term);
                d.add(x, be_term)
            });

            let target = d.add(fm_fj2, fm1_fj3);
            let h6 = d.congr(be_term, fm1_fj3, be_to_fm1_fj3, &|d, x| {
                let fm_fj2 = d.mul(fm, fj2);
                d.add(fm_fj2, x)
            });

            let (_e, new_second) = d.chain(
                start,
                &[
                    (next1, h1),
                    (next2, h2),
                    (next3, h3),
                    (next4, h4),
                    (next5, h5),
                    (target, h6),
                ],
            );

            let new_a_ty = stmt_at(d, succ_j);
            let new_b_ty = stmt_at(d, succ_succ_j);
            d.const_app(
                p.logic.and_intro,
                &[new_a_ty, new_b_ty, new_first, new_second],
            )
        };

        let pair_proof = d.induct(&pair_motive, &base, &step, n);
        let a_ty = stmt_at(d, n);
        let succ_n = d.succ(n);
        let b_ty = stmt_at(d, succ_n);
        let proof = and_left(d, a_ty, b_ty, pair_proof);
        (a_ty, proof)
    })?;
    Ok(())
}

// ============================================================================
// `coprime_fib_succ`.
// ============================================================================

/// `Nat.coprime_fib_succ : ∀ n, gcd (fib n) (fib (succ n)) = 1` — consecutive
/// Fibonacci numbers are coprime.
///
/// Ordinary induction on `n`; the base case is `gcd_zero_left` at `1`
/// (`gcd (fib 0) (fib 1) = gcd 0 1 = 1`, defeq on both `fib` calls — exactly
/// the same device [`declare_fib_le_succ`]'s base case uses). The step
/// NEVER computes the new `gcd` equation directly: it shows the new gcd
/// divides `1`, then closes with `eq_one_of_dvd_one`. The divisibility
/// chase, writing `g` for the new gcd: `g` divides both its arguments
/// (`gcd_dvd_left`, `gcd_dvd_right`); `fib_add_two` rewrites the LARGER
/// argument as a sum, and `dvd_add_iff_right` peels the known-divisible
/// summand off, giving `g` divides the SMALLER fib value too; `dvd_gcd`
/// then gives `g` divides the OLD gcd, which the induction hypothesis says
/// is `1`.
fn declare_coprime_fib_succ(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.coprime_fib_succ, 1, &|d, values| {
        let n = values[0];

        let motive = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
            let fk = d.const_app(p.fib, &[k]);
            let succ_k = d.succ(k);
            let fk1 = d.const_app(p.fib, &[succ_k]);
            let g = d.gcd(fk, fk1);
            let one = d.num(1);
            d.eq(g, one)
        };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let one = d.num(1);
            d.lemma(p.gcd_zero_left, &[one]) // gcd 0 1 = 1, defeq gcd (fib 0) (fib 1) = 1
        };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            // ih : Eq (gcd (fib j) (fib (succ j))) 1
            let fj = d.const_app(p.fib, &[j]);
            let succ_j = d.succ(j);
            let fj1 = d.const_app(p.fib, &[succ_j]);
            let succ_succ_j = d.succ(succ_j);
            let fj2 = d.const_app(p.fib, &[succ_succ_j]);
            let g = d.gcd(fj1, fj2);
            let one = d.num(1);

            let g_dvd_fj1 = d.lemma(p.gcd_dvd_left, &[fj1, fj2]); // g | fj1
            let g_dvd_fj2 = d.lemma(p.gcd_dvd_right, &[fj1, fj2]); // g | fj2

            // fj2 = add fj1 fj  (fib_add_two j)
            let h_add2 = d.lemma(p.fib_add_two, &[j]);
            let sum = d.add(fj1, fj);
            let g_dvd_sum = {
                let motive = d.eq_motive(fj2, &|d, x| d.dvd(g, x));
                d.transport(fj2, motive, g_dvd_fj2, sum, h_add2) // g | (fj1 + fj)
            };

            // dvd_add_iff_right : dvd g fj1 -> (dvd g fj <-> dvd g (fj1+fj))
            let iff_g = d.lemma(p.dvd_add_iff_right, &[g, fj1, fj, g_dvd_fj1]);
            let dvd_fj_ty = d.dvd(g, fj);
            let dvd_sum_ty = d.dvd(g, sum);
            let reverse = iff_reverse(d, dvd_fj_ty, dvd_sum_ty, iff_g);
            let g_dvd_fj = d.apply(reverse, &[g_dvd_sum]); // g | fj

            // g | gcd (fj, fj1) via dvd_gcd
            let g_dvd_gcd_j = d.lemma(p.dvd_gcd, &[g, fj, fj1, g_dvd_fj, g_dvd_fj1]);
            let gcd_j = d.gcd(fj, fj1);
            let g_dvd_one = {
                let motive = d.eq_motive(gcd_j, &|d, x| d.dvd(g, x));
                d.transport(gcd_j, motive, g_dvd_gcd_j, one, ih) // g | 1
            };
            d.lemma(p.eq_one_of_dvd_one, &[g, g_dvd_one])
        };

        let proof = d.induct(&motive, &base, &step, n);
        (motive(d, n), proof)
    })?;
    Ok(())
}

// ============================================================================
// `fib_add_two_strictmono` and `fib_strictmonoOn`.
// ============================================================================

/// `Lt (fib (succ (succ n))) (fib (succ (succ (succ n))))` — the
/// shifted-by-two Fibonacci sequence's adjacent-step strict inequality,
/// unconditional in `n`.
///
/// Retired to the `tactic` combinator (ADR-1589), `Tactic::Linarith` alone
/// (no `Simp` stage): the hand proof this replaces is itself "rewrite [an
/// equation hypothesis] then an order step" (transport `h_add2` through an
/// `add_lt_add_left`/`add_zero` chain), and `linarith`'s own `collect`
/// already turns an `Eq` HYPOTHESIS into both `Le` directions and searches a
/// Farkas certificate over every hypothesis it is given — no separate
/// rewrite stage is needed when the rewriting is of a HYPOTHESIS rather than
/// the goal itself. `fib(...)` is an opaque atom to `linarith` either way;
/// the certificate is `1·(fib_sssn = fib_ssn+fib_sn, "down" direction) +
/// 1·(0 < fib_sn)`, which sums to exactly the goal.
fn fib_add_two_lt_succ(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let sn = d.succ(n);
    let ssn = d.succ(sn);
    let sssn = d.succ(ssn);

    let fib_ssn = d.const_app(p.fib, &[ssn]); // fib(n+2)
    let fib_sssn = d.const_app(p.fib, &[sssn]); // fib(n+3)
    let fib_sn = d.const_app(p.fib, &[sn]); // fib(n+1)

    // h_add2 : fib(n+3) = fib(n+2) + fib(n+1)
    let h_add2 = d.lemma(p.fib_add_two, &[sn]);
    let fib_ssn_plus_fibsn = d.add(fib_ssn, fib_sn);
    let h_add2_ty = d.eq(fib_sssn, fib_ssn_plus_fibsn);

    // h_pos : Lt zero fib(n+1)
    let h_zlt = d.zero_lt_succ(n); // Lt zero (succ n)
    let h_pos = d.lemma(p.fib_pos_of_pos, &[sn, h_zlt]);
    let zero = d.zero();
    let h_pos_ty = d.lt(zero, fib_sn);

    let goal = d.lt(fib_ssn, fib_sssn);
    let assumptions = [(h_add2_ty, h_add2), (h_pos_ty, h_pos)];
    let ctx = crate::tactic::Ctx {
        prelude: p,
        assumptions: &assumptions,
        rules: &[],
    };
    crate::tactic::run(d, &ctx, &crate::tactic::Tactic::Linarith, goal)
        .unwrap_or_else(|e| panic!("fib_add_two_lt_succ: linarith declined: {e:?}"))
}

/// `Nat.fib_add_two_strictmono : ∀ a b, Lt a b → Lt (fib (succ (succ a)))
/// (fib (succ (succ b)))`. Induction on `b` (fixing `a`), mirroring
/// `perfect.rs`'s `pow_lt_pow_of_lt` exactly but with no base-positivity
/// hypothesis to thread, since [`fib_add_two_lt_succ`] holds unconditionally.
///
/// Base (`b = zero`): `Lt a zero` is impossible (`not_lt_zero`); `False.rec`
/// closes it vacuously. Step (`b = succ b'`, `ih : Lt a b' → …`): `h : Lt a
/// (succ b')` (defeq `Le (succ a) (succ b')`) strips to `Le a b'` via
/// `le_of_succ_le_succ`, then `lt_or_eq_of_le` splits:
/// - `Lt a b'`: `ih` gives the result at `b'`; [`fib_add_two_lt_succ`] at
///   `b'` gives the adjacent step, weakened `Lt` to `Le` (`le_succ` +
///   `le_trans`, since `Lt` IS `Le (succ ·) ·`) and composed via
///   `lt_of_lt_of_le`.
/// - `Eq a b'`: [`fib_add_two_lt_succ`] at `a` gives `Lt (fib(a+2))
///   (fib(a+3))` directly; transport along `congr succ` of the equality
///   lands on the goal.
fn declare_fib_add_two_strictmono(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fib_add_two_strictmono, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let sa_ = d.succ(a);
        let ssa = d.succ(sa_);
        let fib_a2 = d.const_app(p.fib, &[ssa]);

        let motive = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
            let hyp = d.lt(a, bb);
            let sbb_ = d.succ(bb);
            let ssbb = d.succ(sbb_);
            let fib_b2 = d.const_app(p.fib, &[ssbb]);
            let concl = d.lt(fib_a2, fib_b2);
            d.arrow(hyp, concl)
        };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hyp_ty = d.lt(a, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let not_lt = d.lemma(p.not_lt_zero, &[a]); // Not (Lt a zero)
            let contradiction = d.apply(not_lt, &[hyp]); // False

            let s_zero_ = d.succ(zero);
            let ss_zero = d.succ(s_zero_);
            let fib_zero2 = d.const_app(p.fib, &[ss_zero]);
            let target = d.lt(fib_a2, fib_zero2);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let motive_false = {
                let anon = d.anon_name();
                d.kernel().lam(anon, false_ty, target, BinderInfo::Default)
            };
            let level_zero = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let body = d.apply(false_rec, &[motive_false, contradiction]);
            d.lam_fv(hyp_fv, hyp_ty, body)
        };

        let step = |d: &mut NatDev<'_>, bp: ExprId, ih: ExprId| -> ExprId {
            let sbp = d.succ(bp);
            let hyp_ty = d.lt(a, sbp); // defeq Le (succ a) (succ bp)
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);

            let le_a_bp = d.lemma(p.le_of_succ_le_succ, &[a, bp, hyp]); // Le a bp
            let split = d.lemma(p.lt_or_eq_of_le, &[a, bp, le_a_bp]); // Lt a bp ∨ Eq a bp

            let sbp_ = d.succ(bp);
            let ssbp = d.succ(sbp_);
            let fib_bp2 = d.const_app(p.fib, &[ssbp]);
            let ssbp_ = d.succ(sbp);
            let ssbp2 = d.succ(ssbp_);
            let fib_sbp2 = d.const_app(p.fib, &[ssbp2]);
            let goal = d.lt(fib_a2, fib_sbp2);
            let lt_ty = d.lt(a, bp);
            let eq_ty = d.eq(a, bp);

            let lt_branch = {
                let lt_fv = d.fresh_fvar();
                let lt_a_bp = d.kernel().fvar(lt_fv);
                let ih_result = d.apply(ih, &[lt_a_bp]); // Lt fib_a2 fib_bp2

                let step_lt = fib_add_two_lt_succ(d, &p, bp); // Lt fib_bp2 fib_sbp2
                let succ_fib_bp2 = d.succ(fib_bp2);
                let le_fib_bp2_self_succ = d.lemma(p.le_succ, &[fib_bp2]); // Le fib_bp2 (succ fib_bp2)
                let le_fib_bp2_sbp2 = d.lemma(
                    p.le_trans,
                    &[
                        fib_bp2,
                        succ_fib_bp2,
                        fib_sbp2,
                        le_fib_bp2_self_succ,
                        step_lt,
                    ],
                ); // Le fib_bp2 fib_sbp2

                let result = d.lemma(
                    p.lt_of_lt_of_le,
                    &[fib_a2, fib_bp2, fib_sbp2, ih_result, le_fib_bp2_sbp2],
                );
                d.lam_fv(lt_fv, lt_ty, result)
            };

            let eq_branch = {
                let eq_fv = d.fresh_fvar();
                let eq_a_bp = d.kernel().fvar(eq_fv);

                let step_a = fib_add_two_lt_succ(d, &p, a); // Lt fib_a2 (fib (succ (succ (succ a))))
                let sa__ = d.succ(a);
                let ssa__ = d.succ(sa__);
                let sssa = d.succ(ssa__);
                let fib_succ_a2 = d.const_app(p.fib, &[sssa]);
                let congr_eq = d.congr(a, bp, eq_a_bp, &|d, x| {
                    let sx_ = d.succ(x);
                    let ssx_ = d.succ(sx_);
                    let ssx = d.succ(ssx_);
                    d.const_app(p.fib, &[ssx])
                }); // Eq fib_succ_a2 fib_sbp2
                let motive_t = d.eq_motive(fib_succ_a2, &|d, x| d.lt(fib_a2, x));
                let result = d.transport(fib_succ_a2, motive_t, step_a, fib_sbp2, congr_eq);
                d.lam_fv(eq_fv, eq_ty, result)
            };

            let anon = d.anon_name();
            let logic = d.prelude().logic;
            let or_ty = d.const_app(logic.or, &[lt_ty, eq_ty]);
            let motive_or = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
            let or_rec = d.kernel().const_(logic.or_rec, vec![]);
            let case_result = d.apply(
                or_rec,
                &[lt_ty, eq_ty, motive_or, lt_branch, eq_branch, split],
            );
            d.lam_fv(hyp_fv, hyp_ty, case_result)
        };

        let proof = d.induct(&motive, &base, &step, b);
        let stmt = motive(d, b);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.fib_strictmonoOn : ∀ a b, Le 2 a → Le 2 b → Lt a b → Lt (fib a) (fib
/// b)` — Mathlib's `StrictMonoOn Nat.fib (Set.Ici 2)`, unwound to two
/// explicit lower-bound hypotheses (matching `fib_mono`'s own style of
/// instantiating the abstract order-theory combinator concretely).
///
/// `Le 2 x` peeled to `x = succ (succ x2)` by two applications of
/// `pos_implies_succ_pred`: the first needs `Lt 0 x`, read directly off `Le
/// 2 x` (which IS `Lt 1 x` up to how `2`/`succ 1` are built — both are
/// `succ(succ zero)`); the second needs `Lt 0 (pred x)`, obtained by
/// transporting `Le 2 x` along the first equation to `Le 2 (succ (pred x))`
/// and stripping one `succ` via `le_of_succ_le_succ`. Composing the two
/// equations gives `x = succ (succ x2)`; doing this for both `a` and `b`,
/// stripping the double `succ` off the transported hypothesis `Lt a b` the
/// same way, and applying [`declare_fib_add_two_strictmono`] lands on `Lt
/// (fib (succ (succ a2))) (fib (succ (succ b2)))`, which transports back
/// along the two (reversed) equations to the goal.
fn declare_fib_strictmonoon(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // `peel(x, hx : Le 2 x) -> (x2, eq_x : Eq x (succ (succ x2)))`.
    let peel = |d: &mut NatDev<'_>, x: ExprId, hx: ExprId| -> (ExprId, ExprId) {
        // hx : Le 2 x, read directly as Lt 1 x (2 ≡ succ 1 by construction).
        let one = d.num(1);
        let eq1 = pos_implies_succ_pred(d, &p, x); // fn : Lt 0 x -> Eq x (succ (pred x))
        // Lt 0 x from hx read as Lt 1 x, via zero_lt_via_c (works for ANY c).
        let h0x = zero_lt_via_c(d, &p, one, x, hx); // Lt 0 x
        let eq_x1 = d.apply(eq1, &[h0x]); // x = succ (pred x)
        let x1 = d.pred(x);
        let sx1 = d.succ(x1);

        // Transport hx : Le 2 x along eq_x1 to get Le 2 (succ x1).
        let motive_h = d.eq_motive(x, &|d, y| {
            let two = d.num(2);
            d.le(two, y)
        });
        let hx_at_sx1 = d.transport(x, motive_h, hx, sx1, eq_x1); // Le 2 (succ x1)
        let h_x1 = d.lemma(p.le_of_succ_le_succ, &[one, x1, hx_at_sx1]); // Le 1 x1 = Lt 0 x1

        let eq2 = pos_implies_succ_pred(d, &p, x1);
        let eq_x1_x2 = d.apply(eq2, &[h_x1]); // x1 = succ (pred x1)
        let x2 = d.pred(x1);
        let sx2 = d.succ(x2);
        let ssx2 = d.succ(sx2);

        // eq_x1_ssx2 : succ x1 = succ (succ x2)
        let eq_sx1_ssx2 = d.congr(x1, sx2, eq_x1_x2, &|d, y| d.succ(y));
        // eq_x_ssx2 : x = succ (succ x2), by trans(eq_x1, eq_sx1_ssx2)
        let eq_x_ssx2 = d.trans(x, sx1, ssx2, eq_x1, eq_sx1_ssx2);
        (x2, eq_x_ssx2)
    };

    d.theorem(p.fib_strictmonoon, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let two = d.num(2);
        let ha_ty = d.le(two, a);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_ty = d.le(two, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let hab_ty = d.lt(a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let (a2, eq_a) = peel(d, a, ha); // a = succ (succ a2)
        let (b2, eq_b) = peel(d, b, hb); // b = succ (succ b2)

        // Transport hab : Lt a b along eq_a, eq_b to Lt (succ (succ a2)) (succ (succ b2)).
        let sa2_ = d.succ(a2);
        let ssa2 = d.succ(sa2_);
        let sb2_ = d.succ(b2);
        let ssb2 = d.succ(sb2_);
        let motive_ab1 = d.eq_motive(a, &|d, x| d.lt(x, b));
        let hab1 = d.transport(a, motive_ab1, hab, ssa2, eq_a); // Lt ssa2 b
        let motive_ab2 = d.eq_motive(b, &|d, y| d.lt(ssa2, y));
        let hab2 = d.transport(b, motive_ab2, hab1, ssb2, eq_b); // Lt ssa2 ssb2

        // Strip the double succ from `hab2 : Lt ssa2 ssb2` (defeq `Le (succ
        // ssa2) ssb2`, i.e. `Le (succ (succ (succ a2))) (succ (succ b2))`) by
        // two applications of `le_of_succ_le_succ`, landing on `Lt a2 b2`.
        let sa2 = d.succ(a2);
        let sb2 = d.succ(b2);
        let h1 = d.lemma(p.le_of_succ_le_succ, &[ssa2, sb2, hab2]); // Le ssa2 sb2 = Lt sa2 sb2...
        let h2 = d.lemma(p.le_of_succ_le_succ, &[sa2, b2, h1]); // Le sa2 b2 = Lt a2 b2
        let hab_final = h2; // Lt a2 b2

        let strictmono = d.lemma(p.fib_add_two_strictmono, &[a2, b2, hab_final]);
        // strictmono : Lt (fib (succ (succ a2))) (fib (succ (succ b2))) = Lt (fib ssa2) (fib ssb2)

        // Transport back along symm(eq_a), symm(eq_b).
        let eq_a_rev = d.symm(a, ssa2, eq_a); // ssa2 = a
        let eq_b_rev = d.symm(b, ssb2, eq_b); // ssb2 = b
        let motive_back1 = d.eq_motive(ssa2, &|d, x| {
            let fib_x = d.const_app(p.fib, &[x]);
            let fib_ssb2 = d.const_app(p.fib, &[ssb2]);
            d.lt(fib_x, fib_ssb2)
        });
        let back1 = d.transport(ssa2, motive_back1, strictmono, a, eq_a_rev); // Lt (fib a) (fib ssb2)
        let motive_back2 = d.eq_motive(ssb2, &|d, y| {
            let fib_a = d.const_app(p.fib, &[a]);
            let fib_y = d.const_app(p.fib, &[y]);
            d.lt(fib_a, fib_y)
        });
        let back2 = d.transport(ssb2, motive_back2, back1, b, eq_b_rev); // Lt (fib a) (fib b)

        let fib_a = d.const_app(p.fib, &[a]);
        let fib_b = d.const_app(p.fib, &[b]);
        let concl = d.lt(fib_a, fib_b);
        let stmt = {
            let inner = d.arrow(hab_ty, concl);
            let with_hb = d.arrow(hb_ty, inner);
            d.arrow(ha_ty, with_hb)
        };
        let value = {
            let inner = d.lam_fv(hab_fv, hab_ty, back2);
            let with_hb = d.lam_fv(hb_fv, hb_ty, inner);
            d.lam_fv(ha_fv, ha_ty, with_hb)
        };
        (stmt, value)
    })?;
    Ok(())
}

// ============================================================================
// `fib_lt_fib`.
// ============================================================================

/// Non-dependent `Or.rec` (private copy; `irrational.rs`, `choose.rs` and
/// `primes.rs` each already carry their own, so this follows the existing
/// per-file pattern rather than introducing a new one).
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

/// `Nat.fib_lt_fib : ∀ m n, Le 2 m → Iff (Lt (fib m) (fib n)) (Lt m n)` —
/// Mathlib's `fib_lt_fib_iff`. See the field doc comment in `nat_prelude.rs`
/// for the proof route.
fn declare_fib_lt_fib(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fib_lt_fib, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let two = d.num(2);
        let hm_ty = d.le(two, m);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);

        let fib_m = d.const_app(p.fib, &[m]);
        let fib_n = d.const_app(p.fib, &[n]);
        let lt_fn_ty = d.lt(fib_m, fib_n);
        let lt_mn_ty = d.lt(m, n);

        // Forward: Lt fib_m fib_n -> Lt m n, by contrapositive on lt_or_ge.
        let forward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let dichotomy = d.lemma(p.lt_or_ge, &[m, n]); // Or (Lt m n) (Le n m)
            let ge_ty = d.le(n, m);

            let left_branch = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                d.lam_fv(h2_fv, lt_mn_ty, h2)
            };
            let right_branch = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let mono = d.lemma(p.fib_mono, &[n, m, h2]); // Le fib_n fib_m
                let contra = d.lemma(p.lt_of_lt_of_le, &[fib_m, fib_n, fib_m, h, mono]); // Lt fib_m fib_m
                let irrefl = d.lemma(p.lt_irrefl, &[fib_m]); // Not (Lt fib_m fib_m)
                let false_proof = d.apply(irrefl, &[contra]);
                let result = absurd(d, lt_mn_ty, false_proof);
                d.lam_fv(h2_fv, ge_ty, result)
            };

            let case_result = or_elim(
                d,
                &p,
                lt_mn_ty,
                ge_ty,
                lt_mn_ty,
                left_branch,
                right_branch,
                dichotomy,
            );
            d.lam_fv(h_fv, lt_fn_ty, case_result)
        };

        // Reverse: Lt m n -> Lt fib_m fib_n, via fib_strictmonoOn (needs Le 2 n too).
        let reverse = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // Lt m n

            let sm = d.succ(m);
            let le_m_sm = d.lemma(p.le_succ, &[m]); // Le m (succ m)
            let le_m_n = d.lemma(p.le_trans, &[m, sm, n, le_m_sm, h]); // Le m n
            let le_2_n = d.lemma(p.le_trans, &[two, m, n, hm, le_m_n]); // Le 2 n

            let result = d.lemma(p.fib_strictmonoon, &[m, n, hm, le_2_n, h]); // Lt fib_m fib_n
            d.lam_fv(h_fv, lt_mn_ty, result)
        };

        let iff_stmt = d.const_app(p.logic.iff, &[lt_fn_ty, lt_mn_ty]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[lt_fn_ty, lt_mn_ty, forward, reverse]);

        let stmt = d.arrow(hm_ty, iff_stmt);
        let value = d.lam_fv(hm_fv, hm_ty, iff_proof);
        (stmt, value)
    })?;
    Ok(())
}

// ============================================================================
// `le_fib_self`.
// ============================================================================

/// `∀ k, Le (add 5 k) (fib (add 5 k))` — the index-shifted growth fact
/// `le_fib_self` specializes. Never exposed as a prelude name (mirrors
/// `fib_aux_add_two_gen`'s own module-doc rationale).
///
/// Pair-induction on `k`, mirroring `declare_fib_add`'s `stmt_at k / stmt_at
/// (succ k)` device exactly: everything below is built from a SINGLE base
/// term `k5 := add 5 k` and its `succ`/`succ succ` shifts, never from a
/// second independently-built `add` term — the same discipline `fib_add`
/// uses (its own `mk = add m k`) to keep every shift a bare `succ`
/// application, which is what makes `add 5 (succ k)` unfold (one `ι` step,
/// regardless of `k`) to `succ (add 5 k)` for free.
///
/// Base (`k=0`): `P(0) = Le 5 (fib 5)`, defeq `Le 5 5` (`le_refl`); `P(1) =
/// Le 6 (fib 6)`, defeq `Le 6 8` (`le_add_right 6 2`) — both magnitudes tiny,
/// pure `δ`/`ι` unfolding.
///
/// Step (`k=j → succ j`, `ih : P(j) ∧ P(succ j)`): writing `K := add 5 j`,
/// `sK := succ K`, `ssK := succ sK`, the new second half needs `Le ssK (fib
/// ssK)`.
/// 1. Sum the two induction hypotheses: `Le (add K sK) (add (fib K) (fib
///    sK))`, via `add_le_add_right`/`add_le_add_left` + `le_trans`.
/// 2. The sum carries `+1` of slack over `ssK`: since `Le 1 K` (`K ≥ 5`,
///    chained through `le_add_right`), `lt_add_one` at `sK` plus
///    `add_le_add_left` gives `Lt sK (add sK K)`, i.e. (by `add_comm`) `Lt sK
///    (add K sK)` — which unfolds (by `Lt`'s own definition) to `Le ssK (add
///    K sK)`.
/// 3. Chain 1 and 2 (`le_trans`) to `Le ssK (add (fib K) (fib sK))`, then
///    `add_comm` and `fib_add_two` (reversed) rewrite the right side to `fib
///    ssK`.
fn fib_ge_shifted_gen(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let five = d.num(5);

    let stmt_at = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let idx = d.add(five, k);
        let fib_idx = d.const_app(p.fib, &[idx]);
        d.le(idx, fib_idx)
    };

    let pair_motive = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let a = stmt_at(d, k);
        let sk = d.succ(k);
        let b = stmt_at(d, sk);
        d.const_app(p.logic.and, &[a, b])
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let one = d.num(1);
        let a_ty = stmt_at(d, zero);
        let b_ty = stmt_at(d, one);

        let a_proof = {
            let five2 = d.num(5);
            d.lemma(p.le_refl, &[five2]) // Le 5 5, defeq Le 5 (fib 5)
        };
        let b_proof = {
            let six = d.num(6);
            let two = d.num(2);
            d.lemma(p.le_add_right, &[six, two]) // Le 6 (add 6 2), defeq Le 6 (fib 6)
        };
        d.const_app(p.logic.and_intro, &[a_ty, b_ty, a_proof, b_proof])
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let a_ty = stmt_at(d, j);
        let sj = d.succ(j);
        let b_ty = stmt_at(d, sj);
        let ih_a = and_left(d, a_ty, b_ty, ih); // Le K (fib K)
        let ih_b = and_right(d, a_ty, b_ty, ih); // Le sK (fib sK), up to defeq

        let k = d.add(five, j); // K
        let sk = d.succ(k); // sK
        let ssk = d.succ(sk); // ssK

        let fib_k = d.const_app(p.fib, &[k]);
        let fib_sk = d.const_app(p.fib, &[sk]);
        let fib_ssk = d.const_app(p.fib, &[ssk]);

        // Sum the two lower bounds: Le (K+sK) (fib_K+fib_sK).
        let h1 = d.lemma(p.add_le_add_right, &[sk, k, fib_k, ih_a]); // Le (K+sK) (fib_K+sK)
        let h2 = d.lemma(p.add_le_add_left, &[fib_k, sk, fib_sk, ih_b]); // Le (fib_K+sK) (fib_K+fib_sK)
        let k_sk = d.add(k, sk);
        let fibk_sk = d.add(fib_k, sk);
        let fibk_fibsk = d.add(fib_k, fib_sk);
        let h3 = d.lemma(p.le_trans, &[k_sk, fibk_sk, fibk_fibsk, h1, h2]);

        // Slack: Le 1 K (K = 5+j >= 5 >= 1).
        let one = d.num(1);
        let four = d.num(4);
        let five_lit = d.num(5);
        let h_1_le_5 = d.lemma(p.le_add_right, &[one, four]); // Le 1 (1+4), defeq Le 1 5
        let h_5_le_k = d.lemma(p.le_add_right, &[five_lit, j]); // Le 5 (5+j) = Le 5 K
        let h_1_le_k = d.lemma(p.le_trans, &[one, five_lit, k, h_1_le_5, h_5_le_k]); // Le 1 K

        // Lt sK (sK+K), then Lt sK (K+sK) via add_comm — defeq Le ssK (K+sK).
        let sk_1 = d.add(sk, one);
        let h_lt1 = d.lemma(p.lt_add_one, &[sk]); // Lt sK (sK+1)
        let sk_k = d.add(sk, k);
        let h_le1 = d.lemma(p.add_le_add_left, &[sk, one, k, h_1_le_k]); // Le (sK+1) (sK+K)
        let h_lt2 = d.lemma(p.lt_of_lt_of_le, &[sk, sk_1, sk_k, h_lt1, h_le1]); // Lt sK (sK+K)

        let h_comm1 = d.lemma(p.add_comm, &[sk, k]); // Eq (sK+K) (K+sK)
        let motive_c1 = d.eq_motive(sk_k, &|d, x| d.lt(sk, x));
        let h_lt3 = d.transport(sk_k, motive_c1, h_lt2, k_sk, h_comm1); // Lt sK (K+sK) = Le ssK (K+sK)

        // Chain: Le ssK (K+sK), Le (K+sK) (fib_K+fib_sK) -> Le ssK (fib_K+fib_sK).
        let h6 = d.lemma(p.le_trans, &[ssk, k_sk, fibk_fibsk, h_lt3, h3]);

        // Reorder to fib_sK+fib_K, then fold via fib_add_two (reversed).
        let h_comm2 = d.lemma(p.add_comm, &[fib_k, fib_sk]); // Eq (fib_K+fib_sK)(fib_sK+fib_K)
        let motive_c2 = d.eq_motive(fibk_fibsk, &|d, x| d.le(ssk, x));
        let fibsk_fibk = d.add(fib_sk, fib_k);
        let h7 = d.transport(fibk_fibsk, motive_c2, h6, fibsk_fibk, h_comm2); // Le ssK (fib_sK+fib_K)

        let h_add2 = d.lemma(p.fib_add_two, &[k]); // Eq fib_ssK (fib_sK+fib_K)
        let rev2 = d.symm(fib_ssk, fibsk_fibk, h_add2); // Eq (fib_sK+fib_K) fib_ssK
        let motive_c3 = d.eq_motive(fibsk_fibk, &|d, x| d.le(ssk, x));
        let new_second = d.transport(fibsk_fibk, motive_c3, h7, fib_ssk, rev2); // Le ssK fib_ssK

        let new_a_ty = stmt_at(d, sj);
        let ssj = d.succ(sj);
        let new_b_ty = stmt_at(d, ssj);
        d.const_app(p.logic.and_intro, &[new_a_ty, new_b_ty, ih_b, new_second])
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pair_proof = d.induct(&pair_motive, &base, &step, n);
    let a_ty = stmt_at(d, n);
    let sn = d.succ(n);
    let b_ty = stmt_at(d, sn);
    let shifted = and_left(d, a_ty, b_ty, pair_proof); // Le (5+n) (fib (5+n))
    d.lam_fv(n_fv, nat, shifted)
}

/// `Nat.le_fib_self : ∀ n, Le 5 n → Le n (fib n)`. `le_dest` reads the
/// hypothesis as a witness `k` with `add 5 k = n`; `Exists.rec` transports
/// [`fib_ge_shifted_gen`] applied at `k` along that equation to land on the
/// goal at `n`.
fn declare_le_fib_self(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let general = fib_ge_shifted_gen(d, &p);
    let nat = d.nat_ty();
    let anon = d.anon_name();

    d.theorem(p.le_fib_self, 1, &|d, v| {
        let n_var = v[0];
        let five_lit = d.num(5);
        let hyp_ty = d.le(five_lit, n_var);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let represented = d.lemma(p.le_dest, &[five_lit, n_var, hyp]); // Exists k, 5+k=n_var

        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(five_lit, k);
            let body = d.eq(sum, n_var);
            d.lam_fv(k_fv, nat, body)
        };
        let fib_n = d.const_app(p.fib, &[n_var]);
        let concl = d.le(n_var, fib_n);

        let represented_ty = {
            let one = d.level_one();
            let exists_ = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists_, &[nat, pred])
        };
        let motive = d
            .kernel()
            .lam(anon, represented_ty, concl, BinderInfo::Default);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(five_lit, k);
            let e_ty = d.eq(sum, n_var);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);

            let at_k = d.apply(general, &[k]); // Le (5+k) (fib (5+k))
            let motive_e = d.eq_motive(sum, &|d, x| {
                let fx = d.const_app(p.fib, &[x]);
                d.le(x, fx)
            });
            let transported = d.transport(sum, motive_e, at_k, n_var, e); // Le n_var (fib n_var)
            let with_e = d.lam_fv(e_fv, e_ty, transported);
            d.lam_fv(k_fv, nat, with_e)
        };

        let one_lvl = d.level_one();
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let body = d.apply(rec, &[nat, pred, motive, minor, represented]);

        let stmt = d.arrow(hyp_ty, concl);
        let value = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, value)
    })?;
    Ok(())
}

// ============================================================================
// `le_fib_add_one`.
// ============================================================================

/// `Nat.le_fib_add_one : ∀ n, Le n (add (fib n) 1)` — unconditional (Mathlib's
/// `n ≤ fib n + 1`).
///
/// Split at `Nat.lt_or_ge n 5`
/// ([`cases_lt_or_ge`](super::ops::cases_lt_or_ge)):
/// - `Le 5 n`: [`le_fib_self`](NatPrelude::le_fib_self) gives `Le n (fib n)`;
///   `le_add_right (fib n) 1` gives `Le (fib n) (add (fib n) 1)`; chain with
///   `le_trans`.
/// - `Lt n 5`: [`cases_lt_bound`](super::ops::cases_lt_bound) reduces this to
///   five concrete branches `n ∈ {0,1,2,3,4}`, each closed by `le_add_right`
///   (or `zero_le` at `n = 0`, which needs no reduction at all) at a hand-
///   picked slack `k` such that `Le i (add i k)` is defeq to `Le i (add (fib
///   i) 1)` — `fib i` unfolds for a literal `i` this small (`δ`/`ι`, no
///   theorem needed), exactly the device `le_fib_self`'s own base case uses
///   (`fib_ge_shifted_gen`'s `a_proof`/`b_proof` above). The margin is TIGHT
///   (`k = 0`, i.e. plain `le_refl`-shaped) at `i = 2, 3, 4`, which is the
///   algebraic fact that rules out a bare pair-induction for this theorem
///   (`docs/plan/status/228-fib-2.md`).
fn declare_le_fib_add_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let one = d.num(1);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let fib_x = d.const_app(p.fib, &[x]);
        let sum = d.add(fib_x, one);
        d.le(x, sum)
    };

    d.theorem(p.le_fib_add_one, 1, &|d, v| {
        let n = v[0];
        let five = d.num(5);

        let small = |d: &mut NatDev<'_>, n: ExprId, lt_n_5: ExprId| -> ExprId {
            // Slack `k` at each `i` so `add i k` numerically equals `fib
            // i + 1`: fib(0..4) = 0,1,1,2,3, so k = 1,1,0,0,0.
            let ks = [1u32, 1, 0, 0, 0];
            let mut branches: Vec<ExprId> = Vec::with_capacity(5);
            for i in 0..5u32 {
                let i_lit = d.num(i);
                let k_lit = d.num(ks[i as usize]);
                branches.push(d.lemma(p.le_add_right, &[i_lit, k_lit]));
            }
            cases_lt_bound(d, &p, n, 5, lt_n_5, &motive, &branches)
        };
        let big = |d: &mut NatDev<'_>, n: ExprId, le_5_n: ExprId| -> ExprId {
            let le_fib = d.lemma(p.le_fib_self, &[n, le_5_n]); // Le n (fib n)
            let fib_n = d.const_app(p.fib, &[n]);
            let one = d.num(1);
            let le_add = d.lemma(p.le_add_right, &[fib_n, one]); // Le (fib n) (add (fib n) 1)
            let sum = d.add(fib_n, one);
            d.lemma(p.le_trans, &[n, fib_n, sum, le_fib, le_add])
        };

        let body = cases_lt_or_ge(d, &p, n, five, &motive, &small, &big);
        let concl = motive(d, n);
        (concl, body)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_fib_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_fib_defs(d, p)?;
    declare_fib_add_two(d, p)?;
    declare_fib_le_succ(d, p)?;
    declare_fib_mono(d, p)?;
    declare_fib_pos_of_pos(d, p)?;
    declare_sum_fib(d, p)?;
    declare_fib_add(d, p)?;
    declare_coprime_fib_succ(d, p)?;
    declare_fib_add_two_strictmono(d, p)?;
    declare_fib_strictmonoon(d, p)?;
    declare_fib_lt_fib(d, p)?;
    declare_le_fib_self(d, p)?;
    declare_le_fib_add_one(d, p)?;
    Ok(())
}
