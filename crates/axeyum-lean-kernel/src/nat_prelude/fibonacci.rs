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
use super::finite::pos_implies_succ_pred;
use super::helpers::{and_left, and_right, iff_reverse};
use super::ops::{NatDev, NatOps};
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

/// `Eq Nat (add (add a b) (add c e)) (add (add a c) (add b e))` — there is no
/// `add_add_add_comm` in this prelude, so build it once from `add_assoc` and
/// `add_right_comm`: `(a+b)+(c+e) = ((a+b)+c)+e` [`add_assoc`, reversed]
/// `= ((a+c)+b)+e` [`add_right_comm` on the inner pair, under `(-)+e`]
/// `= (a+c)+(b+e)` [`add_assoc`]. Needed once, in [`declare_fib_add`]'s step
/// case, to reconcile the two different pairings `fib_add_two` applied at two
/// different indices produces.
fn add_regroup_four(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let p = *p;
    let ab = d.add(a, b);
    let ce = d.add(c, e);
    let start = d.add(ab, ce);

    let abc = d.add(ab, c);
    let step1 = d.add(abc, e);
    let h1 = {
        let fwd = d.lemma(p.add_assoc, &[ab, c, e]); // (ab+c)+e = ab+(c+e)
        d.symm(step1, start, fwd)
    };

    let ac = d.add(a, c);
    let acb = d.add(ac, b);
    let step2 = d.add(acb, e);
    let h2 = {
        let h_comm = d.lemma(p.add_right_comm, &[a, b, c]); // (a+b)+c = (a+c)+b
        d.congr(abc, acb, h_comm, &|d, x| d.add(x, e))
    };

    let be = d.add(b, e);
    let target = d.add(ac, be);
    let h3 = d.lemma(p.add_assoc, &[ac, b, e]); // (ac+b)+e = ac+(b+e)

    let (_end, proof) = d.chain(start, &[(step1, h1), (step2, h2), (target, h3)]);
    proof
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
    Ok(())
}
