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
//! # `gcd_fib`: pieces exist, not started
//!
//! `gcd (fib m) (fib n) = fib (gcd m n)` is not attempted. The pieces this
//! file DOES provide — `fib_add_two`, monotonicity (`fib_le_succ`), and
//! positivity (`fib_pos_of_pos`) — are necessary ingredients (any proof needs
//! to relate `fib` at a sum of indices, e.g. `fib (m+n) = fib m * fib (n+1) +
//! fib (m-1) * fib n`, itself unproved here), but the identity's own proof
//! (strong induction on the Euclidean algorithm's descent, mirroring
//! `gcd.rs`/`bezout.rs`'s use of `Nat.gcd`'s recursion) is its own slice.

use super::NatPrelude;
use super::finite::pos_implies_succ_pred;
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

/// Declare every theorem in this module.
pub(super) fn declare_fib_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_fib_defs(d, p)?;
    declare_fib_add_two(d, p)?;
    declare_fib_le_succ(d, p)?;
    declare_fib_pos_of_pos(d, p)?;
    declare_sum_fib(d, p)?;
    Ok(())
}
