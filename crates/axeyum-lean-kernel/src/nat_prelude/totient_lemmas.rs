//! The `ml430` `Nat.totient` mirrors that build on `totient.rs`'s
//! `Nat.countRange`/`Nat.totient` without needing the subset-permutation
//! machinery `totient.rs`'s own module doc calls out as separate, larger
//! work ("Euler's theorem itself needs a permutation/pairing argument over
//! the *subset* of residues coprime to `n`").
//!
//! ## Mirror-flip check
//!
//! Mathlib's `Nat.totient n := #{a ∈ range n | n.Coprime a}` (pinned v4.30
//! source, `Mathlib/Data/Nat/Totient.lean:38`) — the cardinality of the
//! coprime-to-`n` subset of `range n = [0,n)`. This kernel's `Nat.totient n
//! := countRange (fun k => beq (gcd k n) 1) n` (`totient.rs`) is the SAME
//! construction: a count over `[0,n)` filtered by a coprimality predicate
//! (`gcd k n = 1` vs Mathlib's `n.Coprime a` i.e. `gcd n a = 1` — the same
//! proposition by `gcd`'s commutativity, differing only in argument order,
//! which every mirror in this file either avoids needing or could bridge
//! with `gcd_comm` if it ever needed to — see "what does not land" below for
//! why it doesn't come up). So every mirror in the task list is an honest
//! flip target in principle; what blocks most of them is PROOF DIFFICULTY
//! over an honest statement, not a definitional mismatch.
//!
//! ## `Nat.coprime_succ_self` — the key building block landed here
//!
//! `∀ m, Eq (gcd m (succ m)) one` — consecutive naturals are coprime, not
//! previously named in this prelude (`gcd_comm`, `gcd_succ_self`, and
//! `coprime_succ_self` all return zero hits; the only prior `gcd_comm`-shaped
//! fact in the tree is `int_prelude`'s, over `Int` arguments). Falls out
//! cheaply from three already-declared facts, no new induction:
//! `coprime_add_self_right(m, one) : Iff (gcd m (add one m) = one) (gcd m
//! one = one)`, `coprime_one_right_iff(m) : Iff (gcd m one = one) True`
//! (so `gcd m one = one` unconditionally via `True.intro`), and `add one m =
//! succ m` (`succ_add` then `zero_add`, congr'd through `succ`).
//!
//! ## `Nat.totient_eq_zero` — the one closed here
//!
//! `∀ n, Iff (Eq (totient n) 0) (Eq n 0)`
//! (`F:ml430-nat-totient-eq-zero-3be161d6`). Case-split `n` via
//! `cases_zero_succ` (no induction hypothesis needed):
//!
//! - `n = 0`: `totient 0 = countRange f 0 = 0` by the `Nat.rec` base case —
//!   pure defeq, `Eq.refl`. Both `Iff` directions are then constant
//!   functions returning `Eq.refl 0`.
//! - `n = succ k`: the WITNESS is always the range's own TOP index, `k`
//!   itself (`n - 1`), never index `0` or `1` — `coprime_succ_self k` gives
//!   `gcd k (succ k) = 1` directly, matching `totient`'s predicate order
//!   with no `gcd_comm` needed. `countRange`'s `succ`-case defining equation
//!   fires by PURE DEFEQ (`Nat.rec` on a literal `succ k` reduces
//!   regardless of `k`'s own shape) to `add (countRange f k) (bool_select
//!   (beq (gcd k (succ k)) 1) 1 0)`; congruence through `coprime_succ_self`
//!   promotes the inner `beq` to `true` (`beq_eq_true_of_eq`) and then the
//!   `bool_select` to the literal `1`, so the whole expression is defeq to
//!   `succ (countRange f k)` — never `0` (`succ_ne_zero`), exactly mirroring
//!   `succ k` itself never being `0`. Both `Iff` directions are then
//!   `ex_falso` from a contradiction, no existential witness needed as a
//!   term (the witness is baked into which index the defining equation
//!   exposes, not an `Exists` elimination).
//!
//! This same "top index is always coprime to `n`" fact is `dvd_two_of_
//! totient_le_one`'s natural second ingredient too (`totient n <= 1` needs a
//! SECOND, DISTINCT witness below the top index once `n >= 3`, or the
//! contrapositive collapses) — see below for why that is not enough on its
//! own to close it this session.
//!
//! ## What does not land here, and why
//!
//! Every other mirror in this task's list needs infrastructure this prelude
//! does not have yet, confirmed by working through each one rather than
//! asserting it:
//!
//! - **`totient_eq_one_iff`** (`totient n = 1 <-> n = 1 \/ n = 2`): the
//!   `n = 1 \/ n = 2 -> totient n = 1` direction is cheap (concrete
//!   `def_eq` computation at each numeral, exactly like
//!   `totient_computes_on_small_numerals`). The FORWARD direction needs a
//!   second, DISTINCT coprime witness below the top index whenever `n >= 3`
//!   (e.g. `k = 1`, which is `coprime_one_right_iff` after a `gcd_comm`
//!   bridge, or a second application of a "count >= 1 from a witness NOT at
//!   the top index" argument) plus a lemma this prelude does not have:
//!   "two distinct true witnesses below `n` give `countRange f n >= 2`". The
//!   top-index technique above only ever produces >=1, by construction —
//!   it consumes the defining equation once and cannot re-fire on a second,
//!   INTERIOR index without either a general existence-witness induction
//!   (`∀ f n k, k < n -> f k = true -> 0 < countRange f n`, itself
//!   undeclared) or `countRange_split` composed with a second top-index
//!   argument on the SHORTER prefix range. Neither is a small addition.
//! - **`totient_even`** (`2 < n -> Even (totient n)`): needs the classical
//!   pairing argument `totient.rs`'s own module doc already calls out as
//!   separate, larger work — the involution `k -> n - k` on the coprime
//!   residues is fixed-point-free once `2 < n` (its only possible fixed
//!   point needs `2*k = n`, ruled out by parity/coprimality), and "a
//!   fixed-point-free involution on a finite set has even cardinality" is
//!   not machinery this prelude has for a `Bool`-predicate-defined subset of
//!   `[0,n)` (as opposed to `permutation.rs`'s `Fin`-indexed permutations).
//! - **`odd_totient_iff`** and **`odd_totient_iff_eq_one`**: both reduce to
//!   `totient_eq_one_iff` combined with `totient_even` (odd XOR even
//!   totality splits `n` at exactly `n <= 2`, and `totient_eq_one_iff`'s
//!   RHS `n = 1 \/ n = 2` is verbatim `odd_totient_iff`'s RHS) — blocked on
//!   BOTH of the above, not a new difficulty of their own.
//! - **`totient_coprime_totient_iff`**: `gcd (totient m) (totient n) = 1`
//!   iff one of `m`,`n` is `1` or `2`. The "if" direction is cheap (`gcd 1
//!   _ = 1`, `coprime_one_left_iff`). The "only if" direction's
//!   contrapositive needs `totient_even` at BOTH `m` and `n` when neither is
//!   `1`/`2` (two even numbers `> 0` cannot be coprime, `2 | gcd` via
//!   `dvd_gcd`, contradicting `gcd = 1` via `2 != 1`), plus the `m = 0`/`n =
//!   0` edge case (`totient 0 = 0`, and `gcd 0 x = x` so `gcd (totient m)
//!   (totient n) = totient n`, needing a further case on whether THAT is
//!   `1`). Blocked on `totient_even`.
//! - **`eq_or_eq_of_totient_eq_totient`** (`a | b -> totient a = totient b
//!   -> a = b \/ 2*a = b`) and **`totient_gcd_mul_totient_mul`** (the
//!   multiplicativity identity `totient(gcd a b) * totient(a*b) = totient a
//!   * totient b * gcd a b`): both need real structural results about how
//!   `totient` interacts with multiplication/divisibility — the standard
//!   routes go through the multiplicative formula `totient (m*n) = totient m
//!   * totient n` for coprime `m`,`n` (itself a CRT-style bijection argument
//!   between `[0,mn)` and `[0,m) x [0,n)` restricted to units) or an
//!   equivalent prime-power decomposition. Neither exists in this prelude;
//!   building it is a project on the scale of `totient_even`'s pairing
//!   argument, not a slice of this one.
//! - **`totient_dvd_of_dvd`** (`a | b -> totient a | totient b`): also
//!   standardly proved via the multiplicative formula (factor `b = a * c`,
//!   split into the coprime and non-coprime parts of `c` relative to `a`'s
//!   prime factors). Same blocker.
//!
//! So the honest shape of this family: ONE closed (`totient_eq_zero`, plus
//! the reusable `coprime_succ_self`), and the other eight all bottleneck on
//! one of two missing pieces of real infrastructure — a general
//! existence-witness-to-positive-count lemma (small, would unlock
//! `totient_eq_one_iff`'s forward direction and `dvd_two_of_totient_le_one`)
//! and the fixed-point-free-involution/pairing argument for `totient_even`
//! (large, would additionally unlock `odd_totient_iff{,_eq_one}` and half of
//! `totient_coprime_totient_iff`) — plus the multiplicative formula for
//! `totient` (largest, needed by `totient_gcd_mul_totient_mul` and
//! `totient_dvd_of_dvd`, and the other half of
//! `eq_or_eq_of_totient_eq_totient`). None of these is a small addition to
//! staple onto a proof under this session's budget; recorded here so the
//! next lane on this family does not re-derive the same triage.

use super::NatPrelude;
use super::helpers::iff_reverse;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local copies of helpers `totient.rs` keeps private to itself (that file's
// own stated convention: local copies per file rather than a shared private
// module).
// ============================================================================

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `h : Eq Bool a b  ⊢  Eq Nat (f a) (f b)`, for `f : Bool → Nat` — the
/// `Nat`-codomain analogue of `NatOps::bool_symm`/`bool_trans`. Exactly
/// `totient.rs`'s private copy of the same name.
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `fun k => beq (gcd k n) 1` — exactly `totient.rs`'s private
/// `totient_predicate`, reproduced locally so `totient`'s own reduction (a
/// substitution instance of this SAME construction) lines up by pure defeq
/// with what this file builds independently, with no shared symbol needed.
fn totient_predicate(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let g = d.gcd(k, n);
    let one = d.num(1);
    let body = d.beq(g, one);
    d.lam_fv(k_fv, nat, body)
}

/// `countRange(d, p, f, n)`, i.e. `d.const_app(p.count_range, &[f, n])` —
/// exactly `totient.rs`'s private helper of the same name.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

// ============================================================================
// `Nat.coprime_succ_self : ∀ m, Eq (gcd m (succ m)) one`.
// ============================================================================

/// See the module doc for the route: `coprime_add_self_right(m, one)` plus
/// `coprime_one_right_iff(m)` give `gcd m (add one m) = one`
/// unconditionally, and `add one m = succ m` by `succ_add`/`zero_add`
/// congr'd through `succ`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_succ_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_succ_self, 1, &|d, v| {
        let m = v[0];
        let one = d.num(1);
        let zero = d.zero();
        let sum = d.add(one, m); // add one m
        let sm = d.succ(m);
        let g_sum = d.gcd(m, sum); // gcd m (add one m)
        let g_one = d.gcd(m, one); // gcd m one

        let cop_sum_ty = d.eq(g_sum, one);
        let cop_one_ty = d.eq(g_one, one);
        let true_ty = d.kernel().const_(p.logic.true_, vec![]);

        // `gcd m one = one`, unconditionally, from `coprime_one_right_iff`.
        let cop_one_iff = d.lemma(p.coprime_one_right_iff, &[m]);
        let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
        let mpr_one = iff_reverse(d, cop_one_ty, true_ty, cop_one_iff);
        let g_one_eq_one = d.apply(mpr_one, &[true_intro]);

        // Promote it to `gcd m (add one m) = one` via `coprime_add_self_right`.
        let iff_sum = d.lemma(p.coprime_add_self_right, &[m, one]);
        let mpr_sum = iff_reverse(d, cop_sum_ty, cop_one_ty, iff_sum);
        let g_sum_eq_one = d.apply(mpr_sum, &[g_one_eq_one]);

        // `add one m = succ m`: `succ_add(zero, m) : add (succ zero) m = succ
        // (add zero m)`, then congr `zero_add(m) : add zero m = m` through
        // `succ`.
        let add_zero_m = d.add(zero, m);
        let succ_add_step = d.lemma(p.succ_add, &[zero, m]);
        let zero_add_m = d.lemma(p.zero_add, &[m]);
        let congr_succ = d.congr(add_zero_m, m, zero_add_m, &|d, x| d.succ(x));
        let succ_add_zero_m = d.succ(add_zero_m);
        let (_e, sum_eq_sm) = d.chain(sum, &[(succ_add_zero_m, succ_add_step), (sm, congr_succ)]);

        let motive = d.eq_motive(sum, &|d, x| {
            let g = d.gcd(m, x);
            d.eq(g, one)
        });
        let result = d.transport(sum, motive, g_sum_eq_one, sm, sum_eq_sm);

        let g_sm = d.gcd(m, sm);
        let stmt = d.eq(g_sm, one);
        (stmt, result)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.totient_eq_zero : ∀ n, Iff (Eq (totient n) 0) (Eq n 0)`.
// ============================================================================

/// See the module doc for the route: the top index of `[0,n)` is always
/// coprime to `n` (`coprime_succ_self`), so `totient (succ k)` is always
/// defeq to `succ (countRange f k)` for SOME `f`/`k` — never `0` — matching
/// `succ k` itself never being `0`; the `n = 0` case holds by the
/// `countRange` base case directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_totient_eq_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let totient_x = d.const_app(p.totient, &[x]);
        let zero = d.zero();
        let lhs = d.eq(totient_x, zero);
        let rhs = d.eq(x, zero);
        d.const_app(p.logic.iff, &[lhs, rhs])
    };
    let stmt = motive(d, n);

    let proof = cases_zero_succ(
        d,
        n,
        &motive,
        &|d| {
            let zero = d.zero();
            let totient0 = d.const_app(p.totient, &[zero]);
            let lhs_ty = d.eq(totient0, zero);
            let rhs_ty = d.eq(zero, zero);
            let mp = {
                let h_fv = d.fresh_fvar();
                d.lam_fv(h_fv, lhs_ty, d.refl(zero))
            };
            let mpr = {
                let h_fv = d.fresh_fvar();
                d.lam_fv(h_fv, rhs_ty, d.refl(zero))
            };
            d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr])
        },
        &|d, k| {
            let one = d.num(1);
            let zero = d.zero();
            let sk = d.succ(k);

            // `gcd k (succ k) = 1`, the top-index witness.
            let gcd_eq = d.lemma(p.coprime_succ_self, &[k]);
            let gk = d.gcd(k, sk);

            // `beq (gcd k (succ k)) 1 = true`.
            let fk_beq_true = d.lemma(p.beq_eq_true_of_eq, &[gk, one, gcd_eq]);
            let beq_gk_one = d.beq(gk, one);
            let true_v = d.bool_true();

            // `bool_select_nat (beq (gcd k (succ k)) 1) 1 0 = bool_select_nat true 1 0`
            // (defeq `1`).
            let sel_congr = bool_congr_nat(d, beq_gk_one, true_v, fk_beq_true, &|d, x| {
                let one_inner = d.num(1);
                let zero_inner = d.zero();
                d.bool_select_nat(x, one_inner, zero_inner)
            });

            // `f := totient's own predicate at `succ k``, `countRange f k` —
            // matches, by pure defeq, the term `totient (succ k)` reduces to.
            let f = totient_predicate(d, sk);
            let crfk = count_range(d, &p, f, k);

            let sel_beq = d.bool_select_nat(beq_gk_one, one, zero);
            let sel_true = d.bool_select_nat(true_v, one, zero);
            let add_congr = d.congr(sel_beq, sel_true, sel_congr, &|d, x| d.add(crfk, x));

            let totient_sk = d.const_app(p.totient, &[sk]);
            let succ_crfk = d.succ(crfk);
            let lhs_ty = d.eq(totient_sk, zero);
            let rhs_ty = d.eq(sk, zero);

            let mp = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // `add_congr`, read at (totient_sk, succ_crfk): defeq to its
                // literal (add-form, add-form) endpoints on both sides.
                let symm_step = d.symm(totient_sk, succ_crfk, add_congr);
                let combined = d.trans(succ_crfk, totient_sk, zero, symm_step, h);
                let ne = d.lemma(p.succ_ne_zero, &[crfk]);
                let false_pf = d.apply(ne, &[combined]);
                let body = ex_falso(d, &p, rhs_ty, false_pf);
                d.lam_fv(h_fv, lhs_ty, body)
            };
            let mpr = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let ne = d.lemma(p.succ_ne_zero, &[k]);
                let false_pf = d.apply(ne, &[h]);
                let body = ex_falso(d, &p, lhs_ty, false_pf);
                d.lam_fv(h_fv, rhs_ty, body)
            };
            d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr])
        },
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.totient_eq_zero, ty, value)
}

/// Declare `Nat.coprime_succ_self` and `Nat.totient_eq_zero`, in dependency
/// order.
pub(super) fn declare_totient_lemmas_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_coprime_succ_self(d, p)?;
    declare_totient_eq_zero(d, p)?;
    Ok(())
}
