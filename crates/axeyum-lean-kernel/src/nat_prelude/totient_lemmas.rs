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
//!   multiplicativity identity relating `totient (gcd a b)`, `totient (a*b)`,
//!   `totient a`, `totient b`, and `gcd a b`): both need real structural
//!   results about how `totient` interacts with multiplication/divisibility
//!   — the standard route is the multiplicative formula (`totient` of a
//!   product of COPRIME factors is the product of their `totient`s, itself a
//!   CRT-style bijection argument between the residues mod `m*n` and pairs of
//!   residues mod `m`, mod `n`) or an equivalent prime-power decomposition.
//!   Neither exists in this prelude; building it is a project on the scale
//!   of `totient_even`'s pairing argument, not a slice of this one.
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
//!
//! ## Update: piece 1 landed (the "≥ 2 witnesses" machinery), 2026-08-29
//!
//! `Nat.countRange_succ_of_true`, `Nat.countRange_le_of_le`, and
//! `Nat.countRange_ge_two_of_two_witnesses` (below) are the general
//! existence-witness-to-positive-count lemma named above as blocking
//! `totient_eq_one_iff`'s forward direction and `dvd_two_of_totient_le_one`.
//! Chosen over the other two pieces because it needed no new induction
//! principle: `Int.prod_range_pairing_collapse`
//! (`int_prelude/wilson.rs`, checked first per this lane's own brief) is a
//! REAL fixed-point-free-involution/pairing lemma, but it collapses an
//! `Int.prodRange` to `1` under `ModEq`, over a Wilson-specific concrete
//! `sigma := Nat.inverseIndex` — it does not transport to "a
//! `Bool`-predicate-defined `countRange` subset has even cardinality"
//! without re-deriving the two-step structural induction against a
//! `Nat`-valued conclusion. `totient_even`'s pairing argument is therefore
//! still a from-scratch piece of work, not a corollary of that lemma.
//!
//! **The concrete witnesses that turn this into the two blocked mirrors are
//! now known and cheap: `i = 1` (always coprime, `coprime_one_left_iff` —
//! `gcd one n = one` directly, no `gcd_comm` bridge needed after all, since
//! `totient`'s predicate order is `gcd k n`) and `j = pred n` (the top
//! index, `coprime_succ_self`), valid whenever `2 < n` (so `i < j`).** What
//! is still missing to actually close either mirror is NOT more counting
//! machinery — it is a small-numeral case split:
//!
//! - **`dvd_two_of_totient_le_one`** (`0 < a → totient a ≤ 1 → a ∣ 2`):
//!   first get `1 ≤ totient a` from `0 < a` (contrapositive of
//!   `totient_eq_zero`, cheap), so `totient a = 1` (antisymmetry with the
//!   hypothesis). Then case-split `a` via `trichotomy(d, &p, 2, a)`
//!   (`finite.rs`, `pub(super)`, already reusable from a sibling module —
//!   see `group.rs`'s `use super::finite::{le_of_lt, pos_implies_succ_pred}`
//!   for the import precedent): `a < 2` combined with `0 < a` forces `a = 1`
//!   (`1 ∣ 2` trivially); `a = 2` is `2 ∣ 2` trivially; `2 < a` contradicts
//!   `totient a = 1` via `countRange_ge_two_of_two_witnesses` at `i=1`,
//!   `j = pred a` — `Le 2 (totient a)` against `totient a = 1` is refuted by
//!   `lt_irrefl`/`le_antisymm`-shaped reasoning on the two concrete
//!   numerals `1`/`2`.
//! - **`totient_eq_one_iff`**: the same `2 < n` case of the same trichotomy
//!   closes the forward direction's hard case identically (`totient n = 1`
//!   contradicts `Le 2 (totient n)`); the reverse direction and the `n ≤ 2`
//!   cases are the cheap concrete `def_eq` computations already noted above.
//!
//! Neither mirror was attempted this session — the trichotomy assembly
//! above is a genuine next slice, not a corollary — but the ingredients
//! (`trichotomy`, `lt_or_eq_of_le`, `le_antisymm`, the three lemmas below)
//! are now all present, so the next lane on this family should not need to
//! build anything new to close them, only compose.

use super::NatPrelude;
use super::finite::{pos_implies_succ_pred, trichotomy, zero_lt_via_c};
use super::helpers::{iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_zero_succ};
use super::parity::{even_predicate, odd_predicate};
use super::steps::dvd_intro;
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
                let body = d.refl(zero);
                d.lam_fv(h_fv, lhs_ty, body)
            };
            let mpr = {
                let h_fv = d.fresh_fvar();
                let body = d.refl(zero);
                d.lam_fv(h_fv, rhs_ty, body)
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

// ============================================================================
// `Nat.countRange_succ_of_true` — piece 1 of the triage: a single witness,
// as a reusable one-step promotion (extracted from `totient_eq_zero`'s own
// technique, not re-derived).
// ============================================================================

/// `Nat.countRange_succ_of_true : ∀ f k, Eq Bool (f k) true →
///   Eq Nat (countRange f (succ k)) (succ (countRange f k))`.
///
/// The same technique `totient_eq_zero`'s succ case already uses, extracted
/// as a general reusable step: `countRange`'s defining equation (proved by
/// `Eq.refl`) makes `countRange f (succ k)` defeq to `add (countRange f k)
/// (bool_select_nat (f k) 1 0)`; a single `bool_congr_nat` promotes that to
/// `add (countRange f k) (bool_select_nat true 1 0)`, which is itself defeq
/// `succ (countRange f k)` (`add x 1 ≡ succ x`, since `add` recurses on its
/// second argument). One `d.congr` on top of the `bool_congr_nat` step is
/// the whole proof; no `d.chain` is needed since both endpoints are already
/// in reduced form.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_count_range_succ_of_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let fk = d.apply(f, &[k]);
    let true_v = d.bool_true();
    let hyp_ty = d.bool_eq(fk, true_v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let one = d.num(1);
    let zero = d.zero();
    let cr_f_k = count_range(d, &p, f, k);

    let sel_congr = bool_congr_nat(d, fk, true_v, h, &|d, x| {
        let one_inner = d.num(1);
        let zero_inner = d.zero();
        d.bool_select_nat(x, one_inner, zero_inner)
    });
    let sel_fk = d.bool_select_nat(fk, one, zero);
    let sel_true = d.bool_select_nat(true_v, one, zero);
    let add_congr = d.congr(sel_fk, sel_true, sel_congr, &|d, x| d.add(cr_f_k, x));

    let sk = d.succ(k);
    let cr_sk = count_range(d, &p, f, sk);
    let succ_cr_fk = d.succ(cr_f_k);
    let stmt = d.eq(cr_sk, succ_cr_fk);
    let full_stmt = d.arrow(hyp_ty, stmt);

    let with_h = d.lam_fv(h_fv, hyp_ty, add_congr);
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, full_stmt);
        d.pi_fv(f_fv, pred_ty, with_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(f_fv, pred_ty, with_k)
    };
    d.declare_theorem(p.count_range_succ_of_true, ty, value)
}

// ============================================================================
// `Nat.countRange_le_of_le` — cardinality monotonicity in the RANGE BOUND.
// ============================================================================

/// `fun k => f (add m k)` — local copy of `totient.rs`'s private
/// `shifted_pred` (this file's own stated convention: local copies per
/// file).
fn shifted_pred(d: &mut NatDev<'_>, f: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.add(m, k);
    let fmk = d.apply(f, &[mk]);
    d.lam_fv(k_fv, nat, fmk)
}

/// `Nat.countRange_le_of_le : ∀ f m n, Le m n → Le (countRange f m)
/// (countRange f n)`.
///
/// Via `le_dest(m, n, h) : Exists (fun k => Eq (add m k) n)`, eliminated
/// (`exists_rec`) into: `countRange_split(f, m, k)` gives `countRange f (add
/// m k) = add (countRange f m) (countRange (shifted f m) k)`; congr the LHS
/// along `e : add m k = n` to reindex to `countRange f n`; and
/// `le_add_right(countRange f m, countRange (shifted f m) k)` gives `Le
/// (countRange f m) (add (countRange f m) (countRange (shifted f m) k))`,
/// which transports along the same equation to the goal. No new induction —
/// this is exactly `le_of_add_le_add_left`'s `le_dest`/`exists_rec` shape
/// (`order.rs`), instantiated at `countRange` in place of a bare `Nat` sum.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_count_range_le_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let anon = d.anon_name();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let hyp_ty = d.le(m, n);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let cr_f_m = count_range(d, &p, f, m);
    let cr_f_n = count_range(d, &p, f, n);
    let conclusion = d.le(cr_f_m, cr_f_n);

    let one_lvl = d.level_one();
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let mk = d.add(m, k);
        let body = d.eq(mk, n);
        d.lam_fv(k_fv, nat, body)
    };
    let represented_ty = {
        let exists_ = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        d.apply(exists_, &[nat, pred])
    };
    let represented = d.lemma(p.le_dest, &[m, n, h]);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let mk = d.add(m, k);
        let e_ty = d.eq(mk, n);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        let g = shifted_pred(d, f, m);
        let cr_g_k = count_range(d, &p, g, k);
        let split_eq = d.lemma(p.count_range_split, &[f, m, k]);
        let cr_f_mk = count_range(d, &p, f, mk);
        let add_form = d.add(cr_f_m, cr_g_k);

        let congr_e = d.congr(mk, n, e, &|d, x| count_range(d, &p, f, x));
        let congr_e_rev = d.symm(cr_f_mk, cr_f_n, congr_e);
        let combined = d.trans(cr_f_n, cr_f_mk, add_form, congr_e_rev, split_eq);

        let le_add = d.lemma(p.le_add_right, &[cr_f_m, cr_g_k]);
        let combined_rev = d.symm(cr_f_n, add_form, combined);
        let motive2 = d.eq_motive(add_form, &|d, x| d.le(cr_f_m, x));
        let final_le = d.transport(add_form, motive2, le_add, cr_f_n, combined_rev);

        let with_e = d.lam_fv(e_fv, e_ty, final_le);
        d.lam_fv(k_fv, nat, with_e)
    };

    let motive = d
        .kernel()
        .lam(anon, represented_ty, conclusion, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    let body = d.apply(rec, &[nat, pred, motive, minor, represented]);

    let full_stmt = d.arrow(hyp_ty, conclusion);
    let with_h = d.lam_fv(h_fv, hyp_ty, body);

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, full_stmt);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(f_fv, pred_ty, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, with_h);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(f_fv, pred_ty, with_m)
    };
    d.declare_theorem(p.count_range_le_of_le, ty, value)
}

// ============================================================================
// `Nat.countRange_ge_two_of_two_witnesses` — the general "two distinct
// witnesses ⇒ count ≥ 2" lemma the module doc names as the blocker for
// `totient_eq_one_iff`'s forward direction and `dvd_two_of_totient_le_one`.
// ============================================================================

/// `Nat.countRange_ge_two_of_two_witnesses : ∀ f n i j, Lt i j → Lt j n →
///   Eq Bool (f i) true → Eq Bool (f j) true → Le 2 (countRange f n)`.
///
/// Composition of `countRange_succ_of_true` and `countRange_le_of_le`, no new
/// induction: promote each witness's own successor to a `≥ 1`/`≥ 2` bound via
/// `succ_le_succ` (`Le (succ 0) (succ x)` from `Le 0 x`, i.e. `Le 1 (succ
/// x)`), transport that bound back through the witness's own succ equation,
/// then carry it up to `n` by monotonicity (`Lt i j` is definitionally `Le
/// (succ i) j`, so it feeds `countRange_le_of_le` directly with no
/// conversion). `i`'s bound reaches `Le 1 (countRange f j)`; `succ_le_succ`
/// again gives `Le 2 (succ (countRange f j))`, which the SAME two steps
/// (witness-succ, then monotonicity to `n`) carry to `Le 2 (countRange f n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_count_range_ge_two_of_two_witnesses(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hij_ty = d.lt(i, j);
    let hij_fv = d.fresh_fvar();
    let hij = d.kernel().fvar(hij_fv);
    let hjn_ty = d.lt(j, n);
    let hjn_fv = d.fresh_fvar();
    let hjn = d.kernel().fvar(hjn_fv);

    let true_v = d.bool_true();
    let fi = d.apply(f, &[i]);
    let hfi_ty = d.bool_eq(fi, true_v);
    let hfi_fv = d.fresh_fvar();
    let hfi = d.kernel().fvar(hfi_fv);
    let fj = d.apply(f, &[j]);
    let hfj_ty = d.bool_eq(fj, true_v);
    let hfj_fv = d.fresh_fvar();
    let hfj = d.kernel().fvar(hfj_fv);

    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    // Witness `i`: `countRange f (succ i) = succ (countRange f i)`, promoted
    // to `Le 1 (countRange f (succ i))`.
    let eq_i = d.lemma(p.count_range_succ_of_true, &[f, i, hfi]);
    let cr_f_i = count_range(d, &p, f, i);
    let si = d.succ(i);
    let cr_f_si = count_range(d, &p, f, si);
    let succ_cr_f_i = d.succ(cr_f_i);
    let zero_le_cri = d.lemma(p.zero_le, &[cr_f_i]);
    let le_1_succ_i = d.lemma(p.succ_le_succ, &[zero, cr_f_i, zero_le_cri]);
    let eq_i_rev = d.symm(cr_f_si, succ_cr_f_i, eq_i);
    let motive_i = d.eq_motive(succ_cr_f_i, &|d, x| d.le(one, x));
    let le_1_cr_f_si = d.transport(succ_cr_f_i, motive_i, le_1_succ_i, cr_f_si, eq_i_rev);

    // Carry `Le 1 (countRange f (succ i))` up to `Le 1 (countRange f j)` by
    // monotonicity (`Lt i j` is `Le (succ i) j` by definition).
    let mono_ij = d.lemma(p.count_range_le_of_le, &[f, si, j, hij]);
    let cr_f_j = count_range(d, &p, f, j);
    let le_1_cr_f_j = d.lemma(p.le_trans, &[one, cr_f_si, cr_f_j, le_1_cr_f_si, mono_ij]);

    // Witness `j`: `countRange f (succ j) = succ (countRange f j)`, promoted
    // to `Le 2 (countRange f (succ j))` using the `Le 1 (countRange f j)` just
    // established.
    let eq_j = d.lemma(p.count_range_succ_of_true, &[f, j, hfj]);
    let sj = d.succ(j);
    let cr_f_sj = count_range(d, &p, f, sj);
    let succ_cr_f_j = d.succ(cr_f_j);
    let le_2_succ_j = d.lemma(p.succ_le_succ, &[one, cr_f_j, le_1_cr_f_j]);
    let eq_j_rev = d.symm(cr_f_sj, succ_cr_f_j, eq_j);
    let motive_j = d.eq_motive(succ_cr_f_j, &|d, x| d.le(two, x));
    let le_2_cr_f_sj = d.transport(succ_cr_f_j, motive_j, le_2_succ_j, cr_f_sj, eq_j_rev);

    // Carry `Le 2 (countRange f (succ j))` up to `Le 2 (countRange f n)`.
    let mono_jn = d.lemma(p.count_range_le_of_le, &[f, sj, n, hjn]);
    let cr_f_n = count_range(d, &p, f, n);
    let final_le = d.lemma(p.le_trans, &[two, cr_f_sj, cr_f_n, le_2_cr_f_sj, mono_jn]);

    let stmt_inner = d.le(two, cr_f_n);
    let with_hfj = d.lam_fv(hfj_fv, hfj_ty, final_le);
    let with_hfi = d.lam_fv(hfi_fv, hfi_ty, with_hfj);
    let with_hjn = d.lam_fv(hjn_fv, hjn_ty, with_hfi);
    let with_hij = d.lam_fv(hij_fv, hij_ty, with_hjn);

    let full_stmt = {
        let s1 = d.arrow(hfj_ty, stmt_inner);
        let s2 = d.arrow(hfi_ty, s1);
        let s3 = d.arrow(hjn_ty, s2);
        d.arrow(hij_ty, s3)
    };

    let ty = {
        let with_j = d.pi_fv(j_fv, nat, full_stmt);
        let with_i = d.pi_fv(i_fv, nat, with_j);
        let with_n = d.pi_fv(n_fv, nat, with_i);
        d.pi_fv(f_fv, pred_ty, with_n)
    };
    let value = {
        let with_j = d.lam_fv(j_fv, nat, with_hij);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_n = d.lam_fv(n_fv, nat, with_i);
        d.lam_fv(f_fv, pred_ty, with_n)
    };
    d.declare_theorem(p.count_range_ge_two_of_two_witnesses, ty, value)
}

// ============================================================================
// Shared core: from `Lt two x` and `Le (totient x) one`, derive `False`.
// The `2 < a`/`2 < n` branch of both `dvd_two_of_totient_le_one` and
// `totient_eq_one_iff`'s forward direction.
// ============================================================================

/// Eliminate a [`trichotomy`] (`Or (Lt x c) (Or (Eq x c) (Lt c x))`) directly
/// into a proof of `target`, given a proof for each of the three cases --
/// local generalization of `finite.rs`'s `two_way_split` (which eliminates
/// only the middle case) into a full three-way eliminator.
#[allow(clippy::too_many_arguments)]
fn trichotomy_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    target: ExprId,
    on_lt: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    on_eq: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    on_gt: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_xc = d.lt(x, c);
    let eq_xc = d.eq(x, c);
    let lt_cx = d.lt(c, x);
    let inner = d.const_app(logic.or, &[eq_xc, lt_cx]);

    let tri = trichotomy(d, &p, c, x);

    let on_left = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = on_lt(d, h);
        d.lam_fv(h_fv, lt_xc, body)
    };
    let on_right = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub_on_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = on_eq(d, h2);
            d.lam_fv(h2_fv, eq_xc, body)
        };
        let sub_on_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = on_gt(d, h2);
            d.lam_fv(h2_fv, lt_cx, body)
        };
        let body = d.const_app(
            logic.or_elim,
            &[eq_xc, lt_cx, target, h, sub_on_left, sub_on_right],
        );
        d.lam_fv(h_fv, inner, body)
    };
    d.const_app(
        logic.or_elim,
        &[lt_xc, inner, target, tri, on_left, on_right],
    )
}

/// From `h_gt : Lt two x` and `h_le : Le (totient x) one`, derive `False`.
///
/// The two coprime residues below `x` that make this a contradiction are
/// `1` (`coprime_one_left_iff`, unconditional) and `pred x` (`coprime_succ_
/// self (pred x)`, valid since `x = succ (pred x)` once `0 < x`) -- distinct
/// whenever `2 < x` (`1 < pred x`, since `pred x >= 2`). Composing
/// `countRange_ge_two_of_two_witnesses` at those two witnesses gives `Le two
/// (totient x)`, which `le_trans` chains with `h_le` into the impossible
/// `Le two one` -- refuted by peeling two `succ`s down to `not_succ_le_zero`.
///
/// Shared by `dvd_two_of_totient_le_one`'s `2 < a` branch and
/// `totient_eq_one_iff`'s forward direction's `2 < n` branch.
fn totient_le_one_contradiction_above_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    h_gt: ExprId,
    h_le: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    // `x = succ (pred x)`, from `0 < x` (via `2 < x`).
    let pos_x = zero_lt_via_c(d, &p, two, x, h_gt);
    let eq_x_fn = pos_implies_succ_pred(d, &p, x);
    let eq_x = d.apply(eq_x_fn, &[pos_x]); // Eq x (succ (pred x))

    let pa = d.pred(x);
    let spa = d.succ(pa);
    let eq_spa_x = d.symm(x, spa, eq_x); // Eq spa x

    // `pred x < x`.
    let lt_pa_spa = d.lemma(p.lt_succ_self, &[pa]);
    let motive_lt = d.eq_motive(spa, &|d, z| d.lt(pa, z));
    let lt_pa_x = d.transport(spa, motive_lt, lt_pa_spa, x, eq_spa_x);

    // `1 < pred x`, rewriting `h_gt`'s underlying `Le (succ two) x` along
    // `x = succ (pred x)`.
    let motive_le = d.eq_motive(x, &|d, z| {
        let succ_two = d.succ(two);
        d.le(succ_two, z)
    });
    let le_succ2_spa = d.transport(x, motive_le, h_gt, spa, eq_x); // Le (succ two) spa
    let le_two_pa = d.lemma(p.le_of_succ_le_succ, &[two, pa, le_succ2_spa]); // Le two pa = Lt one pa

    // Witness `1`: `gcd one x = one` unconditionally.
    let true_ty = d.kernel().const_(p.logic.true_, vec![]);
    let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
    let gcd1x = d.gcd(one, x);
    let cop1_ty = d.eq(gcd1x, one);
    let iff1 = d.lemma(p.coprime_one_left_iff, &[x]);
    let mpr1 = iff_reverse(d, cop1_ty, true_ty, iff1);
    let gcd1x_eq1 = d.apply(mpr1, &[true_intro]);
    let hfi = d.lemma(p.beq_eq_true_of_eq, &[gcd1x, one, gcd1x_eq1]);

    // Witness `pred x`: `gcd (pred x) x = one`.
    let gcd_pa_spa_eq1 = d.lemma(p.coprime_succ_self, &[pa]); // Eq (gcd pa spa) one
    let motive_gcd = d.eq_motive(spa, &|d, z| {
        let g = d.gcd(pa, z);
        d.eq(g, one)
    });
    let gcd_pa_x_eq1 = d.transport(spa, motive_gcd, gcd_pa_spa_eq1, x, eq_spa_x);
    let gcd_pa_x = d.gcd(pa, x);
    let hfj = d.lemma(p.beq_eq_true_of_eq, &[gcd_pa_x, one, gcd_pa_x_eq1]);

    // Assemble: `Le two (countRange f x)`, defeq `Le two (totient x)`.
    let f = totient_predicate(d, x);
    let cr_f_x = count_range(d, &p, f, x);
    let le_two_cr = d.lemma(
        p.count_range_ge_two_of_two_witnesses,
        &[f, x, one, pa, le_two_pa, lt_pa_x, hfi, hfj],
    );

    // `Le two one`, then refute.
    let le_2_1 = d.lemma(p.le_trans, &[two, cr_f_x, one, le_two_cr, h_le]);
    let le_1_0 = d.lemma(p.le_of_succ_le_succ, &[one, zero, le_2_1]);
    let not_le_1_0 = d.lemma(p.not_succ_le_zero, &[zero]);
    d.apply(not_le_1_0, &[le_1_0])
}

// ============================================================================
// `Nat.dvd_two_of_totient_le_one : ∀ a, Lt zero a → Le (totient a) one →
// dvd a two`.
// ============================================================================

/// See the module doc / `NatPrelude::dvd_two_of_totient_le_one` for the
/// route: `trichotomy` at `c = two` on `a`, with the `a < 2` and `a = 2`
/// branches closed by direct concrete divisibility witnesses and the
/// `2 < a` branch refuted by [`totient_le_one_contradiction_above_two`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_two_of_totient_le_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    let hpos_ty = d.lt(zero, a);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let totient_a = d.const_app(p.totient, &[a]);
    let hle_ty = d.le(totient_a, one);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let goal = d.dvd(a, two);

    let body = trichotomy_elim(
        d,
        &p,
        two,
        a,
        goal,
        &|d, h_lt| {
            // h_lt : Lt a two. Combined with hpos : Lt zero a (defeq Le one
            // a), forces a = one.
            let le_a_1 = d.lemma(p.le_of_succ_le_succ, &[a, one, h_lt]); // Le a one
            let eq_a_1 = d.lemma(p.le_antisymm, &[a, one, le_a_1, hpos]); // Eq a one

            // `dvd one two`, witness `two`: `Eq two (mul one two)`.
            let mul_1_2 = d.mul(one, two);
            let one_mul_2 = d.lemma(p.one_mul, &[two]); // Eq (mul one two) two
            let eq_2_mul = d.symm(mul_1_2, two, one_mul_2); // Eq two (mul one two)
            let dvd_1_2 = dvd_intro(d, one, two, two, eq_2_mul);

            let eq_1_a = d.symm(a, one, eq_a_1); // Eq one a
            let motive = d.eq_motive(one, &|d, z| d.dvd(z, two));
            d.transport(one, motive, dvd_1_2, a, eq_1_a)
        },
        &|d, h_eq| {
            // h_eq : Eq a two.
            let dvd_2_2 = d.lemma(p.dvd_refl, &[two]);
            let eq_2_a = d.symm(a, two, h_eq);
            let motive = d.eq_motive(two, &|d, z| d.dvd(z, two));
            d.transport(two, motive, dvd_2_2, a, eq_2_a)
        },
        &|d, h_gt| {
            // h_gt : Lt two a.
            let false_pf = totient_le_one_contradiction_above_two(d, &p, a, h_gt, hle);
            ex_falso(d, &p, goal, false_pf)
        },
    );

    let inner_stmt = d.arrow(hle_ty, goal);
    let full_stmt = d.arrow(hpos_ty, inner_stmt);
    let ty = d.pi_fv(a_fv, nat, full_stmt);
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, body);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hle);
        d.lam_fv(a_fv, nat, with_hpos)
    };
    d.declare_theorem(p.dvd_two_of_totient_le_one, ty, value)
}

// ============================================================================
// `Nat.totient_eq_one_iff : ∀ n, Iff (Eq (totient n) one) (Or (Eq n one)
// (Eq n two))`.
// ============================================================================

/// See the module doc / `NatPrelude::totient_eq_one_iff` for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_totient_eq_one_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    let totient_n = d.const_app(p.totient, &[n]);
    let lhs_ty = d.eq(totient_n, one);
    let eq_n_1 = d.eq(n, one);
    let eq_n_2 = d.eq(n, two);
    let rhs_ty = d.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
    let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

    // Forward: `Eq (totient n) one -> Or (Eq n one) (Eq n two)`.
    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = trichotomy_elim(
            d,
            &p,
            two,
            n,
            rhs_ty,
            &|d, h_lt| {
                // h_lt : Lt n two. Split `n = 0` vs `n = 1`.
                let le_n_1 = d.lemma(p.le_of_succ_le_succ, &[n, one, h_lt]); // Le n one
                let disj = d.lemma(p.lt_or_eq_of_le, &[n, one, le_n_1]); // Or (Lt n one) (Eq n one)
                let lt_n_1 = d.lt(n, one);

                let on_zero = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // h2 : Lt n one
                    let le_n_0 = d.lemma(p.le_of_succ_le_succ, &[n, zero, h2]); // Le n zero
                    let le_0_n = d.lemma(p.zero_le, &[n]);
                    let eq_n_0 = d.lemma(p.le_antisymm, &[n, zero, le_n_0, le_0_n]); // Eq n zero

                    // `Eq (totient n) one` rewritten along `n = 0` gives
                    // `Eq (totient zero) one`, defeq `Eq zero one`.
                    let motive_t0 = d.eq_motive(n, &|d, x| {
                        let t = d.const_app(p.totient, &[x]);
                        d.eq(t, one)
                    });
                    let h_t0_1 = d.transport(n, motive_t0, h, zero, eq_n_0);
                    let totient_zero = d.const_app(p.totient, &[zero]);
                    let symm1 = d.symm(totient_zero, one, h_t0_1); // Eq one (totient zero), defeq Eq one zero
                    let ne1 = d.lemma(p.succ_ne_zero, &[zero]); // Not (Eq one zero)
                    let false_pf = d.apply(ne1, &[symm1]);
                    let body = ex_falso(d, &p, rhs_ty, false_pf);
                    d.lam_fv(h2_fv, lt_n_1, body)
                };
                let on_one = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // h2 : Eq n one
                    let body = d.const_app(p.logic.or_inl, &[eq_n_1, eq_n_2, h2]);
                    d.lam_fv(h2_fv, eq_n_1, body)
                };
                d.const_app(
                    p.logic.or_elim,
                    &[lt_n_1, eq_n_1, rhs_ty, disj, on_zero, on_one],
                )
            },
            &|d, h_eq| d.const_app(p.logic.or_inr, &[eq_n_1, eq_n_2, h_eq]),
            &|d, h_gt| {
                // h_gt : Lt two n. `Le (totient n) one`, from `h : Eq
                // (totient n) one`, via `le_refl` transported along `h`.
                let le_refl_tn = d.lemma(p.le_refl, &[totient_n]);
                let motive_le = d.eq_motive(totient_n, &|d, x| d.le(totient_n, x));
                let le_tn_1 = d.transport(totient_n, motive_le, le_refl_tn, one, h);
                let false_pf = totient_le_one_contradiction_above_two(d, &p, n, h_gt, le_tn_1);
                ex_falso(d, &p, rhs_ty, false_pf)
            },
        );
        d.lam_fv(h_fv, lhs_ty, body)
    };

    // Reverse: `Or (Eq n one) (Eq n two) -> Eq (totient n) one`.
    let mpr = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let on_one = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // h2 : Eq n one
            let motive = d.eq_motive(one, &|d, x| {
                let t = d.const_app(p.totient, &[x]);
                d.eq(t, one)
            });
            let refl_at_one = d.refl(one);
            let eq_1_n = d.symm(n, one, h2);
            let body = d.transport(one, motive, refl_at_one, n, eq_1_n);
            d.lam_fv(h2_fv, eq_n_1, body)
        };
        let on_two = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // h2 : Eq n two
            let motive = d.eq_motive(two, &|d, x| {
                let t = d.const_app(p.totient, &[x]);
                d.eq(t, one)
            });
            let refl_at_two = d.refl(one);
            let eq_2_n = d.symm(n, two, h2);
            let body = d.transport(two, motive, refl_at_two, n, eq_2_n);
            d.lam_fv(h2_fv, eq_n_2, body)
        };
        let body = d.const_app(
            p.logic.or_elim,
            &[eq_n_1, eq_n_2, lhs_ty, h, on_one, on_two],
        );
        d.lam_fv(h_fv, rhs_ty, body)
    };

    let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.totient_eq_one_iff, ty, value)
}

// ============================================================================
// `Nat.totient_even : ∀ n, Lt two n → Even (totient n)`.
//
// See the module doc's "Update: `totient_even` landed" note (below the
// pre-existing history) and `docs/plan/status/295-totient-even.md` /
// `299-totient-even-exec.md` for the full route this section implements:
// peel index `0` off `[0,n)` via `countRange_split`, then apply
// `countRange_reversal_even` (`count_range_reversal.rs`) to the shifted
// predicate at `L := n - 1`.
// ============================================================================

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)`, for `f : Nat → Bool` — the
/// Bool-codomain analogue of [`NatOps::congr`] (hardcoded to `Nat`). Local
/// copy of `totient.rs`'s/`count_range_reversal.rs`'s private helper of the
/// same name, per this file's own local-copies-per-file convention.
fn nat_congr_bool(
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

/// `Eq (add one x) (succ x)` — `x` generalized from `coprime_succ_self`'s own
/// `add one m = succ m` derivation (`succ_add(zero,x)` congr'd through
/// `zero_add(x)`), reused here at both reflection indices `j` and `pred L -
/// j`, and once more at `x := one` itself (`add one one = two`, in the
/// `hyp2` fixed-point contradiction).
/// Retired to the `simp` rewrite-chain producer (ADR-1586): `succ_add` +
/// `zero_add` alone close `Eq (add one x) (succ x)`, and this was one of two
/// byte-identical hand-written copies of exactly this identity (the other in
/// `count_range_reversal.rs`).
fn one_add_eq_succ(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let one = d.num(1);
    let one_x = d.add(one, x);
    let succ_x = d.succ(x);
    let rules = crate::simp::nat::default_rules(p);
    crate::simp::nat::prove_eq(d, &rules, one_x, succ_x)
        .unwrap_or_else(|e| panic!("one_add_eq_succ: simp declined: {e:?}"))
}

/// `Not (Eq n one)`, from `hn : Lt two n`. Transport `hn` along an assumed
/// `Eq n one` to get `Lt two one` (i.e. `Le (succ two) (succ zero)`), peel
/// one `succ` via `le_of_succ_le_succ` to `Le two zero`, refuted by
/// `not_succ_le_zero one` (`Le two zero` is `Le (succ one) zero`).
fn n_ne_one_from_lt_two(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, hn: ExprId) -> ExprId {
    let p = *p;
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let one = d.num(1);
    let two = d.num(2);
    let zero = d.zero();
    let motive = d.eq_motive(n, &|d, x| {
        let two_ = d.num(2);
        d.lt(two_, x)
    });
    let transported = d.transport(n, motive, hn, one, h); // Lt two one
    let le_two_zero = d.lemma(p.le_of_succ_le_succ, &[two, zero, transported]);
    let not_le = d.lemma(p.not_succ_le_zero, &[one]);
    let absurd = d.apply(not_le, &[le_two_zero]);
    let eq_ty = d.eq(n, one);
    d.lam_fv(h_fv, eq_ty, absurd)
}

/// From `hsum : Eq (add k1 k2) n`, derive `Iff (Eq (gcd k1 n) one) (Eq (gcd
/// k2 n) one)` — `gcd(n-k,n) = gcd(k,n)` restated symmetrically over `k1`,
/// `k2` with `k1 + k2 = n`, via THREE already-declared `Iff`s (no new gcd
/// fact): `coprime_self_add_right(k1,k2)` rewritten along `hsum` relates
/// `gcd k1 n = 1` to `gcd k1 k2 = 1`; `coprime_symmetric` (applied both ways)
/// relates `gcd k1 k2 = 1` to `gcd k2 k1 = 1`; `coprime_self_add_right(k2,k1)`
/// rewritten along `hsum` composed with `add_comm` relates `gcd k2 n = 1` to
/// `gcd k2 k1 = 1`. Composing the three (by direct `mp`/`mpr` function
/// composition, not a general `iff_trans` helper) closes the chain.
fn gcd_reflection_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    k1: ExprId,
    k2: ExprId,
    hsum: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let gk1n_ty = {
        let g = d.gcd(k1, n);
        d.eq(g, one)
    };
    let gk1k2_ty = {
        let g = d.gcd(k1, k2);
        d.eq(g, one)
    };
    let gk2n_ty = {
        let g = d.gcd(k2, n);
        d.eq(g, one)
    };
    let gk2k1_ty = {
        let g = d.gcd(k2, k1);
        d.eq(g, one)
    };

    // Iff_A : Iff (gcd k1 n = 1) (gcd k1 k2 = 1).
    let iff_a = {
        let iff_a_raw = d.lemma(p.coprime_self_add_right, &[k1, k2]);
        let add_k1_k2 = d.add(k1, k2);
        let motive = d.eq_motive(add_k1_k2, &|d, x| {
            let g = d.gcd(k1, x);
            let one_ = d.num(1);
            let eqt = d.eq(g, one_);
            let gk1k2_ty_ = {
                let g2 = d.gcd(k1, k2);
                d.eq(g2, one_)
            };
            d.const_app(p.logic.iff, &[eqt, gk1k2_ty_])
        });
        d.transport(add_k1_k2, motive, iff_a_raw, n, hsum)
    };

    // Iff_B : Iff (gcd k1 k2 = 1) (gcd k2 k1 = 1).
    let iff_b = {
        let mp_b = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.coprime_symmetric, &[k1, k2, h]);
            d.lam_fv(h_fv, gk1k2_ty, body)
        };
        let mpr_b = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.coprime_symmetric, &[k2, k1, h]);
            d.lam_fv(h_fv, gk2k1_ty, body)
        };
        d.const_app(p.logic.iff_intro, &[gk1k2_ty, gk2k1_ty, mp_b, mpr_b])
    };

    // Iff_C : Iff (gcd k2 n = 1) (gcd k2 k1 = 1).
    let iff_c = {
        let iff_c_raw = d.lemma(p.coprime_self_add_right, &[k2, k1]);
        let add_k2_k1 = d.add(k2, k1);
        let add_k1_k2 = d.add(k1, k2);
        let comm = d.lemma(p.add_comm, &[k1, k2]); // Eq (add k1 k2) (add k2 k1)
        let comm_rev = d.symm(add_k1_k2, add_k2_k1, comm); // Eq (add k2 k1) (add k1 k2)
        let hsum2 = d.trans(add_k2_k1, add_k1_k2, n, comm_rev, hsum); // Eq (add k2 k1) n
        let motive = d.eq_motive(add_k2_k1, &|d, x| {
            let g = d.gcd(k2, x);
            let one_ = d.num(1);
            let eqt = d.eq(g, one_);
            let gk2k1_ty_ = {
                let g2 = d.gcd(k2, k1);
                d.eq(g2, one_)
            };
            d.const_app(p.logic.iff, &[eqt, gk2k1_ty_])
        });
        d.transport(add_k2_k1, motive, iff_c_raw, n, hsum2)
    };

    let mp_final = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let f_a = iff_forward(d, gk1n_ty, gk1k2_ty, iff_a);
        let step1 = d.apply(f_a, &[h]);
        let f_b = iff_forward(d, gk1k2_ty, gk2k1_ty, iff_b);
        let step2 = d.apply(f_b, &[step1]);
        let r_c = iff_reverse(d, gk2n_ty, gk2k1_ty, iff_c);
        let step3 = d.apply(r_c, &[step2]);
        d.lam_fv(h_fv, gk1n_ty, step3)
    };
    let mpr_final = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let f_c = iff_forward(d, gk2n_ty, gk2k1_ty, iff_c);
        let step1 = d.apply(f_c, &[h]);
        let r_b = iff_reverse(d, gk1k2_ty, gk2k1_ty, iff_b);
        let step2 = d.apply(r_b, &[step1]);
        let r_a = iff_reverse(d, gk1n_ty, gk1k2_ty, iff_a);
        let step3 = d.apply(r_a, &[step2]);
        d.lam_fv(h_fv, gk2n_ty, step3)
    };
    d.const_app(p.logic.iff_intro, &[gk1n_ty, gk2n_ty, mp_final, mpr_final])
}

/// Given `j`, `hj : Lt j Lrng` (`Lrng` the outer range bound `pred n`, `pm`
/// its own predecessor, `f := totient_predicate(n)`, `h(k) := f(add one k)`
/// the shifted predicate), compute the reflection pieces shared by
/// `hyp1`/`hyp2`: the two indices `k1 := succ j`, `k2 := succ (sub pm j)`
/// with `k1 + k2 = n` (`hsum`), the gcd `Iff` this yields
/// ([`gcd_reflection_iff`]), and the two Bool bridges relating `h j`/`h (sub
/// pm j)` to `f k1`/`f k2` respectively (needed because `h`'s own argument
/// is `add one k`, not `succ k` — [`one_add_eq_succ`] bridges the two).
///
/// Returns `(k1, k2, x2, hsum, gcd_iff, h_j_eq_f_k1, h_x2_eq_f_k2)` where
/// `x2 := sub pm j` is the reflected index (`h`'s argument at `sub (pred
/// Lrng) j`, matching `count_range_reversal_even`'s own statement exactly).
#[allow(clippy::too_many_arguments)]
fn reflection_pieces(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    lrng: ExprId,
    pm: ExprId,
    eq_lrng_succ_pm: ExprId,
    eq_n_succ_lrng: ExprId,
    f: ExprId,
    j: ExprId,
    hj: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let p = *p;

    // `Le j pm`, from `hj : Lt j Lrng` rewritten along `Lrng = succ pm`.
    let succ_pm = d.succ(pm);
    let succ_j = d.succ(j);
    let motive_j = d.eq_motive(lrng, &|d, x| {
        let sj = d.succ(j);
        d.le(sj, x)
    });
    let le_succj_succpm = d.transport(lrng, motive_j, hj, succ_pm, eq_lrng_succ_pm);
    let hj_le = d.lemma(p.le_of_succ_le_succ, &[j, pm, le_succj_succpm]);

    let x2 = d.sub(pm, j);
    let k1 = succ_j;
    let k2 = d.succ(x2);

    let one = d.num(1);
    let one_j = d.add(one, j);
    let eq_one_j_succj = one_add_eq_succ(d, &p, j);
    let h_j_eq_f_k1 = nat_congr_bool(d, one_j, k1, eq_one_j_succj, &|d, x| d.apply(f, &[x]));

    let one_x2 = d.add(one, x2);
    let eq_one_x2_succx2 = one_add_eq_succ(d, &p, x2);
    let h_x2_eq_f_k2 = nat_congr_bool(d, one_x2, k2, eq_one_x2_succx2, &|d, x| d.apply(f, &[x]));

    // `add j x2 = pm`.
    let add_j_x2_eq_pm = d.lemma(p.add_sub_cancel_of_le, &[j, pm, hj_le]);

    // `hsum : Eq (add k1 k2) n`, by peeling two `succ`s down to `add j x2 =
    // pm` and then `n = succ (succ pm)` (from `Lrng = succ pm`, `n = succ
    // Lrng`).
    let addk1k2 = d.add(k1, k2);
    let succ_add_step = d.lemma(p.succ_add, &[j, k2]); // Eq (add (succ j) k2) (succ (add j k2))
    let addjk2 = d.add(j, k2);
    let add_succ_step = d.lemma(p.add_succ, &[j, x2]); // Eq (add j (succ x2)) (succ (add j x2))
    let addjx2 = d.add(j, x2);
    let succ_addjx2 = d.succ(addjx2);
    let congr1 = d.congr(addjk2, succ_addjx2, add_succ_step, &|d, y| d.succ(y));
    let succ_succ_addjx2 = d.succ(succ_addjx2);
    let succ_succ_pm = d.succ(succ_pm);
    let congr2 = d.congr(addjx2, pm, add_j_x2_eq_pm, &|d, y| {
        let s = d.succ(y);
        d.succ(s)
    });
    let succ_succ_pm_eq_n = {
        let succ_pm_eq_lrng = d.symm(lrng, succ_pm, eq_lrng_succ_pm);
        let congr_s = d.congr(succ_pm, lrng, succ_pm_eq_lrng, &|d, y| d.succ(y));
        let succ_lrng = d.succ(lrng);
        let symm_n = d.symm(n, succ_lrng, eq_n_succ_lrng);
        d.trans(succ_succ_pm, succ_lrng, n, congr_s, symm_n)
    };
    let succ_addjk2 = d.succ(addjk2);
    let (_final_val, hsum) = d.chain(
        addk1k2,
        &[
            (succ_addjk2, succ_add_step),
            (succ_succ_addjx2, congr1),
            (succ_succ_pm, congr2),
            (n, succ_succ_pm_eq_n),
        ],
    );

    let gcd_iff = gcd_reflection_iff(d, &p, n, k1, k2, hsum);

    (k1, k2, x2, hsum, gcd_iff, h_j_eq_f_k1, h_x2_eq_f_k2)
}

/// See the module doc / [`NatPrelude::totient_even`] for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_totient_even(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let (ty, value) = {
        let n = d.kernel().fvar(n_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let two = d.num(2);
        let one = d.num(1);
        let zero = d.zero();
        let hn_ty = d.lt(two, n);

        // `n = succ Lrng`, `Lrng > 0` (so `Lrng = succ pm`).
        let hpos_n = zero_lt_via_c(d, &p, two, n, hn); // Lt zero n
        let eq_n_succ_lrng = {
            let f = pos_implies_succ_pred(d, &p, n); // Lt zero n -> Eq n (succ (pred n))
            d.apply(f, &[hpos_n])
        };
        let lrng = d.pred(n);
        let succ_lrng = d.succ(lrng);

        let le_two_lrng = {
            let motive_le = d.eq_motive(n, &|d, z| {
                let succ_two = d.succ(two);
                d.le(succ_two, z)
            });
            let le_succ2_succlrng = d.transport(n, motive_le, hn, succ_lrng, eq_n_succ_lrng);
            d.lemma(p.le_of_succ_le_succ, &[two, lrng, le_succ2_succlrng])
        };
        let le_one_lrng = {
            let r = d.lemma(p.le_refl, &[one]);
            let le_one_two = d.lemma(p.le_step, &[one, one, r]); // Le one two
            d.lemma(p.le_trans, &[one, two, lrng, le_one_two, le_two_lrng])
        };
        let eq_lrng_succ_pm = {
            let f = pos_implies_succ_pred(d, &p, lrng); // Lt zero Lrng -> Eq Lrng (succ (pred Lrng))
            d.apply(f, &[le_one_lrng]) // `le_one_lrng : Le one Lrng` IS `Lt zero Lrng`.
        };
        let pm = d.pred(lrng);

        // `f := totient_predicate(n)`; `h(k) := f(add one k)`.
        let f = totient_predicate(d, n);
        let h = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let arg = d.add(one, k);
            let fk = d.apply(f, &[arg]);
            d.lam_fv(k_fv, nat, fk)
        };

        // Step 0: `totient n = countRange f n = countRange h Lrng`.
        let not_eq_n_one = n_ne_one_from_lt_two(d, &p, n, hn);
        let f0_false = {
            let beq_n_1_false = d.lemma(p.beq_eq_false_of_ne, &[n, one, not_eq_n_one]);
            let g0 = d.gcd(zero, n);
            let gcd_zero_n = d.lemma(p.gcd_zero_left, &[n]);
            let congr_g0 = nat_congr_bool(d, g0, n, gcd_zero_n, &|d, x| {
                let one_i = d.num(1);
                d.beq(x, one_i)
            });
            let false_v = d.bool_false();
            let beq_g0_1 = d.beq(g0, one);
            let beq_n_1 = d.beq(n, one);
            d.bool_trans(beq_g0_1, beq_n_1, false_v, congr_g0, beq_n_1_false)
        };
        let cr_f_1_eq_0 = {
            let fz = d.apply(f, &[zero]);
            let false_v = d.bool_false();
            let one_v = d.num(1);
            let zero_v = d.zero();
            let sel = d.bool_select_nat(fz, one_v, zero_v);
            let congr_sel = bool_congr_nat(d, fz, false_v, f0_false, &|d, x| {
                let one_inner = d.num(1);
                let zero_inner = d.zero();
                d.bool_select_nat(x, one_inner, zero_inner)
            });
            let add_zero_sel = d.add(zero_v, sel);
            let zero_add_sel = d.lemma(p.zero_add, &[sel]);
            let sel_false = d.bool_select_nat(false_v, one_v, zero_v);
            let (_e, eq_final) =
                d.chain(add_zero_sel, &[(sel, zero_add_sel), (sel_false, congr_sel)]);
            eq_final
        };

        let eq_add1lrng_succlrng = one_add_eq_succ(d, &p, lrng);
        let succ_lrng_eq_n = d.symm(n, succ_lrng, eq_n_succ_lrng);
        let add1lrng = d.add(one, lrng);
        let eq_add1lrng_n = d.trans(add1lrng, succ_lrng, n, eq_add1lrng_succlrng, succ_lrng_eq_n);

        let cr_split = d.lemma(p.count_range_split, &[f, one, lrng]);
        let cr_h_lrng = count_range(d, &p, h, lrng);
        let cr_f_one = count_range(d, &p, f, one);
        let rhs_val = d.add(cr_f_one, cr_h_lrng);
        let cr_n_eq_rhs = {
            let motive_split = d.eq_motive(add1lrng, &|d, x| {
                let cr = count_range(d, &p, f, x);
                d.eq(cr, rhs_val)
            });
            d.transport(add1lrng, motive_split, cr_split, n, eq_add1lrng_n)
        };
        let totient_eq_cr_h = {
            let congr_rhs = d.congr(cr_f_one, zero, cr_f_1_eq_0, &|d, x| {
                let cr_h = count_range(d, &p, h, lrng);
                d.add(x, cr_h)
            });
            let zero_add_crh = d.lemma(p.zero_add, &[cr_h_lrng]);
            let add_zero_crh = d.add(zero, cr_h_lrng);
            let cr_f_n = count_range(d, &p, f, n);
            let (_e2, tec) = d.chain(
                cr_f_n,
                &[
                    (rhs_val, cr_n_eq_rhs),
                    (add_zero_crh, congr_rhs),
                    (cr_h_lrng, zero_add_crh),
                ],
            );
            tec
        };

        // `hyp1 : ∀ j, Lt j Lrng → Eq Bool (h (sub pm j)) (h j)`.
        let hyp1_term = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, lrng);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let (k1, k2, x2, _hsum, gcd_iff, h_j_eq_f_k1, h_x2_eq_f_k2) = reflection_pieces(
                d,
                &p,
                n,
                lrng,
                pm,
                eq_lrng_succ_pm,
                eq_n_succ_lrng,
                f,
                j,
                hj,
            );

            let ga = d.gcd(k1, n);
            let gb = d.gcd(k2, n);
            let bridge_eq = bool_eq_of_iff_eq_one(d, &p, ga, gb, gcd_iff); // Eq Bool (f k1) (f k2)
            let fk1 = d.apply(f, &[k1]);
            let fk2 = d.apply(f, &[k2]);
            let hx2 = d.apply(h, &[x2]);
            let hj_app = d.apply(h, &[j]);

            let symm_bridge = d.bool_symm(fk1, fk2, bridge_eq); // Eq Bool fk2 fk1
            let step1 = d.bool_trans(hx2, fk2, fk1, h_x2_eq_f_k2, symm_bridge); // Eq Bool hx2 fk1
            let symm_hj = d.bool_symm(hj_app, fk1, h_j_eq_f_k1); // Eq Bool fk1 hj_app
            let final_body = d.bool_trans(hx2, fk1, hj_app, step1, symm_hj); // Eq Bool hx2 hj_app

            let with_hj = d.lam_fv(hj_fv, hj_ty, final_body);
            d.lam_fv(j_fv, nat, with_hj)
        };

        // `hyp2 : ∀ j, Lt j Lrng → Eq Bool (h j) true → Not (Eq Nat j (sub pm
        // j))`.
        let hyp2_term = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, lrng);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);
            let hj_app_for_ty = d.apply(h, &[j]);
            let true_v = d.bool_true();
            let ht_ty = d.bool_eq(hj_app_for_ty, true_v);
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);

            let (k1, k2, x2, hsum, _gcd_iff, h_j_eq_f_k1, _h_x2_eq_f_k2) = reflection_pieces(
                d,
                &p,
                n,
                lrng,
                pm,
                eq_lrng_succ_pm,
                eq_n_succ_lrng,
                f,
                j,
                hj,
            );

            let eq_j_x2_ty = d.eq(j, x2);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            // `f k1 = true`, from `ht` and `h_j_eq_f_k1`.
            let hj_app = d.apply(h, &[j]);
            let fk1 = d.apply(f, &[k1]);
            let symm_hjk1 = d.bool_symm(hj_app, fk1, h_j_eq_f_k1); // Eq Bool fk1 hj_app
            let fk1_true = d.bool_trans(fk1, hj_app, true_v, symm_hjk1, ht); // Eq Bool fk1 true
            let gcd_k1_n = d.gcd(k1, n);
            let gcd_k1_n_eq_one = d.lemma(p.eq_of_beq_eq_true, &[gcd_k1_n, one, fk1_true]);

            // `K2 = K1` under `heq : Eq j x2`.
            let eq_x2_j = d.symm(j, x2, heq);
            let eq_k2_k1 = d.congr(x2, j, eq_x2_j, &|d, y| d.succ(y));
            let addk1k2 = d.add(k1, k2);
            let addk1k1 = d.add(k1, k1);
            let step_a = d.congr(k2, k1, eq_k2_k1, &|d, y| d.add(k1, y));
            let symm_step_a = d.symm(addk1k2, addk1k1, step_a);
            let sum_k1k1_eq_n = d.trans(addk1k1, addk1k2, n, symm_step_a, hsum);

            // `k1 | n`, `k1 | gcd k1 n = 1`, so `k1 = 1`.
            let dvd_refl_k1 = d.lemma(p.dvd_refl, &[k1]);
            let dvd_k1_addk1k1 = d.lemma(p.dvd_add, &[k1, k1, k1, dvd_refl_k1, dvd_refl_k1]);
            let dvd_k1_n = {
                let motive = d.eq_motive(addk1k1, &|d, x| d.dvd(k1, x));
                d.transport(addk1k1, motive, dvd_k1_addk1k1, n, sum_k1k1_eq_n)
            };
            let dvd_k1_gcd = d.lemma(p.dvd_gcd, &[k1, k1, n, dvd_refl_k1, dvd_k1_n]);
            let dvd_k1_one = {
                let motive = d.eq_motive(gcd_k1_n, &|d, x| d.dvd(k1, x));
                d.transport(gcd_k1_n, motive, dvd_k1_gcd, one, gcd_k1_n_eq_one)
            };
            let k1_eq_one = d.lemma(p.eq_one_of_dvd_one, &[k1, dvd_k1_one]);

            // `n = add k1 k1 = add one one = two`, contradicting `hn`.
            let add_one_one_eq_two = one_add_eq_succ(d, &p, one);
            let congr_addk1k1 = d.congr(k1, one, k1_eq_one, &|d, y| d.add(y, y));
            let symm_sum = d.symm(addk1k1, n, sum_k1k1_eq_n);
            let one_one = d.add(one, one);
            let (_e3, eq_n_two) = d.chain(
                n,
                &[
                    (addk1k1, symm_sum),
                    (one_one, congr_addk1k1),
                    (two, add_one_one_eq_two),
                ],
            );

            let motive_hn = d.eq_motive(n, &|d, x| {
                let two_ = d.num(2);
                d.lt(two_, x)
            });
            let lt_two_two = d.transport(n, motive_hn, hn, two, eq_n_two);
            let lt_irrefl_two = d.lemma(p.lt_irrefl, &[two]);
            let absurd = d.apply(lt_irrefl_two, &[lt_two_two]);

            let with_heq = d.lam_fv(heq_fv, eq_j_x2_ty, absurd);
            let with_ht = d.lam_fv(ht_fv, ht_ty, with_heq);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_ht);
            d.lam_fv(j_fv, nat, with_hj)
        };

        let even_cr_h = d.lemma(
            p.count_range_reversal_even,
            &[lrng, h, hyp1_term, hyp2_term],
        );

        let totient_n = d.const_app(p.totient, &[n]);
        let even_totient_ty = d.const_app(p.even, &[totient_n]);
        let even_totient = {
            let cr_f_n = count_range(d, &p, f, n);
            let symm_tec = d.symm(cr_f_n, cr_h_lrng, totient_eq_cr_h);
            let motive_even = d.eq_motive(cr_h_lrng, &|d, x| d.const_app(p.even, &[x]));
            d.transport(cr_h_lrng, motive_even, even_cr_h, cr_f_n, symm_tec)
        };

        let full_stmt = d.arrow(hn_ty, even_totient_ty);
        let full_proof = d.lam_fv(hn_fv, hn_ty, even_totient);
        let ty = d.pi_fv(n_fv, nat, full_stmt);
        let value = d.lam_fv(n_fv, nat, full_proof);
        (ty, value)
    };
    d.declare_theorem(p.totient_even, ty, value)?;
    Ok(())
}

/// `Exists.intro one (odd_predicate one) zero (Eq.refl one) : Odd one`
/// (`one = succ (add zero zero)` by pure defeq).
fn odd_one_witness(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.num(1);
    let zero = d.zero();
    let pred = odd_predicate(d, one);
    let one_lvl = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
    let refl_one = d.refl(one);
    d.apply(intro, &[nat, pred, zero, refl_one])
}

/// `Exists.intro zero (even_predicate zero) zero (Eq.refl zero) : Even zero`.
fn even_zero_witness(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let pred = even_predicate(d, zero);
    let one_lvl = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
    let refl_zero = d.refl(zero);
    d.apply(intro, &[nat, pred, zero, refl_zero])
}

// ============================================================================
// `Nat.odd_totient_iff_eq_one : ∀ n, Iff (Odd (totient n)) (Eq (totient n)
// one)`.
// ============================================================================

/// See the module doc / [`NatPrelude::odd_totient_iff_eq_one`] for the route:
/// the SAME `trichotomy(two, n)` shape `totient_eq_one_iff` uses, with the
/// `2 < n` branch now refuted by `totient_even` + `odd_not_even` instead of
/// a counting contradiction.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_odd_totient_iff_eq_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.odd_totient_iff_eq_one, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);

        let totient_n = d.const_app(p.totient, &[n]);
        let lhs_ty = d.const_app(p.odd, &[totient_n]);
        let rhs_ty = d.eq(totient_n, one);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // Odd (totient n)
            let body = trichotomy_elim(
                d,
                &p,
                two,
                n,
                rhs_ty,
                &|d, h_lt| {
                    // h_lt : Lt n two. Split n = 0 vs n = 1 (same shape as
                    // `totient_eq_one_iff`'s forward direction).
                    let le_n_1 = d.lemma(p.le_of_succ_le_succ, &[n, one, h_lt]);
                    let disj = d.lemma(p.lt_or_eq_of_le, &[n, one, le_n_1]);
                    let lt_n_1 = d.lt(n, one);
                    let eq_n_1 = d.eq(n, one);

                    let on_zero = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv); // h2 : Lt n one
                        let le_n_0 = d.lemma(p.le_of_succ_le_succ, &[n, zero, h2]);
                        let le_0_n = d.lemma(p.zero_le, &[n]);
                        let eq_n_0 = d.lemma(p.le_antisymm, &[n, zero, le_n_0, le_0_n]);

                        // Rewrite `h : Odd (totient n)` along `n = 0` to
                        // `Odd (totient zero)` (defeq `Odd zero`), then
                        // refute via `even_not_odd(zero, even_zero_witness)`.
                        let motive_odd = d.eq_motive(n, &|d, x| {
                            let t = d.const_app(p.totient, &[x]);
                            d.const_app(p.odd, &[t])
                        });
                        let h_odd0 = d.transport(n, motive_odd, h, zero, eq_n_0);
                        let even_zero = even_zero_witness(d, &p);
                        let not_odd_zero = d.lemma(p.even_not_odd, &[zero, even_zero]);
                        let false_pf = d.apply(not_odd_zero, &[h_odd0]);
                        let body = ex_falso(d, &p, rhs_ty, false_pf);
                        d.lam_fv(h2_fv, lt_n_1, body)
                    };
                    let on_one = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv); // h2 : Eq n one
                        let motive = d.eq_motive(one, &|d, x| {
                            let t = d.const_app(p.totient, &[x]);
                            d.eq(t, one)
                        });
                        let refl_at_one = d.refl(one); // Eq (totient one) one, by defeq
                        let eq_1_n = d.symm(n, one, h2);
                        let body = d.transport(one, motive, refl_at_one, n, eq_1_n);
                        d.lam_fv(h2_fv, eq_n_1, body)
                    };
                    d.const_app(
                        p.logic.or_elim,
                        &[lt_n_1, eq_n_1, rhs_ty, disj, on_zero, on_one],
                    )
                },
                &|d, h_eq| {
                    // h_eq : Eq n two.
                    let motive = d.eq_motive(two, &|d, x| {
                        let t = d.const_app(p.totient, &[x]);
                        d.eq(t, one)
                    });
                    let refl_at_two = d.refl(one); // Eq (totient two) one, by defeq
                    let eq_2_n = d.symm(n, two, h_eq);
                    d.transport(two, motive, refl_at_two, n, eq_2_n)
                },
                &|d, h_gt| {
                    // h_gt : Lt two n. `Even (totient n)` from `totient_even`,
                    // refuted against `h : Odd (totient n)` via `odd_not_even`.
                    let even_tn = d.lemma(p.totient_even, &[n, h_gt]);
                    let not_even_tn = d.lemma(p.odd_not_even, &[totient_n, h]);
                    let false_pf = d.apply(not_even_tn, &[even_tn]);
                    ex_falso(d, &p, rhs_ty, false_pf)
                },
            );
            d.lam_fv(h_fv, lhs_ty, body)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // Eq (totient n) one
            let odd_one = odd_one_witness(d, &p); // Odd one
            let motive = d.eq_motive(one, &|d, x| d.const_app(p.odd, &[x]));
            let eq_one_tn = d.symm(totient_n, one, h); // Eq one (totient n)
            let body = d.transport(one, motive, odd_one, totient_n, eq_one_tn);
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.odd_totient_iff : ∀ n, Iff (Odd (totient n)) (Or (Eq n one) (Eq n
// two))`.
// ============================================================================

/// [`NatPrelude::odd_totient_iff_eq_one`] composed with
/// [`NatPrelude::totient_eq_one_iff`] by direct `mp`/`mpr` function
/// composition.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_odd_totient_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.odd_totient_iff, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let two = d.num(2);

        let totient_n = d.const_app(p.totient, &[n]);
        let lhs_ty = d.const_app(p.odd, &[totient_n]);
        let mid_ty = d.eq(totient_n, one);
        let eq_n_1 = d.eq(n, one);
        let eq_n_2 = d.eq(n, two);
        let rhs_ty = d.const_app(p.logic.or, &[eq_n_1, eq_n_2]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        let iff_a = d.lemma(p.odd_totient_iff_eq_one, &[n]); // Iff lhs_ty mid_ty
        let iff_b = d.lemma(p.totient_eq_one_iff, &[n]); // Iff mid_ty rhs_ty

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let f_a = iff_forward(d, lhs_ty, mid_ty, iff_a);
            let step1 = d.apply(f_a, &[h]);
            let f_b = iff_forward(d, mid_ty, rhs_ty, iff_b);
            let step2 = d.apply(f_b, &[step1]);
            d.lam_fv(h_fv, lhs_ty, step2)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let r_b = iff_reverse(d, mid_ty, rhs_ty, iff_b);
            let step1 = d.apply(r_b, &[h]);
            let r_a = iff_reverse(d, lhs_ty, mid_ty, iff_a);
            let step2 = d.apply(r_a, &[step1]);
            d.lam_fv(h_fv, rhs_ty, step2)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// From `iff_ab : Iff (Eq a one) (Eq b one)`, derive `Eq Bool (beq a one)
/// (beq b one)` by deciding `beq a one` ([`bool_true_or_false`]) and pushing
/// each case through `eq_of_beq_eq_true`/`ne_of_beq_eq_false` and
/// `beq_eq_true_of_eq`/`beq_eq_false_of_ne`.
fn bool_eq_of_iff_eq_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    iff_ab: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let beq_a = d.beq(a, one);
    let beq_b = d.beq(b, one);
    let a_eq_one = d.eq(a, one);
    let b_eq_one = d.eq(b, one);
    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let cases = bool_true_or_false(d, &p, beq_a);

    let is_true_ty = d.bool_eq(beq_a, true_v);
    let is_false_ty = d.bool_eq(beq_a, false_v);
    let target = d.bool_eq(beq_a, beq_b);

    let on_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let a_eq = d.lemma(p.eq_of_beq_eq_true, &[a, one, h]);
        let mp = iff_forward(d, a_eq_one, b_eq_one, iff_ab);
        let b_eq = d.apply(mp, &[a_eq]);
        let beq_b_true = d.lemma(p.beq_eq_true_of_eq, &[b, one, b_eq]);
        let beq_b_true_rev = d.bool_symm(beq_b, true_v, beq_b_true);
        let result = d.bool_trans(beq_a, true_v, beq_b, h, beq_b_true_rev);
        d.lam_fv(h_fv, is_true_ty, result)
    };
    let on_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let a_ne_one = d.lemma(p.ne_of_beq_eq_false, &[a, one, h]);
        let not_b_eq_one = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let mpr = iff_reverse(d, a_eq_one, b_eq_one, iff_ab);
            let a_eq_from_b = d.apply(mpr, &[hb]);
            let absurd = d.apply(a_ne_one, &[a_eq_from_b]);
            d.lam_fv(hb_fv, b_eq_one, absurd)
        };
        let beq_b_false = d.lemma(p.beq_eq_false_of_ne, &[b, one, not_b_eq_one]);
        let beq_b_false_rev = d.bool_symm(beq_b, false_v, beq_b_false);
        let result = d.bool_trans(beq_a, false_v, beq_b, h, beq_b_false_rev);
        d.lam_fv(h_fv, is_false_ty, result)
    };
    d.const_app(
        p.logic.or_elim,
        &[is_true_ty, is_false_ty, target, cases, on_true, on_false],
    )
}

// ============================================================================
// `Nat.totient_coprime_totient_iff : ∀ m n, Iff (Eq (gcd (totient m)
// (totient n)) one) (Or (Or (Eq m one) (Eq m two)) (Or (Eq n one) (Eq n
// two)))`.
// ============================================================================

/// Non-dependent `Exists.rec` over `Nat` (local copy of the same helper
/// several other files carry privately, per this file's own local-copies-
/// per-file convention).
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

/// `Nat.dvd two x`, from `h_even : Even x`. Destructures the witness `k`
/// (`x = add k k`) via [`exists_elim`] and builds `Eq x (mul two k)` from
/// `succ_mul`/`one_mul` (`mul two k = mul (succ one) k = add (mul one k) k
/// = add k k`, since `succ one` and `two` are the same interned `ExprId`).
fn even_dvd_two(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, h_even: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let predicate = even_predicate(d, x);
    let goal = d.dvd(two, x);

    let minor = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let ww = d.add(w, w);
        let hw_ty = d.eq(x, ww);
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);

        let mul_two_w = d.mul(two, w);
        let one_w = d.mul(one, w);
        let succ_mul_step = d.lemma(p.succ_mul, &[one, w]); // Eq mul_two_w (add one_w w)
        let one_mul_w = d.lemma(p.one_mul, &[w]); // Eq one_w w
        let add_one_w_w = d.add(one_w, w);
        let congr_add = d.congr(one_w, w, one_mul_w, &|d, y| d.add(y, w));
        let (_e, mul_two_w_eq_ww) =
            d.chain(mul_two_w, &[(add_one_w_w, succ_mul_step), (ww, congr_add)]);
        let ww_eq_mul = d.symm(mul_two_w, ww, mul_two_w_eq_ww);
        let x_eq_mul = d.trans(x, ww, mul_two_w, hw, ww_eq_mul);
        let dvd_proof = dvd_intro(d, two, x, w, x_eq_mul);

        let inner = d.lam_fv(hw_fv, hw_ty, dvd_proof);
        d.lam_fv(w_fv, nat, inner)
    };
    exists_elim(d, &p, predicate, goal, minor, h_even)
}

/// `Eq two one -> False`: transport `le_refl two` along the (false) equation
/// to `Le two one`, then peel one `succ` (`le_of_succ_le_succ`) to `Le one
/// zero`, refuted by `not_succ_le_zero` -- the same ending
/// [`totient_le_one_contradiction_above_two`] and [`n_ne_one_from_lt_two`]
/// already use.
fn refute_eq_two_one(d: &mut NatDev<'_>, p: &NatPrelude, h: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let zero = d.zero();
    let le_refl_two = d.lemma(p.le_refl, &[two]);
    let motive = d.eq_motive(two, &|d, x| {
        let two_ = d.num(2);
        d.le(two_, x)
    });
    let le_two_one = d.transport(two, motive, le_refl_two, one, h); // Le two one
    let le_1_0 = d.lemma(p.le_of_succ_le_succ, &[one, zero, le_two_one]);
    let not_le_1_0 = d.lemma(p.not_succ_le_zero, &[zero]);
    d.apply(not_le_1_0, &[le_1_0])
}

/// From `Even a`, `Even b`, and `h : Eq (gcd a b) one`, derive `False`: both
/// are divisible by `2` ([`even_dvd_two`]), so `2 | gcd a b = 1` (`dvd_gcd`
/// transported along `h`), forcing `Eq two one` (`eq_one_of_dvd_one`),
/// refuted by [`refute_eq_two_one`].
fn two_evens_coprime_contradiction(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h_even_a: ExprId,
    h_even_b: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let dvd2a = even_dvd_two(d, &p, a, h_even_a);
    let dvd2b = even_dvd_two(d, &p, b, h_even_b);
    let dvd2gcd = d.lemma(p.dvd_gcd, &[two, a, b, dvd2a, dvd2b]); // dvd two (gcd a b)
    let gcd_ab = d.gcd(a, b);
    let motive = d.eq_motive(gcd_ab, &|d, x| d.dvd(two, x));
    let dvd2one = d.transport(gcd_ab, motive, dvd2gcd, one, h);
    let eq_2_1 = d.lemma(p.eq_one_of_dvd_one, &[two, dvd2one]);
    refute_eq_two_one(d, &p, eq_2_1)
}

/// From `h : Eq a one`, derive `Eq (gcd a b) one` unconditionally:
/// `coprime_one_left_iff(b)`'s `mpr` at `True.intro` gives `Eq (gcd one b)
/// one`, and transport along `symm h` bridges `one` back to `a`.
fn close_via_gcd_left_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let true_ty = d.kernel().const_(p.logic.true_, vec![]);
    let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
    let gcd_one_b = d.gcd(one, b);
    let cop_ty = d.eq(gcd_one_b, one);
    let iff1 = d.lemma(p.coprime_one_left_iff, &[b]);
    let mpr1 = iff_reverse(d, cop_ty, true_ty, iff1);
    let gcd_one_b_eq_one = d.apply(mpr1, &[true_intro]);
    let eq_one_a = d.symm(a, one, h);
    let motive = d.eq_motive(one, &|d, x| {
        let g = d.gcd(x, b);
        d.eq(g, one)
    });
    d.transport(one, motive, gcd_one_b_eq_one, a, eq_one_a)
}

/// Mirror of [`close_via_gcd_left_one`] via `coprime_one_right_iff`, for
/// `Eq (gcd a b) one` from `h : Eq b one`.
fn close_via_gcd_right_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let true_ty = d.kernel().const_(p.logic.true_, vec![]);
    let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
    let gcd_a_one = d.gcd(a, one);
    let cop_ty = d.eq(gcd_a_one, one);
    let iff1 = d.lemma(p.coprime_one_right_iff, &[a]);
    let mpr1 = iff_reverse(d, cop_ty, true_ty, iff1);
    let gcd_a_one_eq_one = d.apply(mpr1, &[true_intro]);
    let eq_one_b = d.symm(b, one, h);
    let motive = d.eq_motive(one, &|d, x| {
        let g = d.gcd(a, x);
        d.eq(g, one)
    });
    d.transport(one, motive, gcd_a_one_eq_one, b, eq_one_b)
}

/// From `h : Eq (gcd (totient m) (totient n)) one` and `heq : Eq m zero`,
/// derive `Eq (totient n) one`: transport `h` along `heq` gives, up to the
/// defeq `totient zero ≡ zero`, `Eq (gcd zero (totient n)) one`; bridge with
/// `gcd_zero_left(totient n)` by `trans`, relying on the kernel's own defeq
/// check to reconcile the two spellings -- the same idiom
/// `totient_eq_one_iff`'s `refl_at_one`/`refl_at_two` branches already use.
fn totient_n_eq_one_from_m_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    h: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let totient_n = d.const_app(p.totient, &[n]);
    let motive = d.eq_motive(m, &|d, x| {
        let tx = d.const_app(p.totient, &[x]);
        let tn = d.const_app(p.totient, &[n]);
        let g = d.gcd(tx, tn);
        d.eq(g, one)
    });
    let h0 = d.transport(m, motive, h, zero, heq); // Eq (gcd (totient zero) totient_n) one
    let gcd_zero_tn = d.gcd(zero, totient_n);
    let gzl = d.lemma(p.gcd_zero_left, &[totient_n]); // Eq gcd_zero_tn totient_n
    let symm_gzl = d.symm(gcd_zero_tn, totient_n, gzl); // Eq totient_n gcd_zero_tn
    d.trans(totient_n, gcd_zero_tn, one, symm_gzl, h0)
}

/// From `h : Eq (gcd (totient m) (totient n)) one`, `heq : Eq n zero`, and
/// `h_even_m : Even (totient m)`, derive `False`: bridge `h` down to
/// `Eq (totient m) one` via `gcd_comm`/`gcd_zero_left` (this prelude has no
/// named `gcd_zero_right`, so the bridge goes through `gcd_comm` first --
/// the mirror image of [`totient_n_eq_one_from_m_zero`]), then contradict
/// `Even (totient m)` against `Odd one` via `even_not_odd`.
fn totient_m_even_n_zero_contradiction(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    h: ExprId,
    heq: ExprId,
    h_even_m: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let totient_m = d.const_app(p.totient, &[m]);
    let motive = d.eq_motive(n, &|d, x| {
        let tm = d.const_app(p.totient, &[m]);
        let tx = d.const_app(p.totient, &[x]);
        let g = d.gcd(tm, tx);
        d.eq(g, one)
    });
    let h0 = d.transport(n, motive, h, zero, heq); // Eq (gcd totient_m (totient zero)) one
    let gcd_tm_zero = d.gcd(totient_m, zero);
    let comm1 = d.lemma(p.gcd_comm, &[totient_m, zero]); // Eq gcd_tm_zero (gcd zero totient_m)
    let gcd_zero_tm = d.gcd(zero, totient_m);
    let gzl = d.lemma(p.gcd_zero_left, &[totient_m]); // Eq gcd_zero_tm totient_m
    let bridge = d.trans(gcd_tm_zero, gcd_zero_tm, totient_m, comm1, gzl); // Eq gcd_tm_zero totient_m
    let symm_bridge = d.symm(gcd_tm_zero, totient_m, bridge); // Eq totient_m gcd_tm_zero
    let totient_m_eq_one = d.trans(totient_m, gcd_tm_zero, one, symm_bridge, h0); // Eq totient_m one
    let even_one = {
        let motive2 = d.eq_motive(totient_m, &|d, x| d.const_app(p.even, &[x]));
        d.transport(totient_m, motive2, h_even_m, one, totient_m_eq_one)
    };
    let not_odd_one = d.lemma(p.even_not_odd, &[one, even_one]);
    let odd_one = odd_one_witness(d, &p);
    d.apply(not_odd_one, &[odd_one])
}

/// See the module doc / [`NatPrelude::totient_coprime_totient_iff`] for the
/// route: `mpr` is unconditional composition via
/// [`close_via_gcd_left_one`]/[`close_via_gcd_right_one`]; `mp`'s hard case
/// (`2 < m`, `2 < n`) refutes two evens sharing a `gcd` of `1` via
/// [`two_evens_coprime_contradiction`], and the `m = 0`/`n = 0` sub-cases
/// route through [`totient_n_eq_one_from_m_zero`]/
/// [`totient_m_even_n_zero_contradiction`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_totient_coprime_totient_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_coprime_totient_iff, 2, &|d, v| {
        let m = v[0];
        let n = v[1];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);

        let totient_m = d.const_app(p.totient, &[m]);
        let totient_n = d.const_app(p.totient, &[n]);
        let gcd_tm_tn = d.gcd(totient_m, totient_n);
        let lhs_ty = d.eq(gcd_tm_tn, one);

        let eq_m1 = d.eq(m, one);
        let eq_m2 = d.eq(m, two);
        let or_m = d.const_app(p.logic.or, &[eq_m1, eq_m2]);
        let eq_n1 = d.eq(n, one);
        let eq_n2 = d.eq(n, two);
        let or_n = d.const_app(p.logic.or, &[eq_n1, eq_n2]);
        let rhs_ty = d.const_app(p.logic.or, &[or_m, or_n]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        // ---- mp: lhs_ty -> rhs_ty ----
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = trichotomy_elim(
                d,
                &p,
                two,
                m,
                rhs_ty,
                &|d, h_lt_m| {
                    // h_lt_m : Lt m two.
                    let le_m1 = d.lemma(p.le_of_succ_le_succ, &[m, one, h_lt_m]);
                    let disj = d.lemma(p.lt_or_eq_of_le, &[m, one, le_m1]); // Or (Lt m one)(Eq m one)
                    let lt_m1 = d.lt(m, one);
                    let on_zero_m = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv); // Lt m one
                        let le_m0 = d.lemma(p.le_of_succ_le_succ, &[m, zero, h2]);
                        let le_0m = d.lemma(p.zero_le, &[m]);
                        let eq_m0 = d.lemma(p.le_antisymm, &[m, zero, le_m0, le_0m]); // Eq m zero
                        let tn_eq_one = totient_n_eq_one_from_m_zero(d, &p, m, n, h, eq_m0);
                        let disj_n = d.lemma(p.totient_eq_one_iff, &[n]);
                        let eq_tn_one = d.eq(totient_n, one);
                        let mpn = iff_forward(d, eq_tn_one, or_n, disj_n);
                        let or_n_proof = d.apply(mpn, &[tn_eq_one]);
                        let goal_proof = d.const_app(p.logic.or_inr, &[or_m, or_n, or_n_proof]);
                        d.lam_fv(h2_fv, lt_m1, goal_proof)
                    };
                    let on_one_m = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv); // Eq m one
                        let or_m_proof = d.const_app(p.logic.or_inl, &[eq_m1, eq_m2, h2]);
                        let goal_proof = d.const_app(p.logic.or_inl, &[or_m, or_n, or_m_proof]);
                        d.lam_fv(h2_fv, eq_m1, goal_proof)
                    };
                    d.const_app(
                        p.logic.or_elim,
                        &[lt_m1, eq_m1, rhs_ty, disj, on_zero_m, on_one_m],
                    )
                },
                &|d, h_eq_m| {
                    // h_eq_m : Eq m two.
                    let or_m_proof = d.const_app(p.logic.or_inr, &[eq_m1, eq_m2, h_eq_m]);
                    d.const_app(p.logic.or_inl, &[or_m, or_n, or_m_proof])
                },
                &|d, h_gt_m| {
                    // h_gt_m : Lt two m.
                    let even_tm = d.lemma(p.totient_even, &[m, h_gt_m]);
                    trichotomy_elim(
                        d,
                        &p,
                        two,
                        n,
                        rhs_ty,
                        &|d, h_lt_n| {
                            let le_n1 = d.lemma(p.le_of_succ_le_succ, &[n, one, h_lt_n]);
                            let disj = d.lemma(p.lt_or_eq_of_le, &[n, one, le_n1]);
                            let lt_n1 = d.lt(n, one);
                            let on_zero_n = {
                                let h2_fv = d.fresh_fvar();
                                let h2 = d.kernel().fvar(h2_fv); // Lt n one
                                let le_n0 = d.lemma(p.le_of_succ_le_succ, &[n, zero, h2]);
                                let le_0n = d.lemma(p.zero_le, &[n]);
                                let eq_n0 = d.lemma(p.le_antisymm, &[n, zero, le_n0, le_0n]);
                                let false_pf = totient_m_even_n_zero_contradiction(
                                    d, &p, m, n, h, eq_n0, even_tm,
                                );
                                let goal_proof = ex_falso(d, &p, rhs_ty, false_pf);
                                d.lam_fv(h2_fv, lt_n1, goal_proof)
                            };
                            let on_one_n = {
                                let h2_fv = d.fresh_fvar();
                                let h2 = d.kernel().fvar(h2_fv); // Eq n one
                                let or_n_proof = d.const_app(p.logic.or_inl, &[eq_n1, eq_n2, h2]);
                                let goal_proof =
                                    d.const_app(p.logic.or_inr, &[or_m, or_n, or_n_proof]);
                                d.lam_fv(h2_fv, eq_n1, goal_proof)
                            };
                            d.const_app(
                                p.logic.or_elim,
                                &[lt_n1, eq_n1, rhs_ty, disj, on_zero_n, on_one_n],
                            )
                        },
                        &|d, h_eq_n| {
                            let or_n_proof = d.const_app(p.logic.or_inr, &[eq_n1, eq_n2, h_eq_n]);
                            d.const_app(p.logic.or_inr, &[or_m, or_n, or_n_proof])
                        },
                        &|d, h_gt_n| {
                            let even_tn = d.lemma(p.totient_even, &[n, h_gt_n]);
                            let false_pf = two_evens_coprime_contradiction(
                                d, &p, totient_m, totient_n, even_tm, even_tn, h,
                            );
                            ex_falso(d, &p, rhs_ty, false_pf)
                        },
                    )
                },
            );
            d.lam_fv(h_fv, lhs_ty, body)
        };

        // ---- mpr: rhs_ty -> lhs_ty ----
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let on_m = {
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv); // Or eq_m1 eq_m2
                let on_m1 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // Eq m one
                    let disj_m = d.const_app(p.logic.or_inl, &[eq_m1, eq_m2, h2]);
                    let iff_m = d.lemma(p.totient_eq_one_iff, &[m]);
                    let eq_tm_one = d.eq(totient_m, one);
                    let mprm = iff_reverse(d, eq_tm_one, or_m, iff_m);
                    let tm_eq_one = d.apply(mprm, &[disj_m]);
                    let body = close_via_gcd_left_one(d, &p, totient_m, totient_n, tm_eq_one);
                    d.lam_fv(h2_fv, eq_m1, body)
                };
                let on_m2 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // Eq m two
                    let disj_m = d.const_app(p.logic.or_inr, &[eq_m1, eq_m2, h2]);
                    let iff_m = d.lemma(p.totient_eq_one_iff, &[m]);
                    let eq_tm_one = d.eq(totient_m, one);
                    let mprm = iff_reverse(d, eq_tm_one, or_m, iff_m);
                    let tm_eq_one = d.apply(mprm, &[disj_m]);
                    let body = close_via_gcd_left_one(d, &p, totient_m, totient_n, tm_eq_one);
                    d.lam_fv(h2_fv, eq_m2, body)
                };
                let body = d.const_app(p.logic.or_elim, &[eq_m1, eq_m2, lhs_ty, hm, on_m1, on_m2]);
                d.lam_fv(hm_fv, or_m, body)
            };
            let on_n = {
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv); // Or eq_n1 eq_n2
                let on_n1 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // Eq n one
                    let disj_n = d.const_app(p.logic.or_inl, &[eq_n1, eq_n2, h2]);
                    let iff_n = d.lemma(p.totient_eq_one_iff, &[n]);
                    let eq_tn_one2 = d.eq(totient_n, one);
                    let mprn = iff_reverse(d, eq_tn_one2, or_n, iff_n);
                    let tn_eq_one = d.apply(mprn, &[disj_n]);
                    let body = close_via_gcd_right_one(d, &p, totient_m, totient_n, tn_eq_one);
                    d.lam_fv(h2_fv, eq_n1, body)
                };
                let on_n2 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv); // Eq n two
                    let disj_n = d.const_app(p.logic.or_inr, &[eq_n1, eq_n2, h2]);
                    let iff_n = d.lemma(p.totient_eq_one_iff, &[n]);
                    let eq_tn_one2 = d.eq(totient_n, one);
                    let mprn = iff_reverse(d, eq_tn_one2, or_n, iff_n);
                    let tn_eq_one = d.apply(mprn, &[disj_n]);
                    let body = close_via_gcd_right_one(d, &p, totient_m, totient_n, tn_eq_one);
                    d.lam_fv(h2_fv, eq_n2, body)
                };
                let body = d.const_app(p.logic.or_elim, &[eq_n1, eq_n2, lhs_ty, hn, on_n1, on_n2]);
                d.lam_fv(hn_fv, or_n, body)
            };
            let body = d.const_app(p.logic.or_elim, &[or_m, or_n, lhs_ty, h, on_m, on_n]);
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.coprime_succ_self`, `Nat.totient_eq_zero`, the general
/// `countRange` counting machinery (`countRange_succ_of_true`,
/// `countRange_le_of_le`, `countRange_ge_two_of_two_witnesses`), and the two
/// mirrors that compose it (`dvd_two_of_totient_le_one`,
/// `totient_eq_one_iff`), in dependency order.
///
/// `Nat.totient_even` is NOT dispatched here: it needs `Nat.Even`
/// (`declare_parity_all`) and `Nat.countRange_reversal_even`
/// (`declare_count_range_reversal_even`), both of which run AFTER this
/// function in `build_nat_prelude`'s own order. See
/// [`declare_totient_even`]'s call site in `nat_prelude.rs`.
pub(super) fn declare_totient_lemmas_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_coprime_succ_self(d, p)?;
    declare_totient_eq_zero(d, p)?;
    declare_count_range_succ_of_true(d, p)?;
    declare_count_range_le_of_le(d, p)?;
    declare_count_range_ge_two_of_two_witnesses(d, p)?;
    declare_dvd_two_of_totient_le_one(d, p)?;
    declare_totient_eq_one_iff(d, p)?;
    Ok(())
}
