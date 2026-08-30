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

/// `Nat.dvd a n` (`Exists (fun q => Eq n (mul a q))`), built from a witness
/// `q` and `eq_proof : Eq n (mul a q)` -- local copy of `divisibility.rs`'s
/// private `dvd_intro`, per this file's own stated convention (local copies
/// per file rather than a shared private module).
fn dvd_intro(d: &mut NatDev<'_>, a: ExprId, n: ExprId, witness: ExprId, eq_proof: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Eliminate a [`trichotomy`] (`Or (Lt x c) (Or (Eq x c) (Lt c x))`) directly
/// into a proof of `target`, given a proof for each of the three cases --
/// local generalization of `finite.rs`'s `two_way_split` (which eliminates
/// only the middle case) into a full three-way eliminator.
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
    d.const_app(logic.or_elim, &[lt_xc, inner, target, tri, on_left, on_right])
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

    let full_stmt = d.arrow(hpos_ty, d.arrow(hle_ty, goal));
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
                d.const_app(p.logic.or_elim, &[lt_n_1, eq_n_1, rhs_ty, disj, on_zero, on_one])
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
        let body = d.const_app(p.logic.or_elim, &[eq_n_1, eq_n_2, lhs_ty, h, on_one, on_two]);
        d.lam_fv(h_fv, rhs_ty, body)
    };

    let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.totient_eq_one_iff, ty, value)
}

/// Declare `Nat.coprime_succ_self`, `Nat.totient_eq_zero`, the general
/// `countRange` counting machinery (`countRange_succ_of_true`,
/// `countRange_le_of_le`, `countRange_ge_two_of_two_witnesses`), and the two
/// mirrors that compose it (`dvd_two_of_totient_le_one`,
/// `totient_eq_one_iff`), in dependency order.
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
