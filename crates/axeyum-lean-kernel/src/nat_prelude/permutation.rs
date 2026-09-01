//! `Nat.permInverse` — an explicit, computable inverse for an injective
//! self-map on `[0,n)` — and the two-sided-inverse theorems it exists for.
//!
//! ## Why this file, and the representation question it answers
//!
//! The brief for this slice was the symmetric group: permutations of `[0,n)`
//! under composition, as a second worked instance of `Nat.IsGroupOn`
//! (`group.rs`). `IsGroupOn op e inv n` is stated over `op : Nat → Nat →
//! Nat`, `e : Nat`, `inv : Nat → Nat` — its carrier elements are bare `Nat`s
//! bounded by `n`. A permutation is not a `Nat`, it is a *function*
//! `Nat → Nat`, so `IsGroupOn` as written cannot be instantiated at the
//! symmetric group directly: there is no encoding of "a permutation" as a
//! natural number anywhere in this kernel (no `List`, no `Finset`, no
//! dependent pair). Two of the three options the brief posed were:
//!
//!  (a) generalise `IsGroupOn` cheaply to a version over function-valued
//!      elements, carrier membership `BijectiveOn f n` in place of `a < n`;
//!  (b) index permutations by naturals below `n!` — explicitly ruled out by
//!      the brief as unreachable in one slice, and this file does not attempt
//!      it.
//!
//! **Note, 2026-08-31 (ADR-1310).** Option (b) is recorded above as out of
//! scope for one slice, which is right, and it is worth saying that it was
//! never the only alternative to (a). A sum or product over a set of
//! permutations does not need permutations to be DATA; it needs a **fold**
//! over them, and a fold is a function. `Int.sumMaps` (`int_prelude/
//! sum_maps.rs`) folds over every map `[0,m) -> [0,n)` with no aggregate type,
//! by `Nat.rec` with a higher-order motive; the permutations are the injective
//! ones, and injectivity on a bounded range is `Nat.beq`-decidable. That does
//! not give a symmetric-group CARRIER — which is what `IsGroupOnFn` needed and
//! what this file solved a different way — but it does mean "there is no
//! encoding of a permutation" should not be read as "no statement quantifying
//! over permutations can be written".
//!
//! **(a) is what this file does relative to `group.rs`'s own machinery**:
//! `Nat.comp` (`relation.rs`) is already the right operation, `Nat.id`
//! (declared below) is the right identity, and `Nat.BijectiveOn`
//! (`relation.rs`) is the right carrier predicate. What was *missing* before
//! this file — and the actual blocker the previous lane hit — was the
//! **inverse**: `IsGroupOn`/any function-valued analogue needs an *explicit*
//! `inv : (Nat→Nat) → (Nat→Nat)`, not merely a proof that one exists.
//! `Nat.bijective_of_injective_on` (`relation.rs`) proves `∃`-shaped
//! surjectivity, and `Exists.rec` eliminates only into `Prop` (this kernel's
//! standing rule) — so no term of a *function* type can be extracted from it.
//! [`Nat.permInverse`](declare_perm_inverse) is that missing explicit
//! construction, built the same way `finite.rs`'s pigeonhole `compact` is:
//! total over every input via `Bool`-selected `Nat.rec`, correct only under
//! the hypotheses that make the search meaningful, proved via the
//! "generalize the selector, then instantiate at `bool_refl(condition)`"
//! trick `finite.rs::compact_eq_of_gt` and `transposition.rs`'s
//! `bool_select_nat_lt` already established (a local copy of the latter's
//! shape lives here, since `transposition.rs` may not be edited by this
//! slice).
//!
//! This file lands the inverse construction and its two-sided-inverse
//! theorems — the brief's explicit "IF ONLY STEPS 1–2 LAND, THAT IS A GOOD
//! OUTCOME" target — plus the cheap half of the group generalisation itself:
//! `Nat.id` and `Nat.comp_assoc`, the operation and identity `IsGroupOnFn`
//! would need, with associativity proved by *pure delta/beta/iota reduction*
//! (`Nat.comp` unfolds to the same normal-form lambda on both sides — no
//! `funext`, no axiom, nothing beyond what `Eq.refl` already checks). A later
//! slice adds `Nat.bijective_on_comp` (closure: composing two bijections on
//! `[0,n)` is one) and `Nat.bijective_on_perm_inverse` (the inverse of a
//! bijection on `[0,n)` is one) — the two "IF ONLY STEP 1/2 LANDS" targets
//! this file's own follow-up brief asked for.
//!
//! ## The full `IsGroupOnFn` instance WAS REFUTED at its original statement —
//! ## fixed by bounding `identity`/`inverse`, not by weakening the claim
//!
//! The natural next step reads as "bundle closure/identity/inverse the way
//! `group.rs::declare_mod_add_is_group` bundles ℤ/n." That target is
//! unreachable, and not for lack of a lemma: `Nat.IsGroupOnFn`'s `identity`
//! and `inverse` conjuncts state `op a e = a` / `op a (inv a) = e` as
//! **`Eq (Nat → Nat) _ _`** — literal, UNBOUNDED equality of total
//! `Nat → Nat` functions (`fn_eq`, below) — and for the symmetric-group
//! instance (`op := Nat.comp`, `inv a := Nat.permInverse a n`) that equality
//! is provably **false**, not merely unproved:
//!
//! `Nat.permInverse a n k < n` holds for **every** `k`, not only `k < n`
//! (`perm_inverse_lt_proof`, needing only `0 < n` — the search bound is `n`
//! regardless of how large `k` is). So for `n > 0` and any `k ≥ n`,
//! `Nat.MapsInto a n` applies at index `Nat.permInverse a n k` (which is
//! `< n`) to give `a (Nat.permInverse a n k) < n ≤ k`, hence
//! `a (Nat.permInverse a n k) ≠ k = Nat.id k`. That is a **counterexample**
//! to `Nat.comp a (Nat.permInverse a n) = Nat.id` at every point `k ≥ n`, for
//! every `n > 0` — and at `n = 0`, `Nat.permInverse a n` is the constant `0`
//! (the base case, unconditionally), so `Nat.comp a (Nat.permInverse a 0)` is
//! the constant `a 0`, which cannot equal `Nat.id` on an infinite carrier
//! either. `Nat.permInverse a n` is only ever a two-sided inverse of `a` ON
//! `[0,n)`; outside that range it is a fixed junk value, and `Nat.id` is the
//! identity EVERYWHERE — no witness for `inv` closes that gap, because no
//! `Nat → Nat` total function can.
//!
//! So `Nat.IsGroupOnFn`'s `identity`/`inverse` conjuncts, AS ORIGINALLY
//! DECLARED, were satisfiable only by a genuinely constant-on-its-complement
//! `op`/`e` (`group.rs`'s bare-`Nat` `IsGroupOn` never has this problem — a
//! bound `a < n` is a real restriction that makes `e`/`inv a` themselves live
//! `< n`, but `BijectiveOn f n` restricts `f`'s *behaviour*, not its *type*:
//! `f` is still a total `Nat → Nat`, defined everywhere, and `Eq (Nat → Nat)`
//! sees all of it). The counterexample is a fact about the STATEMENT, not
//! about permutations — it never claimed `Nat.comp a (Nat.permInverse a n)`
//! disagrees with `Nat.id` anywhere on `[0,n)`, only that unbounded equality
//! also inspects points nothing here ever promised to control.
//!
//! **The fix**: `identity`/`inverse` now state their two equality conjuncts
//! with `Nat.EqOn f g n := ∀ i, i < n → f i = g i` ([`declare_eq_on`], below)
//! in place of `Eq (Nat → Nat) f g` — the same restriction `BijectiveOn f n`
//! already applies to a function's *behaviour*, now applied to the equalities
//! that behaviour must satisfy. This is a **new definition and a redeclared
//! `IsGroupOnFn`**, not a lemma about the old predicate (this repository's
//! standing rule against editing an existing declaration's statement is
//! waived here for exactly this reason — the old statement was
//! unsatisfiable, so nothing could depend on it; every reference was checked
//! before the edit, see the commit this lands in). With that fix,
//! `Nat.symmetric_group_isGroupOnFn` ([`declare_symmetric_group_is_group_on_fn`],
//! below) is the instance this file's brief was written for: closure is
//! `Nat.bijective_on_comp`, associativity is `Nat.comp_assoc`, and the
//! `identity`/`inverse` conjuncts are exactly `Nat.permInverse_right`/`_left`
//! — the theorems this file already proved, which only ever promised the
//! equality ON `[0,n)` in the first place.
//!
//! ## What's declared
//!
//! - `Nat.permInverse (f : Nat → Nat) (n k : Nat) : Nat` — a bounded
//!   downward search: `Nat.rec` on `n` with base `0` (an arbitrary default,
//!   never reached under this file's hypotheses) and step `fun j ih =>
//!   if Nat.beq (f j) k then j else ih`. Computes the least index actually
//!   found scanning `n-1, n-2, …, 0`; **which** index among possibly-several
//!   in a non-injective `f` is unspecified by the correctness theorems below
//!   (they only ever need *some* preimage), so nothing here claims it is
//!   "the least" beyond what the recursion happens to produce.
//! - `Nat.permInverse_right : ∀ f n, SurjectiveOn f n → ∀ k, k < n →
//!   f (permInverse f n k) = k` — `f` composed with `permInverse f n` is
//!   the identity on `[0,n)`: a genuine RIGHT inverse (`f ∘ g = id`). Proved
//!   by induction on the search bound, generalizing nothing (the target `k`
//!   is fixed throughout the recursion): the base case is vacuous
//!   (`Lt i 0` is impossible), the step case-splits the witness index
//!   `i < succ j` into `i < j` (carried by the induction hypothesis, closed
//!   regardless of which way `Nat.beq (f j) k` falls via the generalize/
//!   `bool_refl` trick) or `i = j` (closed directly: `f j = k` makes
//!   `Nat.beq (f j) k` compute to `true`, selecting `j` on the nose).
//! - `Nat.permInverse_left : ∀ f n, MapsInto f n → InjectiveOn f n →
//!   ∀ i, i < n → permInverse f n (f i) = i` — `permInverse f n` composed
//!   with `f` is the identity on `[0,n)`: a genuine LEFT inverse
//!   (`g ∘ f = id`). Does **not** need `SurjectiveOn`: `i` itself is already
//!   a witness that `f i` has a preimage below `n`, so the induction above
//!   applies directly at `k := f i` with `i` as the existence witness: the
//!   search is guaranteed to land on *some* index `i₀` with `f i₀ = f i`,
//!   and `f`'s injectivity (plus `Nat.permInverse`'s own boundedness, see
//!   below) then forces `i₀ = i`.
//! - `Nat.id : Nat → Nat := fun x => x` — the identity self-map;
//!   `IsGroupOnFn`'s `e`.
//! - `Nat.comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)` — the
//!   associativity conjunct `IsGroupOnFn` (over `Nat.comp`) would need,
//!   proved by `Eq.refl`: both sides delta/beta-reduce to the literal term
//!   `fun x => f (g (h x))`, so the kernel's own conversion check *is* the
//!   proof.
//! - `Nat.bijective_on_comp : ∀ n a b, BijectiveOn a n → BijectiveOn b n →
//!   BijectiveOn (comp a b) n` — `IsGroupOnFn`'s closure conjunct.
//! - `Nat.bijective_on_perm_inverse : ∀ n f, BijectiveOn f n →
//!   BijectiveOn (permInverse f n) n` — the inverse of a bijection on
//!   `[0,n)` is itself one.
//! - `Nat.EqOn (f g : Nat → Nat) (n : Nat) : Prop := ∀ i, i < n →
//!   Eq Nat (f i) (g i)` — bounded function equality, the fix described
//!   above, plus `Nat.eqOn_refl`/`Nat.eqOn_symm`/`Nat.eqOn_trans` (reflexive,
//!   symmetric, transitive at every bound `n`).
//! - `Nat.IsGroupOnFn` — REDECLARED (see "The fix", above): `identity`'s and
//!   `inverse`'s two equality conjuncts now use `Nat.EqOn · · n` in place of
//!   the unbounded `Eq (Nat → Nat) · ·`; `assoc` is untouched (it holds
//!   unbounded, genuinely, via `Nat.comp_assoc`).
//! - `Nat.symmetric_group_isGroupOnFn : ∀ n, IsGroupOnFn Nat.comp Nat.id
//!   (fun f => Nat.permInverse f n) n` — the symmetric group on `[0,n)`,
//!   landed. No side condition on `n`: every conjunct holds at `n = 0` too
//!   (vacuously, the same way `group.rs`'s bounded predicates do).
//!
//! Internal to the induction (never given a kernel-level name, matching how
//! `finite.rs`'s `compact_eq_of_le`/`_of_gt`/`compact_injective` stay plain
//! Rust functions rather than declared theorems): the boundedness fact
//! `permInverse f n k < n` for `0 < n`, and the raw existence-hypothesis
//! correctness lemma both public theorems specialize.
//!
//! ## Status
//!
//! All of the above are declared here and axiom-free. No classical logic:
//! every case split is on `Nat`'s decidable order/equality (`Nat.beq`,
//! `trichotomy`-free — only `lt_or_eq_of_le`/`le_of_lt_succ`, already proved)
//! or on a concrete `Bool` value via `Bool.rec`, never on an assumed
//! excluded middle.
//!
//! `Nat.symmetric_group_isGroupOnFn` — the full instance — IS declared, once
//! `Nat.IsGroupOnFn`'s `identity`/`inverse` conjuncts were rebuilt on
//! `Nat.EqOn`. See "The fix", above.

use super::NatPrelude;
use super::finite::ex_falso;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.permInverse`: it calls `Nat.beq` (height 1) inside
/// a `Bool.rec` selection, so `2` is strictly above what it unfolds through.
const INVERSE_INDEX_HEIGHT: u16 = 2;

/// Delta height for `Nat.id`: it calls nothing, so `1` is sound (matches
/// `Nat.comp`'s own height in `relation.rs`).
const ID_HEIGHT: u16 = 1;

/// Delta height for `Nat.IsGroupOnFn`: a plain bounded `Prop` predicate over
/// caller-supplied `op`/`inv` and `Nat.bijectiveOn` (height 1), the same
/// height `group.rs::GROUP_HEIGHT` uses for `Nat.IsGroupOn`.
const GROUP_FN_HEIGHT: u16 = 1;

/// `Nat.permInverse f m k`, built directly (no lambda redex), for a
/// caller-supplied bound `m` (usually the induction variable, not always the
/// final `n`).
fn perm_inverse_at(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, m: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.perm_inverse, &[f, m, k])
}

/// The predicate `fun i => And (Lt i m) (Eq Nat (f i) k)`, the existential
/// body `permInverse`'s correctness lemma both destructures (as a
/// hypothesis) and builds (as a witness) against.
fn exists_predicate(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let logic = p.logic;
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let bound = d.lt(i, m);
    let fi = d.apply(f, &[i]);
    let eqk = d.eq(fi, k);
    let body = d.const_app(logic.and, &[bound, eqk]);
    d.lam_fv(i_fv, nat, body)
}

/// `Exists (fun i => And (Lt i m) (Eq Nat (f i) k))`, from an
/// already-built predicate (see [`exists_predicate`]) — kept as a separate
/// step so a caller needing both the `Exists` type and the raw predicate
/// (for `Exists.rec`) shares one interned predicate term.
fn exists_of_predicate(d: &mut NatDev<'_>, pred: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let logic = d.prelude().logic;
    let e = d.kernel().const_(logic.exists_, vec![one]);
    d.apply(e, &[nat, pred])
}

/// `ha : Lt a n, hb : Lt b n ⊢ Lt (bool_select_nat cond a b) n`, for an
/// arbitrary `cond : Bool` — direct `Bool.rec` on `cond`, needing no fact
/// about which branch it actually selects. A local copy of
/// `transposition.rs::bool_select_nat_lt` (private there, and
/// `transposition.rs` is off-limits to this slice).
#[allow(clippy::too_many_arguments)]
fn bool_select_nat_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let sv = d.bool_select_nat(sel, a, b);
        let body = d.lt(sv, n);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, hb, ha, cond])
}

/// `Or (Eq Nat m 0) (Lt (permInverse f m k) m)`, by induction on `m`
/// (`f`, `k` fixed throughout, captured from the enclosing scope). Base
/// `m = 0` takes the left disjunct (`Eq.refl`). Step `m = succ j`: reduce
/// the prior bound `Or (Eq j 0) (Lt (permInverse f j k) j)` to
/// `Lt (permInverse f j k) (succ j)` either way (via `zero_lt_succ`
/// transported along `j = 0`, or `lt_of_lt_of_le` through `le_succ`), then
/// [`bool_select_nat_lt`] with `a := j` (`lt_succ_self`) closes the right
/// disjunct unconditionally in the selector.
fn perm_inverse_bounded(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    m: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;

    d.induct(
        &|d, x| {
            let idx = perm_inverse_at(d, &p, f, x, k);
            let zero = d.zero();
            let eq0 = d.eq(x, zero);
            let ltx = d.lt(idx, x);
            d.const_app(logic.or, &[eq0, ltx])
        },
        &|d| {
            let zero = d.zero();
            let idx0 = perm_inverse_at(d, &p, f, zero, k);
            let eq0 = d.eq(zero, zero);
            let lt0 = d.lt(idx0, zero);
            let refl0 = d.refl(zero);
            d.const_app(logic.or_inl, &[eq0, lt0, refl0])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let zero = d.zero();
            let eq_sj0 = d.eq(sj, zero);
            let idx_j = perm_inverse_at(d, &p, f, j, k);
            let idx_sj = perm_inverse_at(d, &p, f, sj, k);
            let lt_sj = d.lt(idx_sj, sj);

            let eq_j0 = d.eq(j, zero);
            let lt_j_j = d.lt(idx_j, j);
            let idx_j_lt_sj_ty = d.lt(idx_j, sj);

            let on_eq = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let h_rev = d.symm(j, zero, h);
                let idx0 = perm_inverse_at(d, &p, f, zero, k);
                let motive = d.eq_motive(zero, &|d, x| {
                    let idxx = perm_inverse_at(d, &p, f, x, k);
                    let sx = d.succ(x);
                    d.lt(idxx, sx)
                });
                let s_zero = d.succ(zero);
                let body_at_zero = d.lemma(p.zero_lt_succ, &[zero]);
                let _ = idx0;
                let _ = s_zero;
                let result = d.transport(zero, motive, body_at_zero, j, h_rev);
                d.lam_fv(h_fv, eq_j0, result)
            };
            let on_lt = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let le_j_sj = d.lemma(p.le_succ, &[j]);
                let result = d.lemma(p.lt_of_lt_of_le, &[idx_j, j, sj, h, le_j_sj]);
                d.lam_fv(h_fv, lt_j_j, result)
            };
            let idx_j_lt_sj = d.const_app(
                logic.or_elim,
                &[eq_j0, lt_j_j, idx_j_lt_sj_ty, ih, on_eq, on_lt],
            );

            let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
            let fj = d.apply(f, &[j]);
            let cond = d.beq(fj, k);
            let sel_lt = bool_select_nat_lt(d, &p, cond, j, idx_j, sj, j_lt_sj, idx_j_lt_sj);
            d.const_app(logic.or_inr, &[eq_sj0, lt_sj, sel_lt])
        },
        m,
    )
}

/// `pos_n : Lt 0 n ⊢ Lt (permInverse f n k) n`, by eliminating
/// [`perm_inverse_bounded`]'s left disjunct (`n = 0` contradicts `pos_n`
/// via `lt_irrefl`, transported).
fn perm_inverse_lt_proof(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    n: ExprId,
    pos_n: ExprId,
) -> ExprId {
    let p = *p;
    let bounded = perm_inverse_bounded(d, &p, f, k, n);
    let zero = d.zero();
    let eq_n0 = d.eq(n, zero);
    let idx = perm_inverse_at(d, &p, f, n, k);
    let lt_n = d.lt(idx, n);

    let on_eq = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = d.eq_motive(n, &|d, x| {
            let zero = d.zero();
            d.lt(zero, x)
        });
        let z_lt_z = d.transport(n, motive, pos_n, zero, h);
        let false_pf = d.lemma(p.lt_irrefl, &[zero, z_lt_z]);
        let result = ex_falso(d, &p, lt_n, false_pf);
        d.lam_fv(h_fv, eq_n0, result)
    };
    let on_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        d.lam_fv(h_fv, lt_n, h)
    };
    d.const_app(p.logic.or_elim, &[eq_n0, lt_n, lt_n, bounded, on_eq, on_lt])
}

/// `cond : Bool` (arbitrary), `ih_correct : Eq Nat (f idx_j) k` ⊢
/// `Eq Nat (f (bool_select_nat cond j idx_j)) k` — the "generalize the
/// selector, then instantiate at `bool_refl(condition)`" trick
/// (`finite.rs::compact_eq_of_gt`'s shape): the `false` branch is exactly
/// `ih_correct` (selection reduces to `idx_j`); the `true` branch derives
/// `f j = k` straight from the `Nat.beq` evidence via `eq_of_beq_eq_true`,
/// independent of `ih_correct`.
#[allow(clippy::too_many_arguments)]
fn select_correct_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    cond: ExprId,
    j: ExprId,
    idx_j: ExprId,
    ih_correct: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let true_val = d.bool_true();
    let bool_ty = d.bool_ty();

    let branch_for = |d: &mut NatDev<'_>, sel: ExprId| -> ExprId {
        let eq_cond_sel = d.bool_eq(cond, sel);
        let sel_val = d.bool_select_nat(sel, j, idx_j);
        let fsel = d.apply(f, &[sel_val]);
        let concl = d.eq(fsel, k);
        d.arrow(eq_cond_sel, concl)
    };
    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        d.lam_fv(heq_fv, heq_ty, ih_correct)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, true_val);
        let fj = d.apply(f, &[j]);
        let fj_eq_k = d.lemma(p.eq_of_beq_eq_true, &[fj, k, heq]);
        d.lam_fv(heq_fv, heq_ty, fj_eq_k)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let body = branch_for(d, sel);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

/// `Exists (fun i => And (Lt i m) (Eq Nat (f i) k)) → Eq Nat (f (permInverse
/// f m k)) k`, by induction on `m` (`f`, `k` fixed throughout). Base `m = 0`:
/// the hypothesis is vacuous (`Lt i 0` impossible), closed by `Exists.rec`
/// into `not_lt_zero`/`ex_falso`. Step `m = succ j`: destructure the witness
/// `i`, `i < succ j`, `f i = k` via `Exists.rec`; `le_of_lt_succ` +
/// `lt_or_eq_of_le` split `i` against `j`. `i < j` reuses the witness for the
/// bound-`j` existential and closes via the induction hypothesis, then
/// [`select_correct_step`] (the search step doesn't care which way
/// `Nat.beq (f j) k` falls). `i = j` transports `f i = k` to `f j = k`
/// directly, which forces `Nat.beq (f j) k = true` (`beq_eq_true_of_eq`) and
/// so `permInverse f (succ j) k` selects `j` on the nose
/// (`finite.rs::select_nat_true`).
fn perm_inverse_correct(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();

    d.induct(
        &|d, m| {
            let pred = exists_predicate(d, &p, f, k, m);
            let ex_ty = exists_of_predicate(d, pred);
            let idx = perm_inverse_at(d, &p, f, m, k);
            let fidx = d.apply(f, &[idx]);
            let concl = d.eq(fidx, k);
            d.arrow(ex_ty, concl)
        },
        &|d| {
            let zero = d.zero();
            let pred0 = exists_predicate(d, &p, f, k, zero);
            let ex0 = exists_of_predicate(d, pred0);
            let idx0 = perm_inverse_at(d, &p, f, zero, k);
            let fidx0 = d.apply(f, &[idx0]);
            let concl = d.eq(fidx0, k);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let bound_ty = d.lt(i, zero);
            let fi_ = d.apply(f, &[i]);
            let eqk_ty = d.eq(fi_, k);
            let hand_ty = d.const_app(logic.and, &[bound_ty, eqk_ty]);
            let hi = and_left(d, bound_ty, eqk_ty, hand);
            let false_pf = d.lemma(p.not_lt_zero, &[i, hi]);
            let inner_result = ex_falso(d, &p, concl, false_pf);
            let minor = {
                let with_hand = d.lam_fv(hand_fv, hand_ty, inner_result);
                d.lam_fv(i_fv, nat, with_hand)
            };

            let motive = d.kernel().lam(anon, ex0, concl, BinderInfo::Default);
            let rec = d.kernel().const_(logic.exists_rec, vec![one]);
            let applied = d.apply(rec, &[nat, pred0, motive, minor, h]);
            d.lam_fv(h_fv, ex0, applied)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let pred_sj = exists_predicate(d, &p, f, k, sj);
            let ex_sj = exists_of_predicate(d, pred_sj);
            let idx_j = perm_inverse_at(d, &p, f, j, k);
            let idx_sj = perm_inverse_at(d, &p, f, sj, k);
            let fidx_sj = d.apply(f, &[idx_sj]);
            let concl = d.eq(fidx_sj, k);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let bound_ty = d.lt(i, sj);
            let fi_ = d.apply(f, &[i]);
            let eqk_ty = d.eq(fi_, k);
            let hand_ty = d.const_app(logic.and, &[bound_ty, eqk_ty]);
            let hi = and_left(d, bound_ty, eqk_ty, hand);
            let heq_fi = and_right(d, bound_ty, eqk_ty, hand);

            let i_le_j = d.lemma(p.le_of_lt_succ, &[i, j, hi]);
            let disj = d.lemma(p.lt_or_eq_of_le, &[i, j, i_le_j]);
            let lt_ij = d.lt(i, j);
            let eq_ij = d.eq(i, j);

            let fj = d.apply(f, &[j]);
            let cond = d.beq(fj, k);
            let bsn = d.bool_select_nat(cond, j, idx_j);
            let f_bsn_ = d.apply(f, &[bsn]);
            let target_ty = d.eq(f_bsn_, k);

            let on_lt = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let and_proof = d.const_app(logic.and_intro, &[lt_ij, eqk_ty, h2, heq_fi]);
                let pred_j = exists_predicate(d, &p, f, k, j);
                let ex_j = exists_of_predicate(d, pred_j);
                let _ = ex_j;
                let intro = d.kernel().const_(logic.exists_intro, vec![one]);
                let ex_j_witness = d.apply(intro, &[nat, pred_j, i, and_proof]);
                let ih_applied = d.apply(ih, &[ex_j_witness]);
                let result = select_correct_step(d, &p, f, k, cond, j, idx_j, ih_applied);
                d.lam_fv(h2_fv, lt_ij, result)
            };
            let on_eq = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let motive2 = d.eq_motive(i, &|d, x| {
                    let fx = d.apply(f, &[x]);
                    d.eq(fx, k)
                });
                let fj_eq_k = d.transport(i, motive2, heq_fi, j, h2);
                let fj = d.apply(f, &[j]);
                let cond_true = d.lemma(p.beq_eq_true_of_eq, &[fj, k, fj_eq_k]);
                let sel_eq_j = super::finite::select_nat_true(d, cond, j, idx_j, cond_true);
                let congr_step = d.congr(bsn, j, sel_eq_j, &|d, v| d.apply(f, &[v]));
                let f_bsn = d.apply(f, &[bsn]);
                let result = d.trans(f_bsn, fj, k, congr_step, fj_eq_k);
                d.lam_fv(h2_fv, eq_ij, result)
            };
            let inner_result = d.const_app(
                logic.or_elim,
                &[lt_ij, eq_ij, target_ty, disj, on_lt, on_eq],
            );

            let minor = {
                let with_hand = d.lam_fv(hand_fv, hand_ty, inner_result);
                d.lam_fv(i_fv, nat, with_hand)
            };
            let motive = d.kernel().lam(anon, ex_sj, concl, BinderInfo::Default);
            let rec = d.kernel().const_(logic.exists_rec, vec![one]);
            let applied = d.apply(rec, &[nat, pred_sj, motive, minor, h]);
            d.lam_fv(h_fv, ex_sj, applied)
        },
        n,
    )
}

/// Admit `Nat.permInverse : (Nat → Nat) → Nat → Nat → Nat`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_perm_inverse(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let anon = d.anon_name();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let zero = d.zero();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let cond = d.beq(fj, k);
        let body = d.bool_select_nat(cond, j, ih);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let one = d.level_one();
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    let body = d.apply(rec, &[motive, zero, minor_succ, n]);

    // Curried argument order must be `f, n, k` (matching this file's
    // `perm_inverse_at` calling convention `[f, m, k]`), so `k` is the
    // OUTERMOST-but-one binder built INNERMOST here (wrapping `body`
    // directly), then `n`, then `f` — nested `lam_fv` builds outermost-last.
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        let over_n = d.arrow(nat, over_k);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.perm_inverse,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(INVERSE_INDEX_HEIGHT),
    })
}

/// Admit `Nat.permInverse_right : ∀ f n, SurjectiveOn f n → ∀ k, k < n →
/// f (permInverse f n k) = k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_perm_inverse_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let surj_ty = d.const_app(p.surjective_on, &[f, n]);
    let surj_fv = d.fresh_fvar();
    let surj = d.kernel().fvar(surj_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let ex = d.apply(surj, &[k, hk]);
    let correct = perm_inverse_correct(d, &p, f, k, n);
    let result = d.apply(correct, &[ex]);

    let idx = perm_inverse_at(d, &p, f, n, k);
    let fidx = d.apply(f, &[idx]);
    let concl = d.eq(fidx, k);

    let value = {
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        let with_k = d.lam_fv(k_fv, nat, with_hk);
        let with_surj = d.lam_fv(surj_fv, surj_ty, with_k);
        let with_n = d.lam_fv(n_fv, nat, with_surj);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let with_hk = d.arrow(hk_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_hk);
        let with_surj = d.arrow(surj_ty, with_k);
        let with_n = d.pi_fv(n_fv, nat, with_surj);
        d.pi_fv(f_fv, fn_ty, with_n)
    };
    d.declare_theorem(p.perm_inverse_right, ty, value)
}

/// Admit `Nat.permInverse_left : ∀ f n, MapsInto f n → InjectiveOn f n →
/// ∀ i, i < n → permInverse f n (f i) = i`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_perm_inverse_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let logic = p.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let maps_ty = d.const_app(p.maps_into, &[f, n]);
    // `MapsInto f n` is not needed by this proof (the existence witness for
    // `k := f i` is `i` itself, which needs only `i < n`), but is kept as a
    // hypothesis so the theorem states the natural "inverse of a self-map"
    // shape rather than the more general "inverse of any function" one.
    let maps_fv = d.fresh_fvar();
    let inj_ty = d.const_app(p.injective_on, &[f, n]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let fi = d.apply(f, &[i]);

    // Existence witness for `perm_inverse_correct` at k := f i: i itself,
    // with `Eq Nat (f i) (f i)` by `Eq.refl`.
    let pred = exists_predicate(d, &p, f, fi, n);
    let ex_ty = exists_of_predicate(d, pred);
    let refl_fi = d.refl(fi);
    let and_ty_r = d.eq(fi, fi);
    let and_proof = d.const_app(logic.and_intro, &[hi_ty, and_ty_r, hi, refl_fi]);
    let one = d.level_one();
    let intro = d.kernel().const_(logic.exists_intro, vec![one]);
    let ex_witness = d.apply(intro, &[nat, pred, i, and_proof]);
    let _ = ex_ty;

    let correct = perm_inverse_correct(d, &p, f, fi, n);
    let correct_at_i = d.apply(correct, &[ex_witness]); // Eq Nat (f (permInverse f n fi)) fi

    // `0 < n` from `i < n` via `zero_le i` and transitivity.
    let zero = d.zero();
    let zero_le_i = d.lemma(p.zero_le, &[i]);
    let pos_n = d.lemma(p.lt_of_le_of_lt, &[zero, i, n, zero_le_i, hi]);

    let idx = perm_inverse_at(d, &p, f, n, fi);
    let idx_lt_n = perm_inverse_lt_proof(d, &p, f, fi, n, pos_n);

    // `InjectiveOn f n` at (idx, i): `f idx = f i` (= `correct_at_i`), both
    // bounded by `n`, gives `idx = i`.
    let idx_eq_i = d.apply(inj, &[idx, i, idx_lt_n, hi, correct_at_i]);

    let concl = d.eq(idx, i);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, idx_eq_i);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_inj = d.lam_fv(inj_fv, inj_ty, with_i);
        let with_maps = d.lam_fv(maps_fv, maps_ty, with_inj);
        let with_n = d.lam_fv(n_fv, nat, with_maps);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let with_hi = d.arrow(hi_ty, concl);
        let with_i = d.pi_fv(i_fv, nat, with_hi);
        let with_inj = d.arrow(inj_ty, with_i);
        let with_maps = d.arrow(maps_ty, with_inj);
        let with_n = d.pi_fv(n_fv, nat, with_maps);
        d.pi_fv(f_fv, fn_ty, with_n)
    };
    d.declare_theorem(p.perm_inverse_left, ty, value)
}

/// Admit `Nat.id : Nat → Nat := fun x => x`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_id(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let value = d.lam_fv(x_fv, nat, x);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.id,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ID_HEIGHT),
    })
}

/// Admit `Nat.comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)`
/// — the associativity conjunct an `IsGroupOnFn` predicate over `Nat.comp`
/// would need. Both sides delta/beta-reduce to the literal term
/// `fun x => f (g (h x))`, so `Eq.refl` of that common normal form is
/// accepted by the kernel's own conversion check — no `funext`, no axiom.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_comp_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let one = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let comp_fg = d.const_app(p.comp, &[f, g]);
    let lhs = d.const_app(p.comp, &[comp_fg, h]);
    let comp_gh = d.const_app(p.comp, &[g, h]);
    let rhs = d.const_app(p.comp, &[f, comp_gh]);

    // `d.eq`/`d.refl` are hardcoded to `Eq Nat`; `lhs`/`rhs` are `Nat → Nat`,
    // so `Eq`/`Eq.refl` are built directly at the function carrier here (the
    // same pattern `helpers.rs::apply_nat_function_equality` uses).
    let eq_const = d.kernel().const_(p.logic.eq, vec![one]);
    let concl = d.apply(eq_const, &[fn_ty, lhs, rhs]);
    let refl_const = d.kernel().const_(p.logic.eq_refl, vec![one]);
    let proof = d.apply(refl_const, &[fn_ty, lhs]);

    let value = {
        let with_h = d.lam_fv(h_fv, fn_ty, proof);
        let with_g = d.lam_fv(g_fv, fn_ty, with_h);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let with_h = d.pi_fv(h_fv, fn_ty, concl);
        let with_g = d.pi_fv(g_fv, fn_ty, with_h);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    d.declare_theorem(p.comp_assoc, ty, value)
}

/// Admit `Nat.bijective_on_comp : ∀ n a b, BijectiveOn a n → BijectiveOn b n →
/// BijectiveOn (comp a b) n` — `IsGroupOnFn`'s closure conjunct over
/// `Nat.comp`, and the first of this slice's two targets.
///
/// Destructure both `BijectiveOn` hypotheses into their three conjuncts
/// (`InjectiveOn`/`MapsInto`/`SurjectiveOn`, `and_left`/`and_right` against
/// `BijectiveOn`'s own right-nested `And` packing), then:
///
/// - `InjectiveOn (comp a b) n` is `Nat.injective_on_comp` (`relation.rs`)
///   applied directly, at `f := a`, `g := b`.
/// - `MapsInto (comp a b) n` needs no case split: `MapsInto b n` puts `b i`
///   inside `a`'s bounded domain, so `MapsInto a n` closes it.
/// - `SurjectiveOn (comp a b) n` destructures both witnesses via nested
///   `Exists.rec` — `k`'s `a`-preimage `j` (from `SurjectiveOn a n`), then
///   `j`'s `b`-preimage `i` (from `SurjectiveOn b n`) — reusing this file's
///   own [`exists_predicate`]/[`exists_of_predicate`] bundling (the same
///   `∃ i, i<m ∧ f i = k` shape [`perm_inverse_correct`] already
///   destructures), the same two-level nesting `divisibility.rs::dvd_trans`
///   uses to compose two existential witnesses.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_bijective_on_comp(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let one = d.level_one();
    let anon = d.anon_name();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let inj_a_ty = d.const_app(p.injective_on, &[a, n]);
    let maps_a_ty = d.const_app(p.maps_into, &[a, n]);
    let surj_a_ty = d.const_app(p.surjective_on, &[a, n]);
    let inner_a_ty = d.const_app(logic.and, &[maps_a_ty, surj_a_ty]);
    let bij_a_ty = d.const_app(logic.and, &[inj_a_ty, inner_a_ty]);
    let bij_a_fv = d.fresh_fvar();
    let bij_a = d.kernel().fvar(bij_a_fv);

    let inj_b_ty = d.const_app(p.injective_on, &[b, n]);
    let maps_b_ty = d.const_app(p.maps_into, &[b, n]);
    let surj_b_ty = d.const_app(p.surjective_on, &[b, n]);
    let inner_b_ty = d.const_app(logic.and, &[maps_b_ty, surj_b_ty]);
    let bij_b_ty = d.const_app(logic.and, &[inj_b_ty, inner_b_ty]);
    let bij_b_fv = d.fresh_fvar();
    let bij_b = d.kernel().fvar(bij_b_fv);

    let inj_a = and_left(d, inj_a_ty, inner_a_ty, bij_a);
    let inner_a = and_right(d, inj_a_ty, inner_a_ty, bij_a);
    let maps_a = and_left(d, maps_a_ty, surj_a_ty, inner_a);
    let surj_a = and_right(d, maps_a_ty, surj_a_ty, inner_a);

    let inj_b = and_left(d, inj_b_ty, inner_b_ty, bij_b);
    let inner_b = and_right(d, inj_b_ty, inner_b_ty, bij_b);
    let maps_b = and_left(d, maps_b_ty, surj_b_ty, inner_b);
    let surj_b = and_right(d, maps_b_ty, surj_b_ty, inner_b);

    let comp_ab = d.const_app(p.comp, &[a, b]);

    // --- InjectiveOn (comp a b) n ---
    let inj_comp = d.lemma(p.injective_on_comp, &[n, a, b, maps_b, inj_b, inj_a]);

    // --- MapsInto (comp a b) n ---
    let maps_comp = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, n);
        let bi = d.apply(b, &[i]);
        let bi_lt_n = d.apply(maps_b, &[i, hi]);
        let ai_lt_n = d.apply(maps_a, &[bi, bi_lt_n]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, ai_lt_n);
        d.lam_fv(i_fv, nat, with_hi)
    };

    // --- SurjectiveOn (comp a b) n ---
    let surj_comp = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n);

        let target_pred = exists_predicate(d, &p, comp_ab, k, n);
        let target_ty = exists_of_predicate(d, target_pred);

        let pred_a = exists_predicate(d, &p, a, k, n);
        let ex_a_ty = exists_of_predicate(d, pred_a);
        let ex_a = d.apply(surj_a, &[k, hk]);

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hand_a_fv = d.fresh_fvar();
        let hand_a = d.kernel().fvar(hand_a_fv);
        let hj_ty = d.lt(j, n);
        let aj = d.apply(a, &[j]);
        let aj_eq_k_ty = d.eq(aj, k);
        let hand_a_ty = d.const_app(logic.and, &[hj_ty, aj_eq_k_ty]);
        let hj = and_left(d, hj_ty, aj_eq_k_ty, hand_a);
        let haj = and_right(d, hj_ty, aj_eq_k_ty, hand_a);

        let pred_b = exists_predicate(d, &p, b, j, n);
        let ex_b_ty = exists_of_predicate(d, pred_b);
        let ex_b = d.apply(surj_b, &[j, hj]);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hand_b_fv = d.fresh_fvar();
        let hand_b = d.kernel().fvar(hand_b_fv);
        let hi_ty = d.lt(i, n);
        let bi = d.apply(b, &[i]);
        let bi_eq_j_ty = d.eq(bi, j);
        let hand_b_ty = d.const_app(logic.and, &[hi_ty, bi_eq_j_ty]);
        let hi = and_left(d, hi_ty, bi_eq_j_ty, hand_b);
        let hbi = and_right(d, hi_ty, bi_eq_j_ty, hand_b);

        let ai_bi = d.apply(a, &[bi]);
        let congr_step = d.congr(bi, j, hbi, &|d, x| d.apply(a, &[x]));
        let ai_bi_eq_k = d.trans(ai_bi, aj, k, congr_step, haj);

        let comp_i = d.apply(comp_ab, &[i]);
        let comp_i_eq_k_ty = d.eq(comp_i, k);
        // `comp_i` is definitionally `a (b i)` (`comp`'s own delta/beta
        // unfolding), so `ai_bi_eq_k` — whose inferred type is literally
        // `Eq Nat (a (b i)) k` — type-checks directly against
        // `comp_i_eq_k_ty` via the kernel's conversion check, the same move
        // `injective_on_comp`'s own proof (`relation.rs`) documents.
        let and_proof_inner =
            d.const_app(logic.and_intro, &[hi_ty, comp_i_eq_k_ty, hi, ai_bi_eq_k]);
        let intro = d.kernel().const_(logic.exists_intro, vec![one]);
        let witness_inner = d.apply(intro, &[nat, target_pred, i, and_proof_inner]);

        let minor_b = {
            let with_hand_b = d.lam_fv(hand_b_fv, hand_b_ty, witness_inner);
            d.lam_fv(i_fv, nat, with_hand_b)
        };
        let motive_b = d
            .kernel()
            .lam(anon, ex_b_ty, target_ty, BinderInfo::Default);
        let rec_b = d.kernel().const_(logic.exists_rec, vec![one]);
        let result_b = d.apply(rec_b, &[nat, pred_b, motive_b, minor_b, ex_b]);

        let minor_a = {
            let with_hand_a = d.lam_fv(hand_a_fv, hand_a_ty, result_b);
            d.lam_fv(j_fv, nat, with_hand_a)
        };
        let motive_a = d
            .kernel()
            .lam(anon, ex_a_ty, target_ty, BinderInfo::Default);
        let rec_a = d.kernel().const_(logic.exists_rec, vec![one]);
        let result_a = d.apply(rec_a, &[nat, pred_a, motive_a, minor_a, ex_a]);

        let with_hk = d.lam_fv(hk_fv, hk_ty, result_a);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let inj_comp_ty = d.const_app(p.injective_on, &[comp_ab, n]);
    let maps_comp_ty = d.const_app(p.maps_into, &[comp_ab, n]);
    let surj_comp_ty = d.const_app(p.surjective_on, &[comp_ab, n]);
    let inner_comp_ty = d.const_app(logic.and, &[maps_comp_ty, surj_comp_ty]);
    let bij_comp_ty = d.const_app(logic.and, &[inj_comp_ty, inner_comp_ty]);

    let inner_comp_proof = d.const_app(
        logic.and_intro,
        &[maps_comp_ty, surj_comp_ty, maps_comp, surj_comp],
    );
    let bij_comp_proof = d.const_app(
        logic.and_intro,
        &[inj_comp_ty, inner_comp_ty, inj_comp, inner_comp_proof],
    );

    let value = {
        let with_bij_b = d.lam_fv(bij_b_fv, bij_b_ty, bij_comp_proof);
        let with_bij_a = d.lam_fv(bij_a_fv, bij_a_ty, with_bij_b);
        let with_b = d.lam_fv(b_fv, fn_ty, with_bij_a);
        let with_a = d.lam_fv(a_fv, fn_ty, with_b);
        d.lam_fv(n_fv, nat, with_a)
    };
    let ty = {
        let with_bij_b = d.arrow(bij_b_ty, bij_comp_ty);
        let with_bij_a = d.arrow(bij_a_ty, with_bij_b);
        let with_b = d.pi_fv(b_fv, fn_ty, with_bij_a);
        let with_a = d.pi_fv(a_fv, fn_ty, with_b);
        d.pi_fv(n_fv, nat, with_a)
    };
    d.declare_theorem(p.bijective_on_comp, ty, value)
}

/// Admit `Nat.bijective_on_perm_inverse : ∀ n f, BijectiveOn f n →
/// BijectiveOn (permInverse f n) n` — the inverse of a bijection on `[0,n)`
/// is itself one, and this slice's second target.
///
/// Write `g := permInverse f n` (a partial application of [`Self`]'s own
/// `Nat.permInverse`, of type `Nat → Nat`).
///
/// - `InjectiveOn g n`: `f` is `g`'s LEFT inverse on `[0,n)`
///   ([`declare_perm_inverse_right`]'s `permInverse_right`, needing
///   `SurjectiveOn f n`), so `g i = g j` composed with `f` on both sides
///   collapses directly to `i = j` — no case split, no use of `InjectiveOn f n`.
/// - `MapsInto g n`: exactly [`perm_inverse_lt_proof`]'s own conclusion
///   (`permInverse f n k < n` for **any** `k`, given `0 < n`, derived from
///   `k < n` via `zero_le`/`lt_of_le_of_lt` the same way
///   [`declare_perm_inverse_left`] derives its own `0 < n`).
/// - `SurjectiveOn g n`: `f k` is the preimage of `k` under `g` —
///   [`declare_perm_inverse_left`]'s `permInverse_left` is precisely
///   `permInverse f n (f k) = k`, needing `MapsInto f n`/`InjectiveOn f n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_bijective_on_perm_inverse(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let one = d.level_one();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let inj_f_ty = d.const_app(p.injective_on, &[f, n]);
    let maps_f_ty = d.const_app(p.maps_into, &[f, n]);
    let surj_f_ty = d.const_app(p.surjective_on, &[f, n]);
    let inner_f_ty = d.const_app(logic.and, &[maps_f_ty, surj_f_ty]);
    let bij_f_ty = d.const_app(logic.and, &[inj_f_ty, inner_f_ty]);
    let bij_f_fv = d.fresh_fvar();
    let bij_f = d.kernel().fvar(bij_f_fv);

    let inj_f = and_left(d, inj_f_ty, inner_f_ty, bij_f);
    let inner_f = and_right(d, inj_f_ty, inner_f_ty, bij_f);
    let maps_f = and_left(d, maps_f_ty, surj_f_ty, inner_f);
    let surj_f = and_right(d, maps_f_ty, surj_f_ty, inner_f);

    let g = d.const_app(p.perm_inverse, &[f, n]); // `permInverse f n : Nat -> Nat`.

    // --- InjectiveOn g n ---
    let inj_g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let hi_ty = d.lt(i, n);
        let hj_ty = d.lt(j, n);
        let gi = d.apply(g, &[i]);
        let gj = d.apply(g, &[j]);
        let heq_ty = d.eq(gi, gj);

        let fgi = d.apply(f, &[gi]);
        let fgj = d.apply(f, &[gj]);
        let congr_step = d.congr(gi, gj, heq, &|d, x| d.apply(f, &[x]));

        let left_eq = d.lemma(p.perm_inverse_right, &[f, n, surj_f, i, hi]); // f (g i) = i
        let right_eq = d.lemma(p.perm_inverse_right, &[f, n, surj_f, j, hj]); // f (g j) = j

        let left_sym = d.symm(fgi, i, left_eq); // i = f (g i)
        let trans1 = d.trans(fgi, fgj, j, congr_step, right_eq); // f (g i) = j
        let i_eq_j = d.trans(i, fgi, j, left_sym, trans1); // i = j

        let with_heq = d.lam_fv(heq_fv, heq_ty, i_eq_j);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // --- MapsInto g n ---
    let maps_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n);
        let zero = d.zero();
        let zero_le_k = d.lemma(p.zero_le, &[k]);
        let pos_n = d.lemma(p.lt_of_le_of_lt, &[zero, k, n, zero_le_k, hk]);
        let gk_lt_n = perm_inverse_lt_proof(d, &p, f, k, n, pos_n);
        let with_hk = d.lam_fv(hk_fv, hk_ty, gk_lt_n);
        d.lam_fv(k_fv, nat, with_hk)
    };

    // --- SurjectiveOn g n ---
    let surj_g = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n);

        let fk = d.apply(f, &[k]);
        let fk_lt_n_ty = d.lt(fk, n);
        let fk_lt_n = d.apply(maps_f, &[k, hk]);
        let g_fk_eq_k = d.lemma(p.perm_inverse_left, &[f, n, maps_f, inj_f, k, hk]);

        let target_pred = exists_predicate(d, &p, g, k, n);
        let g_fk = d.apply(g, &[fk]);
        let eq_ty = d.eq(g_fk, k);
        let and_proof = d.const_app(logic.and_intro, &[fk_lt_n_ty, eq_ty, fk_lt_n, g_fk_eq_k]);
        let intro = d.kernel().const_(logic.exists_intro, vec![one]);
        let witness = d.apply(intro, &[nat, target_pred, fk, and_proof]);

        let with_hk = d.lam_fv(hk_fv, hk_ty, witness);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let inj_g_ty = d.const_app(p.injective_on, &[g, n]);
    let maps_g_ty = d.const_app(p.maps_into, &[g, n]);
    let surj_g_ty = d.const_app(p.surjective_on, &[g, n]);
    let inner_g_ty = d.const_app(logic.and, &[maps_g_ty, surj_g_ty]);
    let bij_g_ty = d.const_app(logic.and, &[inj_g_ty, inner_g_ty]);

    let inner_g_proof = d.const_app(logic.and_intro, &[maps_g_ty, surj_g_ty, maps_g, surj_g]);
    let bij_g_proof = d.const_app(
        logic.and_intro,
        &[inj_g_ty, inner_g_ty, inj_g, inner_g_proof],
    );

    let value = {
        let with_bij_f = d.lam_fv(bij_f_fv, bij_f_ty, bij_g_proof);
        let with_f = d.lam_fv(f_fv, fn_ty, with_bij_f);
        d.lam_fv(n_fv, nat, with_f)
    };
    let ty = {
        let with_bij_f = d.arrow(bij_f_ty, bij_g_ty);
        let with_f = d.pi_fv(f_fv, fn_ty, with_bij_f);
        d.pi_fv(n_fv, nat, with_f)
    };
    d.declare_theorem(p.bijective_on_perm_inverse, ty, value)
}

/// Delta height for `Nat.EqOn`: a `Pi` over `Nat.lt` (height 1) and `Eq`
/// (a primitive-family application, not itself unfolded), so `1` matches
/// `GROUP_FN_HEIGHT` and every other bounded predicate in this file.
const EQ_ON_HEIGHT: u16 = 1;

/// Admit `Nat.EqOn (f g : Nat → Nat) (n : Nat) : Prop := ∀ i, i < n →
/// Eq Nat (f i) (g i)` — **bounded** function equality, in place of the
/// literal, unbounded `Eq (Nat → Nat) f g` this kernel cannot productively
/// use here (see this module's top-of-file doc, "The full `IsGroupOnFn`
/// instance was REFUTED"): `Nat.permInverse a n` is a two-sided inverse of
/// `a` only ON `[0,n)`, and `EqOn` is exactly the equality that statement
/// needs, no more. `EqOn` exists precisely BECAUSE this kernel has no
/// `funext` — an unbounded pointwise equality is not even a full function
/// equality here, so there is nothing weaker to fall back to; bounding it is
/// the fix, not a workaround.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_eq_on(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let bound = d.lt(i, n);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eq_fi_gi = d.eq(fi, gi);
    let body_i = d.arrow(bound, eq_fi_gi);
    let body = d.pi_fv(i_fv, nat, body_i);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_g = d.lam_fv(g_fv, fn_ty, with_n);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_g = d.arrow(fn_ty, over_n);
        d.arrow(fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.eq_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EQ_ON_HEIGHT),
    })
}

/// Admit `Nat.eqOn_refl : ∀ f n, EqOn f f n`, by `Eq.refl` at each point
/// (`EqOn f f n` unfolds to `∀ i, i<n → f i = f i`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_eq_on_refl(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();

    let fi = d.apply(f, &[i]);
    let refl_fi = d.refl(fi);

    let concl_ty = d.const_app(p.eq_on, &[f, f, n]);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, refl_fi);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_n = d.lam_fv(n_fv, nat, with_i);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, concl_ty);
        d.pi_fv(f_fv, fn_ty, with_n)
    };
    d.declare_theorem(p.eq_on_refl, ty, value)
}

/// Admit `Nat.eqOn_symm : ∀ f g n, EqOn f g n → EqOn g f n`, by [`NatOps::symm`]
/// at each point.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_eq_on_symm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_ty = d.const_app(p.eq_on, &[f, g, n]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let h_at_i = d.apply(h, &[i, hi]);
    let sym = d.symm(fi, gi, h_at_i);

    let concl_ty = d.const_app(p.eq_on, &[g, f, n]);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, sym);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_h = d.lam_fv(h_fv, h_ty, with_i);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        let with_g = d.lam_fv(g_fv, fn_ty, with_n);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let with_h = d.arrow(h_ty, concl_ty);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        let with_g = d.pi_fv(g_fv, fn_ty, with_n);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    d.declare_theorem(p.eq_on_symm, ty, value)
}

/// Admit `Nat.eqOn_trans : ∀ f g h n, EqOn f g n → EqOn g h n → EqOn f h n`,
/// by [`NatOps::trans`] at each point. The third function is bound as `k`
/// (not `h`) to keep it distinct from the two hypothesis fvars this proof
/// also needs named `h1`/`h2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_eq_on_trans(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let h1_ty = d.const_app(p.eq_on, &[f, g, n]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = d.const_app(p.eq_on, &[g, k, n]);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let ki = d.apply(k, &[i]);
    let h1_at_i = d.apply(h1, &[i, hi]);
    let h2_at_i = d.apply(h2, &[i, hi]);
    let tr = d.trans(fi, gi, ki, h1_at_i, h2_at_i);

    let concl_ty = d.const_app(p.eq_on, &[f, k, n]);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, tr);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_h2 = d.lam_fv(h2_fv, h2_ty, with_i);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_n = d.lam_fv(n_fv, nat, with_h1);
        let with_k = d.lam_fv(k_fv, fn_ty, with_n);
        let with_g = d.lam_fv(g_fv, fn_ty, with_k);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let with_h2 = d.arrow(h2_ty, concl_ty);
        let with_h1 = d.arrow(h1_ty, with_h2);
        let with_n = d.pi_fv(n_fv, nat, with_h1);
        let with_k = d.pi_fv(k_fv, fn_ty, with_n);
        let with_g = d.pi_fv(g_fv, fn_ty, with_k);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    d.declare_theorem(p.eq_on_trans, ty, value)
}

/// `Eq.{1} fn_ty x y`, for `fn_ty` the `Nat → Nat` carrier — `d.eq` is
/// hardcoded to `Eq Nat`, so every UNBOUNDED function-valued equality still
/// used in `Nat.IsGroupOnFn` (its `assoc` conjunct only — `identity`/
/// `inverse` now use [`declare_eq_on`]'s bounded `Nat.EqOn`, see this
/// module's top-of-file doc) is built directly this way, the same pattern
/// [`declare_comp_assoc`] and `helpers.rs::apply_nat_function_equality` use.
fn fn_eq(d: &mut NatDev<'_>, fn_ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = d.prelude().logic;
    let eq_const = d.kernel().const_(logic.eq, vec![one]);
    d.apply(eq_const, &[fn_ty, x, y])
}

/// `closure op n := ∀ a b, BijectiveOn a n → BijectiveOn b n →
/// BijectiveOn (op a b) n` — `Nat.IsGroupOnFn`'s closure conjunct, the
/// function-valued analogue of `group.rs::closure_prop`'s `a<n → b<n →
/// op a b<n` with `BijectiveOn · n` standing in for `· < n` as carrier
/// membership.
fn closure_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ab = d.apply(op, &[a, b]);
    let concl = d.const_app(p.bijective_on, &[ab, n]);
    let bij_b = d.const_app(p.bijective_on, &[b, n]);
    let step_b = d.arrow(bij_b, concl);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, step_b);
    let with_b = d.pi_fv(b_fv, fn_ty, inner);
    d.pi_fv(a_fv, fn_ty, with_b)
}

/// `assoc op n := ∀ a b c, BijectiveOn a n → BijectiveOn b n →
/// BijectiveOn c n → op (op a b) c = op a (op b c)`.
fn assoc_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let ab = d.apply(op, &[a, b]);
    let ab_c = d.apply(op, &[ab, c]);
    let bc = d.apply(op, &[b, c]);
    let a_bc = d.apply(op, &[a, bc]);
    let concl = fn_eq(d, fn_ty, ab_c, a_bc);
    let bij_c = d.const_app(p.bijective_on, &[c, n]);
    let step_c = d.arrow(bij_c, concl);
    let bij_b = d.const_app(p.bijective_on, &[b, n]);
    let step_b = d.arrow(bij_b, step_c);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, step_b);
    let with_c = d.pi_fv(c_fv, fn_ty, inner);
    let with_b = d.pi_fv(b_fv, fn_ty, with_c);
    d.pi_fv(a_fv, fn_ty, with_b)
}

/// `BijectiveOn e n`, the bound half of `identity`.
fn identity_bound_prop_fn(d: &mut NatDev<'_>, p: &NatPrelude, e: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.bijective_on, &[e, n])
}

/// `∀ a, BijectiveOn a n → (op a e = a ∧ op e a = a)`, the quantified half
/// of `identity`.
fn identity_forall_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ae = d.apply(op, &[a, e]);
    let ea = d.apply(op, &[e, a]);
    let left_eq = d.const_app(p.eq_on, &[ae, a, n]);
    let right_eq = d.const_app(p.eq_on, &[ea, a, n]);
    let both = d.const_app(logic.and, &[left_eq, right_eq]);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, both);
    d.pi_fv(a_fv, fn_ty, inner)
}

/// `identity op e n := BijectiveOn e n ∧ (∀ a, BijectiveOn a n → op a e=a
/// ∧ op e a=a)`.
fn identity_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    n: ExprId,
) -> ExprId {
    let logic = p.logic;
    let bound = identity_bound_prop_fn(d, p, e, n);
    let forall_part = identity_forall_prop_fn(d, p, fn_ty, op, e, n);
    d.const_app(logic.and, &[bound, forall_part])
}

/// `inverse op e inv n := ∀ a, BijectiveOn a n → BijectiveOn (inv a) n ∧
/// (op a (inv a)=e ∧ op (inv a) a=e)`.
fn inverse_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    inv: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ia = d.apply(inv, &[a]);
    let ia_bij = d.const_app(p.bijective_on, &[ia, n]);
    let a_ia = d.apply(op, &[a, ia]);
    let ia_a = d.apply(op, &[ia, a]);
    let left_eq = d.const_app(p.eq_on, &[a_ia, e, n]);
    let right_eq = d.const_app(p.eq_on, &[ia_a, e, n]);
    let eqs = d.const_app(logic.and, &[left_eq, right_eq]);
    let bundle = d.const_app(logic.and, &[ia_bij, eqs]);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, bundle);
    d.pi_fv(a_fv, fn_ty, inner)
}

/// Admit `Nat.IsGroupOnFn (op : (Nat→Nat)→(Nat→Nat)→(Nat→Nat)) (e : Nat→Nat)
/// (inv : (Nat→Nat)→(Nat→Nat)) (n : Nat) : Prop := closure ∧ (associativity
/// ∧ (identity ∧ inverse))` — the representation-(a) generalisation of
/// `group.rs::IsGroupOn` this file's module doc argues for: the same four
/// conjuncts, `Nat → Nat`-valued elements in place of bare `Nat`s, and
/// `BijectiveOn · n` in place of `· < n` as carrier membership (the natural
/// "is a permutation of `[0,n)`" predicate, already proved equivalent to
/// `InjectiveOn ∧ MapsInto` by `relation.rs::bijective_of_injective_on`).
///
/// **Fixed, not merely restated.** An earlier version of this predicate
/// stated `identity`/`inverse` with literal, UNBOUNDED `Eq (Nat → Nat) _ _`
/// (via [`fn_eq`]), and was unsatisfiable at the symmetric group: this
/// kernel's own module doc found the counterexample and refused to paper
/// over it (see this module's top-of-file doc, "The full `IsGroupOnFn`
/// instance was REFUTED", for the derivation this predicate's shape had to
/// change to survive). `identity`/`inverse` now use
/// [`declare_eq_on`]'s bounded `Nat.EqOn f g n := ∀ i, i<n → f i = g i` in
/// place of `Eq (Nat → Nat) f g` — the same restriction `BijectiveOn · n`
/// already applies to a function's *behaviour*, now applied to the
/// equalities that behaviour must satisfy. `assoc` is left at the unbounded
/// `fn_eq`: `Nat.comp_assoc` proves the genuinely unbounded form by
/// `Eq.refl`, so bounding it would only weaken a true statement.
/// `Nat.comp`/`Nat.id`/`Nat.comp_assoc` supply the closure and associativity
/// conjuncts (closure needs [`declare_bijective_on_comp`]'s
/// `Nat.bijective_on_comp`, landed alongside this predicate), and
/// [`declare_symmetric_group_is_group_on_fn`] is the instance this fix
/// exists for.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_group_on_fn(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();
    let unop_ty = d.arrow(fn_ty, fn_ty);
    let binop_ty = d.arrow(fn_ty, unop_ty);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let closure = closure_prop_fn(d, &p, fn_ty, op, n);
    let assoc = assoc_prop_fn(d, &p, fn_ty, op, n);
    let identity = identity_prop_fn(d, &p, fn_ty, op, e, n);
    let inverse = inverse_prop_fn(d, &p, fn_ty, op, e, inv, n);

    let logic = p.logic;
    let id_inv = d.const_app(logic.and, &[identity, inverse]);
    let assoc_rest = d.const_app(logic.and, &[assoc, id_inv]);
    let body = d.const_app(logic.and, &[closure, assoc_rest]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_inv = d.lam_fv(inv_fv, unop_ty, with_n);
        let with_e = d.lam_fv(e_fv, fn_ty, with_inv);
        d.lam_fv(op_fv, binop_ty, with_e)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_inv = d.arrow(unop_ty, over_n);
        let over_e = d.arrow(fn_ty, over_inv);
        d.arrow(binop_ty, over_e)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_group_on_fn,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GROUP_FN_HEIGHT),
    })
}

/// `BijectiveOn Nat.id n`, for a fixed `n : Nat` — needed as the bound half
/// of [`declare_symmetric_group_is_group_on_fn`]'s identity conjunct.
/// `Nat.id`'s three components each close with no induction: `id i` is
/// definitionally `i`, so `InjectiveOn`'s hypothesis literally IS its own
/// conclusion once `id` is unfolded, `MapsInto`'s hypothesis literally IS
/// its conclusion, and `SurjectiveOn`'s witness for `k` is `k` itself
/// (reusing [`exists_predicate`]'s own `∃ i, i<n ∧ f i = k` shape at
/// `f := id`).
fn bijective_on_id_proof(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let logic = p.logic;
    let one = d.level_one();
    let id = d.const_app(p.id, &[]);

    // InjectiveOn id n := ∀ i j, i<n → j<n → id i = id j → i = j.
    let inj_ty = d.const_app(p.injective_on, &[id, n]);
    let inj_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, n);
        let hj_fv = d.fresh_fvar();
        let hj_ty = d.lt(j, n);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let idi = d.apply(id, &[i]);
        let idj = d.apply(id, &[j]);
        let heq_ty = d.eq(idi, idj);
        let with_heq = d.lam_fv(heq_fv, heq_ty, heq);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // MapsInto id n := ∀ i, i<n → id i<n.
    let maps_ty = d.const_app(p.maps_into, &[id, n]);
    let maps_proof = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, n);
        let with_hi = d.lam_fv(hi_fv, hi_ty, hi);
        d.lam_fv(i_fv, nat, with_hi)
    };

    // SurjectiveOn id n := ∀ k, k<n → ∃ i, i<n ∧ id i = k. Witness i := k.
    let surj_ty = d.const_app(p.surjective_on, &[id, n]);
    let surj_proof = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n);
        let idk = d.apply(id, &[k]);
        let eq_ty = d.eq(idk, k);
        let refl_k = d.refl(k);
        let pred = exists_predicate(d, &p, id, k, n);
        let and_proof = d.const_app(logic.and_intro, &[hk_ty, eq_ty, hk, refl_k]);
        let intro = d.kernel().const_(logic.exists_intro, vec![one]);
        let witness = d.apply(intro, &[nat, pred, k, and_proof]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, witness);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let inner_ty = d.const_app(logic.and, &[maps_ty, surj_ty]);
    let inner_proof = d.const_app(logic.and_intro, &[maps_ty, surj_ty, maps_proof, surj_proof]);
    d.const_app(logic.and_intro, &[inj_ty, inner_ty, inj_proof, inner_proof])
}

/// Admit `Nat.symmetric_group_isGroupOnFn : ∀ n, IsGroupOnFn Nat.comp Nat.id
/// (fun f => Nat.permInverse f n) n` — the symmetric group on `[0,n)`,
/// permutations under composition, as an actual instance of `Nat.IsGroupOnFn`
/// (see this module's top-of-file doc, and [`declare_is_group_on_fn`]'s own
/// doc, for why the predicate's earlier unbounded form could never reach
/// this).
///
/// - **Closure** is [`declare_bijective_on_comp`]'s `Nat.bijective_on_comp`,
///   applied directly: `Nat.bijective_on_comp n` already has exactly the
///   closure conjunct's type.
/// - **Associativity** is `Nat.comp_assoc`, ignoring the (unneeded)
///   bijectivity hypotheses.
/// - **Identity**'s bound half is [`bijective_on_id_proof`]; its forall half
///   needs no case split — `comp a id i` and `comp id a i` both delta/beta-
///   reduce to `a i` (through `comp`'s definition and then `id`'s), so
///   `Eq.refl Nat (a i)` proves BOTH `EqOn (comp a id) a n` and
///   `EqOn (comp id a) a n` at every point.
/// - **Inverse**'s bijectivity half is `Nat.bijective_on_perm_inverse`; its
///   two `EqOn` equalities are exactly `Nat.permInverse_right`/`_left`'s
///   conclusions once `comp _ _ k` and `id k` are unfolded — the whole
///   reason this predicate needed `EqOn` rather than `Eq (Nat → Nat)`:
///   `permInverse_right`/`_left` only ever promised the equality ON `[0,n)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** the proof, not that a script gave up.
fn declare_symmetric_group_is_group_on_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let logic = p.logic;

    d.theorem(p.symmetric_group_is_group_on_fn, 1, &|d, values| {
        let n = values[0];

        let op = d.const_app(p.comp, &[]);
        let e = d.const_app(p.id, &[]);
        let inv = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let body = d.const_app(p.perm_inverse, &[f, n]);
            d.lam_fv(f_fv, fn_ty, body)
        };

        let closure_ty = closure_prop_fn(d, &p, fn_ty, op, n);
        let assoc_ty = assoc_prop_fn(d, &p, fn_ty, op, n);
        let identity_ty = identity_prop_fn(d, &p, fn_ty, op, e, n);
        let inverse_ty = inverse_prop_fn(d, &p, fn_ty, op, e, inv, n);

        // --- closure: Nat.bijective_on_comp, partially applied at n. ---
        let closure_proof = d.const_app(p.bijective_on_comp, &[n]);

        // --- associativity: Nat.comp_assoc, ignoring the bijectivity hyps. ---
        let assoc_proof = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let bij_a_fv = d.fresh_fvar();
            let bij_b_fv = d.fresh_fvar();
            let bij_c_fv = d.fresh_fvar();
            let body = d.lemma(p.comp_assoc, &[a, b, c]);
            let bij_c_ty = d.const_app(p.bijective_on, &[c, n]);
            let bij_b_ty = d.const_app(p.bijective_on, &[b, n]);
            let bij_a_ty = d.const_app(p.bijective_on, &[a, n]);
            let with_bc = d.lam_fv(bij_c_fv, bij_c_ty, body);
            let with_bb = d.lam_fv(bij_b_fv, bij_b_ty, with_bc);
            let with_ba = d.lam_fv(bij_a_fv, bij_a_ty, with_bb);
            let with_c = d.lam_fv(c_fv, fn_ty, with_ba);
            let with_b = d.lam_fv(b_fv, fn_ty, with_c);
            d.lam_fv(a_fv, fn_ty, with_b)
        };

        // --- identity: BijectiveOn id n ∧ (∀a, BijectiveOn a n →
        //     EqOn(comp a id) a n ∧ EqOn(comp id a) a n), both by Eq.refl. ---
        let identity_proof = {
            let bound_ty = identity_bound_prop_fn(d, &p, e, n);
            let bound_proof = bijective_on_id_proof(d, &p, n);
            let forall_ty = identity_forall_prop_fn(d, &p, fn_ty, op, e, n);
            let forall_proof = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let bij_a_fv = d.fresh_fvar();
                let bij_a_ty = d.const_app(p.bijective_on, &[a, n]);

                let ae = d.apply(op, &[a, e]);
                let ea = d.apply(op, &[e, a]);
                let left_ty = d.const_app(p.eq_on, &[ae, a, n]);
                let right_ty = d.const_app(p.eq_on, &[ea, a, n]);

                let left_proof = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_fv = d.fresh_fvar();
                    let hi_ty = d.lt(i, n);
                    let ai = d.apply(a, &[i]);
                    let refl_ai = d.refl(ai);
                    let with_hi = d.lam_fv(hi_fv, hi_ty, refl_ai);
                    d.lam_fv(i_fv, nat, with_hi)
                };
                let right_proof = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_fv = d.fresh_fvar();
                    let hi_ty = d.lt(i, n);
                    let ai = d.apply(a, &[i]);
                    let refl_ai = d.refl(ai);
                    let with_hi = d.lam_fv(hi_fv, hi_ty, refl_ai);
                    d.lam_fv(i_fv, nat, with_hi)
                };
                let both = d.const_app(
                    logic.and_intro,
                    &[left_ty, right_ty, left_proof, right_proof],
                );
                let with_bij = d.lam_fv(bij_a_fv, bij_a_ty, both);
                d.lam_fv(a_fv, fn_ty, with_bij)
            };
            d.const_app(
                logic.and_intro,
                &[bound_ty, forall_ty, bound_proof, forall_proof],
            )
        };

        // --- inverse: ∀a, BijectiveOn a n → BijectiveOn(permInverse a n)n ∧
        //     (EqOn(comp a (permInverse a n)) id n ∧
        //      EqOn(comp (permInverse a n) a) id n). ---
        let inverse_proof = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let bij_a_fv = d.fresh_fvar();
            let bij_a = d.kernel().fvar(bij_a_fv);
            let bij_a_ty = d.const_app(p.bijective_on, &[a, n]);

            let inj_a_ty = d.const_app(p.injective_on, &[a, n]);
            let maps_a_ty = d.const_app(p.maps_into, &[a, n]);
            let surj_a_ty = d.const_app(p.surjective_on, &[a, n]);
            let inner_a_ty = d.const_app(logic.and, &[maps_a_ty, surj_a_ty]);
            let inj_a = and_left(d, inj_a_ty, inner_a_ty, bij_a);
            let inner_a = and_right(d, inj_a_ty, inner_a_ty, bij_a);
            let maps_a = and_left(d, maps_a_ty, surj_a_ty, inner_a);
            let surj_a = and_right(d, maps_a_ty, surj_a_ty, inner_a);

            let ia = d.apply(inv, &[a]);
            let ia_bij_ty = d.const_app(p.bijective_on, &[ia, n]);
            let ia_bij_proof = d.lemma(p.bijective_on_perm_inverse, &[n, a, bij_a]);

            let a_ia = d.apply(op, &[a, ia]);
            let ia_a = d.apply(op, &[ia, a]);
            let left_ty = d.const_app(p.eq_on, &[a_ia, e, n]);
            let right_ty = d.const_app(p.eq_on, &[ia_a, e, n]);

            let left_proof = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = d.lt(k, n);
                let body = d.lemma(p.perm_inverse_right, &[a, n, surj_a, k, hk]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, body);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let right_proof = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = d.lt(k, n);
                let body = d.lemma(p.perm_inverse_left, &[a, n, maps_a, inj_a, k, hk]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, body);
                d.lam_fv(k_fv, nat, with_hk)
            };

            let eqs_ty = d.const_app(logic.and, &[left_ty, right_ty]);
            let eqs = d.const_app(
                logic.and_intro,
                &[left_ty, right_ty, left_proof, right_proof],
            );
            let bundle = d.const_app(logic.and_intro, &[ia_bij_ty, eqs_ty, ia_bij_proof, eqs]);
            let with_bij_a = d.lam_fv(bij_a_fv, bij_a_ty, bundle);
            d.lam_fv(a_fv, fn_ty, with_bij_a)
        };

        let id_inv = d.const_app(
            logic.and_intro,
            &[identity_ty, inverse_ty, identity_proof, inverse_proof],
        );
        let assoc_rest_ty = d.const_app(logic.and, &[identity_ty, inverse_ty]);
        let assoc_rest = d.const_app(
            logic.and_intro,
            &[assoc_ty, assoc_rest_ty, assoc_proof, id_inv],
        );
        let rest_ty = d.const_app(logic.and, &[assoc_ty, assoc_rest_ty]);
        let full = d.const_app(
            logic.and_intro,
            &[closure_ty, rest_ty, closure_proof, assoc_rest],
        );

        let stmt = d.const_app(p.is_group_on_fn, &[op, e, inv, n]);
        (stmt, full)
    })?;
    Ok(())
}

/// Admit `Nat.permInverse`, its two two-sided-inverse theorems, `Nat.id`,
/// `Nat.comp_assoc`, `Nat.EqOn` (plus reflexivity/symmetry/transitivity),
/// `Nat.IsGroupOnFn`, and the symmetric group instance
/// `Nat.symmetric_group_isGroupOnFn`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_permutation_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_perm_inverse(d, p)?;
    declare_perm_inverse_right(d, p)?;
    declare_perm_inverse_left(d, p)?;
    declare_id(d, p)?;
    declare_comp_assoc(d, p)?;
    declare_eq_on(d, p)?;
    declare_eq_on_refl(d, p)?;
    declare_eq_on_symm(d, p)?;
    declare_eq_on_trans(d, p)?;
    declare_is_group_on_fn(d, p)?;
    declare_bijective_on_comp(d, p)?;
    declare_bijective_on_perm_inverse(d, p)?;
    declare_symmetric_group_is_group_on_fn(d, p)?;
    Ok(())
}
