//! `cardinality.rs` — curriculum node
//! [`cardinality`](../../../../docs/curriculum/00-foundations/cardinality.md),
//! Layer 0, `lean-horizon`. That doc is honest that the *heart* of the
//! subject — countability of ℚ, Cantor's uncountability of ℝ,
//! Schröder–Bernstein, cardinal arithmetic — needs a genuine set type and
//! injections between arbitrary types, neither of which this kernel has, and
//! says so under its own "Lean-horizon" heading. What the doc's own "Testable
//! in axeyum" section *does* claim is narrower and finite: "The pigeonhole
//! principle for fixed sizes (no injection from an `n+1`-set into an `n`-set)
//! is a finite, checkable statement." This file lands exactly that statement,
//! generalized from `n+1` to any `m` with `n < m`.
//!
//! ## `Nat.pigeonhole`
//!
//! [`super::finite::declare_injective_surjective`]'s
//! `Nat.injective_on_imp_surjective_on : ∀ n f, InjectiveOn f n →
//! MapsInto f n → SurjectiveOn f n` is **not** this pigeonhole, and the
//! difference is exactly the one bound vs. two: it is a statement about a
//! *self-map* — `MapsInto f n` requires the codomain bound to be the SAME `n`
//! as the domain bound. The pigeonhole principle this curriculum node and the
//! Layer-2 `counting` node actually want crosses two bounds — an injection
//! from `[0, m)` INTO `[0, n)` with `n < m` is impossible — and no existing
//! declaration in `finite.rs`, `finite_set.rs`, or `relation.rs` states that.
//!
//! [`declare_nat_pigeonhole`] builds it as a short **reduction to the
//! self-map lemma**, not a fresh induction: given `f`, `Lt n m`, `∀ i, i < m →
//! f i < n` (the two-bound "maps into", stated inline as a bare `Prop`
//! rather than as a new named `Definition` — nothing else needs to refer to
//! it, and `finite.rs` is off-limits to edit for this file's task, so it is
//! not registered as `Nat.mapsIntoBound` or similar), and `InjectiveOn f m`:
//!
//! 1. **Widen the codomain bound from `n` to `m`.** Since `f i < n` and
//!    `n < m`, transitivity (`f i < n`, i.e. `Le (succ (f i)) n`, chained
//!    through `Le n m` — itself `le_trans n (succ n) m (le_succ n) hnm`,
//!    since `Lt n m` unfolds to `Le (succ n) m`) gives `Le (succ (f i)) m`,
//!    i.e. `f i < m`. So `f` is `MapsInto f m`, a genuine **self**-map on `m`.
//! 2. **Apply the self-map lemma** at `m`: `InjectiveOn f m → MapsInto f m →
//!    SurjectiveOn f m`.
//! 3. **Instantiate surjectivity at the target `n`** (valid since `n < m`):
//!    `∃ i, i < m ∧ f i = n`.
//! 4. **Contradiction.** For the witness `i`, `f i < n` (from the two-bound
//!    hypothesis) and `f i = n` (from step 3) together transport `f i < n`
//!    along the equality to `Lt n n`, refuted by `lt_irrefl`.
//!
//! No induction is needed because the self-map pigeonhole already IS the
//! induction; this is packaging, the same relationship
//! `bijective_of_injective_on` (`relation.rs`) has to it. `Exists.rec`
//! eliminates into `False` — a `Prop` — which is the one target it is
//! constructively allowed to reach into (see this prelude's standing
//! constraint: no computable witness extraction from an existential).
//!
//! ## Status
//!
//! `Nat.pigeonhole` is declared here and axiom-free: it composes
//! `Nat.injective_on_imp_surjective_on`, `Nat.le_trans`, `Nat.le_succ`, and
//! `Nat.lt_irrefl` — all already axiom-free in the constructed `nat` prelude
//! — through the kernel's trusted `add_declaration` gate, which re-checks the
//! proof term against the stated type.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;

/// Declare `Nat.pigeonhole : ∀ n m f, Lt n m → (∀ i, i < m → f i < n) →
/// InjectiveOn f m → False` — see the module doc for the four-step reduction
/// to [`super::finite::declare_injective_surjective`]'s
/// `Nat.injective_on_imp_surjective_on`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_nat_pigeonhole(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pigeonhole, 2, &|d, values| {
        let n = values[0];
        let m = values[1];
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let logic = p.logic;
        let one = d.level_one();
        let anon = d.anon_name();

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let hnm_ty = d.lt(n, m);
        let hnm_fv = d.fresh_fvar();
        let hnm = d.kernel().fvar(hnm_fv);

        // The two-bound "maps into": `∀ i, i < m → f i < n`, inline — not a
        // new named `Definition` (see module doc).
        let hmaps_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, m);
            let fi = d.apply(f, &[i]);
            let concl = d.lt(fi, n);
            let inner = d.arrow(bound, concl);
            d.pi_fv(i_fv, nat, inner)
        };
        let hmaps_fv = d.fresh_fvar();
        let hmaps = d.kernel().fvar(hmaps_fv);

        let hinj_ty = d.const_app(p.injective_on, &[f, m]);
        let hinj_fv = d.fresh_fvar();
        let hinj = d.kernel().fvar(hinj_fv);

        let false_ty = d.kernel().const_(logic.false_, vec![]);

        // --- Step 1: f is a self-map on m (f i < n < m, so f i < m). ---
        let maps_self = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let hi_ty = d.lt(i, m);

            let fi = d.apply(f, &[i]);
            let hfi_lt_n = d.apply(hmaps, &[i, hi]); // Lt (f i) n

            let succ_n = d.succ(n);
            let le_succ_n = d.lemma(p.le_succ, &[n]); // Le n (succ n)
            let le_n_m = d.lemma(p.le_trans, &[n, succ_n, m, le_succ_n, hnm]); // Le n m

            let succ_fi = d.succ(fi);
            // Le (succ (f i)) n [= hfi_lt_n, unfolding Lt] chained with
            // Le n m gives Le (succ (f i)) m, i.e. Lt (f i) m.
            let fi_lt_m = d.lemma(p.le_trans, &[succ_fi, n, m, hfi_lt_n, le_n_m]);

            let with_hi = d.lam_fv(hi_fv, hi_ty, fi_lt_m);
            d.lam_fv(i_fv, nat, with_hi)
        };

        // --- Step 2: the self-map pigeonhole gives surjectivity on m. ---
        let surj = d.const_app(p.injective_on_imp_surjective_on, &[m, f, hinj, maps_self]);

        // --- Step 3: instantiate surjectivity at k := n (valid: n < m). ---
        let ex = d.apply(surj, &[n, hnm]); // Exists i, i < m ∧ f i = n

        // --- Step 4: the witness contradicts f i < n. ---
        let source_predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, m);
            let fi = d.apply(f, &[i]);
            let eqn = d.eq(fi, n);
            let body = d.const_app(logic.and, &[bound, eqn]);
            d.lam_fv(i_fv, nat, body)
        };
        let source_ty = {
            let e = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(e, &[nat, source_predicate])
        };
        let motive = d
            .kernel()
            .lam(anon, source_ty, false_ty, BinderInfo::Default);

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let bound_ty = d.lt(i, m);
            let fi = d.apply(f, &[i]);
            let eqn_ty = d.eq(fi, n);
            let hand_ty = d.const_app(logic.and, &[bound_ty, eqn_ty]);

            let hi = and_left(d, bound_ty, eqn_ty, hand);
            let heq = and_right(d, bound_ty, eqn_ty, hand); // Eq (f i) n

            let hfi_lt_n = d.apply(hmaps, &[i, hi]); // Lt (f i) n
            let n_lt_n = {
                let transport_motive = d.eq_motive(fi, &|d, x| d.lt(x, n));
                d.transport(fi, transport_motive, hfi_lt_n, n, heq)
            };
            let false_val = d.lemma(p.lt_irrefl, &[n, n_lt_n]);

            let with_hand = d.lam_fv(hand_fv, hand_ty, false_val);
            d.lam_fv(i_fv, nat, with_hand)
        };

        let exists_rec = d.kernel().const_(logic.exists_rec, vec![one]);
        let contradiction = d.apply(exists_rec, &[nat, source_predicate, motive, minor, ex]);

        // ∀ f, Lt n m → (∀ i, i < m → f i < n) → InjectiveOn f m → False
        let stmt = {
            let inner3 = d.arrow(hinj_ty, false_ty);
            let inner2 = d.arrow(hmaps_ty, inner3);
            let inner1 = d.arrow(hnm_ty, inner2);
            d.pi_fv(f_fv, fn_ty, inner1)
        };
        let value = {
            let with_hinj = d.lam_fv(hinj_fv, hinj_ty, contradiction);
            let with_hmaps = d.lam_fv(hmaps_fv, hmaps_ty, with_hinj);
            let with_hnm = d.lam_fv(hnm_fv, hnm_ty, with_hmaps);
            d.lam_fv(f_fv, fn_ty, with_hnm)
        };
        (stmt, value)
    })?;
    Ok(())
}
