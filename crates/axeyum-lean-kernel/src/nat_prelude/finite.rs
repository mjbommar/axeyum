//! `Nat.Fin` — the canonical finite index type `{0, …, n-1}` — and
//! `Nat.injectiveOn`/`Nat.surjectiveOn`/`Nat.mapsInto`, the notions the finite
//! pigeonhole principle is stated with.
//!
//! ## Representation
//!
//! `Fin` is the **subtype form**: `⟨val : Nat, isLt : val < n⟩`, declared as a
//! one-constructor inductive exactly the way `CReal` carries its `seq` and
//! `regular` fields (`creal.rs::declare_carrier`/`declare_projections`): a
//! `Type 0`-valued family with a data field (`val`) and a dependent `Prop`
//! field over it (`isLt`), both projected out through the kernel-generated
//! recursor rather than declared as primitives. The one structural difference
//! from `CReal` is that `Fin` is a genuine one-*parameter* family — `n : Nat`
//! is a parameter shared by the family and its constructor, the same shape
//! `inductive_tests.rs::prod_two_params_one_ctor`'s `Prod α β` uses for its
//! two type parameters, just with a single `Nat`-sorted one here.
//!
//! The subtype form was chosen over an `fz`/`fs` (zero/successor) inductive —
//! Lean's own history has used both — because this development's finite-index
//! reasoning is stated directly over **bounded `Nat` quantifiers**
//! (`∀ i, i < n → …`, as `InjectiveOn`/`SurjectiveOn`/`MapsInto` below all are),
//! never over functions `Fin n → X`. `Fin.val` therefore only ever needs to
//! *compose* with the existing `Nat`-indexed folds (`Int.prodRange`,
//! `Nat.sumRange`) and their bound hypotheses, and the subtype form gives that
//! for free — `Fin.val` IS a `Nat`, with a separately-carried bound proof — with
//! no re-indexing step. An `fz`/`fs` inductive would make induction on `Fin n`
//! itself more direct, but nothing here inducts on `Fin n`; every proof below
//! inducts on the bounding `Nat`, so that advantage does not apply.
//!
//! ## `InjectiveOn` / `SurjectiveOn` / `MapsInto`
//!
//! These are stated directly over plain `Nat → Nat` functions, **not** over
//! `Fin n → Fin n` — no new type is needed for a bounded quantifier, and a
//! `Fin`-based formulation would force every consumer through `Fin.mk`'s bound
//! obligation for no gain here. `MapsInto` is the "self-map" hypothesis the
//! pigeonhole principle needs and the brief's plain-prose statement elides: an
//! injective function into a *larger* codomain need not be surjective onto a
//! smaller one, so `injective_on_imp_surjective_on` (when it lands) must carry
//! it as an explicit premise.
//!
//! ## Status
//!
//! `Fin`, the three definitions, and the pigeonhole theorem
//! `Nat.injective_on_imp_surjective_on` are all declared here and
//! axiom-free — see the route note above [`declare_pigeonhole`] for how the
//! induction closes.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Fin n`, i.e. `Nat.Fin` applied to the index bound `n`.
fn fin_ty(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let fin = d.prelude().fin;
    d.const_app(fin, &[n])
}

/// Declare the `Nat.Fin` family: the inductive itself, its two projections
/// (`val`, `isLt`), and `Fin.mk`'s defining equation on `val`.
///
/// # Errors
///
/// Returns the kernel's rejection if any generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_fin(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // Fin : Nat → Type 0.
    let family_ty = d.arrow(nat, type0);

    // mk : Π (n val : Nat), Lt val n → Fin n.
    let mk_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let val_fv = d.fresh_fvar();
        let val = d.kernel().fvar(val_fv);
        let concl = fin_ty(d, n);
        let bound = d.lt(val, n);
        let with_bound = d.arrow(bound, concl);
        let with_val = d.pi_fv(val_fv, nat, with_bound);
        d.pi_fv(n_fv, nat, with_val)
    };
    d.kernel()
        .add_inductive(p.fin, &[], 1, family_ty, &[(p.fin_mk, mk_ty)])?;

    // val : Π (n : Nat), Fin n → Nat
    //     := fun n x => Fin.rec.{1} n (fun _ => Nat) (fun val _ => val) x.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fin_n = fin_ty(d, n);
        let motive = d.kernel().lam(anon, fin_n, nat, BinderInfo::Default);
        let minor = {
            let val_fv = d.fresh_fvar();
            let val = d.kernel().fvar(val_fv);
            let h_fv = d.fresh_fvar();
            let bound = d.lt(val, n);
            let inner = d.lam_fv(h_fv, bound, val);
            d.lam_fv(val_fv, nat, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let rec = d.kernel().const_(p.fin_rec, vec![one]);
        let body = d.apply(rec, &[n, motive, minor, x]);
        let value = {
            let with_x = d.lam_fv(x_fv, fin_n, body);
            d.lam_fv(n_fv, nat, with_x)
        };
        let ty = {
            let over_x = d.arrow(fin_n, nat);
            d.pi_fv(n_fv, nat, over_x)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.fin_val,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // isLt : Π (n : Nat) (x : Fin n), Lt (val n x) n
    //      := fun n x => Fin.rec.{0} n (fun y => Lt (val n y) n) (fun val h => h) x.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fin_n = fin_ty(d, n);
        let claim = |d: &mut NatDev<'_>, y: ExprId| {
            let val_y = d.const_app(p.fin_val, &[n, y]);
            d.lt(val_y, n)
        };
        let motive = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = claim(d, y);
            d.lam_fv(y_fv, fin_n, body)
        };
        let minor = {
            let val_fv = d.fresh_fvar();
            let val = d.kernel().fvar(val_fv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let bound = d.lt(val, n);
            let inner = d.lam_fv(h_fv, bound, h);
            d.lam_fv(val_fv, nat, inner)
        };
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero_level = d.kernel().level_zero();
        let rec = d.kernel().const_(p.fin_rec, vec![zero_level]);
        let body = d.apply(rec, &[n, motive, minor, x]);
        let value = {
            let with_x = d.lam_fv(x_fv, fin_n, body);
            d.lam_fv(n_fv, nat, with_x)
        };
        let ty = {
            let inner = claim(d, x);
            let with_x = d.pi_fv(x_fv, fin_n, inner);
            d.pi_fv(n_fv, nat, with_x)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.fin_is_lt,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // val_mk : ∀ (n val : Nat) (h : Lt val n), Eq Nat (val n (mk n val h)) val.
    // Closes by `Eq.refl val`: the recursor ι-reduces on the literal
    // constructor `mk n val h`, exactly as `Int.factorial_zero`/`_succ`
    // (`wilson.rs`) close over `Int.prodRange`'s own `Nat.rec` minors.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let val_fv = d.fresh_fvar();
        let val = d.kernel().fvar(val_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bound = d.lt(val, n);
        let mk_nvh = d.const_app(p.fin_mk, &[n, val, h]);
        let lhs = d.const_app(p.fin_val, &[n, mk_nvh]);
        let stmt = d.eq(lhs, val);
        let proof = d.refl(val);
        let ty = {
            let with_h = d.pi_fv(h_fv, bound, stmt);
            let with_val = d.pi_fv(val_fv, nat, with_h);
            d.pi_fv(n_fv, nat, with_val)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, bound, proof);
            let with_val = d.lam_fv(val_fv, nat, with_h);
            d.lam_fv(n_fv, nat, with_val)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.fin_val_mk,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

/// Declare `Nat.injectiveOn`, `Nat.surjectiveOn`, and `Nat.mapsInto` — plain
/// `Prop`-valued definitions over `Nat → Nat` functions, no `Fin` needed (see
/// the module doc).
///
/// # Errors
///
/// Returns the kernel's rejection if any generated definition does not
/// type-check or a name is already taken.
pub(super) fn declare_injective_surjective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    // injectiveOn f n := ∀ i j, i < n → j < n → f i = f j → i = j.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let concl = d.eq(i, j);
        let hyp_eq = d.eq(fi, fj);
        let step_eq = d.arrow(hyp_eq, concl);
        let hyp_j = d.lt(j, n);
        let step_j = d.arrow(hyp_j, step_eq);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_j);
        let body = {
            let with_j = d.pi_fv(j_fv, nat, inner);
            d.pi_fv(i_fv, nat, with_j)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.injective_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // surjectiveOn f n := ∀ k, k < n → ∃ i, i < n ∧ f i = k.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let one = d.level_one();
        let logic = d.prelude().logic;
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, n);
            let fi = d.apply(f, &[i]);
            let eqk = d.eq(fi, k);
            let body = d.const_app(logic.and, &[bound, eqk]);
            d.lam_fv(i_fv, nat, body)
        };
        let exists_ty = {
            let e = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(e, &[nat, predicate])
        };
        let hyp_k = d.lt(k, n);
        let inner = d.arrow(hyp_k, exists_ty);
        let body = d.pi_fv(k_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.surjective_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // mapsInto f n := ∀ i, i < n → f i < n.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);

        let hyp = d.lt(i, n);
        let fi = d.apply(f, &[i]);
        let concl = d.lt(fi, n);
        let inner = d.arrow(hyp, concl);
        let body = d.pi_fv(i_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.maps_into,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The pigeonhole principle: `Nat.injective_on_imp_surjective_on`
// ---------------------------------------------------------------------------
//
// `MapsInto f n → InjectiveOn f n → SurjectiveOn f n`, by induction on `n`
// generalized over `f` (the recursive call below is applied to a *different*
// function `g`, not the original `f`, so the induction hypothesis must be
// `∀ f, …` rather than fixed at one `f`). Base `n = 0` is vacuous
// (`Nat.not_lt_zero`). Step `n = succ m`: let `c := f m` (so `c ≤ m`, from
// `MapsInto`). Define the order-based "compaction"
//
//     compact(x) := if Nat.ble x c then x else Nat.pred x        -- Nat → Nat
//
// via `bool_select_nat`, and `g(i) := compact(f i)`. `MapsInto g m` and
// `InjectiveOn g m` both hold (`compact` is injective on `{x ≤ m : x ≠ c}` —
// identity below `c`, `pred` above it), giving `SurjectiveOn g m` by the
// induction hypothesis. Recovering `f i = k` for an arbitrary `k < succ m`
// case-splits `k` against `c` the same way (`Nat.lt_or_eq_of_le` twice, via
// the `trichotomy` helper below): `k = c` is witnessed by `m` directly
// (`f m = c` by definition); otherwise apply the `g`-surjectivity fact at
// `compact(k)` and recover `f i = k` from `compact(f i) = compact(k)` via
// `compact`'s own injectivity (`compact_injective` below) — the general
// "right inverse" step the previous slice stalled on, closed not by building
// `uncompact` as a separate named function but by noting `compact_injective`
// applied at `y := k` (using `compact(k) = k` when `k < c`, or `= pred k`
// when `k > c`) *is* that right inverse: it recovers `f i` from
// `compact(f i) = compact(k)` for every `k`, not just `k = m`.
//
// No `Nat.beq`, and no classical logic: **checked**, `Nat.beq`'s completeness
// in the "false" direction (`a ≠ b → beq a b = false`) is still not a named
// lemma anywhere in the `nat` prelude (confirmed via
// `prelude_theorem_inventory --include-constructed`, filtered to `nat`: the
// five `beq`-related rows are `beq_eq_true_iff`, `beq_eq_true_of_eq`,
// `beq_refl`, `eq_of_beq_eq_true`, `ne_of_beq_eq_false` — the last is
// `beq = false → a ≠ b`, not the converse). The route below needs no such
// lemma: every case split is on `Nat`'s *order* (`Nat.le_total` +
// `Nat.lt_or_eq_of_le`, both already proved), and the one place a `Bool`
// value must be pinned to a literal (deciding which branch of `compact` a
// concrete `x` takes) uses the "generalize-then-instantiate" trick already
// established in `division.rs`'s `executable_division_spec_step`
// (`Bool.rec` over a motive parameterized by an arbitrary selector, applied
// to `bool_refl(condition)`), not a hand-rolled excluded-middle-shaped
// dichotomy.

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `compact c x := bool_select_nat (Nat.ble x c) x (Nat.pred x)`.
fn compact(d: &mut NatDev<'_>, c: ExprId, x: ExprId) -> ExprId {
    let cond = d.ble(x, c);
    let px = d.pred(x);
    d.bool_select_nat(cond, x, px)
}

/// `h : Le x c ⊢ Eq Nat (compact c x) x`.
fn compact_eq_of_le(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, x: ExprId, h_le: ExprId) -> ExprId {
    let p = *p;
    let cond = d.ble(x, c);
    let true_val = d.bool_true();
    let hb = d.lemma(p.ble_eq_true_of_le, &[x, c, h_le]);
    let symm_hb = d.bool_symm(cond, true_val, hb);
    let px = d.pred(x);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = d.bool_select_nat(value, x, px);
        d.eq(sel, x)
    });
    let refl_case = d.refl(x);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `h : Lt c x ⊢ Eq Nat (compact c x) (pred x)`, via the "generalize then
/// instantiate at `bool_refl(condition)`" trick already used in
/// `division.rs`'s `executable_division_spec_step`.
fn compact_eq_of_gt(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, x: ExprId, h_gt: ExprId) -> ExprId {
    let p = *p;
    let cond = d.ble(x, c);
    let px = d.pred(x);
    let false_val = d.bool_false();
    let true_val = d.bool_true();
    let bool_ty = d.bool_ty();

    let branch_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
        let eq_cond_sel = d.bool_eq(cond, selector);
        let sel_val = d.bool_select_nat(selector, x, px);
        let concl = d.eq(sel_val, px);
        d.arrow(eq_cond_sel, concl)
    };

    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        let body = d.refl(px);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, true_val);
        let x_le_c = d.lemma(p.le_of_ble_eq_true, &[x, c, heq]);
        let succ_c = d.succ(c);
        let succ_c_le_c = d.lemma(p.le_trans, &[succ_c, x, c, h_gt, x_le_c]);
        let false_pf = d.lemma(p.not_succ_le_self, &[c, succ_c_le_c]);
        let sel_val = d.bool_select_nat(true_val, x, px);
        let concl_true = d.eq(sel_val, px);
        let body = ex_falso(d, &p, concl_true, false_pf);
        d.lam_fv(heq_fv, heq_ty, body)
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

/// `h : Lt a b ⊢ Le a b`, by weakening `Le (succ a) b` through `Le a (succ a)`.
fn le_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let sa = d.succ(a);
    let le_a_sa = d.lemma(p.le_succ, &[a]);
    d.lemma(p.le_trans, &[a, sa, b, le_a_sa, h])
}

/// `h : Lt zero n ⊢ Eq n (succ (pred n))`, by induction on `n` (the base case
/// is impossible via `not_lt_zero`; the successor case is `refl`, since
/// `pred (succ m)` reduces to `m` definitionally). `n` may be any `Nat`-typed
/// expression, not just a bound variable — `Nat.rec` does not require its
/// target to reduce. A private copy of the identical lemma in `fermat.rs`.
fn pos_implies_succ_pred(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp = d.lt(zero, x);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = d.eq(x, spx);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = d.lt(zero, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let pz = d.pred(zero);
            let spz = d.succ(pz);
            let target_ty = d.eq(zero, spz);
            let not_lt = d.lemma(p.not_lt_zero, &[zero]);
            let false_proof = d.apply(not_lt, &[hyp]);
            let body = ex_falso(d, &p, target_ty, false_proof);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d, m, _ih| {
            let sm = d.succ(m);
            let zero = d.zero();
            let hyp_ty = d.lt(zero, sm);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let body = d.refl(sm);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        n,
    )
}

/// `h : Lt c x ⊢ Lt zero x`, from `c ≥ 0` and `c < x`.
fn zero_lt_via_c(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, x: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let zero_le_c = d.lemma(p.zero_le, &[c]);
    let succ_zero_le_succ_c = d.lemma(p.le_succ_succ, &[zero, c, zero_le_c]);
    let succ_zero = d.succ(zero);
    let succ_c = d.succ(c);
    d.lemma(p.le_trans, &[succ_zero, succ_c, x, succ_zero_le_succ_c, h])
}

/// `Or (Lt x c) (Or (Eq Nat x c) (Lt c x))`, by `Nat.le_total` then
/// `Nat.lt_or_eq_of_le` on whichever side holds.
fn trichotomy(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, x: ExprId) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_xc = d.lt(x, c);
    let eq_xc = d.eq(x, c);
    let lt_cx = d.lt(c, x);
    let inner = d.const_app(logic.or, &[eq_xc, lt_cx]);
    let target = d.const_app(logic.or, &[lt_xc, inner]);

    let total = d.lemma(p.le_total, &[x, c]);
    let le_xc = d.le(x, c);
    let le_cx = d.le(c, x);

    let on_left = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub = d.lemma(p.lt_or_eq_of_le, &[x, c, h]);
        let sub_on_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = d.const_app(logic.or_inl, &[lt_xc, inner, h2]);
            d.lam_fv(h2_fv, lt_xc, body)
        };
        let sub_on_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let mid = d.const_app(logic.or_inl, &[eq_xc, lt_cx, h2]);
            let body = d.const_app(logic.or_inr, &[lt_xc, inner, mid]);
            d.lam_fv(h2_fv, eq_xc, body)
        };
        let body =
            d.const_app(logic.or_elim, &[lt_xc, eq_xc, target, sub, sub_on_left, sub_on_right]);
        d.lam_fv(h_fv, le_xc, body)
    };
    let on_right = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub = d.lemma(p.lt_or_eq_of_le, &[c, x, h]);
        let eq_cx = d.eq(c, x);
        let sub_on_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let mid = d.const_app(logic.or_inr, &[eq_xc, lt_cx, h2]);
            let body = d.const_app(logic.or_inr, &[lt_xc, inner, mid]);
            d.lam_fv(h2_fv, lt_cx, body)
        };
        let sub_on_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let h2_symm = d.symm(c, x, h2);
            let mid = d.const_app(logic.or_inl, &[eq_xc, lt_cx, h2_symm]);
            let body = d.const_app(logic.or_inr, &[lt_xc, inner, mid]);
            d.lam_fv(h2_fv, eq_cx, body)
        };
        let body =
            d.const_app(logic.or_elim, &[lt_cx, eq_cx, target, sub, sub_on_left, sub_on_right]);
        d.lam_fv(h_fv, le_cx, body)
    };
    d.const_app(logic.or_elim, &[le_xc, le_cx, target, total, on_left, on_right])
}

/// Eliminate the middle `Eq Nat x c` case of [`trichotomy`] using
/// `eq_case_false`, producing `Or (Lt x c) (Lt c x)`.
fn two_way_split(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    tri: ExprId,
    eq_case_false: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_xc = d.lt(x, c);
    let eq_xc = d.eq(x, c);
    let lt_cx = d.lt(c, x);
    let inner = d.const_app(logic.or, &[eq_xc, lt_cx]);
    let target = d.const_app(logic.or, &[lt_xc, lt_cx]);

    let on_left = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.const_app(logic.or_inl, &[lt_xc, lt_cx, h]);
        d.lam_fv(h_fv, lt_xc, body)
    };
    let on_right = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub_on_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let false_pf = eq_case_false(d, h2);
            let body = ex_falso(d, &p, target, false_pf);
            d.lam_fv(h2_fv, eq_xc, body)
        };
        let sub_on_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = d.const_app(logic.or_inr, &[lt_xc, lt_cx, h2]);
            d.lam_fv(h2_fv, lt_cx, body)
        };
        let body = d.const_app(logic.or_elim, &[eq_xc, lt_cx, target, h, sub_on_left, sub_on_right]);
        d.lam_fv(h_fv, inner, body)
    };
    d.const_app(logic.or_elim, &[lt_xc, inner, target, tri, on_left, on_right])
}

/// `heq : Eq Nat (f i) (f m) ⊢ False`, from `hi : Lt i m` and `f`'s
/// injectivity on `succ m` (`Eq i m` contradicts `Lt i m` via `lt_irrefl`).
#[allow(clippy::too_many_arguments)]
fn false_from_index_eq_c(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    inj: ExprId,
    i: ExprId,
    m: ExprId,
    hi: ExprId,
    i_lt_sm: ExprId,
    m_lt_sm: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let i_eq_m = d.apply(inj, &[i, m, i_lt_sm, m_lt_sm, heq]);
    let motive = d.eq_motive(i, &|d, z| d.lt(z, m));
    let m_lt_m = d.transport(i, motive, hi, m, i_eq_m);
    d.lemma(p.lt_irrefl, &[m, m_lt_m])
}

/// `Or (Lt (f i) c) (Lt c (f i))`, for `i < m`: `f i ≠ c` follows from `f`'s
/// injectivity on `succ m` (`i ≠ m`), which turns [`trichotomy`]'s middle
/// case into a contradiction via [`false_from_index_eq_c`].
#[allow(clippy::too_many_arguments)]
fn split_fi(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    inj: ExprId,
    c: ExprId,
    i: ExprId,
    m: ExprId,
    hi: ExprId,
    i_lt_sm: ExprId,
    m_lt_sm: ExprId,
) -> ExprId {
    let p = *p;
    let fi = d.apply(f, &[i]);
    let tri = trichotomy(d, &p, c, fi);
    two_way_split(d, &p, c, fi, tri, &|d, heq| {
        false_from_index_eq_c(d, &p, inj, i, m, hi, i_lt_sm, m_lt_sm, heq)
    })
}

/// `hi : Lt i m ⊢ Lt i (succ m)`.
fn lift_lt(d: &mut NatDev<'_>, p: &NatPrelude, i: ExprId, m: ExprId, hi: ExprId) -> ExprId {
    let p = *p;
    let succ_i = d.succ(i);
    let sm = d.succ(m);
    let m_le_sm = d.lemma(p.le_succ, &[m]);
    d.lemma(p.le_trans, &[succ_i, m, sm, hi, m_le_sm])
}

/// `x ≤ m`, `Or (Lt x c) (Lt c x)` ⊢ `Lt (compact c x) m` — `compact` maps
/// `{0,…,m} \ {c}` into `{0,…,m-1}` on either side of `c`.
#[allow(clippy::too_many_arguments)]
fn compact_lt_of(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    m: ExprId,
    c_le_m: ExprId,
    x_le_m: ExprId,
    split: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_xc = d.lt(x, c);
    let lt_cx = d.lt(c, x);
    let gx = compact(d, c, x);
    let target = d.lt(gx, m);

    let on_left = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let x_le_c = le_of_lt(d, &p, x, c, h);
        let eq1 = compact_eq_of_le(d, &p, c, x, x_le_c);
        let x_lt_m = d.lemma(p.lt_of_lt_of_le, &[x, c, m, h, c_le_m]);
        let motive = d.eq_motive(x, &|d, z| d.lt(z, m));
        let sym_eq1 = d.symm(gx, x, eq1);
        let result = d.transport(x, motive, x_lt_m, gx, sym_eq1);
        d.lam_fv(h_fv, lt_xc, result)
    };
    let on_right = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let eq2 = compact_eq_of_gt(d, &p, c, x, h);
        let px = d.pred(x);
        let zero_lt_x = zero_lt_via_c(d, &p, c, x, h);
        let pos_x = pos_implies_succ_pred(d, &p, x);
        let x_eq_succpx = d.apply(pos_x, &[zero_lt_x]);
        let succ_px = d.succ(px);
        let le_refl_x = d.lemma(p.le_refl, &[x]);
        let motive2 = d.eq_motive(x, &|d, z| d.le(z, x));
        let succ_px_le_x = d.transport(x, motive2, le_refl_x, succ_px, x_eq_succpx);
        let px_lt_m = d.lemma(p.le_trans, &[succ_px, x, m, succ_px_le_x, x_le_m]);
        let motive3 = d.eq_motive(px, &|d, z| d.lt(z, m));
        let sym_eq2 = d.symm(gx, px, eq2);
        let result = d.transport(px, motive3, px_lt_m, gx, sym_eq2);
        d.lam_fv(h_fv, lt_cx, result)
    };
    d.const_app(logic.or_elim, &[lt_xc, lt_cx, target, split, on_left, on_right])
}

// x < c, y < c: compact is the identity on both.
#[allow(clippy::too_many_arguments)]
fn case_lt_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    cx: ExprId,
    cy: ExprId,
    h: ExprId,
    h2: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let x_le_c = le_of_lt(d, &p, x, c, h);
    let y_le_c = le_of_lt(d, &p, y, c, h2);
    let eqx = compact_eq_of_le(d, &p, c, x, x_le_c);
    let eqy = compact_eq_of_le(d, &p, c, y, y_le_c);
    let step1 = d.symm(cx, x, eqx);
    let step2 = d.trans(x, cx, cy, step1, heq);
    d.trans(x, cy, y, step2, eqy)
}

// x < c, c < y: impossible.
#[allow(clippy::too_many_arguments)]
fn case_lt_gt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    cx: ExprId,
    cy: ExprId,
    h: ExprId,
    h2: ExprId,
    heq: ExprId,
    target: ExprId,
) -> ExprId {
    let p = *p;
    let x_le_c = le_of_lt(d, &p, x, c, h);
    let eqx = compact_eq_of_le(d, &p, c, x, x_le_c);
    let eqy = compact_eq_of_gt(d, &p, c, y, h2);
    let py = d.pred(y);
    let step1 = d.symm(cx, x, eqx);
    let step2 = d.trans(x, cx, cy, step1, heq);
    let step3 = d.trans(x, cy, py, step2, eqy);
    let succ_c = d.succ(c);
    let c_le_py = d.lemma(p.pred_le_pred, &[succ_c, y, h2]);
    let x_lt_py = d.lemma(p.lt_of_lt_of_le, &[x, c, py, h, c_le_py]);
    let motive = d.eq_motive(x, &|d, z| d.lt(z, py));
    let py_lt_py = d.transport(x, motive, x_lt_py, py, step3);
    let false_pf = d.lemma(p.lt_irrefl, &[py, py_lt_py]);
    ex_falso(d, &p, target, false_pf)
}

// c < x, y < c: impossible.
#[allow(clippy::too_many_arguments)]
fn case_gt_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    cx: ExprId,
    cy: ExprId,
    h: ExprId,
    h2: ExprId,
    heq: ExprId,
    target: ExprId,
) -> ExprId {
    let p = *p;
    let eqx = compact_eq_of_gt(d, &p, c, x, h);
    let px = d.pred(x);
    let y_le_c = le_of_lt(d, &p, y, c, h2);
    let eqy = compact_eq_of_le(d, &p, c, y, y_le_c);
    let step1 = d.symm(cx, px, eqx);
    let step2 = d.trans(px, cx, cy, step1, heq);
    let step3 = d.trans(px, cy, y, step2, eqy);
    let succ_c = d.succ(c);
    let c_le_px = d.lemma(p.pred_le_pred, &[succ_c, x, h]);
    let y_lt_px = d.lemma(p.lt_of_lt_of_le, &[y, c, px, h2, c_le_px]);
    let motive = d.eq_motive(px, &|d, z| d.lt(y, z));
    let y_lt_y = d.transport(px, motive, y_lt_px, y, step3);
    let false_pf = d.lemma(p.lt_irrefl, &[y, y_lt_y]);
    ex_falso(d, &p, target, false_pf)
}

// c < x, c < y: compact is `pred` on both, injective above `c ≥ 0`.
#[allow(clippy::too_many_arguments)]
fn case_gt_gt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    cx: ExprId,
    cy: ExprId,
    h: ExprId,
    h2: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let eqx = compact_eq_of_gt(d, &p, c, x, h);
    let eqy = compact_eq_of_gt(d, &p, c, y, h2);
    let px = d.pred(x);
    let py = d.pred(y);
    let step1 = d.symm(cx, px, eqx);
    let step2 = d.trans(px, cx, cy, step1, heq);
    let step3 = d.trans(px, cy, py, step2, eqy);
    let zero_lt_x = zero_lt_via_c(d, &p, c, x, h);
    let zero_lt_y = zero_lt_via_c(d, &p, c, y, h2);
    let pos_x = pos_implies_succ_pred(d, &p, x);
    let x_eq_succpx = d.apply(pos_x, &[zero_lt_x]);
    let pos_y = pos_implies_succ_pred(d, &p, y);
    let y_eq_succpy = d.apply(pos_y, &[zero_lt_y]);
    let succ_px = d.succ(px);
    let succ_py = d.succ(py);
    let succpx_eq_succpy = d.congr(px, py, step3, &|d, z| d.succ(z));
    let step_a = d.trans(x, succ_px, succ_py, x_eq_succpx, succpx_eq_succpy);
    let y_symm = d.symm(y, succ_py, y_eq_succpy);
    d.trans(x, succ_py, y, step_a, y_symm)
}

/// `compact` is injective on values known to lie strictly on one side of `c`:
/// `Or (Lt x c) (Lt c x)`, `Or (Lt y c) (Lt c y)`, `Eq (compact c x) (compact
/// c y) ⊢ Eq x y`. The mixed cases (`x` and `y` on opposite sides) are
/// impossible — `compact` maps `{<c}` into `[0,c)` and `{>c}` into `[c,…)`,
/// disjoint ranges — and are closed by contradiction.
#[allow(clippy::too_many_arguments)]
fn compact_injective(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    hx: ExprId,
    hy: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let lt_xc = d.lt(x, c);
    let lt_cx = d.lt(c, x);
    let lt_yc = d.lt(y, c);
    let lt_cy = d.lt(c, y);
    let target = d.eq(x, y);
    let cx = compact(d, c, x);
    let cy = compact(d, c, y);

    let branch_given_x_lt_c = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let result = case_lt_lt(d, &p, c, x, y, cx, cy, h, h2, heq);
            d.lam_fv(h2_fv, lt_yc, result)
        };
        let sub_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let result = case_lt_gt(d, &p, c, x, y, cx, cy, h, h2, heq, target);
            d.lam_fv(h2_fv, lt_cy, result)
        };
        let body = d.const_app(logic.or_elim, &[lt_yc, lt_cy, target, hy, sub_left, sub_right]);
        d.lam_fv(h_fv, lt_xc, body)
    };
    let branch_given_c_lt_x = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub_left = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let result = case_gt_lt(d, &p, c, x, y, cx, cy, h, h2, heq, target);
            d.lam_fv(h2_fv, lt_yc, result)
        };
        let sub_right = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let result = case_gt_gt(d, &p, c, x, y, cx, cy, h, h2, heq);
            d.lam_fv(h2_fv, lt_cy, result)
        };
        let body = d.const_app(logic.or_elim, &[lt_yc, lt_cy, target, hy, sub_left, sub_right]);
        d.lam_fv(h_fv, lt_cx, body)
    };
    d.const_app(logic.or_elim, &[lt_xc, lt_cx, target, hx, branch_given_x_lt_c, branch_given_c_lt_x])
}

/// Given `k ≤ m` and `Or (Lt k c) (Lt c k)`, recover a witness for
/// `∃ i, i < succ m ∧ f i = k` from `surj_g : SurjectiveOn g m` — apply
/// `surj_g` at `compact c k` (which is `< m` by [`compact_lt_of`]), then use
/// [`compact_injective`] to turn `g i = compact c k` into `f i = k`.
#[allow(clippy::too_many_arguments)]
fn recover_witness(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    g: ExprId,
    inj: ExprId,
    c: ExprId,
    m: ExprId,
    sm: ExprId,
    m_lt_sm: ExprId,
    c_le_m: ExprId,
    surj_g: ExprId,
    k: ExprId,
    k_le_m: ExprId,
    hk_split: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();

    let t = compact(d, c, k);
    let t_lt_m = compact_lt_of(d, &p, c, k, m, c_le_m, k_le_m, hk_split);
    let ex = d.apply(surj_g, &[t, t_lt_m]);

    let source_predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, m);
        let gi = d.apply(g, &[i]);
        let eqt = d.eq(gi, t);
        let body = d.const_app(logic.and, &[bound, eqt]);
        d.lam_fv(i_fv, nat, body)
    };
    let source_ty = {
        let e = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(e, &[nat, source_predicate])
    };

    let target_predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, sm);
        let fi = d.apply(f, &[i]);
        let eqk = d.eq(fi, k);
        let body = d.const_app(logic.and, &[bound, eqk]);
        d.lam_fv(i_fv, nat, body)
    };
    let target = {
        let e = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(e, &[nat, target_predicate])
    };

    let motive = d.kernel().lam(anon, source_ty, target, BinderInfo::Default);

    let minor = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hand_fv = d.fresh_fvar();
        let hand = d.kernel().fvar(hand_fv);
        let bound_ty = d.lt(i, m);
        let gi = d.apply(g, &[i]);
        let eqt_ty = d.eq(gi, t);
        let hand_ty = d.const_app(logic.and, &[bound_ty, eqt_ty]);
        let hi = and_left(d, bound_ty, eqt_ty, hand);
        let heq_git = and_right(d, bound_ty, eqt_ty, hand);

        let i_lt_sm = lift_lt(d, &p, i, m, hi);
        let fi = d.apply(f, &[i]);
        let split_i = split_fi(d, &p, f, inj, c, i, m, hi, i_lt_sm, m_lt_sm);
        let fi_eq_k = compact_injective(d, &p, c, fi, k, split_i, hk_split, heq_git);

        let a_ty = d.lt(i, sm);
        let b_ty = d.eq(fi, k);
        let and_proof = d.const_app(logic.and_intro, &[a_ty, b_ty, i_lt_sm, fi_eq_k]);
        let exists_intro_name = d.kernel().const_(logic.exists_intro, vec![one]);
        let witness_proof = d.apply(exists_intro_name, &[nat, target_predicate, i, and_proof]);

        let with_hand = d.lam_fv(hand_fv, hand_ty, witness_proof);
        d.lam_fv(i_fv, nat, with_hand)
    };
    let exists_rec = d.kernel().const_(logic.exists_rec, vec![one]);
    d.apply(exists_rec, &[nat, source_predicate, motive, minor, ex])
}

/// `motive(n) := ∀ f, InjectiveOn f n → MapsInto f n → SurjectiveOn f n`.
fn pigeonhole_motive(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let inj = d.const_app(p.injective_on, &[f, n]);
    let maps = d.const_app(p.maps_into, &[f, n]);
    let surj = d.const_app(p.surjective_on, &[f, n]);
    let inner = d.arrow(maps, surj);
    let body = d.arrow(inj, inner);
    d.pi_fv(f_fv, fn_ty, body)
}

/// Base case `n = 0`: `SurjectiveOn f 0` is vacuous, via `Nat.not_lt_zero`.
fn pigeonhole_base_case(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let zero = d.zero();
    let logic = p.logic;
    let one = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let inj_ty = d.const_app(p.injective_on, &[f, zero]);
    let maps_ty = d.const_app(p.maps_into, &[f, zero]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, zero);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, zero);
        let fi = d.apply(f, &[i]);
        let eqk = d.eq(fi, k);
        let body = d.const_app(logic.and, &[bound, eqk]);
        d.lam_fv(i_fv, nat, body)
    };
    let exists_ty = {
        let e = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(e, &[nat, predicate])
    };
    let false_pf = d.lemma(p.not_lt_zero, &[k, hk]);
    let body_at_k = ex_falso(d, &p, exists_ty, false_pf);

    let k_lambda = d.lam_fv(hk_fv, hk_ty, body_at_k);
    let surj_body = d.lam_fv(k_fv, nat, k_lambda);

    let inj_fv = d.fresh_fvar();
    let maps_fv = d.fresh_fvar();
    let with_maps = d.lam_fv(maps_fv, maps_ty, surj_body);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    d.lam_fv(f_fv, fn_ty, with_inj)
}

/// Step case `n = succ m`: build `g := compact c ∘ f`, apply the induction
/// hypothesis to `g` (not `f`) at `m`, then recover `SurjectiveOn f (succ m)`
/// via [`recover_witness`]. See the module doc above for the route.
fn pigeonhole_step_case(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let logic = p.logic;
    let one = d.level_one();
    let sm = d.succ(m);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let inj_ty = d.const_app(p.injective_on, &[f, sm]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let maps_ty = d.const_app(p.maps_into, &[f, sm]);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);

    let c = d.apply(f, &[m]);
    let m_lt_sm = d.lemma(p.lt_succ_self, &[m]);
    let c_lt_sm = d.apply(maps, &[m, m_lt_sm]);
    let c_le_m = d.lemma(p.le_of_succ_le_succ, &[c, m, c_lt_sm]);

    // g := fun i => compact c (f i)
    let g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = compact(d, c, fi);
        d.lam_fv(i_fv, nat, body)
    };

    let ih_at_g = d.apply(ih, &[g]);

    // --- MapsInto g m ---
    let maps_g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, m);
        let i_lt_sm = lift_lt(d, &p, i, m, hi);
        let fi = d.apply(f, &[i]);
        let fi_lt_sm = d.apply(maps, &[i, i_lt_sm]);
        let fi_le_m = d.lemma(p.le_of_succ_le_succ, &[fi, m, fi_lt_sm]);
        let split = split_fi(d, &p, f, inj, c, i, m, hi, i_lt_sm, m_lt_sm);
        let result = compact_lt_of(d, &p, c, fi, m, c_le_m, fi_le_m, split);
        let with_hi = d.lam_fv(hi_fv, hi_ty, result);
        d.lam_fv(i_fv, nat, with_hi)
    };

    // --- InjectiveOn g m ---
    let inj_g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(i, m);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let hj_ty = d.lt(j, m);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let gi = compact(d, c, fi);
        let gj = compact(d, c, fj);
        let heq_ty = d.eq(gi, gj);

        let i_lt_sm = lift_lt(d, &p, i, m, hi);
        let j_lt_sm = lift_lt(d, &p, j, m, hj);
        let split_i = split_fi(d, &p, f, inj, c, i, m, hi, i_lt_sm, m_lt_sm);
        let split_j = split_fi(d, &p, f, inj, c, j, m, hj, j_lt_sm, m_lt_sm);
        let fi_eq_fj = compact_injective(d, &p, c, fi, fj, split_i, split_j, heq);
        let i_eq_j = d.apply(inj, &[i, j, i_lt_sm, j_lt_sm, fi_eq_fj]);

        let with_heq = d.lam_fv(heq_fv, heq_ty, i_eq_j);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    let surj_g = d.apply(ih_at_g, &[inj_g, maps_g]);

    // --- SurjectiveOn f (succ m) ---
    let surj_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, sm);

        let k_le_m = d.lemma(p.le_of_succ_le_succ, &[k, m, hk]);

        let target_predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, sm);
            let fi = d.apply(f, &[i]);
            let eqk = d.eq(fi, k);
            let body = d.const_app(logic.and, &[bound, eqk]);
            d.lam_fv(i_fv, nat, body)
        };
        let target = {
            let e = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(e, &[nat, target_predicate])
        };

        let tri = trichotomy(d, &p, c, k);
        let lt_kc = d.lt(k, c);
        let eq_kc = d.eq(k, c);
        let lt_ck = d.lt(c, k);
        let inner_ty = d.const_app(logic.or, &[eq_kc, lt_ck]);

        let case_lt = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hk_split = d.const_app(logic.or_inl, &[lt_kc, lt_ck, h]);
            let result = recover_witness(
                d, &p, f, g, inj, c, m, sm, m_lt_sm, c_le_m, surj_g, k, k_le_m, hk_split,
            );
            d.lam_fv(h_fv, lt_kc, result)
        };
        let case_mid = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let sub_eq = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let c_eq_k = d.symm(k, c, h2);
                let a_ty = d.lt(m, sm);
                let b_ty = d.eq(c, k);
                let and_proof = d.const_app(logic.and_intro, &[a_ty, b_ty, m_lt_sm, c_eq_k]);
                let exists_intro_name = d.kernel().const_(logic.exists_intro, vec![one]);
                let result = d.apply(exists_intro_name, &[nat, target_predicate, m, and_proof]);
                d.lam_fv(h2_fv, eq_kc, result)
            };
            let sub_gt = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let hk_split = d.const_app(logic.or_inr, &[lt_kc, lt_ck, h2]);
                let result = recover_witness(
                    d, &p, f, g, inj, c, m, sm, m_lt_sm, c_le_m, surj_g, k, k_le_m, hk_split,
                );
                d.lam_fv(h2_fv, lt_ck, result)
            };
            let body = d.const_app(logic.or_elim, &[eq_kc, lt_ck, target, h, sub_eq, sub_gt]);
            d.lam_fv(h_fv, inner_ty, body)
        };
        let body = d.const_app(logic.or_elim, &[lt_kc, inner_ty, target, tri, case_lt, case_mid]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let with_maps = d.lam_fv(maps_fv, maps_ty, surj_f);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    d.lam_fv(f_fv, fn_ty, with_inj)
}

/// Declare `Nat.injective_on_imp_surjective_on` — the pigeonhole principle —
/// by induction on `n`, generalized over `f`. See the module doc above.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_pigeonhole(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.injective_on_imp_surjective_on, 1, &|d, values| {
        let n = values[0];
        let stmt = pigeonhole_motive(d, &p, n);
        let proof = d.induct(
            &|d, x| pigeonhole_motive(d, &p, x),
            &|d| pigeonhole_base_case(d, &p),
            &|d, m, ih| pigeonhole_step_case(d, &p, m, ih),
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}
