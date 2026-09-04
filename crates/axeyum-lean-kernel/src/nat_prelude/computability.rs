//! A minimal machine model over ℕ, and the undecidability of its
//! self-referential halting predicate — connected to
//! [`super::cantor::declare_cantor_all`]'s diagonalization rather than
//! rebuilt from scratch. See `docs/research/09-decisions/adr-1611-*.md` for
//! the model choice (a "step-function" register machine over a μ-recursive
//! encoding) and what was rejected.
//!
//! # The model
//!
//! A *machine* here is nothing but a total transition function
//! `step : Nat → Nat` on a Nat-encoded configuration space, run for a given
//! number of fuel steps:
//!
//! ```text
//! Nat.RM.runFuel (step : Nat → Nat) (c fuel : Nat) : Nat
//!   := Nat.rec (fun _ => Nat) c (fun _ ih => step ih) fuel
//! Nat.RM.Halts (step : Nat → Nat) (x : Nat) : Prop
//!   := ∃ fuel, Eq Nat (runFuel step x fuel) 0
//! ```
//!
//! `0` is the distinguished halted configuration (once reached, every `step`
//! this file builds is a self-loop at `0`, so "reaches `0`" is a stable
//! notion of halting). This is deliberately the μ-recursive-flavoured
//! **shallow** embedding: a "program" is not a syntactic object decoded by a
//! universal interpreter, it *is* its `step` function. ADR-1611 records why
//! that shortest-route choice was made over an explicit register-machine
//! front end (`List`-free Gödel numbering of an instruction stream) and over
//! building `Nat.Primrec`'s sibling `Nat.Partrec.Code` with a fuel-bounded
//! evaluator.
//!
//! # The diagonal machine, and why it needs no universal interpreter
//!
//! Given a candidate total decider `H : Nat → Bool`, build the machine that
//! *asks H about its own current configuration*:
//!
//! ```text
//! Nat.RM.diagStep (H : Nat → Bool) (c : Nat) : Nat
//!   := Bool.rec (fun _ => Nat) 0 c (H c)   -- if H c then c else 0
//! ```
//!
//! Starting `diagStep H` from the fixed marker configuration `1` (any
//! nonzero numeral would do): if `H 1 = true`, the machine stays at `1`
//! forever — a genuine, PROVED (not merely evaluated) non-halting fact, the
//! `fuel_inv_forall` fuel-induction local lemma inside
//! [`declare_self_halting_not_decidable`] below; if `H 1 = false`, it
//! reaches `0` in exactly one step. So `H`'s own value at
//! `1` decides `diagStep H`'s behaviour at `1` — this is the self-reference,
//! and it costs nothing beyond `H` being an arbitrary total `Nat → Bool`
//! function, the same "call the assumed function directly" move
//! [`super::cantor::declare_cantor_diagonal`]'s witness `g := fun n => not
//! (f n n)` already makes.
//!
//! # The connection to Cantor, precisely
//!
//! [`declare_self_halting_not_decidable`] does **not** literally dispatch
//! through `Nat.cantor_no_fixed_point` as a function call. It was built that
//! way first, and the attempt is recorded in ADR-1611: the theorem's two
//! cases close via two DIFFERENT disjointness facts (`Nat.succ_ne_zero` in
//! the "H 1 = true" case, which needs the fuel-induction non-halting fact
//! and so is irreducibly Π₁-shaped; `Bool.true_ne_false` in the "H 1 =
//! false" case, which needs only one step and is Σ₁-shaped), and forcing
//! both through a shared `Eq Bool (not b) b` fixed point would route the
//! first case through `False.rec` after the contradiction is already in
//! hand — decorative, not load-bearing. What IS reused, literally, is
//! `Nat.RM`'s sibling of [`super::cantor::cantor_pointwise`]'s own technique:
//! a `Bool.rec`/`Or`-case split (via `bool_true_or_false`, already shared
//! plumbing in `ops.rs`) discharged with the SAME two `Bool` disjointness
//! facts (`bool_true_ne_false`/here, `succ_ne_zero`) `cantor.rs`'s three
//! theorems are built from. The theorem this file proves is the one the
//! task named as the likely shape: **a total, two-sided-correct decider
//! for THIS machine's self-referential halting would force a genuine
//! contradiction constructed exactly as Cantor's argument constructs one**,
//! not a literal `#[reuse]` of the declared name.
//!
//! # What is proved, precisely (read before citing this as "the halting
//! problem is undecidable")
//!
//! `Nat.RM.self_halting_not_decidable` refutes a `H : Nat → Bool` assumed
//! correct **only at the single point `1`**, for **the single machine
//! `diagStep H`** — deliberately narrower hypotheses than "H decides Halts
//! for every step function at every input", because the proof never uses
//! more. This is a genuine constructive undecidability result (the two
//! correctness directions plus `diagStep`'s definition are jointly
//! inconsistent, full stop — no excluded middle, no choice, empty
//! footprint), but it is **not** Turing's theorem for a fixed
//! Turing-complete universal machine: there is no encode/decode of
//! programs-as-data here, no s-m-n theorem, no recursion theorem, and
//! `Halts` is not shown undecidable for an ENUMERATION of machines — only
//! for the one self-referential instance a candidate `H` itself determines.
//! ADR-1611 records this scope boundary and the natural next step (an
//! actual `Nat.Partrec.Code`-style universal evaluator) explicitly.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Eq Bool a x → Eq Nat (f a) (f x)`, the `Bool`-hypothesis analogue of
/// [`NatOps::congr`] (which is `Nat`-hypothesis only). Built the same way
/// `NatOps::bool_symm`/`bool_trans` build a `Bool`-conclusion transport: via
/// [`NatOps::bool_eq_motive`] with a `Nat`-`Eq`-valued body and
/// [`NatOps::bool_transport`], rather than a fresh `Bool.rec`.
fn bool_congr_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    x: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, v| {
        let fv = f(d, v);
        d.eq(fa, fv)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, x, h)
}

/// `Nat.RM.runFuel (step : Nat → Nat) (c fuel : Nat) : Nat`, structural
/// recursion on `fuel` alone (`step`/`c` are held fixed across the
/// recursion, exactly the shape `Nat.add`'s right-recursion holds its left
/// argument fixed): `runFuel step c 0 ≡ c`, `runFuel step c (succ f) ≡ step
/// (runFuel step c f)`, both by ι-reduction — no equation lemma is declared
/// because none is needed, every later proof uses the reduction directly.
pub(super) fn declare_run_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let nat_to_nat = d.arrow(nat, nat);

    let step_fv = d.fresh_fvar();
    let c_fv = d.fresh_fvar();
    let fuel_fv = d.fresh_fvar();
    let step = d.kernel().fvar(step_fv);
    let c = d.kernel().fvar(c_fv);

    let motive = {
        let dummy_fv = d.fresh_fvar();
        d.lam_fv(dummy_fv, nat, nat)
    };
    let succ_case = {
        let f_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = d.apply(step, &[ih]);
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(f_fv, nat, with_ih)
    };
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let fuel = d.kernel().fvar(fuel_fv);
    let body = d.apply(rec, &[motive, c, succ_case, fuel]);

    let value = {
        let with_fuel = d.lam_fv(fuel_fv, nat, body);
        let with_c = d.lam_fv(c_fv, nat, with_fuel);
        d.lam_fv(step_fv, nat_to_nat, with_c)
    };
    let ty = {
        let with_fuel_ty = d.arrow(nat, nat);
        let with_c_ty = d.arrow(nat, with_fuel_ty);
        d.arrow(nat_to_nat, with_c_ty)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rm_run_fuel,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Nat.RM.diagStep (H : Nat → Bool) (c : Nat) : Nat := if H c then c else
/// 0` — the machine that queries `H` about its OWN current configuration at
/// every step. See the module doc for why this needs no universal
/// interpreter: `H` is an ordinary bound `Nat → Bool` function, called
/// directly, exactly as `cantor_diagonal`'s witness calls its `f`.
pub(super) fn declare_diag_step(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let h_ty = d.arrow(nat, bool_ty);

    let h_fv = d.fresh_fvar();
    let c_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let c = d.kernel().fvar(c_fv);

    let hc = d.apply(h, &[c]);
    let motive = {
        let dummy_fv = d.fresh_fvar();
        d.lam_fv(dummy_fv, bool_ty, nat)
    };
    let one = d.level_one();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    let zero = d.zero();
    let body = d.apply(bool_rec, &[motive, zero, c, hc]);

    let value = {
        let with_c = d.lam_fv(c_fv, nat, body);
        d.lam_fv(h_fv, h_ty, with_c)
    };
    let ty = {
        let with_c_ty = d.arrow(nat, nat);
        d.arrow(h_ty, with_c_ty)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rm_diag_step,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Nat.RM.Halts (step : Nat → Nat) (x : Nat) : Prop := ∃ fuel, Eq Nat
/// (runFuel step x fuel) 0` — this machine model's halting predicate,
/// parametric in the step function so it states the general notion, not
/// only the diagonal instance.
pub(super) fn declare_halts(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let nat_to_nat = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    let step_fv = d.fresh_fvar();
    let x_fv = d.fresh_fvar();
    let step = d.kernel().fvar(step_fv);
    let x = d.kernel().fvar(x_fv);

    let run_fuel_const = d.kernel().const_(p.rm_run_fuel, vec![]);
    let pred = {
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let rf = d.apply(run_fuel_const, &[step, x, fuel]);
        let zero = d.zero();
        let eq_ty = d.eq(rf, zero);
        d.lam_fv(fuel_fv, nat, eq_ty)
    };
    let one = d.level_one();
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
    let body = d.apply(exists_c, &[nat, pred]);

    let value = {
        let with_x = d.lam_fv(x_fv, nat, body);
        d.lam_fv(step_fv, nat_to_nat, with_x)
    };
    let ty = {
        let with_x_ty = d.arrow(nat, prop);
        d.arrow(nat_to_nat, with_x_ty)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rm_halts,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// Build `Eq Nat (diagStep H 1) target`, given `hb : Eq Bool (H 1) b_lit`
/// where `b_lit` reduces `diagStep`'s `Bool.rec` to `target` (`b_lit :=
/// true_ → target := x1`; `b_lit := false_ → target := zero`). Shared by
/// both the fuel-induction lemma and the one-step halting witness.
fn diag_step_at_one_of(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    h: ExprId,
    x1: ExprId,
    b_lit: ExprId,
    hb: ExprId,
) -> ExprId {
    let p = *p;
    let hx1 = d.apply(h, &[x1]);
    let f = |d: &mut NatDev<'_>, v: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let nat = d.nat_ty();
        let dummy_fv = d.fresh_fvar();
        let motive = d.lam_fv(dummy_fv, bool_ty, nat);
        let one = d.level_one();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
        let zero = d.zero();
        d.apply(bool_rec, &[motive, zero, x1, v])
    };
    bool_congr_to_nat(d, hx1, b_lit, hb, &f)
}

/// `Nat.RM.self_halting_not_decidable : ∀ H : Nat → Bool, (Eq Bool (H 1)
/// true → Halts (diagStep H) 1) → (Halts (diagStep H) 1 → Eq Bool (H 1)
/// true) → False`.
///
/// Read the module doc first: `H` is assumed correct only AT the marker
/// point `1`, deliberately — the proof never needs more, so stating more
/// would overclaim. The two hypotheses are the two directions of "H
/// correctly decides whether `diagStep H` halts from `1`"; from them alone,
/// `diagStep H`'s definition forces a contradiction via
/// [`bool_true_or_false`]'s case split on `H 1`, closed the same way
/// `cantor.rs`'s three theorems close their `Bool.rec` branches — with
/// `Nat.succ_ne_zero`/`Bool.true_ne_false` disjointness, not excluded
/// middle.
pub(super) fn declare_self_halting_not_decidable(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let false_const = d.kernel().const_(p.logic.false_, vec![]);
    let h_ty = d.arrow(nat, bool_ty);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = d.zero();
    let x1 = d.succ(zero);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let hx1 = d.apply(h, &[x1]);

    let diag_step_const = d.kernel().const_(p.rm_diag_step, vec![]);
    let diag_step_h = d.apply(diag_step_const, &[h]);
    let halts_const = d.kernel().const_(p.rm_halts, vec![]);
    let halts_at_1 = d.apply(halts_const, &[diag_step_h, x1]);

    let true_eq_ty = d.bool_eq(hx1, true_);
    let hcomplete_ty = d.arrow(true_eq_ty, halts_at_1);
    let hsound_ty = d.arrow(halts_at_1, true_eq_ty);

    let hcomplete_fv = d.fresh_fvar();
    let hsound_fv = d.fresh_fvar();
    let hcomplete = d.kernel().fvar(hcomplete_fv);
    let hsound = d.kernel().fvar(hsound_fv);

    // --- fuel-invariance under the self-loop, as a LOCAL (undeclared) proof
    //     term: `fuel_inv_forall : ∀ fuel, Eq Bool (H 1) true → Eq Nat
    //     (runFuel (diagStep H) 1 fuel) 1`. `d.induct`'s `target` must be the
    //     genuine free variable the surrounding `lam_fv` abstracts over, the
    //     same discipline `d.theorem`'s own `arity`-driven Pi-binding uses. --
    let run_fuel_const = d.kernel().const_(p.rm_run_fuel, vec![]);
    let fuel_inv_forall = {
        let fuel_fv = d.fresh_fvar();
        let fuel_var = d.kernel().fvar(fuel_fv);
        let motive_fn = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
            let rf = d.apply(run_fuel_const, &[diag_step_h, x1, fuel]);
            let concl = d.eq(rf, x1);
            d.arrow(true_eq_ty, concl)
        };
        let base_fn = |d: &mut NatDev<'_>| -> ExprId {
            let hb_fv = d.fresh_fvar();
            let refl_x1 = d.refl(x1);
            d.lam_fv(hb_fv, true_eq_ty, refl_x1)
        };
        let step_fn = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let rf_j = d.apply(run_fuel_const, &[diag_step_h, x1, j]);
            let ih_j = d.apply(ih, &[hb]);
            let start = d.apply(diag_step_h, &[rf_j]);
            let next1 = d.apply(diag_step_h, &[x1]);
            let congr_step = d.congr(rf_j, x1, ih_j, &|d, v| d.apply(diag_step_h, &[v]));
            let diag_true = diag_step_at_one_of(d, &p, h, x1, true_, hb);
            let (_last, chained) = d.chain(start, &[(next1, congr_step), (x1, diag_true)]);
            d.lam_fv(hb_fv, true_eq_ty, chained)
        };
        let at_fuel = d.induct(&motive_fn, &base_fn, &step_fn, fuel_var);
        d.lam_fv(fuel_fv, nat, at_fuel)
    };

    // --- case `H 1 = true`: `diagStep H` self-loops at 1 forever, so
    //     `¬ Halts (diagStep H) 1`, contradicting `hcomplete hb`. -----------
    let case_true_ty = d.bool_eq(hx1, true_);
    let case_true = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let halts_pf = d.apply(hcomplete, &[hb]);

        // ∀ fuel, Eq Nat (runFuel (diagStep H) 1 fuel) 0 → False.
        let minor = {
            let fuel_fv = d.fresh_fvar();
            let fuel = d.kernel().fvar(fuel_fv);
            let heq0_fv = d.fresh_fvar();
            let heq0 = d.kernel().fvar(heq0_fv);
            let rf_fuel = d.apply(run_fuel_const, &[diag_step_h, x1, fuel]);
            let heq0_ty = d.eq(rf_fuel, zero);

            let inv_at_fuel = d.apply(fuel_inv_forall, &[fuel]);
            let x1_eq_x1_true = d.apply(inv_at_fuel, &[hb]);
            let x1_eq_0 = {
                let sym = d.symm(rf_fuel, x1, x1_eq_x1_true);
                d.trans(x1, rf_fuel, zero, sym, heq0)
            };
            let succ_ne_zero_zero = d.lemma(p.succ_ne_zero, &[zero]);
            let contra = d.apply(succ_ne_zero_zero, &[x1_eq_0]);
            let with_heq0 = d.lam_fv(heq0_fv, heq0_ty, contra);
            d.lam_fv(fuel_fv, nat, with_heq0)
        };
        let motive = {
            let dummy_fv = d.fresh_fvar();
            d.lam_fv(dummy_fv, halts_at_1, false_const)
        };
        let pred_for_rec = {
            let fuel_fv2 = d.fresh_fvar();
            let fuel2 = d.kernel().fvar(fuel_fv2);
            let rf2 = d.apply(run_fuel_const, &[diag_step_h, x1, fuel2]);
            let eq_ty2 = d.eq(rf2, zero);
            d.lam_fv(fuel_fv2, nat, eq_ty2)
        };
        let one_lvl_rec = d.level_one();
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl_rec]);
        let false_pf = d.apply(exists_rec, &[nat, pred_for_rec, motive, minor, halts_pf]);
        d.lam_fv(hb_fv, case_true_ty, false_pf)
    };

    // --- case `H 1 = false`: `diagStep H` halts in one step, so `hsound`
    //     forces `H 1 = true`, contradicting `hb : H 1 = false`. -----------
    let case_false_ty = d.bool_eq(hx1, false_);
    let case_false = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let diag_false = diag_step_at_one_of(d, &p, h, x1, false_, hb);
        let one_num = d.succ(zero);
        let halts_pf = {
            let pred = {
                let fuel_fv = d.fresh_fvar();
                let fuel = d.kernel().fvar(fuel_fv);
                let rf = d.apply(run_fuel_const, &[diag_step_h, x1, fuel]);
                let eq_ty = d.eq(rf, zero);
                d.lam_fv(fuel_fv, nat, eq_ty)
            };
            let one_lvl = d.level_one();
            let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
            d.apply(exists_intro, &[nat, pred, one_num, diag_false])
        };
        let h1_eq_true = d.apply(hsound, &[halts_pf]);
        let true_eq_false = {
            let sym = d.bool_symm(hx1, true_, h1_eq_true);
            d.bool_trans(true_, hx1, false_, sym, hb)
        };
        let contra = d.lemma(p.logic.bool_true_ne_false, &[true_eq_false]);
        d.lam_fv(hb_fv, case_false_ty, contra)
    };

    let disj = bool_true_or_false(d, &p, hx1);
    let motive_or = {
        let dummy_fv = d.fresh_fvar();
        let or_ty = d.const_app(p.logic.or, &[case_true_ty, case_false_ty]);
        d.lam_fv(dummy_fv, or_ty, false_const)
    };
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    let false_pf = d.apply(
        or_rec,
        &[
            case_true_ty,
            case_false_ty,
            motive_or,
            case_true,
            case_false,
            disj,
        ],
    );

    let stmt = {
        let inner = d.arrow(hsound_ty, false_const);
        d.arrow(hcomplete_ty, inner)
    };
    let value = {
        let with_sound = d.lam_fv(hsound_fv, hsound_ty, false_pf);
        d.lam_fv(hcomplete_fv, hcomplete_ty, with_sound)
    };
    let ty = d.pi_fv(h_fv, h_ty, stmt);
    let full_value = d.lam_fv(h_fv, h_ty, value);
    d.declare_theorem(p.rm_self_halting_not_decidable, ty, full_value)
}

pub(super) fn declare_computability_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_run_fuel(d, p)?;
    declare_diag_step(d, p)?;
    declare_halts(d, p)?;
    declare_self_halting_not_decidable(d, p)?;
    Ok(())
}
