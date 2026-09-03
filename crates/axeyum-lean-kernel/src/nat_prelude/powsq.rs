//! Exponentiation by squaring, `Nat.powSq`, and its correctness against the
//! specification `Nat.pow`.
//!
//! ## Why fuel, not well-founded recursion
//!
//! The recursion `powSq b e := if e = 0 then 1 else h*h[*b]` where
//! `h := powSq b (e/2)` is on `e/2`, which is not structural in `e` — the same
//! obstacle [`super::gcd`]'s `Nat.gcd` solved with `WellFounded.fix` over
//! `Nat.lt`. This module takes the other route the handover offered: a fuel
//! parameter, structural in `Nat.rec`, exactly the shape `sizeAux`/`size`
//! already use in [`super::binary`] for the same "recurse on `n/2`" problem.
//!
//! The handover flagged a prior misstep worth restating precisely, because it
//! shaped this proof: an earlier lane was asked to prove
//! `sizeAux n n = sizeAux (succ n) n` (comparing two adjacent fuel amounts)
//! and refused it as **the wrong statement** — see
//! [`super::binary::declare_size_aux_lt_pow`]'s doc comment. Fuel-vs-fuel
//! agreement says nothing about *why* a given amount of fuel is enough; it is
//! consistent with both fuel amounts being wrong in the same way. What
//! `size_aux_lt_pow` proves instead, and what [`pow_sq_aux_sufficient`] below
//! proves for `powSqAux`, is a **sufficiency-implies-correctness** statement:
//! `Le e fuel → powSqAux fuel b e = pow b e`, anchored directly to the
//! specification (`Nat.pow`) rather than to another fuel amount. Specializing
//! at `fuel := e` (via `le_refl`) is what then proves `e` itself is enough
//! fuel for `powSq b e := powSqAux e b e` — the ledger's `pow_sq_eq_pow`.
//!
//! `powSq`'s own two defining equations (`pow_sq_zero`, `pow_sq_succ`) are
//! *derived* from `pow_sq_eq_pow` plus `pow`'s own equations (`pow_zero`,
//! `pow_add`, `pow_succ`) rather than proved directly against `powSqAux`'s
//! `Nat.rec` unfolding: the direct unfolding of `powSq b (succ k)` bottoms
//! out in `powSqAux k b (half)` (fuel `k`), not in `powSq b half := powSqAux
//! half b half` (fuel `half`), and relating the two IS the sufficiency
//! argument. So there is no cheaper route to the defining equations that
//! skips the correctness theorem; proving correctness first and reading the
//! equations off it is the actual order of the work below.
//!
//! `pow_half_split` is the reusable core of that correctness argument,
//! factored out because it is pure arithmetic about `Nat.pow`/`div`/`mod`
//! with no fuel or induction hypothesis in it at all: `pow b e` always equals
//! the even/odd split at `e/2`, for every `e` including `0`. Both the
//! correctness induction step and `pow_sq_succ` consume it directly.
//!
//! Every helper below hoists each sub-expression into its own `let` before
//! passing it on, matching [`super::factorization`]'s convention: `&mut
//! NatDev` cannot be reborrowed twice in one expression, so nothing here
//! nests a `d.`-method call inside another one's argument list.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward};
use super::ops::{NatDev, NatOps, two_mul_eq_add_self};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `h : Lt zero n ⊢ Lt n (mul two n)`. A direct copy of
/// [`super::binary`]'s private `n_lt_mul_two` (that copy is module-private,
/// and this module does not touch `binary.rs`): `n < n+n` from `0 < n` via
/// `add_lt_add_left` (at `add n zero`, restored to `n` by `add_zero`), then
/// `n+n = mul (succ one) n` via `succ_mul`/`one_mul`.
fn n_lt_mul_two(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, pos: ExprId) -> ExprId {
    // Retired to the `tactic` combinator (ADR-1589): `simp`'s default rules
    // rewrite `mul 2 n` to `add n n` (`succ_mul` twice, `zero_mul`,
    // `zero_add`), then `linarith` closes `Lt n (add n n)` from `pos : Lt
    // zero n` directly (`linarith::nat` also recognizes a literal-numeral
    // `mul` on its own -- this retirement keeps `Then(Simp, Linarith)`
    // because that is the hand proof's own shape, a rewrite step then an
    // order step, not because `Linarith` alone cannot reach it here).
    let p = *p;
    let zero = d.zero();
    let two = d.num(2);
    let mul_two_n = d.mul(two, n);
    let goal = d.lt(n, mul_two_n);
    let pos_ty = d.lt(zero, n);
    let assumptions = [(pos_ty, pos)];
    let rules = crate::simp::nat::default_rules(&p);
    let ctx = crate::tactic::Ctx {
        prelude: p,
        assumptions: &assumptions,
        rules: &rules,
    };
    let tactic = crate::tactic::Tactic::Then(
        Box::new(crate::tactic::Tactic::Simp),
        Box::new(crate::tactic::Tactic::Linarith),
    );
    crate::tactic::run(d, &ctx, &tactic, goal)
        .unwrap_or_else(|e| panic!("n_lt_mul_two: Then(Simp, Linarith) declined: {e:?}"))
}

/// `Eq (add x one) (succ x)`, via `add_succ` then `add_zero`.
///
/// Retired to the `simp` rewrite-chain producer (ADR-1586): the mirror
/// direction of `one_add_eq_succ` (variable on the LEFT of `add`), closed by
/// `add_succ` + `add_zero` alone.
fn add_one_eq_succ(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let one = d.num(1);
    let lhs = d.add(x, one);
    let succ_x = d.succ(x);
    let rules = crate::simp::nat::default_rules(p);
    crate::simp::nat::prove_eq(d, &rules, lhs, succ_x)
        .unwrap_or_else(|e| panic!("add_one_eq_succ: simp declined: {e:?}"))
}

/// `Eq r one`, given `r < 2` and `r ≠ 0`. From `r < 2 = succ 1`,
/// `le_of_lt_succ` gives `r ≤ 1`; `lt_or_eq_of_le` splits `r < 1` (which
/// forces `r = 0`, contradicting `r ≠ 0`, closed by `False.rec`) from
/// `r = 1` (immediate).
fn mod_two_eq_one_of_ne_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    r: ExprId,
    r_lt_two: ExprId,
    r_ne_zero: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let r_le_one = d.lemma(p.le_of_lt_succ, &[r, one, r_lt_two]);
    let split = d.lemma(p.lt_or_eq_of_le, &[r, one, r_le_one]);

    let lt_ty = d.lt(r, one);
    let eq_ty = d.eq(r, one);

    let lt_minor = {
        let lt_fv = d.fresh_fvar();
        let lt_h = d.kernel().fvar(lt_fv);
        let zero = d.zero();
        let r_le_zero = d.lemma(p.le_of_succ_le_succ, &[r, zero, lt_h]);
        let zero_le_r = d.lemma(p.zero_le, &[r]);
        let r_eq_zero = d.lemma(p.le_antisymm, &[r, zero, r_le_zero, zero_le_r]);
        let absurd = d.apply(r_ne_zero, &[r_eq_zero]);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let anon = d.anon_name();
        let target_ty = d.eq(r, one);
        let false_motive = d
            .kernel()
            .lam(anon, false_ty, target_ty, BinderInfo::Default);
        let level_zero = d.kernel().level_zero();
        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
        let elim = d.apply(false_rec, &[false_motive, absurd]);
        d.lam_fv(lt_fv, lt_ty, elim)
    };
    let eq_minor = {
        let eq_fv = d.fresh_fvar();
        let eqh = d.kernel().fvar(eq_fv);
        d.lam_fv(eq_fv, eq_ty, eqh)
    };
    let target = d.eq(r, one);
    let motive = {
        let anon = d.anon_name();
        let or_ty = d.const_app(p.logic.or, &[lt_ty, eq_ty]);
        d.kernel().lam(anon, or_ty, target, BinderInfo::Default)
    };
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(or_rec, &[lt_ty, eq_ty, motive, lt_minor, eq_minor, split])
}

/// `powSqAux fuel b e`: structural `Nat.rec` on the fuel, threading `b`, `e`
/// through as ordinary curried parameters. `powSqAux 0 b e ≡ 1` (arbitrary —
/// only ever consumed at `e = 0`, where it is also the right answer);
/// `powSqAux (succ f) b e ≡ if beq e 0 then 1 else
///   let h := powSqAux f b (e/2) in if beq (e%2) 0 then h*h else h*h*b`.
/// `powSq b e := powSqAux e b e`.
fn declare_powsq_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let inner_fn_ty = d.arrow(nat, nat);
    let fn_ty = d.arrow(nat, inner_fn_ty);

    let base_term = {
        let b_fv = d.fresh_fvar();
        let e_fv = d.fresh_fvar();
        let one = d.num(1);
        let inner = d.lam_fv(e_fv, nat, one);
        d.lam_fv(b_fv, nat, inner)
    };
    let step_term = {
        let f_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        let zero = d.zero();
        let two = d.num(2);
        let one = d.num(1);
        let condition_zero = d.beq(e, zero);
        let half = d.div(e, two);
        let r = d.modulo(e, two);
        let condition_parity = d.beq(r, zero);

        let ih_half = d.apply(ih, &[b, half]);
        let hh = d.mul(ih_half, ih_half);
        let hhb = d.mul(hh, b);
        let inner_selected = d.bool_select_nat(condition_parity, hh, hhb);
        let outer_selected = d.bool_select_nat(condition_zero, one, inner_selected);

        let with_e = d.lam_fv(e_fv, nat, outer_selected);
        let with_b = d.lam_fv(b_fv, nat, with_e);
        let with_ih = d.lam_fv(ih_fv, fn_ty, with_b);
        d.lam_fv(f_fv, nat, with_ih)
    };
    let motive = d.kernel().lam(anon, nat, fn_ty, BinderInfo::Default);
    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let one_lvl = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one_lvl]);
    let body = d.apply(rec, &[motive, base_term, step_term, fuel]);
    let value = d.lam_fv(fuel_fv, nat, body);
    let ty = d.arrow(nat, fn_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pow_sq_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(6),
    })?;

    {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let applied = d.const_app(p.pow_sq_aux, &[e, b, e]);
        let inner = d.lam_fv(e_fv, nat, applied);
        let value = d.lam_fv(b_fv, nat, inner);
        let inner_ty = d.arrow(nat, nat);
        let ty = d.arrow(nat, inner_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.pow_sq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }
    Ok(())
}

/// `pow_half_split : ∀ b e, Eq (pow b e)
///   (bool_select_nat (beq (mod e two) 0)
///      (mul (pow b (div e two)) (pow b (div e two)))
///      (mul (mul (pow b (div e two)) (pow b (div e two))) b))`.
///
/// Pure arithmetic about `Nat.pow`/`div`/`mod`, with no fuel and no
/// induction hypothesis: `e = 2*(e/2) + e%2` from `div_mod_exec`, and either
/// `e%2 = 0` (so `e = half+half`, closed by `pow_add`) or `e%2 ≠ 0` — hence
/// `= 1` by [`mod_two_eq_one_of_ne_zero`] — (so `e = succ(half+half)`,
/// closed by `pow_add` then `pow_succ`). Holds uniformly at `e = 0` too (no
/// positivity side condition), which is what lets both the correctness
/// induction step and `pow_sq_succ` consume it directly.
fn declare_pow_half_split(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_half_split, 2, &|d, values| {
        let (b, e) = (values[0], values[1]);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let half = d.div(e, two);
        let r = d.modulo(e, two);
        let condition = d.beq(r, zero);
        let pow_half = d.pow(b, half);
        let hh = d.mul(pow_half, pow_half);
        let hhb = d.mul(hh, b);
        let pow_b_e = d.pow(b, e);

        let h_exec = d.lemma(p.div_mod_exec, &[one, e]);
        let mul_two_half = d.mul(two, half);
        let recon = d.add(mul_two_half, r);
        let eq_ty = d.eq(e, recon);
        let bound_ty = d.lt(r, two);
        let eq_e_recon = and_left(d, eq_ty, bound_ty, h_exec);
        let r_lt_two = and_right(d, eq_ty, bound_ty, h_exec);
        let two_half_eq = two_mul_eq_add_self(d, &p, half);
        let half_plus_half = d.add(half, half);

        let target_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
            let selected = d.bool_select_nat(selector, hh, hhb);
            d.eq(pow_b_e, selected)
        };
        let branch_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
            let eq_ty = d.bool_eq(condition, selector);
            let target = target_for(d, selector);
            d.arrow(eq_ty, target)
        };

        let true_val = d.bool_true();
        let false_val = d.bool_false();

        let even_minor = {
            let eq_ty = d.bool_eq(condition, true_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);
            let r_eq_zero = d.lemma(p.eq_of_beq_eq_true, &[r, zero, eqp]);
            let recon0 = d.add(mul_two_half, zero);
            let recon_to_recon0 = d.congr(r, zero, r_eq_zero, &|d, x| d.add(mul_two_half, x));
            let add_zero_eq = d.lemma(p.add_zero, &[mul_two_half]);
            let (_, e_eq_final) = d.chain(
                e,
                &[
                    (recon, eq_e_recon),
                    (recon0, recon_to_recon0),
                    (mul_two_half, add_zero_eq),
                    (half_plus_half, two_half_eq),
                ],
            );
            let pow_e_eq_pow_hh = d.congr(e, half_plus_half, e_eq_final, &|d, x| d.pow(b, x));
            let pow_hh = d.pow(b, half_plus_half);
            let pow_add_eq = d.lemma(p.pow_add, &[b, half, half]);
            let (_, pow_e_eq_hh) = d.chain(pow_b_e, &[(pow_hh, pow_e_eq_pow_hh), (hh, pow_add_eq)]);
            d.lam_fv(eq_fv, eq_ty, pow_e_eq_hh)
        };

        let odd_minor = {
            let eq_ty = d.bool_eq(condition, false_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);
            let r_ne_zero = d.lemma(p.ne_of_beq_eq_false, &[r, zero, eqp]);
            let r_eq_one = mod_two_eq_one_of_ne_zero(d, &p, r, r_lt_two, r_ne_zero);
            let recon1 = d.add(mul_two_half, one);
            let recon_to_recon1 = d.congr(r, one, r_eq_one, &|d, x| d.add(mul_two_half, x));
            let add_one_eq = add_one_eq_succ(d, &p, mul_two_half);
            let succ_mul_two_half = d.succ(mul_two_half);
            let succ_half_plus_half = d.succ(half_plus_half);
            let succ_congr = d.congr(mul_two_half, half_plus_half, two_half_eq, &|d, x| d.succ(x));
            let (_, e_eq_final) = d.chain(
                e,
                &[
                    (recon, eq_e_recon),
                    (recon1, recon_to_recon1),
                    (succ_mul_two_half, add_one_eq),
                    (succ_half_plus_half, succ_congr),
                ],
            );
            let pow_e_eq_pow_succ_hh =
                d.congr(e, succ_half_plus_half, e_eq_final, &|d, x| d.pow(b, x));
            let pow_succ_hh = d.pow(b, succ_half_plus_half);
            let pow_succ_eq = d.lemma(p.pow_succ, &[b, half_plus_half]);
            let pow_hh = d.pow(b, half_plus_half);
            let pow_hh_mul_b = d.mul(pow_hh, b);
            let pow_add_eq = d.lemma(p.pow_add, &[b, half, half]);
            let hh_mul_b_eq = d.congr(pow_hh, hh, pow_add_eq, &|d, x| d.mul(x, b));
            let (_, pow_e_eq_hhb) = d.chain(
                pow_b_e,
                &[
                    (pow_succ_hh, pow_e_eq_pow_succ_hh),
                    (pow_hh_mul_b, pow_succ_eq),
                    (hhb, hh_mul_b_eq),
                ],
            );
            d.lam_fv(eq_fv, eq_ty, pow_e_eq_hhb)
        };

        let motive_bool = {
            let selector_fv = d.fresh_fvar();
            let selector = d.kernel().fvar(selector_fv);
            let body = branch_for(d, selector);
            let bool_ty = d.bool_ty();
            d.lam_fv(selector_fv, bool_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
        let selected = d.apply(bool_rec, &[motive_bool, odd_minor, even_minor, condition]);
        let condition_refl = d.bool_refl(condition);
        let result = d.apply(selected, &[condition_refl]);
        let stmt = target_for(d, condition);
        (stmt, result)
    })?;
    Ok(())
}

/// `even_or_odd : ∀ n, Or (Eq n (add (div n 2) (div n 2)))
///   (Eq n (succ (add (div n 2) (div n 2))))` — the decidable-parity split
/// with a COMPUTED half (`div n 2`, substituted directly into the statement),
/// never an existential witness.
///
/// This is [`declare_pow_half_split`]'s own construction, stopped one step
/// earlier: that proof builds exactly this fact as its `e_eq_final`
/// intermediate in each branch (`e = half+half` in the even branch, `e =
/// succ(half+half)` in the odd one) before continuing on to compose it with
/// `pow`. Packaging it as its own `Or`-valued theorem here, rather than
/// duplicating the `div_mod_exec` + `Bool.rec` machinery a second time,
/// reuses [`two_mul_eq_add_self`] and the same case split; nothing about the
/// construction is specific to `powSq` or exponentiation.
fn declare_even_or_odd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.even_or_odd, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let half = d.div(n, two);
        let r = d.modulo(n, two);
        let condition = d.beq(r, zero);

        let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
        let mul_two_half = d.mul(two, half);
        let recon = d.add(mul_two_half, r);
        let eq_ty = d.eq(n, recon);
        let bound_ty = d.lt(r, two);
        let eq_n_recon = and_left(d, eq_ty, bound_ty, h_exec);
        let r_lt_two = and_right(d, eq_ty, bound_ty, h_exec);
        let two_half_eq = two_mul_eq_add_self(d, &p, half);
        let half_plus_half = d.add(half, half);
        let succ_half_plus_half = d.succ(half_plus_half);

        let even_disjunct = d.eq(n, half_plus_half);
        let odd_disjunct = d.eq(n, succ_half_plus_half);
        let target = d.const_app(p.logic.or, &[even_disjunct, odd_disjunct]);

        let branch_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
            let eq_ty = d.bool_eq(condition, selector);
            d.arrow(eq_ty, target)
        };

        let true_val = d.bool_true();
        let false_val = d.bool_false();

        let even_minor = {
            let eq_ty = d.bool_eq(condition, true_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);
            let r_eq_zero = d.lemma(p.eq_of_beq_eq_true, &[r, zero, eqp]);
            let recon0 = d.add(mul_two_half, zero);
            let recon_to_recon0 = d.congr(r, zero, r_eq_zero, &|d, x| d.add(mul_two_half, x));
            let add_zero_eq = d.lemma(p.add_zero, &[mul_two_half]);
            let (_, n_eq_half_plus_half) = d.chain(
                n,
                &[
                    (recon, eq_n_recon),
                    (recon0, recon_to_recon0),
                    (mul_two_half, add_zero_eq),
                    (half_plus_half, two_half_eq),
                ],
            );
            let proof = d.const_app(
                p.logic.or_inl,
                &[even_disjunct, odd_disjunct, n_eq_half_plus_half],
            );
            d.lam_fv(eq_fv, eq_ty, proof)
        };

        let odd_minor = {
            let eq_ty = d.bool_eq(condition, false_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);
            let r_ne_zero = d.lemma(p.ne_of_beq_eq_false, &[r, zero, eqp]);
            let r_eq_one = mod_two_eq_one_of_ne_zero(d, &p, r, r_lt_two, r_ne_zero);
            let recon1 = d.add(mul_two_half, one);
            let recon_to_recon1 = d.congr(r, one, r_eq_one, &|d, x| d.add(mul_two_half, x));
            let add_one_eq = add_one_eq_succ(d, &p, mul_two_half);
            let succ_mul_two_half = d.succ(mul_two_half);
            let succ_congr = d.congr(mul_two_half, half_plus_half, two_half_eq, &|d, x| d.succ(x));
            let (_, n_eq_succ_half_plus_half) = d.chain(
                n,
                &[
                    (recon, eq_n_recon),
                    (recon1, recon_to_recon1),
                    (succ_mul_two_half, add_one_eq),
                    (succ_half_plus_half, succ_congr),
                ],
            );
            let proof = d.const_app(
                p.logic.or_inr,
                &[even_disjunct, odd_disjunct, n_eq_succ_half_plus_half],
            );
            d.lam_fv(eq_fv, eq_ty, proof)
        };

        let motive_bool = {
            let selector_fv = d.fresh_fvar();
            let selector = d.kernel().fvar(selector_fv);
            let body = branch_for(d, selector);
            let bool_ty = d.bool_ty();
            d.lam_fv(selector_fv, bool_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
        let selected = d.apply(bool_rec, &[motive_bool, odd_minor, even_minor, condition]);
        let condition_refl = d.bool_refl(condition);
        let result = d.apply(selected, &[condition_refl]);
        (target, result)
    })?;
    Ok(())
}

/// `pow_sq_aux_eq_pow : ∀ fuel b e, Le e fuel → powSqAux fuel b e = pow b e`
/// (the sufficiency-implies-correctness statement, see the module doc), and
/// its `fuel := e` specialization `pow_sq_eq_pow : ∀ b e, powSq b e = pow b
/// e`. Induction on `fuel`; the step splits on `beq e 0` exactly like
/// `powSqAux`'s own definition, and in the `e ≠ 0` branch derives `e/2 ≤ f`
/// from `e ≤ succ f` and `e/2 < e` (itself from `e < 2*e` at positive `e`,
/// via `div_mod_lt_mul_iff` — the same route `size_aux_lt_pow` uses) to
/// invoke the induction hypothesis, then closes with [`declare_pow_half_split`].
fn declare_powsq_eq_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let bound_ty = d.le(e, fuel);
        let lhs = d.const_app(p.pow_sq_aux, &[fuel, b, e]);
        let rhs = d.pow(b, e);
        let concl = d.eq(lhs, rhs);
        let body = d.arrow(bound_ty, concl);
        let with_e = d.pi_fv(e_fv, nat, body);
        d.pi_fv(b_fv, nat, with_e)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let zero = d.zero();
        let bound_ty = d.le(e, zero);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let zero_le_e = d.lemma(p.zero_le, &[e]);
        let e_eq_zero = d.lemma(p.le_antisymm, &[e, zero, bound, zero_le_e]);
        let zero_eq_e = d.symm(e, zero, e_eq_zero);

        let pow_b_zero = d.lemma(p.pow_zero, &[b]);
        let one = d.num(1);
        let motive_pb = d.eq_motive(zero, &|d, x| {
            let pbx = d.pow(b, x);
            d.eq(pbx, one)
        });
        let pow_b_e_eq_one = d.transport(zero, motive_pb, pow_b_zero, e, zero_eq_e);
        let pow_b_e = d.pow(b, e);
        let proof = d.symm(pow_b_e, one, pow_b_e_eq_one);

        let with_bound = d.lam_fv(bound_fv, bound_ty, proof);
        let with_e = d.lam_fv(e_fv, nat, with_bound);
        d.lam_fv(b_fv, nat, with_e)
    };

    let step = |d: &mut NatDev<'_>, f: ExprId, ih: ExprId| -> ExprId {
        let bool_ty = d.bool_ty();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sf = d.succ(f);
        let bound_ty = d.le(e, sf);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let condition_zero = d.beq(e, zero);
        let half = d.div(e, two);
        let r = d.modulo(e, two);
        let condition_parity = d.beq(r, zero);
        let h = d.const_app(p.pow_sq_aux, &[f, b, half]);
        let hh = d.mul(h, h);
        let hhb = d.mul(hh, b);
        let inner_selected = d.bool_select_nat(condition_parity, hh, hhb);
        let pow_b_e = d.pow(b, e);

        let target_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
            let selected = d.bool_select_nat(selector, one, inner_selected);
            d.eq(selected, pow_b_e)
        };
        let branch_for = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
            let eq_ty = d.bool_eq(condition_zero, selector);
            let target = target_for(d, selector);
            d.arrow(eq_ty, target)
        };

        let true_val = d.bool_true();
        let false_val = d.bool_false();

        let false_minor = {
            let eq_ty = d.bool_eq(condition_zero, false_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);

            let not_eq = d.lemma(p.ne_of_beq_eq_false, &[e, zero, eqp]);
            let pos = d.lemma(p.zero_lt_of_ne_zero, &[e, not_eq]);

            let h_exec = d.lemma(p.div_mod_exec, &[one, e]);
            let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[two, e, half, r, e]);
            let the_iff = d.apply(iff_fn, &[h_exec]);
            let mul_two_e = d.mul(two, e);
            let lt_e_2e_ty = d.lt(e, mul_two_e);
            let lt_half_e_ty = d.lt(half, e);
            let forward = iff_forward(d, lt_e_2e_ty, lt_half_e_ty, the_iff);
            let e_lt_2e = n_lt_mul_two(d, &p, e, pos);
            let half_lt_e = d.apply(forward, &[e_lt_2e]);

            let half_lt_sf = d.lemma(p.lt_of_lt_of_le, &[half, e, sf, half_lt_e, bound]);
            let half_le_f = d.lemma(p.le_of_succ_le_succ, &[half, f, half_lt_sf]);

            let ih_half = d.apply(ih, &[b, half, half_le_f]);
            let pow_half = d.pow(b, half);
            let pow_half_eq_h = d.symm(h, pow_half, ih_half);

            let pow_half_split_at_e = d.lemma(p.pow_half_split, &[b, e]);
            let pow_half_sq = d.mul(pow_half, pow_half);
            let pow_half_sq_b = d.mul(pow_half_sq, b);
            let pow_half_version = d.bool_select_nat(condition_parity, pow_half_sq, pow_half_sq_b);

            let selected_eq = d.congr(pow_half, h, pow_half_eq_h, &|d, x| {
                let xx = d.mul(x, x);
                let xxb = d.mul(xx, b);
                d.bool_select_nat(condition_parity, xx, xxb)
            });

            let (_, pow_e_eq_inner) = d.chain(
                pow_b_e,
                &[
                    (pow_half_version, pow_half_split_at_e),
                    (inner_selected, selected_eq),
                ],
            );
            let target = d.symm(pow_b_e, inner_selected, pow_e_eq_inner);
            d.lam_fv(eq_fv, eq_ty, target)
        };

        let true_minor = {
            let eq_ty = d.bool_eq(condition_zero, true_val);
            let eq_fv = d.fresh_fvar();
            let eqp = d.kernel().fvar(eq_fv);
            let e_eq_zero = d.lemma(p.eq_of_beq_eq_true, &[e, zero, eqp]);
            let zero_eq_e = d.symm(e, zero, e_eq_zero);
            let pow_b_zero = d.lemma(p.pow_zero, &[b]);
            let motive_pb = d.eq_motive(zero, &|d, x| {
                let pbx = d.pow(b, x);
                d.eq(pbx, one)
            });
            let pow_b_e_eq_one = d.transport(zero, motive_pb, pow_b_zero, e, zero_eq_e);
            let target = d.symm(pow_b_e, one, pow_b_e_eq_one);
            d.lam_fv(eq_fv, eq_ty, target)
        };

        let motive_bool = {
            let selector_fv = d.fresh_fvar();
            let selector = d.kernel().fvar(selector_fv);
            let body = branch_for(d, selector);
            d.lam_fv(selector_fv, bool_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
        let selected = d.apply(
            bool_rec,
            &[motive_bool, false_minor, true_minor, condition_zero],
        );
        let condition_refl = d.bool_refl(condition_zero);
        let step_result = d.apply(selected, &[condition_refl]);

        let with_bound = d.lam_fv(bound_fv, bound_ty, step_result);
        let with_e = d.lam_fv(e_fv, nat, with_bound);
        d.lam_fv(b_fv, nat, with_e)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = d.induct(&motive, &base, &step, fuel);

    // pow_sq_aux_eq_pow : ∀ fuel b e, Le e fuel → powSqAux fuel b e = pow b e
    {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let bound_ty = d.le(e, fuel);
        let applied = d.apply(proof_fn, &[b, e]);
        let lhs = d.const_app(p.pow_sq_aux, &[fuel, b, e]);
        let rhs = d.pow(b, e);
        let concl = d.eq(lhs, rhs);
        let inner_ty = d.arrow(bound_ty, concl);
        let ty = {
            let with_e = d.pi_fv(e_fv, nat, inner_ty);
            let with_b = d.pi_fv(b_fv, nat, with_e);
            d.pi_fv(fuel_fv, nat, with_b)
        };
        let value = {
            let with_e = d.lam_fv(e_fv, nat, applied);
            let with_b = d.lam_fv(b_fv, nat, with_e);
            d.lam_fv(fuel_fv, nat, with_b)
        };
        d.declare_theorem(p.pow_sq_aux_eq_pow, ty, value)?;
    }

    // pow_sq_eq_pow : ∀ b e, powSq b e = pow b e, via fuel := e (le_refl).
    d.theorem(p.pow_sq_eq_pow, 2, &|d, v| {
        let (b, e) = (v[0], v[1]);
        let le_refl_e = d.lemma(p.le_refl, &[e]);
        let generic = d.lemma(p.pow_sq_aux_eq_pow, &[e, b, e, le_refl_e]);
        let lhs = d.const_app(p.pow_sq, &[b, e]);
        let rhs = d.pow(b, e);
        let stmt = d.eq(lhs, rhs);
        (stmt, generic)
    })?;
    Ok(())
}

/// `powSq`'s own two defining equations, read off [`declare_powsq_eq_pow`]'s
/// `pow_sq_eq_pow` plus `pow`'s own equations rather than proved directly
/// against `powSqAux`'s raw unfolding — see the module doc for why.
///
/// `pow_sq_zero : ∀ b, powSq b 0 = 1` — `pow_sq_eq_pow` then `pow_zero`.
///
/// `pow_sq_succ : ∀ b k, powSq b (succ k) =
///   bool_select_nat (beq ((succ k) % 2) 0)
///     (mul (powSq b ((succ k)/2)) (powSq b ((succ k)/2)))
///     (mul (mul (powSq b ((succ k)/2)) (powSq b ((succ k)/2))) b)`
/// — `pow_sq_eq_pow` at `succ k`, `pow_half_split`, and `pow_sq_eq_pow` again
/// at the half (to translate the split's `pow b half` back into `powSq b
/// half`).
fn declare_powsq_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.pow_sq_zero, 1, &|d, v| {
        let b = v[0];
        let zero = d.zero();
        let lhs = d.const_app(p.pow_sq, &[b, zero]);
        let sq_eq_pow = d.lemma(p.pow_sq_eq_pow, &[b, zero]);
        let pow_zero_eq = d.lemma(p.pow_zero, &[b]);
        let pow_b_zero = d.pow(b, zero);
        let one = d.num(1);
        let (_, proof) = d.chain(lhs, &[(pow_b_zero, sq_eq_pow), (one, pow_zero_eq)]);
        let stmt = d.eq(lhs, one);
        (stmt, proof)
    })?;

    d.theorem(p.pow_sq_succ, 2, &|d, v| {
        let (b, k) = (v[0], v[1]);
        let e = d.succ(k);
        let zero = d.zero();
        let two = d.num(2);
        let half = d.div(e, two);
        let r = d.modulo(e, two);
        let condition = d.beq(r, zero);

        let lhs = d.const_app(p.pow_sq, &[b, e]);
        let sq_half = d.const_app(p.pow_sq, &[b, half]);
        let sq_hh = d.mul(sq_half, sq_half);
        let sq_hhb = d.mul(sq_hh, b);
        let rhs = d.bool_select_nat(condition, sq_hh, sq_hhb);

        let sq_eq_pow_e = d.lemma(p.pow_sq_eq_pow, &[b, e]);
        let half_split = d.lemma(p.pow_half_split, &[b, e]);
        let pow_half = d.pow(b, half);
        let pow_half_sq = d.mul(pow_half, pow_half);
        let pow_half_sq_b = d.mul(pow_half_sq, b);
        let pow_half_version = d.bool_select_nat(condition, pow_half_sq, pow_half_sq_b);

        let sq_eq_pow_half = d.lemma(p.pow_sq_eq_pow, &[b, half]);
        let pow_half_eq_sq = d.symm(sq_half, pow_half, sq_eq_pow_half);
        let congr_eq = d.congr(pow_half, sq_half, pow_half_eq_sq, &|d, x| {
            let xx = d.mul(x, x);
            let xxb = d.mul(xx, b);
            d.bool_select_nat(condition, xx, xxb)
        });

        let pow_b_e = d.pow(b, e);
        let (_, proof) = d.chain(
            lhs,
            &[
                (pow_b_e, sq_eq_pow_e),
                (pow_half_version, half_split),
                (rhs, congr_eq),
            ],
        );
        let stmt = d.eq(lhs, rhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `powSqAux`/`powSq`, their correctness against `Nat.pow`, and
/// `powSq`'s own defining equations, in that order (each later step consumes
/// the one before it).
pub(super) fn declare_powsq_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_powsq_defs(d, p)?;
    declare_pow_half_split(d, p)?;
    declare_even_or_odd(d, p)?;
    declare_powsq_eq_pow(d, p)?;
    declare_powsq_equations(d, p)?;
    Ok(())
}
