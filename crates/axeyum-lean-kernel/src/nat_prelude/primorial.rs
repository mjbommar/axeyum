//! `Nat.primorial n = ∏ { p : p prime, p ≤ n }`, and the bridge that makes it
//! computable: **`minFac k = k` is primality**, for every `k ≥ 2`.
//!
//! ## Why `minFac`, and not `Nat.isPrime`
//!
//! This prelude already carries a `Bool`-valued primality predicate,
//! [`Nat.isPrime`](NatPrelude::is_prime) (`prime_counting.rs`), spelled as a
//! DIVISOR COUNT:
//!
//! ```text
//! isPrime n := beq (countRange (fun d => beq (n % (d+1)) 0) n) 2
//! ```
//!
//! and `prime_counting.rs` deliberately declares no theorem about it
//! (ADR-0653). Bridging that spelling to this prelude's
//! `prime_condition x := 2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x` means proving
//! "`n` has exactly two divisors in `[1,n]` iff `n` is prime" — a counting
//! argument over `countRange` with an explicit two-element enumeration, which
//! is a lemma in its own right and is NOT what the primorial needs.
//!
//! `Nat.minFac` needs no counting at all. `min_fac_dvd.rs` already proves
//! `min_fac_dvd : 2 ≤ n → minFac n ∣ n`, `min_fac_two_le : 2 ≤ n → 2 ≤ minFac n`
//! and `min_fac_prime : 2 ≤ n → prime_condition (minFac n)`, and those three
//! give BOTH directions of the bridge in a dozen lines each:
//!
//! - `minFac n = n` with `2 ≤ n`: rewrite `min_fac_prime` along the equation.
//! - `prime_condition n`: `minFac n ∣ n` so `minFac n = 1` or `minFac n = n`,
//!   and `2 ≤ minFac n` rules the first out.
//!
//! So this file's predicate is `fun i => Nat.beq (Nat.minFac i) i`.
//!
//! ### The `i = 1` row is deliberate, and harmless
//!
//! `minFac` has two boundary conventions (Mathlib's own): `minFac 0 = 2` and
//! `minFac 1 = 1`. So `beq (minFac i) i` is
//!
//! | `i` | `minFac i` | predicate | contributed factor |
//! | ---: | ---: | --- | ---: |
//! | 0 | 2 | `false` | 1 |
//! | 1 | 1 | **`true`** | **1** |
//! | 2 | 2 | `true` | 2 |
//! | 4 | 2 | `false` | 1 |
//!
//! `i = 1` passes the predicate and is not prime. It contributes the factor
//! `1`, which is the multiplicative identity, so **the product is still
//! exactly `∏ {p prime, p ≤ n}`**. A COUNT built on this predicate would be
//! off by one and would need `ble 2 i` conjoined; a PRODUCT does not, and
//! adding the conjunct would cost a `Bool`-valued `and` (this prelude has
//! `bool_select_nat`, `Bool.rec` at `Nat`, but no `Bool.rec` at `Bool`) for
//! no mathematical gain. The evaluation tests below pin `primorial 1 = 1`
//! against exactly this row, and the negative controls separate it from the
//! `∏ {p ≤ n}` a `2 ≤ i` conjunct would produce only if the two ever
//! differed — they do not.
//!
//! ## What is declared
//!
//! | name | statement |
//! | --- | --- |
//! | `Nat.primorial` | `fun n => prodRangeIf (fun i => beq (minFac i) i) (fun i => i) (succ n)` |
//! | `Nat.primorial_zero` | `primorial 0 = 1` |
//! | `Nat.primorial_succ` | `primorial (succ n) = mul (primorial n) (bool_select_nat (beq (minFac (succ n)) (succ n)) (succ n) 1)` |
//! | `Nat.min_fac_eq_self_of_prime` | `∀ n, prime_condition n → minFac n = n` |
//! | `Nat.prime_of_min_fac_eq_self` | `∀ n, 2 ≤ n → minFac n = n → prime_condition n` |
//! | `Nat.primorial_succ_of_prime` | `∀ n, prime_condition (succ n) → primorial (succ n) = mul (primorial n) (succ n)` |
//! | `Nat.primorial_succ_of_not_prime` | `∀ n, ¬ prime_condition (succ n) → primorial (succ n) = primorial n` |
//! | `Nat.primorial_pos` | `∀ n, 0 < primorial n` |
//! | `Nat.primorial_le_succ` | `∀ n, primorial n ≤ primorial (succ n)` |
//! | `Nat.primorial_mono` | `∀ m n, m ≤ n → primorial m ≤ primorial n` |
//!
//! Both defining equations are `Eq.refl`: `primorial` delta-unfolds into
//! `prodRangeIf`, which delta-unfolds into `prodRange`'s own `Nat.rec`, and
//! `prodRangeIf_zero`/`prodRangeIf_succ` are themselves `refl` for the same
//! reason (`subset_product.rs`).
//!
//! ## Holdout note (read before adding anything here)
//!
//! `Nat.primeCounting` and `Nat.primeCounting'` are the subject of **five of
//! the ten** rows of the preregistered held-out family
//! `discrete-step-and-counting-bounds`
//! (`artifacts/autogenesis/nursery-v2-extension.json`), and that family has
//! never been scored. **Nothing in this file mentions either constant**, by
//! construction: the primorial is a product over `minFac`, not a count, and
//! `Nat.primorial_mono` is monotonicity of the PRODUCT, not of
//! `Nat.primeCounting` (`Monotone Nat.primeCounting` is held-out row 6).
//! Do not add a `primeCounting` lemma here without reading ADR-1637.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use super::primes::prime_condition;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `fun i => Nat.beq (Nat.minFac i) i` — the `Bool` primality predicate the
/// primorial folds over. See the module doc for the `i = 1` row.
pub(super) fn is_prime_pred(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let mf = d.const_app(p.min_fac, &[i]);
    let body = d.beq(mf, i);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => i`, the factor the primorial contributes at a prime index.
fn identity_fn(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    d.lam_fv(i_fv, nat, i)
}

/// `Nat.prodRangeIf (fun i => beq (minFac i) i) (fun i => i) bound`, the body
/// `Nat.primorial` is defined as at `bound := succ n`.
fn primorial_body(d: &mut NatDev<'_>, p: &NatPrelude, bound: ExprId) -> ExprId {
    let pred = is_prime_pred(d, p);
    let f = identity_fn(d);
    d.const_app(p.prod_range_if, &[pred, f, bound])
}

/// `Nat.primorial n`, as a `const` application.
fn primorial(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.primorial, &[n])
}

/// `Nat.primorial : Nat → Nat`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_primorial(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let bound = d.succ(n);
    let body = primorial_body(d, &p, bound);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    // Strictly greater than `prodRangeIf` (`Regular(3)`, `subset_product.rs`),
    // `minFac` (`Regular(5)`, `min_fac.rs`) and `beq` (`Regular(1)`).
    d.kernel().add_declaration(Declaration::Definition {
        name: p.primorial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(6),
    })?;
    Ok(())
}

/// `Nat.primorial_zero : primorial 0 = 1` and
/// `Nat.primorial_succ : ∀ n, primorial (succ n)
///   = mul (primorial n) (bool_select_nat (beq (minFac (succ n)) (succ n)) (succ n) 1)`.
///
/// Both by `Eq.refl`: delta into `prodRangeIf`, delta into `prodRange`, then
/// `Nat.rec`'s own iota step — the same reduction that makes
/// `prodRangeIf_zero`/`prodRangeIf_succ` refl one level down.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_primorial_defining_equations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    {
        let zero = d.zero();
        let lhs = primorial(d, &p, zero);
        let one = d.num(1);
        let stmt = d.eq(lhs, one);
        let proof = d.refl(one);
        d.declare_theorem(p.primorial_zero, stmt, proof)?;
    }
    {
        d.theorem(p.primorial_succ, 1, &|d, vars| {
            let p = d.prelude();
            let n = vars[0];
            let sn = d.succ(n);
            let lhs = primorial(d, &p, sn);
            let prior = primorial(d, &p, n);
            let mf = d.const_app(p.min_fac, &[sn]);
            let cond = d.beq(mf, sn);
            let one = d.num(1);
            let sel = d.bool_select_nat(cond, sn, one);
            let rhs = d.mul(prior, sel);
            let stmt = d.eq(lhs, rhs);
            let proof = d.refl(rhs);
            (stmt, proof)
        })?;
    }
    Ok(())
}

/// `Nat.min_fac_eq_self_of_prime : ∀ n, prime_condition n → Eq (minFac n) n`
/// and `Nat.prime_of_min_fac_eq_self : ∀ n, Le 2 n → Eq (minFac n) n →
/// prime_condition n`.
///
/// Forward: `min_fac_dvd` gives `minFac n ∣ n` (its `2 ≤ n` premise is the
/// left conjunct of `prime_condition n`), primality's right conjunct turns
/// that into `minFac n = 1 ∨ minFac n = n`, and `Or.resolve_left` discharges
/// the left disjunct — transporting `min_fac_two_le : 2 ≤ minFac n` along
/// `minFac n = 1` gives `Le 2 1`, which is `Le (succ 1) 1`, refuted by
/// `not_succ_le_self 1`.
///
/// Reverse: transport `min_fac_prime n h : prime_condition (minFac n)` along
/// the equation. No new induction in either direction.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_prime_bridge(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // min_fac_eq_self_of_prime : ∀ n, prime_condition n → Eq (minFac n) n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let nat = d.nat_ty();
        let hp_ty = prime_condition(d, &p, n);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let mf = d.const_app(p.min_fac, &[n]);
        let one = d.num(1);
        let two = d.num(2);
        let concl = d.eq(mf, n);

        // Re-derive the two conjuncts of `prime_condition n` to project along.
        let lower = d.le(two, n);
        let divisors = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let hyp = d.dvd(c, n);
            let trivial = d.eq(c, one);
            let whole = d.eq(c, n);
            let disj = d.const_app(p.logic.or, &[trivial, whole]);
            let body = d.arrow(hyp, disj);
            d.pi_fv(c_fv, nat, body)
        };
        let h_two_le = and_left(d, lower, divisors, hp);
        let h_divisors = and_right(d, lower, divisors, hp);

        let h_dvd = d.const_app(p.min_fac_dvd, &[n, h_two_le]);
        let h_or = d.apply(h_divisors, &[mf, h_dvd]);

        let left_prop = d.eq(mf, one);
        let right_prop = d.eq(mf, n);
        let refutation = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let h_two_le_mf = d.const_app(p.min_fac_two_le, &[n, h_two_le]);
            // `Le 2 (minFac n)` transported along `minFac n = 1` is `Le 2 1`,
            // i.e. `Le (succ 1) 1`.
            let motive = d.eq_motive(mf, &|d, x| {
                let two = d.num(2);
                d.le(two, x)
            });
            let bad = d.transport(mf, motive, h_two_le_mf, one, he);
            let contradiction = d.const_app(p.not_succ_le_self, &[one, bad]);
            let anon = d.anon_name();
            d.kernel()
                .lam(anon, left_prop, contradiction, crate::BinderInfo::Default)
        };
        let proof_core = d.const_app(
            p.logic.or_resolve_left,
            &[left_prop, right_prop, h_or, refutation],
        );

        let ty = {
            let inner = d.arrow(hp_ty, concl);
            d.pi_fv(n_fv, nat, inner)
        };
        let value = {
            let inner = d.lam_fv(hp_fv, hp_ty, proof_core);
            d.lam_fv(n_fv, nat, inner)
        };
        d.declare_theorem(p.min_fac_eq_self_of_prime, ty, value)?;
    }

    // prime_of_min_fac_eq_self : ∀ n, Le 2 n → Eq (minFac n) n → prime_condition n
    {
        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let h2_ty = d.le(two, n);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let mf = d.const_app(p.min_fac, &[n]);
        let he_ty = d.eq(mf, n);
        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);

        let at_mf = d.const_app(p.min_fac_prime, &[n, h2]);
        let motive = d.eq_motive(mf, &|d, x| {
            let p = d.prelude();
            prime_condition(d, &p, x)
        });
        let proof_core = d.transport(mf, motive, at_mf, n, he);
        let concl = prime_condition(d, &p, n);

        let ty = {
            let inner = d.arrow(he_ty, concl);
            let mid = d.arrow(h2_ty, inner);
            d.pi_fv(n_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(he_fv, he_ty, proof_core);
            let mid = d.lam_fv(h2_fv, h2_ty, inner);
            d.lam_fv(n_fv, nat, mid)
        };
        d.declare_theorem(p.prime_of_min_fac_eq_self, ty, value)?;
    }
    Ok(())
}

/// `Le 1 (bool_select_nat cond (succ n) 1)` — the primorial's `succ`-step
/// factor is positive whichever branch the predicate takes.
///
/// Decided by `Bool.rec` at `Prop`: at `true` the factor is `succ n` and
/// `le_succ_succ` on `zero_le` gives `1 ≤ succ n`; at `false` it is `1` and
/// `Nat.le.refl` closes it. A `Bool.rec` on a symbolic scrutinee is stuck, so
/// this cannot be done by reduction — it is the same device
/// `ops::bool_select_nat_same` uses.
fn one_le_step_factor(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let sn = d.succ(n);
    let one = d.num(1);

    let motive = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let sel = d.bool_select_nat(c, sn, one);
        let body = d.le(one, sel);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let at_true = {
        let zero = d.zero();
        let h = d.const_app(p.zero_le, &[n]);
        d.const_app(p.le_succ_succ, &[zero, n, h])
    };
    let at_false = d.const_app(p.le_refl, &[one]);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let mf = d.const_app(p.min_fac, &[sn]);
    let cond = d.beq(mf, sn);
    d.apply(bool_rec, &[motive, at_false, at_true, cond])
}

/// `Nat.primorial_succ_of_prime`, `Nat.primorial_succ_of_not_prime`,
/// `Nat.primorial_pos`, `Nat.primorial_le_succ` and `Nat.primorial_mono`.
///
/// The two `succ` cases both turn the `Bool` selector into a literal and then
/// `Eq.rec` at `Bool`: `beq_refl` transported along the bridge gives
/// `cond = true` (prime), `beq_eq_false_of_ne` gives `cond = false`
/// (composite). At a literal branch `bool_select_nat` iota-reduces, so the
/// stated right-hand sides are definitionally what `primorial_succ` produces —
/// except for the `false` branch's trailing `* 1`, which is `add zero x` after
/// reduction and needs `mul_one` explicitly (`Nat.mul` recurses on its RIGHT
/// argument and `Nat.add zero x` is stuck for symbolic `x`).
///
/// `primorial_succ_of_not_prime` carries a `Le 2 (succ n)` premise it looks
/// like it should not need. It does: `succ 0 = 1` is not prime and yet
/// `minFac 1 = 1` makes the selector TRUE, so `cond = false` is simply not
/// derivable at `n = 0`. The conclusion still HOLDS there
/// (`primorial 1 = primorial 0 = 1`); what fails is this route to it, and the
/// Erdős induction only ever needs the premise-carrying form.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_primorial_order(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // primorial_succ_of_prime : ∀ n, prime_condition (succ n) →
    //   Eq (primorial (succ n)) (mul (primorial n) (succ n))
    {
        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let hp_ty = prime_condition(d, &p, sn);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let mf = d.const_app(p.min_fac, &[sn]);
        let he = d.const_app(p.min_fac_eq_self_of_prime, &[sn, hp]);
        // `he : minFac (succ n) = succ n`; flip it so the transport rewrites
        // the `succ n` inside `beq (succ n) (succ n) = true`.
        let he_sym = d.symm(mf, sn, he);
        let base = d.const_app(p.beq_refl, &[sn]);
        let motive = d.eq_motive(sn, &|d, x| {
            let lhs = d.beq(x, sn);
            let t = d.bool_true();
            d.bool_eq(lhs, t)
        });
        let hcond = d.transport(sn, motive, base, mf, he_sym);

        let prior = primorial(d, &p, n);
        let lhs = primorial(d, &p, sn);
        let cond = d.beq(mf, sn);
        let at_cond = d.const_app(p.primorial_succ, &[n]);
        let bool_motive = d.bool_eq_motive(cond, &|d, c| {
            let one = d.num(1);
            let sel = d.bool_select_nat(c, sn, one);
            let rhs = d.mul(prior, sel);
            d.eq(lhs, rhs)
        });
        let true_value = d.bool_true();
        let proof = d.bool_transport(cond, bool_motive, at_cond, true_value, hcond);

        let concl = {
            let rhs = d.mul(prior, sn);
            d.eq(lhs, rhs)
        };
        let ty = {
            let inner = d.arrow(hp_ty, concl);
            d.pi_fv(n_fv, nat, inner)
        };
        let value = {
            let inner = d.lam_fv(hp_fv, hp_ty, proof);
            d.lam_fv(n_fv, nat, inner)
        };
        d.declare_theorem(p.primorial_succ_of_prime, ty, value)?;
    }

    // primorial_succ_of_not_prime : ∀ n, Le 2 (succ n) →
    //   Not (prime_condition (succ n)) → Eq (primorial (succ n)) (primorial n)
    {
        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let two = d.num(2);
        let h2_ty = d.le(two, sn);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let prime_sn = prime_condition(d, &p, sn);
        let hnp_ty = d.const_app(p.logic.not, &[prime_sn]);
        let hnp_fv = d.fresh_fvar();
        let hnp = d.kernel().fvar(hnp_fv);

        let mf = d.const_app(p.min_fac, &[sn]);
        let eq_ty = d.eq(mf, sn);
        // hne : Not (minFac (succ n) = succ n)
        let hne = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let prime = d.const_app(p.prime_of_min_fac_eq_self, &[sn, h2, he]);
            let body = d.apply(hnp, &[prime]);
            d.lam_fv(he_fv, eq_ty, body)
        };
        let hcond = d.const_app(p.beq_eq_false_of_ne, &[mf, sn, hne]);

        let prior = primorial(d, &p, n);
        let lhs = primorial(d, &p, sn);
        let cond = d.beq(mf, sn);
        let at_cond = d.const_app(p.primorial_succ, &[n]);
        let bool_motive = d.bool_eq_motive(cond, &|d, c| {
            let one = d.num(1);
            let sel = d.bool_select_nat(c, sn, one);
            let rhs = d.mul(prior, sel);
            d.eq(lhs, rhs)
        });
        let false_value = d.bool_false();
        let at_false = d.bool_transport(cond, bool_motive, at_cond, false_value, hcond);
        // `at_false : primorial (succ n) = primorial n * 1`; `mul_one` closes
        // the last step (`mul x 1` reduces to `add zero x`, which is stuck).
        let one = d.num(1);
        let prod_one = d.mul(prior, one);
        let mul_one = d.const_app(p.mul_one, &[prior]);
        let proof = d.trans(lhs, prod_one, prior, at_false, mul_one);

        let concl = d.eq(lhs, prior);
        let ty = {
            let inner = d.arrow(hnp_ty, concl);
            let mid = d.arrow(h2_ty, inner);
            d.pi_fv(n_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(hnp_fv, hnp_ty, proof);
            let mid = d.lam_fv(h2_fv, h2_ty, inner);
            d.lam_fv(n_fv, nat, mid)
        };
        d.declare_theorem(p.primorial_succ_of_not_prime, ty, value)?;
    }

    // primorial_pos : ∀ n, Lt 0 (primorial n)
    {
        d.theorem(p.primorial_pos, 1, &|d, vars| {
            let p = d.prelude();
            let n = vars[0];
            let stmt = {
                let zero = d.zero();
                let value = primorial(d, &p, n);
                d.lt(zero, value)
            };
            let proof = d.induct(
                &|d, x| {
                    let p = d.prelude();
                    let zero = d.zero();
                    let value = primorial(d, &p, x);
                    d.lt(zero, value)
                },
                &|d| {
                    let one = d.num(1);
                    let p = d.prelude();
                    d.const_app(p.le_refl, &[one])
                },
                &|d, j, ih| {
                    let p = d.prelude();
                    let prior = primorial(d, &p, j);
                    let sj = d.succ(j);
                    let one = d.num(1);
                    let mf = d.const_app(p.min_fac, &[sj]);
                    let cond = d.beq(mf, sj);
                    let sel = d.bool_select_nat(cond, sj, one);
                    let hsel = one_le_step_factor(d, &p, j);
                    d.const_app(p.one_le_mul, &[prior, sel, ih, hsel])
                },
                n,
            );
            (stmt, proof)
        })?;
    }

    // primorial_le_succ : ∀ n, Le (primorial n) (primorial (succ n))
    {
        d.theorem(p.primorial_le_succ, 1, &|d, vars| {
            let p = d.prelude();
            let n = vars[0];
            let prior = primorial(d, &p, n);
            let sn = d.succ(n);
            let next = primorial(d, &p, sn);
            let stmt = d.le(prior, next);

            let one = d.num(1);
            let mf = d.const_app(p.min_fac, &[sn]);
            let cond = d.beq(mf, sn);
            let sel = d.bool_select_nat(cond, sn, one);
            let hsel = one_le_step_factor(d, &p, n);
            // `Le (primorial n * 1) (primorial n * sel)`; the right side is
            // definitionally `primorial (succ n)`.
            let scaled = d.const_app(p.mul_le_mul_left, &[prior, one, sel, hsel]);
            let prod_one = d.mul(prior, one);
            let mul_one = d.const_app(p.mul_one, &[prior]);
            let motive = d.eq_motive(prod_one, &|d, y| d.le(y, next));
            let proof = d.transport(prod_one, motive, scaled, prior, mul_one);
            (stmt, proof)
        })?;
    }

    // primorial_mono : ∀ m n, Le m n → Le (primorial m) (primorial n)
    {
        let nat = d.nat_ty();
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let f = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = primorial(d, &p, x);
            d.lam_fv(x_fv, nat, body)
        };
        let step = d.kernel().const_(p.primorial_le_succ, vec![]);
        let proof = d.const_app(p.monotone_of_le_succ, &[f, step, m, n, h]);

        let left = primorial(d, &p, m);
        let right = primorial(d, &p, n);
        let concl = d.le(left, right);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(m_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(m_fv, nat, mid)
        };
        d.declare_theorem(p.primorial_mono, ty, value)?;
    }
    Ok(())
}
