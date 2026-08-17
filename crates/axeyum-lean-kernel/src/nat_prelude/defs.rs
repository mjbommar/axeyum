//! Recursive arithmetic definitions and their defining equations.
//!
//! `Nat.add`/`mul`/`pow`, truncated subtraction, boolean equality (`Nat.beq`),
//! the executable division state, finite ranges, and the `Eq.refl`-proved
//! defining-equation theorems that let callers rewrite by name.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `add`, `mul`, `pow` — structural recursion on the second argument.
pub(super) fn declare_arithmetic(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // add x zero ≡ x ; add x (succ j) ≡ succ (add x j)
    d.define_binary(p.add, 1, &|_d, x| x, &|d, _x, _j, ih| d.succ(ih))?;
    // mul x zero ≡ zero ; mul x (succ j) ≡ add (mul x j) x
    d.define_binary(p.mul, 2, &|d, _x| d.zero(), &|d, x, _j, ih| d.add(ih, x))?;
    // pow x zero ≡ 1 ; pow x (succ j) ≡ mul (pow x j) x
    d.define_binary(p.pow, 3, &|d, _x| d.num(1), &|d, x, _j, ih| d.mul(ih, x))?;
    Ok(())
}

/// Computational equality and its exact propositional specification.
pub(super) fn declare_boolean_equality(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_bool = d.arrow(nat, bool_ty);
    let bool_motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);

    // beq zero y: true only at zero.
    let zero_minor = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let step = {
            let predecessor_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let false_ = d.bool_false();
            let with_ih = d.lam_fv(ih_fv, bool_ty, false_);
            d.lam_fv(predecessor_fv, nat, with_ih)
        };
        let true_ = d.bool_true();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[bool_motive, true_, step, y]);
        d.lam_fv(y_fv, nat, body)
    };

    // beq (succ x) y: false at zero; at succ y, compare x with y.
    let succ_minor = {
        let x_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let y = d.kernel().fvar(y_fv);
        let step = {
            let predecessor_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let unused_ih_fv = d.fresh_fvar();
            let body = d.apply(ih, &[predecessor]);
            let with_ih = d.lam_fv(unused_ih_fv, bool_ty, body);
            d.lam_fv(predecessor_fv, nat, with_ih)
        };
        let false_ = d.bool_false();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[bool_motive, false_, step, y]);
        let with_y = d.lam_fv(y_fv, nat, body);
        let with_ih = d.lam_fv(ih_fv, nat_to_bool, with_y);
        d.lam_fv(x_fv, nat, with_ih)
    };

    let outer_motive = d.kernel().lam(anon, nat, nat_to_bool, BinderInfo::Default);
    let x_fv = d.fresh_fvar();
    let y_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y = d.kernel().fvar(y_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let row = d.apply(rec, &[outer_motive, zero_minor, succ_minor, x]);
    let body = d.apply(row, &[y]);
    let value = {
        let with_y = d.lam_fv(y_fv, nat, body);
        d.lam_fv(x_fv, nat, with_y)
    };
    let over_right = d.arrow(nat, bool_ty);
    let ty = d.arrow(nat, over_right);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.beq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;

    // beq_refl : ∀ n, beq n n = true
    d.theorem(p.beq_refl, 1, &|d, values| {
        let value = values[0];
        let lhs = d.beq(value, value);
        let true_ = d.bool_true();
        let stmt = d.bool_eq(lhs, true_);
        let proof = d.induct(
            &|d, n| {
                let lhs = d.beq(n, n);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            },
            &|d| {
                let true_ = d.bool_true();
                d.bool_refl(true_)
            },
            &|_d, _n, ih| ih,
            value,
        );
        (stmt, proof)
    })?;

    // eq_of_beq_eq_true : ∀ a b, beq a b = true → a = b
    d.theorem(p.eq_of_beq_eq_true, 2, &|d, values| {
        let (left, right) = (values[0], values[1]);
        let all_right = d.induct(
            &|d, a| beq_sound_row_type(d, a),
            &|d| beq_sound_zero_row(d),
            &|d, predecessor, ih| beq_sound_succ_row(d, predecessor, ih),
            left,
        );
        let proof = d.apply(all_right, &[right]);
        let lhs = d.beq(left, right);
        let true_ = d.bool_true();
        let source = d.bool_eq(lhs, true_);
        let target = d.eq(left, right);
        (d.arrow(source, target), proof)
    })?;

    // beq_eq_true_of_eq : ∀ a b, a = b → beq a b = true
    d.theorem(p.beq_eq_true_of_eq, 2, &|d, values| {
        let (left, right) = (values[0], values[1]);
        let source = d.eq(left, right);
        let lhs = d.beq(left, right);
        let true_ = d.bool_true();
        let target = d.bool_eq(lhs, true_);
        let equality_fv = d.fresh_fvar();
        let equality = d.kernel().fvar(equality_fv);
        let motive = d.eq_motive(left, &|d, candidate| {
            let lhs = d.beq(left, candidate);
            let true_ = d.bool_true();
            d.bool_eq(lhs, true_)
        });
        let refl_case = d.lemma(p.beq_refl, &[left]);
        let body = d.transport(left, motive, refl_case, right, equality);
        let proof = d.lam_fv(equality_fv, source, body);
        (d.arrow(source, target), proof)
    })?;

    // beq_eq_true_iff : ∀ a b, beq a b = true ↔ a = b
    d.theorem(p.beq_eq_true_iff, 2, &|d, values| {
        let (left, right) = (values[0], values[1]);
        let lhs = d.beq(left, right);
        let true_ = d.bool_true();
        let boolean = d.bool_eq(lhs, true_);
        let equality = d.eq(left, right);
        let forward = d.lemma(p.eq_of_beq_eq_true, &[left, right]);
        let reverse = d.lemma(p.beq_eq_true_of_eq, &[left, right]);
        let iff_intro = d.kernel().const_(p.logic.iff_intro, vec![]);
        let proof = d.apply(iff_intro, &[boolean, equality, forward, reverse]);
        let stmt = d.const_app(p.logic.iff, &[boolean, equality]);
        (stmt, proof)
    })?;

    Ok(())
}

/// `∀ b, beq a b = true → a = b`.
fn beq_sound_row_type(d: &mut NatDev<'_>, left: ExprId) -> ExprId {
    let right_fv = d.fresh_fvar();
    let right = d.kernel().fvar(right_fv);
    let lhs = d.beq(left, right);
    let true_ = d.bool_true();
    let premise = d.bool_eq(lhs, true_);
    let conclusion = d.eq(left, right);
    let implication = d.arrow(premise, conclusion);
    let nat = d.nat_ty();
    d.pi_fv(right_fv, nat, implication)
}

fn beq_sound_zero_row(d: &mut NatDev<'_>) -> ExprId {
    let right_fv = d.fresh_fvar();
    let right = d.kernel().fvar(right_fv);
    let proof_for_right = d.induct(
        &|d, candidate| {
            let zero = d.zero();
            let lhs = d.beq(zero, candidate);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let conclusion = d.eq(zero, candidate);
            d.arrow(premise, conclusion)
        },
        &|d| {
            let premise_fv = d.fresh_fvar();
            let zero = d.zero();
            let lhs = d.beq(zero, zero);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let body = d.refl(zero);
            d.lam_fv(premise_fv, premise, body)
        },
        &|d, predecessor, _ih| {
            let premise_fv = d.fresh_fvar();
            let premise_value = d.kernel().fvar(premise_fv);
            let zero = d.zero();
            let successor = d.succ(predecessor);
            let lhs = d.beq(zero, successor);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let conclusion = d.eq(zero, successor);
            let body = d.false_true_elim(conclusion, premise_value);
            d.lam_fv(premise_fv, premise, body)
        },
        right,
    );
    let nat = d.nat_ty();
    d.lam_fv(right_fv, nat, proof_for_right)
}

fn beq_sound_succ_row(d: &mut NatDev<'_>, predecessor: ExprId, ih: ExprId) -> ExprId {
    let right_fv = d.fresh_fvar();
    let right = d.kernel().fvar(right_fv);
    let proof_for_right = d.induct(
        &|d, candidate| {
            let left = d.succ(predecessor);
            let lhs = d.beq(left, candidate);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let conclusion = d.eq(left, candidate);
            d.arrow(premise, conclusion)
        },
        &|d| {
            let premise_fv = d.fresh_fvar();
            let premise_value = d.kernel().fvar(premise_fv);
            let left = d.succ(predecessor);
            let zero = d.zero();
            let lhs = d.beq(left, zero);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let conclusion = d.eq(left, zero);
            let body = d.false_true_elim(conclusion, premise_value);
            d.lam_fv(premise_fv, premise, body)
        },
        &|d, right_predecessor, _right_ih| {
            let premise_fv = d.fresh_fvar();
            let premise_value = d.kernel().fvar(premise_fv);
            let left = d.succ(predecessor);
            let right = d.succ(right_predecessor);
            let lhs = d.beq(left, right);
            let true_ = d.bool_true();
            let premise = d.bool_eq(lhs, true_);
            let predecessor_eq = d.apply(ih, &[right_predecessor, premise_value]);
            let body = d.congr(
                predecessor,
                right_predecessor,
                predecessor_eq,
                &|d, value| d.succ(value),
            );
            d.lam_fv(premise_fv, premise, body)
        },
        right,
    );
    let nat = d.nat_ty();
    d.lam_fv(right_fv, nat, proof_for_right)
}

/// One structurally recursive state computes executable quotient and remainder.
///
/// The state is encoded as `Bool → Nat`: `true` projects the quotient and
/// `false` the remainder. This avoids both a new Nat-specific pair type and two
/// independently recursive functions that could drift semantically.
pub(super) fn declare_executable_division(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let state_ty = d.arrow(bool_ty, nat);
    let dividend_to_state = d.arrow(nat, state_ty);

    // Divisor zero follows Lean's totality: quotient zero, remainder dividend.
    let zero_divisor_minor = {
        let dividend_fv = d.fresh_fvar();
        let selector_fv = d.fresh_fvar();
        let dividend = d.kernel().fvar(dividend_fv);
        let selector = d.kernel().fvar(selector_fv);
        let zero = d.zero();
        let selected = d.bool_select_nat(selector, zero, dividend);
        let with_selector = d.lam_fv(selector_fv, bool_ty, selected);
        d.lam_fv(dividend_fv, nat, with_selector)
    };

    // For divisor `succ k`, count remainders `0 .. k`; rolling over from `k`
    // increments the quotient and resets the remainder.
    let successor_divisor_minor = {
        let predecessor_fv = d.fresh_fvar();
        let unused_divisor_ih_fv = d.fresh_fvar();
        let dividend_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let dividend = d.kernel().fvar(dividend_fv);
        let initial_state = {
            let selector_fv = d.fresh_fvar();
            let zero = d.zero();
            d.lam_fv(selector_fv, bool_ty, zero)
        };
        let dividend_step = {
            let prior_fv = d.fresh_fvar();
            let prior_state_fv = d.fresh_fvar();
            let selector_fv = d.fresh_fvar();
            let prior_state = d.kernel().fvar(prior_state_fv);
            let selector = d.kernel().fvar(selector_fv);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let quotient = d.apply(prior_state, &[true_]);
            let remainder = d.apply(prior_state, &[false_]);
            let rollover = d.beq(remainder, predecessor);
            let successor_quotient = d.succ(quotient);
            let next_quotient = d.bool_select_nat(rollover, successor_quotient, quotient);
            let zero = d.zero();
            let successor_remainder = d.succ(remainder);
            let next_remainder = d.bool_select_nat(rollover, zero, successor_remainder);
            let next_state = d.bool_select_nat(selector, next_quotient, next_remainder);
            let with_selector = d.lam_fv(selector_fv, bool_ty, next_state);
            let with_state = d.lam_fv(prior_state_fv, state_ty, with_selector);
            d.lam_fv(prior_fv, nat, with_state)
        };
        let state_motive = d.kernel().lam(anon, nat, state_ty, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[state_motive, initial_state, dividend_step, dividend]);
        let with_dividend = d.lam_fv(dividend_fv, nat, body);
        let with_unused_ih = d.lam_fv(unused_divisor_ih_fv, dividend_to_state, with_dividend);
        d.lam_fv(predecessor_fv, nat, with_unused_ih)
    };

    let divisor_motive = d
        .kernel()
        .lam(anon, nat, dividend_to_state, BinderInfo::Default);
    let divisor_fv = d.fresh_fvar();
    let dividend_fv = d.fresh_fvar();
    let selector_fv = d.fresh_fvar();
    let divisor = d.kernel().fvar(divisor_fv);
    let dividend = d.kernel().fvar(dividend_fv);
    let selector = d.kernel().fvar(selector_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let row = d.apply(
        rec,
        &[
            divisor_motive,
            zero_divisor_minor,
            successor_divisor_minor,
            divisor,
        ],
    );
    let state = d.apply(row, &[dividend, selector]);
    let value = {
        let with_selector = d.lam_fv(selector_fv, bool_ty, state);
        let with_dividend = d.lam_fv(dividend_fv, nat, with_selector);
        d.lam_fv(divisor_fv, nat, with_dividend)
    };
    let ty = d.arrow(nat, dividend_to_state);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.div_mod_state,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;

    // Public projections use Lean-compatible `(dividend, divisor)` order.
    for (name, selector) in [(p.div, d.bool_true()), (p.mod_, d.bool_false())] {
        let dividend_fv = d.fresh_fvar();
        let divisor_fv = d.fresh_fvar();
        let dividend = d.kernel().fvar(dividend_fv);
        let divisor = d.kernel().fvar(divisor_fv);
        let body = d.div_mod_state(divisor, dividend, selector);
        let value = {
            let with_divisor = d.lam_fv(divisor_fv, nat, body);
            d.lam_fv(dividend_fv, nat, with_divisor)
        };
        let over_divisor = d.arrow(nat, nat);
        let ty = d.arrow(nat, over_divisor);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // Totality and structural step equations all reduce from the definition.
    d.theorem(p.div_zero, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let lhs = d.div(value, zero);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;
    d.theorem(p.mod_zero, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let lhs = d.modulo(value, zero);
        (d.eq(lhs, value), d.refl(lhs))
    })?;
    d.theorem(p.zero_div, 1, &|d, values| {
        let divisor = values[0];
        let zero = d.zero();
        let lhs = d.div(zero, divisor);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let lhs = d.div(zero, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let lhs = d.div(zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let zero = d.zero();
                let divisor = d.succ(predecessor);
                let lhs = d.div(zero, divisor);
                d.refl(lhs)
            },
            divisor,
        );
        (stmt, proof)
    })?;
    d.theorem(p.zero_mod, 1, &|d, values| {
        let divisor = values[0];
        let zero = d.zero();
        let lhs = d.modulo(zero, divisor);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let lhs = d.modulo(zero, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let lhs = d.modulo(zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let zero = d.zero();
                let divisor = d.succ(predecessor);
                let lhs = d.modulo(zero, divisor);
                d.refl(lhs)
            },
            divisor,
        );
        (stmt, proof)
    })?;
    d.theorem(p.div_succ, 2, &|d, values| {
        let (dividend, divisor_predecessor) = (values[0], values[1]);
        let divisor = d.succ(divisor_predecessor);
        let successor_dividend = d.succ(dividend);
        let quotient = d.div(dividend, divisor);
        let remainder = d.modulo(dividend, divisor);
        let rollover = d.beq(remainder, divisor_predecessor);
        let successor_quotient = d.succ(quotient);
        let rhs = d.bool_select_nat(rollover, successor_quotient, quotient);
        let lhs = d.div(successor_dividend, divisor);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;
    d.theorem(p.mod_succ, 2, &|d, values| {
        let (dividend, divisor_predecessor) = (values[0], values[1]);
        let divisor = d.succ(divisor_predecessor);
        let successor_dividend = d.succ(dividend);
        let remainder = d.modulo(dividend, divisor);
        let rollover = d.beq(remainder, divisor_predecessor);
        let zero = d.zero();
        let successor_remainder = d.succ(remainder);
        let rhs = d.bool_select_nat(rollover, zero, successor_remainder);
        let lhs = d.modulo(successor_dividend, divisor);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;

    Ok(())
}

/// `pred` and truncated `sub`, both by structural recursion. Subtraction
/// recurses on its second argument exactly as Lean's core `Nat.sub` does.
pub(super) fn declare_subtraction(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let body = j;
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pred,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;

    // sub x zero ≡ x ; sub x (succ j) ≡ pred (sub x j)
    d.define_binary(p.sub, 2, &|_d, x| x, &|d, _x, _j, ih| d.pred(ih))?;
    Ok(())
}

/// `sumRange f n = f 0 + ... + f (n-1)`, by structural recursion on `n`.
pub(super) fn declare_finite_ranges(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.add(ih, fj);
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })?;

    // factorial zero ≡ 1 ; factorial (succ j) ≡ factorial j * succ j
    //
    // Unary, so `define_binary` does not apply and the `Nat.rec` application is
    // spelled out the way `pred` is. The recursor eliminates into `Nat` (level
    // `1`), the motive is the constant family `fun _ => Nat`, and the step takes
    // the predecessor `j` together with the recursive value `ih = factorial j`.
    //
    // Writing it this way — rather than via an equation lemma — is what makes
    // both computation rules hold DEFINITIONALLY (β/δ/ι), so
    // `dvd_factorial_of_le` can read `dvd d (factorial (succ j))` and
    // `dvd d (factorial j * succ j)` as the same proposition with no rewrite.
    // `factorial_zero`/`factorial_succ` below are therefore `refl` proofs and
    // exist only so callers can rewrite by name.
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.num(1);
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let successor = d.succ(j);
        let body = d.mul(ih, successor);
        let with_ih = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let one = d.level_one();
    let rec = d.kernel().const_(p.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    // Strictly greater delta height than `mul` (2), the only definition it calls.
    d.kernel().add_declaration(Declaration::Definition {
        name: p.factorial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// The defining equations, each a one-line `Eq.refl` proof: they hold by β/δ/ι,
/// so the kernel accepts `refl` against the stated equation.
pub(super) fn declare_defining_equations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_zero, 1, &|d, v| {
        let n = v[0];
        let z = d.zero();
        let lhs = d.add(n, z);
        let stmt = d.eq(lhs, n);
        let proof = d.refl(n);
        (stmt, proof)
    })?;
    d.theorem(p.add_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sm = d.succ(m);
        let lhs = d.add(n, sm);
        let inner = d.add(n, m);
        let rhs = d.succ(inner);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;
    d.theorem(p.mul_zero, 1, &|d, v| {
        let n = v[0];
        let z = d.zero();
        let lhs = d.mul(n, z);
        let stmt = d.eq(lhs, z);
        let proof = d.refl(z);
        (stmt, proof)
    })?;
    d.theorem(p.mul_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sm = d.succ(m);
        let lhs = d.mul(n, sm);
        let nm = d.mul(n, m);
        let rhs = d.add(nm, n);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;
    d.theorem(p.pow_zero, 1, &|d, v| {
        let n = v[0];
        let z = d.zero();
        let lhs = d.pow(n, z);
        let one = d.num(1);
        let stmt = d.eq(lhs, one);
        let proof = d.refl(one);
        (stmt, proof)
    })?;
    d.theorem(p.pow_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sm = d.succ(m);
        let lhs = d.pow(n, sm);
        let pm = d.pow(n, m);
        let rhs = d.mul(pm, n);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;
    d.theorem(p.pred_zero, 0, &|d, _v| {
        let z = d.zero();
        let lhs = d.pred(z);
        (d.eq(lhs, z), d.refl(z))
    })?;
    d.theorem(p.pred_succ, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let lhs = d.pred(sn);
        (d.eq(lhs, n), d.refl(n))
    })?;
    d.theorem(p.sub_zero, 1, &|d, v| {
        let n = v[0];
        let z = d.zero();
        let lhs = d.sub(n, z);
        (d.eq(lhs, n), d.refl(n))
    })?;
    d.theorem(p.sub_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sm = d.succ(m);
        let lhs = d.sub(n, sm);
        let inner = d.sub(n, m);
        let rhs = d.pred(inner);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = d.sum_range(f, zero);
        let stmt = d.eq(lhs, zero);
        let proof = d.refl(zero);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        d.declare_theorem(p.sum_range_zero, ty, value)?;
    }
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.sum_range(f, sn);
        let prior = d.sum_range(f, n);
        let fj = d.apply(f, &[n]);
        let rhs = d.add(prior, fj);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        d.declare_theorem(p.sum_range_succ, ty, value)?;
    }
    // factorial_zero : factorial zero = 1
    d.theorem(p.factorial_zero, 0, &|d, _v| {
        let zero = d.zero();
        let lhs = d.factorial(zero);
        let one = d.num(1);
        (d.eq(lhs, one), d.refl(one))
    })?;
    // factorial_succ : ∀ n, factorial (succ n) = factorial n * succ n
    d.theorem(p.factorial_succ, 1, &|d, v| {
        let n = v[0];
        let successor = d.succ(n);
        let lhs = d.factorial(successor);
        let prior = d.factorial(n);
        let rhs = d.mul(prior, successor);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;
    Ok(())
}
