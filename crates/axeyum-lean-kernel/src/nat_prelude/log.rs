//! `Nat.log` — the floor base-`b` logarithm, by **structural fuel recursion**.
//!
//! Mathlib v4.30 defines
//!
//! ```text
//! def Nat.log (b : ℕ) : ℕ → ℕ
//!   | n => if h : 1 < b ∧ b ≤ n then log b (n / b) + 1 else 0
//! ```
//!
//! which is *not* structural: the recursive call is at `n / b`, and `n / b` is
//! not a constructor predecessor of `n`. Mathlib discharges that with
//! well-founded recursion, which in a Lean-style kernel drags in `WellFounded`
//! and (through the equation compiler) `Quot.sound`/`propext` — fatal to this
//! project's axiom-freedom metric.
//!
//! This prelude has an established alternative, and it is the same one
//! [`declare_executable_division`](super::defs::declare_executable_division)
//! uses for `Nat.div`/`Nat.mod`: **recurse structurally on a fuel argument**
//! and instantiate the fuel at a value large enough to reach the base case.
//! Here that value is `n` itself, because the guard forces `2 ≤ b ≤ n`, and
//! then `n / b ≤ n / 2 < n`, so `n` iterations always suffice.
//!
//! ```text
//! Nat.logAux b 0        n ≡ 0
//! Nat.logAux b (succ f) n ≡ if b ≤ n then (if 2 ≤ b then succ (logAux b f (n / b)) else 0) else 0
//! Nat.log b n           := Nat.logAux b n n
//! ```
//!
//! Both equations hold **definitionally** (β/δ/ι), so no equation lemmas are
//! needed and nothing in this file appeals to an axiom. The guard is spelled as
//! two nested `Nat.ble` cuts rather than one `Bool` conjunction, exactly as
//! `transposition.rs` spells its cuts, so that a *single* false `ble` collapses
//! the whole term by ι-reduction alone.
//!
//! **The nesting ORDER is load-bearing**, and it is `b ≤ n` outermost. The two
//! cuts commute semantically — the guard is a conjunction — but not for proof
//! cost, because only the outermost cut collapses the whole term with a single
//! rewrite. [`log_of_lt`](NatPrelude::log_of_lt) refutes exactly `b ≤ n`, so
//! that proof is one `Eq.rec` over
//! [`ble_eq_false_of_lt`](NatPrelude::ble_eq_false_of_lt); with the cuts the
//! other way round it would additionally need `bool_select c 0 0 = 0`, a case
//! analysis on the *other* cut.
//!
//! `1 < b` is spelled `Nat.ble 2 b`: `Nat.ble` reduces `ble (succ x) (succ y)`
//! to `ble x y` and `ble (succ x) zero` to `false`, so `ble 2 b` decides in two
//! ι-steps once `b`'s constructor shape is known — which is why the four
//! boundary theorems are case analyses closed by `refl`, with no rewriting at
//! all. Nothing is given up to the order above, because `ble zero y` reduces to
//! `true` unconditionally: the outer cut never blocks the base-`0` and base-`1`
//! equations.
//!
//! The fuel argument sits **second** (`logAux b f n`) so that the `Nat.rec` on
//! it is the outer application and the motive is the plain row `fun _ => Nat →
//! Nat`; the recursive call `ih (n / b)` then simply applies that row at the
//! shrunk argument.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use super::steps::or_cases;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.logAux base fuel value`.
fn log_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    base: ExprId,
    fuel: ExprId,
    value: ExprId,
) -> ExprId {
    d.const_app(p.log_aux, &[base, fuel, value])
}

/// `Nat.log base value`.
fn log(d: &mut NatDev<'_>, p: &NatPrelude, base: ExprId, value: ExprId) -> ExprId {
    d.const_app(p.log, &[base, value])
}

/// `Le (bool_select_nat test on_true on_false) bound`, built from proofs at
/// each *literal* branch (`proof_true : Le on_true bound`,
/// `proof_false : Le on_false bound`).
///
/// The technique is [`declare_log_all`]'s `log_of_lt` `bool_transport`
/// generalized two ways: to *both* branches of the cut (that proof only ever
/// needed the refuted one) and to an inequality goal rather than an equation.
/// For each branch, `bool_eq_motive` builds the dependent `Eq.rec` motive
/// `fun (x : Bool) (_ : Eq Bool literal x) => Le (bool_select_nat x on_true
/// on_false) bound`; at `x = literal` this motive reduces (ι, on the outer
/// `bool_select_nat`) to `Le on_<branch> bound`, which is exactly the
/// caller-supplied proof, and `bool_transport` carries it across to `x =
/// test` using the branch hypothesis from [`bool_true_or_false`]'s `Or`.
#[allow(clippy::too_many_arguments)]
fn le_of_bool_select(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    test: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    bound: ExprId,
    proof_true: ExprId,
    proof_false: ExprId,
) -> ExprId {
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let is_true = d.bool_eq(test, true_);
    let true_case = {
        let motive_true = d.bool_eq_motive(true_, &|d, x| {
            let selected = d.bool_select_nat(x, on_true, on_false);
            d.le(selected, bound)
        });
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reversed = d.bool_symm(test, true_, h);
        let result = d.bool_transport(true_, motive_true, proof_true, test, reversed);
        d.lam_fv(h_fv, is_true, result)
    };

    let is_false = d.bool_eq(test, false_);
    let false_case = {
        let motive_false = d.bool_eq_motive(false_, &|d, x| {
            let selected = d.bool_select_nat(x, on_true, on_false);
            d.le(selected, bound)
        });
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reversed = d.bool_symm(test, false_, h);
        let result = d.bool_transport(false_, motive_false, proof_false, test, reversed);
        d.lam_fv(h_fv, is_false, result)
    };

    let goal = {
        let selected = d.bool_select_nat(test, on_true, on_false);
        d.le(selected, bound)
    };
    let split = super::ops::bool_true_or_false(d, p, test);
    or_cases(d, is_true, is_false, goal, true_case, false_case, split)
}

/// Declare `Nat.logAux`, `Nat.log`, and the four boundary equations that fall
/// out of the guard by ι-reduction alone.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_log_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);

    // --- Nat.logAux : Nat -> Nat -> Nat -> Nat ------------------------------
    {
        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);

        // fuel = zero: the constant-zero row.
        let zero_minor = {
            let unused_fv = d.fresh_fvar();
            let zero = d.zero();
            d.lam_fv(unused_fv, nat, zero)
        };

        // fuel = succ f: guard on `base <= value` OUTERMOST, then on `2 <= base`.
        //
        // The order is load-bearing and was chosen after the fact. The two cuts
        // commute semantically -- the guard is a conjunction -- but they do not
        // commute for PROOF cost, because only the outermost cut collapses the
        // whole term by a single rewrite. `log_of_lt` (`n < b`) refutes the
        // `base <= value` cut, and with that cut outermost its proof is one
        // `Eq.rec` over a `Bool` equation; with it nested it would additionally
        // need `bool_select c 0 0 = 0`, i.e. a case analysis on the *other*
        // cut. Nothing is lost: `log_zero_left`/`log_one_left`/`log_one_right`
        // stay pure `refl` under this order too, because `ble zero y` reduces
        // to `true` unconditionally, so the outer cut never blocks them.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            let quotient = d.div(argument, base);
            let recursive = d.apply(row, &[quotient]);
            let stepped = d.succ(recursive);
            let zero = d.zero();
            let two = d.num(2);
            let base_exceeds_one = d.ble(two, base);
            let inner = d.bool_select_nat(base_exceeds_one, stepped, zero);
            let base_fits = d.ble(base, argument);
            let body = d.bool_select_nat(base_fits, inner, zero);
            let with_argument = d.lam_fv(argument_fv, nat, body);
            let with_row = d.lam_fv(row_fv, nat_to_nat, with_argument);
            d.lam_fv(predecessor_fv, nat, with_row)
        };

        let motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let applied = d.apply(row, &[value]);
        let value_term = {
            let with_value = d.lam_fv(value_fv, nat, applied);
            let with_fuel = d.lam_fv(fuel_fv, nat, with_value);
            d.lam_fv(base_fv, nat, with_fuel)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            let middle = d.arrow(nat, inner);
            d.arrow(nat, middle)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.log_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.log b n := Nat.logAux b n n ------------------------------------
    {
        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let body = log_aux(d, &p, base, value, value);
        let value_term = {
            let with_value = d.lam_fv(value_fv, nat, body);
            d.lam_fv(base_fv, nat, with_value)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.log,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // log b 0 = 0 -- the fuel is already exhausted, so this is pure ι.
    d.theorem(p.log_zero_right, 1, &|d, values| {
        let base = values[0];
        let zero = d.zero();
        let lhs = log(d, &p, base, zero);
        (d.eq(lhs, zero), d.refl(lhs))
    })?;

    // log 0 n = 0 -- `ble 2 0` is `false`, so the outer cut collapses in every
    // fuel case. The induction on `n` only exposes the fuel's constructor; the
    // induction hypothesis is never used.
    d.theorem(p.log_zero_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let lhs = log(d, &p, zero, value);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let lhs = log(d, &p, zero, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let lhs = log(d, &p, zero, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let zero = d.zero();
                let candidate = d.succ(predecessor);
                let lhs = log(d, &p, zero, candidate);
                d.refl(lhs)
            },
            value,
        );
        (stmt, proof)
    })?;

    // log 1 n = 0 -- `ble 2 1` reduces to `ble 1 0`, i.e. `false`.
    d.theorem(p.log_one_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let lhs = log(d, &p, one, value);
        let stmt = d.eq(lhs, zero);
        let proof = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let one = d.num(1);
                let lhs = log(d, &p, one, candidate);
                d.eq(lhs, zero)
            },
            &|d| {
                let zero = d.zero();
                let one = d.num(1);
                let lhs = log(d, &p, one, zero);
                d.refl(lhs)
            },
            &|d, predecessor, _ih| {
                let one = d.num(1);
                let candidate = d.succ(predecessor);
                let lhs = log(d, &p, one, candidate);
                d.refl(lhs)
            },
            value,
        );
        (stmt, proof)
    })?;

    // log b 1 = 0 -- a THREE-way case analysis on `b`, because the two cuts
    // fail for different reasons: `b = 0` and `b = 1` fail `2 <= b`, while
    // `b = succ (succ k)` passes it and then fails `b <= 1`.
    d.theorem(p.log_one_right, 1, &|d, values| {
        let base = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let lhs = log(d, &p, base, one);
        let stmt = d.eq(lhs, zero);
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let zero = d.zero();
            let one = d.num(1);
            let lhs = log(d, &p, candidate, one);
            d.eq(lhs, zero)
        };
        let refl_at = |d: &mut NatDev<'_>, candidate: ExprId| {
            let one = d.num(1);
            let lhs = log(d, &p, candidate, one);
            d.refl(lhs)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                refl_at(d, zero)
            },
            &|d, predecessor, _ih| {
                d.induct(
                    &|d, inner| {
                        let candidate = d.succ(inner);
                        statement_at(d, candidate)
                    },
                    &|d| {
                        let one = d.num(1);
                        refl_at(d, one)
                    },
                    &|d, inner, _inner_ih| {
                        let candidate = d.succ(inner);
                        let candidate = d.succ(candidate);
                        refl_at(d, candidate)
                    },
                    predecessor,
                )
            },
            base,
        );
        (stmt, proof)
    })?;

    // ble b n = false, from n < b. A general `Nat.ble` fact with no `Nat.log`
    // in it, filed here under its first consumer -- which is exactly the
    // retrieval hazard CLAUDE.md names, so: if you need "the boolean `<=` is
    // false", it is `Nat.ble_eq_false_of_lt` and it lives in `log.rs`, not in
    // `ble.rs`. `ble.rs` has the two POSITIVE bridges (`ble_eq_true_of_le`,
    // `le_of_ble_eq_true`) and the negated-Prop form
    // (`not_le_of_not_ble_eq_true`), but nothing producing `Eq Bool _ false`,
    // which is the form a `Bool.rec` cut needs to be rewritten with.
    d.theorem(p.ble_eq_false_of_lt, 2, &|d, values| {
        let (base, value) = (values[0], values[1]);
        let false_ = d.bool_false();
        let true_ = d.bool_true();
        let test = d.ble(base, value);
        let target = d.bool_eq(test, false_);
        let hypothesis_ty = d.lt(value, base);
        let hypothesis_fv = d.fresh_fvar();
        let hypothesis = d.kernel().fvar(hypothesis_fv);

        let is_true = d.bool_eq(test, true_);
        let is_false = d.bool_eq(test, false_);
        let split = super::ops::bool_true_or_false(d, &p, test);
        let anon = d.anon_name();
        let split_ty = d.const_app(p.logic.or, &[is_true, is_false]);
        let motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);

        // `ble b n = true` gives `b <= n`, which with `n < b` gives `n < n`.
        let true_case = {
            let evidence_fv = d.fresh_fvar();
            let evidence = d.kernel().fvar(evidence_fv);
            let le_proof = d.lemma(p.le_of_ble_eq_true, &[base, value, evidence]);
            let strict = d.lemma(
                p.lt_of_lt_of_le,
                &[value, base, value, hypothesis, le_proof],
            );
            let irrefl = d.lemma(p.lt_irrefl, &[value]);
            let absurd = d.apply(irrefl, &[strict]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let false_motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
            let level_zero = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let body = d.apply(false_rec, &[false_motive, absurd]);
            d.lam_fv(evidence_fv, is_true, body)
        };
        let false_case = {
            let evidence_fv = d.fresh_fvar();
            let evidence = d.kernel().fvar(evidence_fv);
            d.lam_fv(evidence_fv, is_false, evidence)
        };

        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[is_true, is_false, motive, true_case, false_case, split],
        );
        let stmt = d.arrow(hypothesis_ty, target);
        let proof = d.lam_fv(hypothesis_fv, hypothesis_ty, body);
        (stmt, proof)
    })?;

    // log b n = 0 when n < b -- the outermost cut is refuted, so ONE rewrite
    // collapses the whole fuel step. The induction on `n` carries the
    // hypothesis in its motive (`fun m => Lt m b -> Eq (log b m) 0`), because
    // `n` is both the fuel and the argument and the hypothesis must specialize
    // with it; the induction hypothesis itself is never used.
    d.theorem(p.log_of_lt, 2, &|d, values| {
        let (base, value) = (values[0], values[1]);
        let zero = d.zero();
        let conclusion = {
            let lhs = log(d, &p, base, value);
            d.eq(lhs, zero)
        };
        let hypothesis_ty = d.lt(value, base);

        let generalized = d.induct(
            &|d, candidate| {
                let zero = d.zero();
                let lhs = log(d, &p, base, candidate);
                let target = d.eq(lhs, zero);
                let guard = d.lt(candidate, base);
                d.arrow(guard, target)
            },
            &|d| {
                let zero = d.zero();
                let lhs = log(d, &p, base, zero);
                let target = d.refl(lhs);
                let guard = d.lt(zero, base);
                let unused_fv = d.fresh_fvar();
                d.lam_fv(unused_fv, guard, target)
            },
            &|d, predecessor, _ih| {
                let candidate = d.succ(predecessor);
                let guard = d.lt(candidate, base);
                let evidence_fv = d.fresh_fvar();
                let evidence = d.kernel().fvar(evidence_fv);
                let zero = d.zero();
                let test = d.ble(base, candidate);
                let false_ = d.bool_false();
                let refuted = d.lemma(p.ble_eq_false_of_lt, &[base, candidate, evidence]);
                let reversed = d.bool_symm(test, false_, refuted);
                // motive c := Eq (bool_select c STEP 0) 0, where STEP is the
                // whole taken branch. At `c = false` this is `Eq 0 0` by iota;
                // transporting to `c = ble b (succ j)` is the goal, because
                // `log b (succ j)` is definitionally that selection.
                let step_taken = {
                    let two = d.num(2);
                    let quotient = d.div(candidate, base);
                    let recursive = log_aux(d, &p, base, predecessor, quotient);
                    let stepped = d.succ(recursive);
                    let base_exceeds_one = d.ble(two, base);
                    d.bool_select_nat(base_exceeds_one, stepped, zero)
                };
                let motive = d.bool_eq_motive(false_, &|d, selector| {
                    let zero = d.zero();
                    let selected = d.bool_select_nat(selector, step_taken, zero);
                    d.eq(selected, zero)
                });
                let refl_case = d.refl(zero);
                let body = d.bool_transport(false_, motive, refl_case, test, reversed);
                d.lam_fv(evidence_fv, guard, body)
            },
            value,
        );
        let hypothesis_fv = d.fresh_fvar();
        let hypothesis = d.kernel().fvar(hypothesis_fv);
        let applied = d.apply(generalized, &[hypothesis]);
        let stmt = d.arrow(hypothesis_ty, conclusion);
        let proof = d.lam_fv(hypothesis_fv, hypothesis_ty, applied);
        (stmt, proof)
    })?;

    // logAux_le_fuel : ∀ b f n, Le (logAux b f n) f -- the fuel bounds the
    // computed logarithm for EVERY value `n`, not merely the diagonal `f = n`
    // that `log` instantiates.
    //
    // This is the genuinely harder tier: induction on `f` alone, at a fixed
    // `n`, gives an induction hypothesis about `logAux b f n` -- but the
    // recursive call inside `logAux b (succ f) n` is at `logAux b f (n / b)`,
    // a DIFFERENT `n`. The hypothesis does not apply there. Generalizing `n`
    // *inside* the motive (`∀ n, Le (logAux b f n) f`) gives a hypothesis at
    // every argument, including `n / b` -- the same "quantify inside the
    // motive" technique `parity.rs`'s `declare_add_self_ne_succ_add_self`
    // uses for its double induction (see that file's `motive`/`inner_target`
    // construction).
    //
    // Base (`f = 0`): `logAux b 0 n` is the constant-zero row, so the goal is
    // `Le 0 0`, closed by `le_refl`.
    //
    // Step (`f = succ m`, given `ih : ∀ n, Le (logAux b m n) m`): unfold
    // `logAux b (succ m) n` to its guard's `bool_select_nat` form exactly as
    // `log_of_lt`'s step case does (`log_aux(d,&p,base,predecessor,quotient)`
    // reconstructs the same normal form the kernel reaches by delta+iota), and
    // case-split on each cut with `le_of_bool_select`:
    //   - `b <= n` false, or `2 <= b` false: the whole term is `0`, and
    //     `zero_le` closes `Le 0 (succ m)`.
    //   - both true: the term is `succ (logAux b m (n / b))`, and
    //     `le_succ_succ` applied to `ih (n / b) : Le (logAux b m (n/b)) m`
    //     closes `Le (succ (logAux b m (n/b))) (succ m)`.
    d.theorem(p.log_aux_le_fuel, 2, &|d, values| {
        let (base, fuel) = (values[0], values[1]);
        let nat = d.nat_ty();

        let motive_at = move |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let lhs = log_aux(d, &p, base, candidate, n);
            let body = d.le(lhs, candidate);
            d.pi_fv(n_fv, nat, body)
        };

        let base_case = move |d: &mut NatDev<'_>| -> ExprId {
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            let proof = d.lemma(p.le_refl, &[zero]);
            d.lam_fv(n_fv, nat, proof)
        };

        let step_case = move |d: &mut NatDev<'_>, predecessor: ExprId, ih: ExprId| -> ExprId {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let succ_predecessor = d.succ(predecessor);

            let quotient = d.div(n, base);
            let ih_at_quotient = d.apply(ih, &[quotient]);
            let inner_recursive = log_aux(d, &p, base, predecessor, quotient);
            let stepped = d.succ(inner_recursive);
            let stepped_le = d.lemma(
                p.le_succ_succ,
                &[inner_recursive, predecessor, ih_at_quotient],
            );

            let zero = d.zero();
            let zero_le_succ_pred = d.lemma(p.zero_le, &[succ_predecessor]);

            let two = d.num(2);
            let base_exceeds_one = d.ble(two, base);
            let inner_term = d.bool_select_nat(base_exceeds_one, stepped, zero);
            let inner_proof = le_of_bool_select(
                d,
                &p,
                base_exceeds_one,
                stepped,
                zero,
                succ_predecessor,
                stepped_le,
                zero_le_succ_pred,
            );

            let base_fits = d.ble(base, n);
            let outer_proof = le_of_bool_select(
                d,
                &p,
                base_fits,
                inner_term,
                zero,
                succ_predecessor,
                inner_proof,
                zero_le_succ_pred,
            );
            d.lam_fv(n_fv, nat, outer_proof)
        };

        let proof = d.induct(&motive_at, &base_case, &step_case, fuel);
        let stmt = motive_at(d, fuel);
        (stmt, proof)
    })?;

    // log_le_self : ∀ b n, Le (log b n) n -- `logAux_le_fuel` specialized at
    // `f := n`, since `log b n := logAux b n n` definitionally.
    d.theorem(p.log_le_self, 2, &|d, values| {
        let (base, value) = (values[0], values[1]);
        let lhs = log(d, &p, base, value);
        let stmt = d.le(lhs, value);
        let proof = d.lemma(p.log_aux_le_fuel, &[base, value, value]);
        (stmt, proof)
    })?;

    Ok(())
}
