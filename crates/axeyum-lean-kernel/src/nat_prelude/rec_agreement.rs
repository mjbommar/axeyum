//! Relating two independently-built `Nat.rec` instances: the universal
//! `∀ m n, Nat.bitwise f m n = <specialization> m n` theorems that
//! [`bitwise`](super::bitwise) explicitly declined, plus the two reusable
//! pieces it named as missing.
//!
//! # The boundary this file crosses
//!
//! `bitwise.rs`'s "what was NOT attempted" says, verbatim:
//!
//! > Closing that gap needs an induction relating two independently-built
//! > `Nat.rec` instances plus a `Nat.mod _ 2 ∈ {0, 1}` case-split lemma this
//! > prelude does not yet carry — real proof engineering, sized past this
//! > lane's scope.
//!
//! The `multichoose` lane hit the same wall from the opposite side (our
//! `choose (pred (add n k)) k` versus Mathlib's three-case double recursion),
//! so this is a recurring boundary rather than one file's gap. Both halves now
//! exist in [`ops`](super::ops) and are used here:
//!
//! - [`cases_mod_two`] — the `Nat.mod _ 2 ∈ {0, 1}` split, as an eliminator
//!   over a motive that varies with the remainder's value.
//! - [`agree_by_fuel_induction`] — induction on the shared fuel counter with
//!   **both** value arguments generalized in the motive. That generalization
//!   is the entire difficulty: `landAux`'s successor row recurses at
//!   `(m / 2, n / 2)`, so an induction hypothesis fixed at the theorem's own
//!   `m`, `n` is about arguments the step never mentions.
//!
//! # What made it tractable, and what the difficulty actually was
//!
//! **It is NOT the base cases, and that is worth stating because
//! `bitwise.rs`, `land.rs`, `lor.rs` and `ldiff.rs` all spend real prose on
//! how their fuel-exhaustion rows differ.** They differ from *each other*;
//! they do not differ from `bitwise`'s. `Nat.bitwiseAux`'s general row is
//! `if f false true then n else 0`, and evaluating a *concrete* `f` at those
//! two boundary `Bool` literals reproduces each sibling's hand-chosen row by
//! δβι alone, with no lemma:
//!
//! | sibling | `f false true` | general row reduces to | sibling's own row |
//! | --- | --- | --- | --- |
//! | `land` | `false` | `0` | `0` |
//! | `lor` | `true` | `n` | `n` |
//! | `ldiff` | `false` | `0` | `0` |
//!
//! and the same holds for the successor row's two zero-guards via
//! `f true false`. So every base case here is `d.refl`, and the alignment is
//! not a coincidence to be checked case by case — it is what
//! `Nat.bitwiseAux`'s "evaluate `f` at the boundary literals" design *is*.
//! The **fuel operand's absorbing zero** (the rule `land`/`lor`/`ldiff`
//! established, and which decides those rows) is therefore invisible to this
//! proof: it decided what each sibling's row had to be, and `bitwise` derives
//! the same answer from `f`.
//!
//! The whole difficulty is the successor row's **per-bit combine**, which is
//! where the two `Nat.rec` instances genuinely disagree syntactically:
//!
//! ```text
//! bitwiseAux : bool_select_nat (f (beq (m % 2) 1) (beq (n % 2) 1)) 1 0
//! landAux    : Nat.mul (m % 2) (n % 2)
//! lorAux     : bool_select_nat (ble (m % 2) (n % 2)) (n % 2) (m % 2)
//! ```
//!
//! At a symbolic `m` neither side reduces: `Nat.mod m 2` is stuck, so `beq`
//! is stuck, so `f` is stuck, and `Nat.mul` is stuck for the same reason. The
//! two agree at all four `{0, 1}` pairs and at nothing the kernel can see.
//! [`bit_agreement`] closes exactly this, by [`cases_mod_two`] on each
//! operand in turn — four leaves, each at concrete numerals, each `d.refl`.
//!
//! Everything else is one `d.congr` per differing subterm inside a shared
//! guard context ([`guarded`]) plus one `d.trans`. The IH supplies the
//! recursive call; [`bit_agreement`] supplies the bit; the guard scaffolding
//! is defeq on both sides and never has to be rewritten.
//!
//! # Why this file rather than `bitwise.rs`
//!
//! The theorems mention `Nat.bitwise` **and** a sibling, so they belong to
//! neither module: putting `bitwise_or_eq_lor` in `bitwise.rs` makes that file
//! depend on `lor.rs`'s per-bit encoding, and putting it in `lor.rs` makes
//! `lor.rs` depend on `bitwise.rs`'s `f`-threading. The shared machinery is in
//! `ops.rs` where the other eliminators live; the *use* of it is here.

use super::NatPrelude;
use super::bitwise::{and_fn, or_fn};
use super::helpers::{and_left, and_right};
use super::ops::{
    NatDev, NatOps, agree_by_double_fuel_induction, agree_by_fuel_induction, bool_select_nat_same,
    cases_lt_bound, cases_mod_two, cases_zero_succ,
};
use super::steps::absurd;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;

/// The shared shape of every `…Aux (succ k)` row in this family:
/// `if n = 0 then on_n_zero else if m = 0 then on_m_zero else
/// 2 * recursive + bit`.
///
/// The guard nesting order (`n = 0` OUTERMOST) is `land`/`lor`/`ldiff`'s and
/// `bitwise`'s alike — see `land.rs`'s module doc for why it is load-bearing
/// there. Here it only has to *match*, which it does on both sides, so the
/// scaffolding never needs rewriting: only `recursive` and `bit` move.
pub(super) fn guarded(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    on_n_zero: ExprId,
    on_m_zero: ExprId,
    recursive: ExprId,
    bit: ExprId,
) -> ExprId {
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.mul(two, recursive);
    let stepped = d.add(doubled, bit);
    let m_is_zero = d.beq(m, zero);
    let inner = d.bool_select_nat(m_is_zero, on_m_zero, stepped);
    let n_is_zero = d.beq(n, zero);
    d.bool_select_nat(n_is_zero, on_n_zero, inner)
}

/// `Eq (bool_select_nat (f (beq (m % 2) 1) (beq (n % 2) 1)) 1 0)
///     (combine (m % 2) (n % 2))` — the per-bit step of `Nat.bitwiseAux`
/// agrees with a specialization's own per-bit formula.
///
/// **The one place real proof content is needed.** Both sides are stuck at a
/// symbolic operand, and they are not definitionally equal — they are equal
/// only *given* that each `Nat.mod _ 2` is `0` or `1`. So this is
/// [`cases_mod_two`] on `m`, then on `n` inside each branch: four leaves at
/// concrete numerals where both sides compute to a literal and `d.refl`
/// closes.
///
/// `combine` is the specialization's formula (`Nat.mul` for `land`, `max` via
/// `ble` + `bool_select_nat` for `lor`); nothing here inspects it beyond
/// evaluating it at the four corners, so a new sibling costs one closure.
fn bit_agreement(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    combine: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bit_n = d.modulo(n, two);

    let general = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let one = d.num(1);
        let zero = d.zero();
        let x_bool = d.beq(x, one);
        let y_bool = d.beq(y, one);
        let combined = d.apply(f, &[x_bool, y_bool]);
        d.bool_select_nat(combined, one, zero)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let lhs = general(d, x, y);
        let rhs = combine(d, x, y);
        d.eq(lhs, rhs)
    };
    // At concrete `x`, `y` both sides evaluate to a literal, so `refl` on the
    // general side is accepted against the specialization's own value.
    let leaf = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let lhs = general(d, x, y);
        d.refl(lhs)
    };
    // Inner split on `n % 2`, at a first component already resolved to a
    // literal by the outer split.
    let inner = |d: &mut NatDev<'_>, x: ExprId| {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = leaf(d, x, zero);
        let at_one = leaf(d, x, one);
        cases_mod_two(d, &p, n, &|d, y| claim(d, x, y), at_zero, at_one)
    };

    let zero = d.zero();
    let one = d.num(1);
    let outer_zero = inner(d, zero);
    let outer_one = inner(d, one);
    cases_mod_two(d, &p, m, &|d, x| claim(d, x, bit_n), outer_zero, outer_one)
}

/// Declare `theorem name : ∀ m n, Eq (Nat.bitwise f m n) (top m n)`, where
/// `top`/`aux` are a specialization's public/auxiliary names and the three
/// closures describe its successor row.
///
/// **Two theorems land, not one, and the FUEL-GENERALIZED one is the
/// reusable half.** `aux_name` is
/// `∀ fuel m n, Eq (bitwiseAux f fuel m n) (aux fuel m n)` — true at
/// *arbitrary* fuel, sufficient or not — and `name` is the public
/// `∀ m n, Eq (bitwise f m n) (top m n)`, which is that lemma at
/// `fuel := m` plus the two definitional unfoldings. The general form is
/// exposed rather than left as an anonymous intermediate because it is what a
/// caller reasoning about a *non-canonical* fuel needs, and an inline step
/// with no name is this repository's most expensive hiding place.
///
/// **No fuel-irrelevance lemma is required, and the reason is structural**:
/// `Nat.bitwise f m n := bitwiseAux f m m n` and `top m n := aux m m n` put
/// the SAME expression `m` in the fuel slot, and the successor row steps both
/// sides to the same `k`. The two `Nat.rec` instances are therefore indexed by
/// **one** counter decrementing in lockstep, never by two that must be
/// reconciled. Note what the step does with it: the IH is used at fuel `k`
/// with operand `m / 2`, which is *not* that operand's canonical fuel — and
/// that is harmless precisely because agreement is proved fuel-parametrically,
/// so both sides carry the same non-canonical fuel. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_arguments)]
fn declare_bitwise_agreement(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    aux_name: NameId,
    name: NameId,
    f: ExprId,
    aux: NameId,
    top: NameId,
    on_n_zero: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    on_m_zero: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
    combine: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(aux_name, 3, &|d, values| {
        let fuel = values[0];
        let m = values[1];
        let n = values[2];

        let statement = |d: &mut NatDev<'_>, fuel: ExprId, x: ExprId, y: ExprId| {
            let lhs = d.const_app(p.bitwise_aux, &[f, fuel, x, y]);
            let rhs = d.const_app(aux, &[fuel, x, y]);
            d.eq(lhs, rhs)
        };
        // Fuel exhausted: `bitwiseAux`'s general row is
        // `if f false true then y else 0`, which for a concrete `f` reduces to
        // the sibling's own row by δβι. No lemma, no case split -- see the
        // module doc's table.
        let base = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let zero = d.zero();
            let lhs = d.const_app(p.bitwise_aux, &[f, zero, x, y]);
            d.refl(lhs)
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, x: ExprId, y: ExprId| {
            let one = d.num(1);
            let two = d.num(2);
            let zero = d.zero();
            let half_x = d.div(x, two);
            let half_y = d.div(y, two);
            let bit_x = d.modulo(x, two);
            let bit_y = d.modulo(y, two);

            let recursive_general = d.const_app(p.bitwise_aux, &[f, k, half_x, half_y]);
            let recursive_special = d.const_app(aux, &[k, half_x, half_y]);

            let x_bool = d.beq(bit_x, one);
            let y_bool = d.beq(bit_y, one);
            let combined = d.apply(f, &[x_bool, y_bool]);
            let bit_general = d.bool_select_nat(combined, one, zero);
            let bit_special = combine(d, bit_x, bit_y);

            let guard_n = on_n_zero(d, x, y);
            let guard_m = on_m_zero(d, x, y);

            // The IH is `∀ a b, …` -- applying it at the HALVED arguments is
            // exactly what generalizing the motive bought.
            let ih_at_halves = d.apply(ih, &[half_x, half_y]);
            let bit_eq = bit_agreement(d, &p, f, combine, x, y);

            let start = guarded(d, x, y, guard_n, guard_m, recursive_general, bit_general);
            let middle = guarded(d, x, y, guard_n, guard_m, recursive_special, bit_general);
            let finish = guarded(d, x, y, guard_n, guard_m, recursive_special, bit_special);

            let recursion_step = d.congr(
                recursive_general,
                recursive_special,
                ih_at_halves,
                &|d, hole| guarded(d, x, y, guard_n, guard_m, hole, bit_general),
            );
            let bit_step = d.congr(bit_general, bit_special, bit_eq, &|d, hole| {
                guarded(d, x, y, guard_n, guard_m, recursive_special, hole)
            });
            d.trans(start, middle, finish, recursion_step, bit_step)
        };

        let agreement = agree_by_fuel_induction(d, &statement, &base, &step, fuel);
        let proof = d.apply(agreement, &[m, n]);
        let stmt = statement(d, fuel, m, n);
        (stmt, proof)
    })?;

    // The public form: the fuel-generalized lemma at `fuel := m`, which is the
    // fuel both `Nat.bitwise` and `top` supply definitionally.
    d.theorem(name, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let proof = d.lemma(aux_name, &[m, m, n]);
        let lhs = d.const_app(p.bitwise, &[f, m, n]);
        let rhs = d.const_app(top, &[m, n]);
        let stmt = d.eq(lhs, rhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// `lt_two_cases : ∀ r, Lt r 2 → Or (Eq r 0) (Eq r 1)` — the propositional
/// form of the bounded split, for callers that want the disjunction rather
/// than an eliminator.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_lt_two_cases(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let two = d.num(2);
    let lt_ty = d.lt(r, two);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let goal_at = |d: &mut NatDev<'_>, x: ExprId| {
        let zero = d.zero();
        let one = d.num(1);
        let is_zero = d.eq(x, zero);
        let is_one = d.eq(x, one);
        let logic = d.prelude().logic;
        d.const_app(logic.or, &[is_zero, is_one])
    };
    let branch_zero = {
        let zero = d.zero();
        let one = d.num(1);
        let is_zero = d.eq(zero, zero);
        let is_one = d.eq(zero, one);
        let witness = d.refl(zero);
        let logic = d.prelude().logic;
        d.const_app(logic.or_inl, &[is_zero, is_one, witness])
    };
    let branch_one = {
        let zero = d.zero();
        let one = d.num(1);
        let is_zero = d.eq(one, zero);
        let is_one = d.eq(one, one);
        let witness = d.refl(one);
        let logic = d.prelude().logic;
        d.const_app(logic.or_inr, &[is_zero, is_one, witness])
    };

    let body = cases_lt_bound(d, &p, r, 2, h, &goal_at, &[branch_zero, branch_one]);
    let stmt = goal_at(d, r);
    let ty = {
        let inner = d.pi_fv(h_fv, lt_ty, stmt);
        d.pi_fv(r_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(h_fv, lt_ty, body);
        d.lam_fv(r_fv, nat, inner)
    };
    d.declare_theorem(p.lt_two_cases, ty, value)
}

/// `mod_two_eq_zero_or_one : ∀ n, Or (Eq (mod n 2) 0) (Eq (mod n 2) 1)` — the
/// `Nat.mod _ 2 ∈ {0, 1}` fact `bitwise.rs` named as missing, stated as a
/// standalone theorem (the eliminator form callers here use is
/// [`cases_mod_two`]).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_mod_two_eq_zero_or_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_two_eq_zero_or_one, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let remainder = d.modulo(n, two);
        let positive = d.zero_lt_succ(one);
        let bounded = d.lemma(p.mod_lt, &[n, two, positive]);
        let proof = d.lemma(p.lt_two_cases, &[remainder, bounded]);
        let is_zero = d.eq(remainder, zero);
        let is_one = d.eq(remainder, one);
        let logic = d.prelude().logic;
        let stmt = d.const_app(logic.or, &[is_zero, is_one]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare the `mod 2` split and the two universal
/// `bitwise f = <specialization>` agreement theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_rec_agreement_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    declare_lt_two_cases(d, &p)?;
    declare_mod_two_eq_zero_or_one(d, &p)?;

    // bitwise_and_eq_land : ∀ m n, Eq (bitwise and_fn m n) (land m n).
    // `landAux`'s successor row selects the constant `0` under both guards
    // (AND's absorbing zero) and combines bits by `Nat.mul`.
    let and_ = and_fn(d);
    declare_bitwise_agreement(
        d,
        &p,
        p.bitwise_aux_eq_land_aux,
        p.bitwise_and_eq_land,
        and_,
        p.land_aux,
        p.land,
        &|d, _m, _n| d.zero(),
        &|d, _m, _n| d.zero(),
        &|d, x, y| d.mul(x, y),
    )?;

    // bitwise_or_eq_lor : ∀ m n, Eq (bitwise or_fn m n) (lor m n).
    // `lorAux` has NO absorbing zero on either guard -- `n = 0` returns `m`
    // and `m = 0` returns `n` -- and combines bits by `max`, built from
    // `Nat.ble` + `bool_select_nat`. Both differences are absorbed by the
    // parameters; the proof term is otherwise identical to `land`'s, which is
    // the point of routing them through one builder.
    let or_ = or_fn(d);
    declare_bitwise_agreement(
        d,
        &p,
        p.bitwise_aux_eq_lor_aux,
        p.bitwise_or_eq_lor,
        or_,
        p.lor_aux,
        p.lor,
        &|_d, m, _n| m,
        &|_d, _m, n| n,
        &|d, x, y| {
            let le = d.ble(x, y);
            d.bool_select_nat(le, y, x)
        },
    )?;

    Ok(())
}

// ============================================================================
// Fuel-irrelevance for `landAux`: the blocker named by `land_comm`,
// `land_assoc`, `land_bit`, `lor_comm`, `lor_assoc`, `lor_bit`, `ldiff_bit`.
//
// # The statement, and why THIS hypothesis
//
// "Sufficient fuel" is `Le m fuel`: the canonical call `landAux m m n` puts
// `m` in the fuel slot, the recursion HALVES the value argument every step,
// and a caller unfolding `landAux` at a bigger fuel (e.g. `fuel = bit a m`,
// `land_bit`'s shape) always arrives with MORE fuel than canonical, never
// less. `landAux 0 m n` for `m > 0` is genuinely `0` while `land m n` need
// not be, so the statement must require `fuel` at least sufficient, not hold
// at arbitrary fuel — this is exactly why `Le m fuel`, not no hypothesis at
// all, has to appear.
//
// # Why the core lemma compares two fuels, not fuel-vs-canonical
//
// The brief's suggested shape,
// `fun fuel => ∀ m n, Le m fuel → Eq (landAux fuel m n) (land m n)`, is
// directly expressible in [`agree_by_fuel_induction`] — but PROVING it by
// induction on `fuel` alone runs into the same self-reference the
// `declare_bitwise_agreement` route above deliberately avoids: `land m n`
// unfolds to `landAux m m n`, which puts the SAME value `m` in the fuel
// slot, so relating it to `landAux (succ k) m n` (`k` from the induction)
// requires `landAux m m n` to unfold via `m`'s own shape — and once `m` is
// exposed as `succ predecessor`, the recursive call on THAT side is at fuel
// `predecessor`, a value the outer induction's hypothesis (fixed at fuel
// `k`) says nothing about.
//
// The fix is to generalize over BOTH fuels at once
// ([`agree_by_double_fuel_induction`]):
// `∀ fuel1 m n fuel2, Le m fuel1 → Le m fuel2 →
//   Eq (landAux fuel1 m n) (landAux fuel2 m n)`.
// This is symmetric in which fuel is "the" canonical one, so it NEVER needs
// `landAux`'s own canonical instance to unfold — both sides are compared as
// independently-chosen sufficient fuels, and `land_aux_eq_land_of_le`
// becomes a one-line corollary at `fuel2 := m` (`land m n` and
// `landAux m m n` are the SAME term by definition, so the kernel accepts the
// double-fuel proof directly against the `land`-headed statement via
// defeq).
//
// # The two case splits this needs, and why each is unavoidable
//
// Induction is on `fuel1`. The base case (`fuel1 = 0`) needs no case split
// at all: `landAux 0 m n` is the constant-`0` row for ANY `m`, `n`
// ([`declare_land_aux_zero_left_any_fuel`] gives the same for the OTHER
// side, `landAux fuel2 0 n`, once `m = 0` is derived from `Le m 0`).
//
// The step (`fuel1 = succ k`) needs a case split on `m` — NOT on `n` — to
// expose whether `landAux(succ k) m n`'s inner `m = 0` guard is decidable by
// reduction. At `m = 0` BOTH sides are `0`
// ([`declare_land_aux_zero_left_any_fuel`] again, no hypotheses needed). At
// `m = succ predecessor`, `beq (succ predecessor) zero` reduces to `false`
// on BOTH sides (the guard only mentions `m`, not the fuel), so the guard
// scaffolding is IDENTICAL on both sides and [`d.congr`](NatOps::congr)
// reduces the goal to the recursive sub-terms alone: `landAux k half half'`
// vs `landAux f2' half half'`, where `f2' := pred fuel2` (fuel2 is positive
// since it's `≥ succ predecessor ≥ 1`, so [`NatPrelude::succ_pred_of_pos`]
// applies). The IH — `∀ a b c, Le a k → Le a c → Eq (landAux k a b)
// (landAux c a b)` — closes this at `a := half`, `b := half'`, `c := f2'`,
// given `Le half k` and `Le half f2'`, both from
// [`half_le_predecessor_of_succ`] (the same "half of a positive value is
// below the fuel that bounds its successor" arithmetic `pow_sq_aux_eq_pow`
// and `size_aux_lt_pow` each derive for their own fuel families).
//
// This case split does NOT need `bool_select_nat_same`: unlike the `m = 0`
// branch (where the OUTER `n = 0` guard stays symbolic and both its
// branches literally are `0`), at `m = succ predecessor` the guard itself
// reduces (`beq (succ _) zero ≡ false`), so no "both branches agree
// regardless of the guard" argument is needed here.
//
// # Transport to `lorAux`/`ldiffAux` — what is generic and what is not
//
// [`agree_by_double_fuel_induction`], [`half_le_predecessor_of_succ`], and
// `n_lt_mul_two` are ENTIRELY generic — none of them mention `land`'s
// absorbing zero, and they transport to `lorAux`/`ldiffAux` UNCHANGED. What
// does NOT transport unchanged is `declare_land_aux_zero_left_any_fuel`:
// `lorAux`'s fuel-exhaustion row returns `n`, not `0`
// ([`super::lor`]'s module doc), so its "any fuel" analogue is
// `Eq (lorAux fuel 0 n) n`, proved the same way (a `bool_select_nat_same`
// call in the `succ` branch) but with a different closing value. The `m =
// succ predecessor` step's proof body is otherwise a direct transcription —
// same case split, same IH application, same congr — with `lor`'s own
// `on_n_zero`/`on_m_zero`/`combine` closures from [`declare_rec_agreement_all`]
// dropped in. `ldiffAux` shares `land`'s absorbing-zero base case exactly
// (see `super::ldiff`'s module doc), so its `any_fuel` lemma is a byte-for-byte
// copy of `land`'s with the name and `p.ldiff_aux` swapped in.

/// `bound : Le (succ predecessor) (succ k) ⊢ Le (div (succ predecessor) two) k`.
///
/// The fuel-sufficiency step every `…Aux` fuel-bound proof in this prelude
/// needs (`Nat.log_aux_le_fuel`, `Nat.size_aux_lt_pow`,
/// `Nat.pow_sq_aux_eq_pow`): from positivity of `e := succ predecessor`,
/// `e < 2*e` ([`n_lt_mul_two`]), hence (via `div_mod_lt_mul_iff`) `e/2 < e`,
/// hence (combined with `bound`) `e/2 < succ k`, hence `e/2 ≤ k`. A direct
/// copy of the derivation inline in `powsq.rs`'s `declare_powsq_eq_pow`
/// (that copy is not exposed, and `powsq.rs` is out of this lane's scope) —
/// this is the fourth site with this exact arithmetic (`log.rs`, `binary.rs`,
/// `powsq.rs`), always duplicated because each fuel family's `…Aux` type
/// differs and there is nothing generic to promote it to.
///
/// `pub(super)` (not private) because it mentions no `land`/`lor`-specific
/// name or type — `bitwise.rs`'s generalized-`f` fuel machinery reuses it
/// directly rather than duplicating a fifth copy.
pub(super) fn half_le_predecessor_of_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    predecessor: ExprId,
    k: ExprId,
    bound: ExprId,
) -> ExprId {
    let p = *p;
    let e = d.succ(predecessor);
    let two = d.num(2);
    let one = d.num(1);
    let half = d.div(e, two);
    let r = d.modulo(e, two);
    let pos = d.zero_lt_succ(predecessor);
    let e_lt_2e = n_lt_mul_two(d, &p, e, pos);

    let h_exec = d.lemma(p.div_mod_exec, &[one, e]);
    let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[two, e, half, r, e]);
    let the_iff = d.apply(iff_fn, &[h_exec]);
    let mul_two_e = d.mul(two, e);
    let lt_e_2e_ty = d.lt(e, mul_two_e);
    let lt_half_e_ty = d.lt(half, e);
    let forward = super::helpers::iff_forward(d, lt_e_2e_ty, lt_half_e_ty, the_iff);
    let half_lt_e = d.apply(forward, &[e_lt_2e]);

    let sk = d.succ(k);
    let half_lt_sk = d.lemma(p.lt_of_lt_of_le, &[half, e, sk, half_lt_e, bound]);
    d.lemma(p.le_of_succ_le_succ, &[half, k, half_lt_sk])
}

/// `h : Lt zero n ⊢ Lt n (mul two n)`. A direct copy of `powsq.rs`'s private
/// `n_lt_mul_two` (itself a copy of `binary.rs`'s — `powsq.rs`'s module doc
/// notes this is already the third instance; this is the fourth, unavoidable
/// because both source modules are outside this lane's scope): `n < n+n`
/// from `0 < n` via `add_lt_add_left` (at `add n zero`, restored to `n` by
/// `add_zero`), then `n+n = mul (succ one) n` via `succ_mul`/`one_mul`.
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

/// `land_aux_zero_left_any_fuel : ∀ fuel n, Eq (landAux fuel 0 n) 0` — holds
/// at ANY fuel, sufficient or not, unlike [`NatPrelude::land_zero_left`]
/// (which needs no lemma because `Nat.land` supplies fuel `= m = 0`
/// automatically). Case-split on `fuel` alone ([`cases_zero_succ`]), no
/// induction hypothesis: at `fuel = 0` the base row is the constant `0`
/// regardless of `m`, `n` (`refl`); at `fuel = succ f` the `m = 0` guard is
/// LITERAL (`m` is the numeral `0`), so it fires by δι alone, short-circuiting
/// the recursive call entirely — only the outer, still-symbolic `n = 0` guard
/// needs [`bool_select_nat_same`] to collapse its two IDENTICAL `0` branches.
fn declare_land_aux_zero_left_any_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_aux_zero_left_any_fuel, 2, &|d, values| {
        let fuel = values[0];
        let n = values[1];
        let zero = d.zero();
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let lhs = d.const_app(p.land_aux, &[candidate, zero, n]);
            d.eq(lhs, zero)
        };
        let proof = cases_zero_succ(
            d,
            fuel,
            &statement_at,
            &|d| {
                let lhs = d.const_app(p.land_aux, &[zero, zero, n]);
                d.refl(lhs)
            },
            &|d, _predecessor| {
                let n_is_zero = d.beq(n, zero);
                bool_select_nat_same(d, &p, n_is_zero, zero)
            },
        );
        let stmt = statement_at(d, fuel);
        (stmt, proof)
    })?;
    Ok(())
}

/// `land_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m fuel2 →
///   Eq (landAux fuel1 m n) (landAux fuel2 m n)`. See the section doc above
/// this block for the full derivation; this is
/// [`agree_by_double_fuel_induction`]'s instantiation.
fn declare_land_aux_agree_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel1: ExprId, m: ExprId, n: ExprId, fuel2: ExprId| {
        let bound1 = d.le(m, fuel1);
        let bound2 = d.le(m, fuel2);
        let lhs = d.const_app(p.land_aux, &[fuel1, m, n]);
        let rhs = d.const_app(p.land_aux, &[fuel2, m, n]);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound2, concl);
        d.arrow(bound1, inner)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(m, zero);
        let bound2_ty = d.le(m, fuel2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        // `Le m 0` + `zero_le m` ⊢ `Eq m 0` (only hypothesis actually used;
        // `h2` is bound only to give the arrow its declared type).
        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, h1, zero_le_m]);

        let left_term = d.const_app(p.land_aux, &[zero, m, n]);
        let right_term = d.const_app(p.land_aux, &[fuel2, m, n]);
        let left_is_zero = d.refl(zero);

        let right_at_zero = d.const_app(p.land_aux, &[fuel2, zero, n]);
        let right_congr = d.congr(m, zero, m_eq_zero, &|d, x| {
            d.const_app(p.land_aux, &[fuel2, x, n])
        });
        let any_fuel = d.lemma(p.land_aux_zero_left_any_fuel, &[fuel2, n]);
        let (_, right_is_zero) = d.chain(
            right_term,
            &[(right_at_zero, right_congr), (zero, any_fuel)],
        );
        let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);

        let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);
        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>,
                k: ExprId,
                ih: ExprId,
                m: ExprId,
                n: ExprId,
                fuel2: ExprId|
     -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, fuel2);
            let lhs = d.const_app(p.land_aux, &[sk, candidate, n]);
            let rhs = d.const_app(p.land_aux, &[fuel2, candidate, n]);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        cases_zero_succ(
            d,
            m,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, fuel2);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let left_term = d.const_app(p.land_aux, &[sk, zero, n]);
                let right_term = d.const_app(p.land_aux, &[fuel2, zero, n]);
                let left_is_zero = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, n]);
                let right_is_zero = d.lemma(p.land_aux_zero_left_any_fuel, &[fuel2, n]);
                let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);
                let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, fuel2);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let two = d.num(2);
                let half = d.div(succ_pred, two);
                let half_n = d.div(n, two);
                let bit_m = d.modulo(succ_pred, two);
                let bit_n = d.modulo(n, two);
                let bit_and = d.mul(bit_m, bit_n);

                // Both sides' inner `m = 0` guard reduces to `false` (`m`
                // is the literal `succ predecessor`), leaving the
                // recursive sub-term as the only difference.
                let half_le_k = half_le_predecessor_of_succ(d, &p, predecessor, k, h1);

                // `fuel2` is positive (`≥ succ predecessor ≥ 1`), so it is
                // `succ (pred fuel2)`; rewrite `h2` along that to get the
                // shape `half_le_predecessor_of_succ` needs.
                let one = d.num(1);
                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_fuel2 =
                    d.lemma(p.le_trans, &[one, succ_pred, fuel2, one_le_succ_pred, h2]);
                // `succ_pred_of_pos(c, h) : Eq c (succ (pred c))` -- note the
                // direction, `c` on the LEFT (see `two_divisor_dichotomy`'s
                // own `Eq.rec` usage, which transports FROM `c` TO
                // `succ (pred c)` directly with no `symm`).
                let succ_pred_fuel2 = d.lemma(p.succ_pred_of_pos, &[fuel2, one_le_fuel2]);
                let f2p = d.pred(fuel2);
                let succ_f2p = d.succ(f2p);
                let h2_motive = d.eq_motive(fuel2, &|d, x| d.le(succ_pred, x));
                let h2_at_succ_f2p = d.transport(fuel2, h2_motive, h2, succ_f2p, succ_pred_fuel2);
                let half_le_f2p =
                    half_le_predecessor_of_succ(d, &p, predecessor, f2p, h2_at_succ_f2p);

                let ih_at_half = d.apply(ih, &[half, half_n, f2p]);
                let ih_at_half = d.apply(ih_at_half, &[half_le_k, half_le_f2p]);
                // ih_at_half : Eq (landAux k half half_n) (landAux f2p half half_n)

                let recursive_general = d.const_app(p.land_aux, &[k, half, half_n]);
                let recursive_at_f2p = d.const_app(p.land_aux, &[f2p, half, half_n]);

                let zero = d.zero();
                let start = guarded(d, succ_pred, n, zero, zero, recursive_general, bit_and);
                let mid = guarded(d, succ_pred, n, zero, zero, recursive_at_f2p, bit_and);
                let inner_step = d.congr(
                    recursive_general,
                    recursive_at_f2p,
                    ih_at_half,
                    &|d, hole| {
                        let zero = d.zero();
                        guarded(d, succ_pred, n, zero, zero, hole, bit_and)
                    },
                );

                // `outer_step : Eq (landAux fuel2 succ_pred n) (landAux
                // succ_f2p succ_pred n)` -- `succ_pred_fuel2`'s direction
                // puts `fuel2` on the left, so `congr`'s `a` is `fuel2` here
                // too; `symm` flips it to match `d.trans`'s `mid -> final`
                // slot.
                let outer_step = d.congr(fuel2, succ_f2p, succ_pred_fuel2, &|d, x| {
                    d.const_app(p.land_aux, &[x, succ_pred, n])
                });
                let final_target = d.const_app(p.land_aux, &[fuel2, succ_pred, n]);
                let mid2 = d.const_app(p.land_aux, &[succ_f2p, succ_pred, n]);
                let outer_step_rev = d.symm(final_target, mid2, outer_step);

                let body = d.trans(start, mid, final_target, inner_step, outer_step_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    let fuel1_fv = d.fresh_fvar();
    let fuel1 = d.kernel().fvar(fuel1_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel1);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fuel2_fv = d.fresh_fvar();
    let fuel2 = d.kernel().fvar(fuel2_fv);
    let applied = d.apply(proof_fn, &[m, n, fuel2]);
    let ty = {
        let body = statement(d, fuel1, m, n, fuel2);
        let with_fuel2 = d.pi_fv(fuel2_fv, nat, body);
        let with_n = d.pi_fv(n_fv, nat, with_fuel2);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel1_fv, nat, with_m)
    };
    let value = {
        let with_fuel2 = d.lam_fv(fuel2_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_fuel2);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel1_fv, nat, with_m)
    };
    d.declare_theorem(p.land_aux_agree_of_fuel, ty, value)
}

/// `land_aux_eq_land_of_le : ∀ fuel m n, Le m fuel → Eq (landAux fuel m n)
/// (land m n)` — the brief's requested statement, a one-line corollary of
/// [`declare_land_aux_agree_of_fuel`] at `fuel2 := m` via `le_refl`: `land m
/// n` and `landAux m m n` are the SAME term by definition, so the kernel
/// accepts the double-fuel proof directly against this `land`-headed
/// statement via defeq, with no extra proof step.
fn declare_land_aux_eq_land_of_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_aux_eq_land_of_le, 3, &|d, values| {
        let fuel = values[0];
        let m = values[1];
        let n = values[2];
        let bound_ty = d.le(m, fuel);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let le_refl_m = d.lemma(p.le_refl, &[m]);
        let agree = d.lemma(p.land_aux_agree_of_fuel, &[fuel, m, n, m]);
        let agree = d.apply(agree, &[bound, le_refl_m]);
        let lhs = d.const_app(p.land_aux, &[fuel, m, n]);
        let rhs = d.const_app(p.land, &[m, n]);
        let stmt = d.eq(lhs, rhs);
        let inner_ty = d.arrow(bound_ty, stmt);
        let value = d.lam_fv(bound_fv, bound_ty, agree);
        (inner_ty, value)
    })?;
    Ok(())
}

/// Declare fuel-irrelevance for `landAux` (see the section doc above). See
/// [`declare_lor_fuel_irrelevance_all`]/[`declare_ldiff_fuel_irrelevance_all`]
/// for the transport to the other two auxiliaries.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_fuel_irrelevance_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_aux_zero_left_any_fuel(d, p)?;
    declare_land_aux_agree_of_fuel(d, p)?;
    declare_land_aux_eq_land_of_le(d, p)?;
    Ok(())
}

// ============================================================================
// Transport to `lorAux`.
//
// The generic machinery ([`agree_by_double_fuel_induction`],
// [`half_le_predecessor_of_succ`], `n_lt_mul_two`) carries over UNCHANGED —
// none of it mentions `land`'s absorbing zero. Two things do NOT transport
// unchanged, and only one of them is the one the handoff named:
//
// - The "any fuel" closing value is `n`, not `0` (`lorAux`'s fuel-exhaustion
//   row RETURNS `n` — see `lor.rs`'s module doc) — anticipated.
// - **[`declare_lor_aux_zero_left_any_fuel`]'s `succ`-branch proof needs an
//   EXTRA case split the handoff did not name.** At `m = 0` (fixed) and
//   `fuel = succ f`, the outer `n = 0` guard's two branches are `m` (= `0`,
//   literal) and the reduced inner term (= `n`, since the `m = 0` guard
//   fires) — two DIFFERENT terms, not one term repeated, so
//   [`bool_select_nat_same`] does not apply the way it does for `land`'s
//   analogue (there, BOTH branches independently reduce to the identical
//   literal `0`). The fix is a nested [`cases_zero_succ`] on `n` itself,
//   inside the `fuel = succ f` branch: once `n`'s shape is exposed, the
//   outer guard's boolean reduces by δι and both leaves close by `refl`.
//   This is genuinely the "careless transport breaks" case the brief warned
//   about, and it is `lor`'s zero-fuel row, not `lor`'s guard order, that
//   causes it.
// ============================================================================

/// `lor_aux_zero_left_any_fuel : ∀ fuel n, Eq (lorAux fuel 0 n) n` — see the
/// section doc above for why this needs an extra case split `land`'s
/// analogue does not.
fn declare_lor_aux_zero_left_any_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lor_aux_zero_left_any_fuel, 2, &|d, values| {
        let fuel = values[0];
        let n = values[1];
        let zero = d.zero();
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let lhs = d.const_app(p.lor_aux, &[candidate, zero, n]);
            d.eq(lhs, n)
        };
        let proof = cases_zero_succ(
            d,
            fuel,
            &statement_at,
            &|d| {
                // fuel = 0: `lorAux`'s base row IGNORES `m` and returns `n`
                // directly (beta alone) -- no case split on `n` needed here,
                // unlike the succ branch below.
                let lhs = d.const_app(p.lor_aux, &[zero, zero, n]);
                d.refl(lhs)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let n_goal = |d: &mut NatDev<'_>, candidate_n: ExprId| -> ExprId {
                    let lhs = d.const_app(p.lor_aux, &[succ_pred, zero, candidate_n]);
                    d.eq(lhs, candidate_n)
                };
                // `n = 0`: outer guard fires -> `m` (= `0`), goal `Eq 0 0`.
                // `n = succ n_pred`: outer guard false -> inner guard
                // (`m = 0`, literal) fires -> `n`, goal `Eq (succ n_pred)
                // (succ n_pred)`. Both close by `refl` once `n`'s shape is
                // exposed, matching `lor_zero_right`'s own guard-collapsing
                // shape.
                cases_zero_succ(
                    d,
                    n,
                    &n_goal,
                    &|d| {
                        let lhs = d.const_app(p.lor_aux, &[succ_pred, zero, zero]);
                        d.refl(lhs)
                    },
                    &|d, n_pred| {
                        let succ_n_pred = d.succ(n_pred);
                        let lhs = d.const_app(p.lor_aux, &[succ_pred, zero, succ_n_pred]);
                        d.refl(lhs)
                    },
                )
            },
        );
        let stmt = statement_at(d, fuel);
        (stmt, proof)
    })?;
    Ok(())
}

/// `lor_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m fuel2 →
///   Eq (lorAux fuel1 m n) (lorAux fuel2 m n)` —
/// [`declare_land_aux_agree_of_fuel`]'s `lor` twin. What differs: the "any
/// fuel" closing value (`n`, not `0` — [`declare_lor_aux_zero_left_any_fuel`])
/// and the guard/bit-combine shapes in the `m = succ predecessor` step:
/// `lorAux`'s guards are `on_n_zero = m`, `on_m_zero = n` (both
/// pass-through — the OPPOSITE of `land`'s absorbing-zero pair), and the
/// per-bit combine is `max` via `Nat.ble` + `bool_select_nat`, not `mul`.
fn declare_lor_aux_agree_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel1: ExprId, m: ExprId, n: ExprId, fuel2: ExprId| {
        let bound1 = d.le(m, fuel1);
        let bound2 = d.le(m, fuel2);
        let lhs = d.const_app(p.lor_aux, &[fuel1, m, n]);
        let rhs = d.const_app(p.lor_aux, &[fuel2, m, n]);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound2, concl);
        d.arrow(bound1, inner)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(m, zero);
        let bound2_ty = d.le(m, fuel2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        // `Le m 0` + `zero_le m` ⊢ `Eq m 0` (only hypothesis actually used).
        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, h1, zero_le_m]);

        let left_term = d.const_app(p.lor_aux, &[zero, m, n]);
        let right_term = d.const_app(p.lor_aux, &[fuel2, m, n]);
        // `lorAux 0 m n` reduces to `n` for ANY `m` (its base row ignores
        // `m` entirely), so no `m_eq_zero` step is needed for the LHS,
        // unlike the RHS below.
        let left_is_n = d.refl(n);

        let right_at_zero = d.const_app(p.lor_aux, &[fuel2, zero, n]);
        let right_congr = d.congr(m, zero, m_eq_zero, &|d, x| {
            d.const_app(p.lor_aux, &[fuel2, x, n])
        });
        let any_fuel = d.lemma(p.lor_aux_zero_left_any_fuel, &[fuel2, n]);
        let (_, right_is_n) = d.chain(right_term, &[(right_at_zero, right_congr), (n, any_fuel)]);
        let right_is_n_rev = d.symm(right_term, n, right_is_n);

        let body = d.trans(left_term, n, right_term, left_is_n, right_is_n_rev);
        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>,
                k: ExprId,
                ih: ExprId,
                m: ExprId,
                n: ExprId,
                fuel2: ExprId|
     -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, fuel2);
            let lhs = d.const_app(p.lor_aux, &[sk, candidate, n]);
            let rhs = d.const_app(p.lor_aux, &[fuel2, candidate, n]);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        cases_zero_succ(
            d,
            m,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, fuel2);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let left_term = d.const_app(p.lor_aux, &[sk, zero, n]);
                let right_term = d.const_app(p.lor_aux, &[fuel2, zero, n]);
                let left_is_n = d.lemma(p.lor_aux_zero_left_any_fuel, &[sk, n]);
                let right_is_n = d.lemma(p.lor_aux_zero_left_any_fuel, &[fuel2, n]);
                let right_is_n_rev = d.symm(right_term, n, right_is_n);
                let body = d.trans(left_term, n, right_term, left_is_n, right_is_n_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, fuel2);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let two = d.num(2);
                let half = d.div(succ_pred, two);
                let half_n = d.div(n, two);
                let bit_m = d.modulo(succ_pred, two);
                let bit_n = d.modulo(n, two);
                let bit_m_le_bit_n = d.ble(bit_m, bit_n);
                let bit_or = d.bool_select_nat(bit_m_le_bit_n, bit_n, bit_m);

                let half_le_k = half_le_predecessor_of_succ(d, &p, predecessor, k, h1);

                let one = d.num(1);
                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_fuel2 =
                    d.lemma(p.le_trans, &[one, succ_pred, fuel2, one_le_succ_pred, h2]);
                // `succ_pred_of_pos(c, h) : Eq c (succ (pred c))` -- `c` on
                // the LEFT, same direction note as `land`'s analogue.
                let succ_pred_fuel2 = d.lemma(p.succ_pred_of_pos, &[fuel2, one_le_fuel2]);
                let f2p = d.pred(fuel2);
                let succ_f2p = d.succ(f2p);
                let h2_motive = d.eq_motive(fuel2, &|d, x| d.le(succ_pred, x));
                let h2_at_succ_f2p = d.transport(fuel2, h2_motive, h2, succ_f2p, succ_pred_fuel2);
                let half_le_f2p =
                    half_le_predecessor_of_succ(d, &p, predecessor, f2p, h2_at_succ_f2p);

                let ih_at_half = d.apply(ih, &[half, half_n, f2p]);
                let ih_at_half = d.apply(ih_at_half, &[half_le_k, half_le_f2p]);
                // ih_at_half : Eq (lorAux k half half_n) (lorAux f2p half half_n)

                let recursive_general = d.const_app(p.lor_aux, &[k, half, half_n]);
                let recursive_at_f2p = d.const_app(p.lor_aux, &[f2p, half, half_n]);

                // `on_n_zero = succ_pred` (= `m`), `on_m_zero = n` -- both
                // pass-through, matching `lorAux`'s guard shape (see
                // `lor.rs`'s module doc), the opposite of `land`'s
                // absorbing-zero pair.
                let start = guarded(d, succ_pred, n, succ_pred, n, recursive_general, bit_or);
                let mid = guarded(d, succ_pred, n, succ_pred, n, recursive_at_f2p, bit_or);
                let inner_step = d.congr(
                    recursive_general,
                    recursive_at_f2p,
                    ih_at_half,
                    &|d, hole| guarded(d, succ_pred, n, succ_pred, n, hole, bit_or),
                );

                let outer_step = d.congr(fuel2, succ_f2p, succ_pred_fuel2, &|d, x| {
                    d.const_app(p.lor_aux, &[x, succ_pred, n])
                });
                let final_target = d.const_app(p.lor_aux, &[fuel2, succ_pred, n]);
                let mid2 = d.const_app(p.lor_aux, &[succ_f2p, succ_pred, n]);
                let outer_step_rev = d.symm(final_target, mid2, outer_step);

                let body = d.trans(start, mid, final_target, inner_step, outer_step_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    let fuel1_fv = d.fresh_fvar();
    let fuel1 = d.kernel().fvar(fuel1_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel1);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fuel2_fv = d.fresh_fvar();
    let fuel2 = d.kernel().fvar(fuel2_fv);
    let applied = d.apply(proof_fn, &[m, n, fuel2]);
    let ty = {
        let body = statement(d, fuel1, m, n, fuel2);
        let with_fuel2 = d.pi_fv(fuel2_fv, nat, body);
        let with_n = d.pi_fv(n_fv, nat, with_fuel2);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel1_fv, nat, with_m)
    };
    let value = {
        let with_fuel2 = d.lam_fv(fuel2_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_fuel2);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel1_fv, nat, with_m)
    };
    d.declare_theorem(p.lor_aux_agree_of_fuel, ty, value)
}

/// `lor_aux_eq_lor_of_le : ∀ fuel m n, Le m fuel → Eq (lorAux fuel m n) (lor
/// m n)` — [`declare_land_aux_eq_land_of_le`]'s `lor` twin, the same
/// one-line corollary of [`declare_lor_aux_agree_of_fuel`] at `fuel2 := m`.
fn declare_lor_aux_eq_lor_of_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lor_aux_eq_lor_of_le, 3, &|d, values| {
        let fuel = values[0];
        let m = values[1];
        let n = values[2];
        let bound_ty = d.le(m, fuel);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let le_refl_m = d.lemma(p.le_refl, &[m]);
        let agree = d.lemma(p.lor_aux_agree_of_fuel, &[fuel, m, n, m]);
        let agree = d.apply(agree, &[bound, le_refl_m]);
        let lhs = d.const_app(p.lor_aux, &[fuel, m, n]);
        let rhs = d.const_app(p.lor, &[m, n]);
        let stmt = d.eq(lhs, rhs);
        let inner_ty = d.arrow(bound_ty, stmt);
        let value = d.lam_fv(bound_fv, bound_ty, agree);
        (inner_ty, value)
    })?;
    Ok(())
}

/// Declare fuel-irrelevance for `lorAux` (see the section doc above).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_lor_fuel_irrelevance_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_lor_aux_zero_left_any_fuel(d, p)?;
    declare_lor_aux_agree_of_fuel(d, p)?;
    declare_lor_aux_eq_lor_of_le(d, p)?;
    Ok(())
}

// ============================================================================
// Transport to `ldiffAux`.
//
// `ldiffAux` shares `land`'s absorbing-zero base case EXACTLY (`ldiff.rs`'s
// module doc: `m` is both the fuel and the absorbing-zero operand, same as
// `land`), so [`declare_ldiff_aux_zero_left_any_fuel`] is a byte-for-byte
// copy of [`declare_land_aux_zero_left_any_fuel`] with the name and
// `p.ldiff_aux` swapped in -- no extra case split, unlike `lor`.
//
// The inner succ-row guard is a HYBRID, though: `on_n_zero = m`
// (pass-through, `ldiff m 0 = m`, `lor`'s shape) and `on_m_zero = 0`
// (absorbing, `ldiff 0 n = 0`, `land`'s shape). The per-bit combine is
// `bool_select_nat (beq (n%2) 0) (m%2) 0`, `ldiff.rs`'s own formula.
// ============================================================================

/// `ldiff_aux_zero_left_any_fuel : ∀ fuel n, Eq (ldiffAux fuel 0 n) 0` — a
/// byte-for-byte copy of [`declare_land_aux_zero_left_any_fuel`]'s proof
/// (see the section doc above for why `ldiff` needs no extra case split).
fn declare_ldiff_aux_zero_left_any_fuel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.ldiff_aux_zero_left_any_fuel, 2, &|d, values| {
        let fuel = values[0];
        let n = values[1];
        let zero = d.zero();
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let lhs = d.const_app(p.ldiff_aux, &[candidate, zero, n]);
            d.eq(lhs, zero)
        };
        let proof = cases_zero_succ(
            d,
            fuel,
            &statement_at,
            &|d| {
                let lhs = d.const_app(p.ldiff_aux, &[zero, zero, n]);
                d.refl(lhs)
            },
            &|d, _predecessor| {
                let n_is_zero = d.beq(n, zero);
                bool_select_nat_same(d, &p, n_is_zero, zero)
            },
        );
        let stmt = statement_at(d, fuel);
        (stmt, proof)
    })?;
    Ok(())
}

/// `ldiff_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m fuel2 →
///   Eq (ldiffAux fuel1 m n) (ldiffAux fuel2 m n)` —
/// [`declare_land_aux_agree_of_fuel`]'s `ldiff` twin. The base case and the
/// `m = 0` step sub-case transport unchanged (same absorbing-zero shape as
/// `land`); what differs is the `m = succ predecessor` step's guard/bit
/// shapes: `on_n_zero = m` (pass-through, `lor`'s shape), `on_m_zero = 0`
/// (absorbing, `land`'s shape), per-bit combine
/// `bool_select_nat (beq (n%2) 0) (m%2) 0`.
fn declare_ldiff_aux_agree_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel1: ExprId, m: ExprId, n: ExprId, fuel2: ExprId| {
        let bound1 = d.le(m, fuel1);
        let bound2 = d.le(m, fuel2);
        let lhs = d.const_app(p.ldiff_aux, &[fuel1, m, n]);
        let rhs = d.const_app(p.ldiff_aux, &[fuel2, m, n]);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound2, concl);
        d.arrow(bound1, inner)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, fuel2: ExprId| -> ExprId {
        let zero = d.zero();
        let bound1_ty = d.le(m, zero);
        let bound2_ty = d.le(m, fuel2);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();

        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, h1, zero_le_m]);

        let left_term = d.const_app(p.ldiff_aux, &[zero, m, n]);
        let right_term = d.const_app(p.ldiff_aux, &[fuel2, m, n]);
        let left_is_zero = d.refl(zero);

        let right_at_zero = d.const_app(p.ldiff_aux, &[fuel2, zero, n]);
        let right_congr = d.congr(m, zero, m_eq_zero, &|d, x| {
            d.const_app(p.ldiff_aux, &[fuel2, x, n])
        });
        let any_fuel = d.lemma(p.ldiff_aux_zero_left_any_fuel, &[fuel2, n]);
        let (_, right_is_zero) = d.chain(
            right_term,
            &[(right_at_zero, right_congr), (zero, any_fuel)],
        );
        let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);

        let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);
        let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
        d.lam_fv(h1_fv, bound1_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>,
                k: ExprId,
                ih: ExprId,
                m: ExprId,
                n: ExprId,
                fuel2: ExprId|
     -> ExprId {
        let sk = d.succ(k);
        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound1 = d.le(candidate, sk);
            let bound2 = d.le(candidate, fuel2);
            let lhs = d.const_app(p.ldiff_aux, &[sk, candidate, n]);
            let rhs = d.const_app(p.ldiff_aux, &[fuel2, candidate, n]);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound2, concl);
            d.arrow(bound1, inner)
        };

        cases_zero_succ(
            d,
            m,
            &goal_at,
            &|d| {
                let zero = d.zero();
                let bound1_ty = d.le(zero, sk);
                let bound2_ty = d.le(zero, fuel2);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let left_term = d.const_app(p.ldiff_aux, &[sk, zero, n]);
                let right_term = d.const_app(p.ldiff_aux, &[fuel2, zero, n]);
                let left_is_zero = d.lemma(p.ldiff_aux_zero_left_any_fuel, &[sk, n]);
                let right_is_zero = d.lemma(p.ldiff_aux_zero_left_any_fuel, &[fuel2, n]);
                let right_is_zero_rev = d.symm(right_term, zero, right_is_zero);
                let body = d.trans(left_term, zero, right_term, left_is_zero, right_is_zero_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
            &|d, predecessor| {
                let succ_pred = d.succ(predecessor);
                let bound1_ty = d.le(succ_pred, sk);
                let bound2_ty = d.le(succ_pred, fuel2);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);

                let two = d.num(2);
                let half = d.div(succ_pred, two);
                let half_n = d.div(n, two);
                let bit_m = d.modulo(succ_pred, two);
                let bit_n = d.modulo(n, two);
                let zero = d.zero();
                let bit_n_is_zero = d.beq(bit_n, zero);
                let bit_ldiff = d.bool_select_nat(bit_n_is_zero, bit_m, zero);

                let half_le_k = half_le_predecessor_of_succ(d, &p, predecessor, k, h1);

                let one = d.num(1);
                let one_le_succ_pred = d.zero_lt_succ(predecessor);
                let one_le_fuel2 =
                    d.lemma(p.le_trans, &[one, succ_pred, fuel2, one_le_succ_pred, h2]);
                let succ_pred_fuel2 = d.lemma(p.succ_pred_of_pos, &[fuel2, one_le_fuel2]);
                let f2p = d.pred(fuel2);
                let succ_f2p = d.succ(f2p);
                let h2_motive = d.eq_motive(fuel2, &|d, x| d.le(succ_pred, x));
                let h2_at_succ_f2p = d.transport(fuel2, h2_motive, h2, succ_f2p, succ_pred_fuel2);
                let half_le_f2p =
                    half_le_predecessor_of_succ(d, &p, predecessor, f2p, h2_at_succ_f2p);

                let ih_at_half = d.apply(ih, &[half, half_n, f2p]);
                let ih_at_half = d.apply(ih_at_half, &[half_le_k, half_le_f2p]);
                // ih_at_half : Eq (ldiffAux k half half_n) (ldiffAux f2p half half_n)

                let recursive_general = d.const_app(p.ldiff_aux, &[k, half, half_n]);
                let recursive_at_f2p = d.const_app(p.ldiff_aux, &[f2p, half, half_n]);

                // `on_n_zero = succ_pred` (= `m`, pass-through -- `lor`'s
                // shape), `on_m_zero = zero` (absorbing -- `land`'s shape).
                let start = guarded(
                    d,
                    succ_pred,
                    n,
                    succ_pred,
                    zero,
                    recursive_general,
                    bit_ldiff,
                );
                let mid = guarded(
                    d,
                    succ_pred,
                    n,
                    succ_pred,
                    zero,
                    recursive_at_f2p,
                    bit_ldiff,
                );
                let inner_step = d.congr(
                    recursive_general,
                    recursive_at_f2p,
                    ih_at_half,
                    &|d, hole| guarded(d, succ_pred, n, succ_pred, zero, hole, bit_ldiff),
                );

                let outer_step = d.congr(fuel2, succ_f2p, succ_pred_fuel2, &|d, x| {
                    d.const_app(p.ldiff_aux, &[x, succ_pred, n])
                });
                let final_target = d.const_app(p.ldiff_aux, &[fuel2, succ_pred, n]);
                let mid2 = d.const_app(p.ldiff_aux, &[succ_f2p, succ_pred, n]);
                let outer_step_rev = d.symm(final_target, mid2, outer_step);

                let body = d.trans(start, mid, final_target, inner_step, outer_step_rev);

                let with_h2 = d.lam_fv(h2_fv, bound2_ty, body);
                d.lam_fv(h1_fv, bound1_ty, with_h2)
            },
        )
    };

    let fuel1_fv = d.fresh_fvar();
    let fuel1 = d.kernel().fvar(fuel1_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel1);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fuel2_fv = d.fresh_fvar();
    let fuel2 = d.kernel().fvar(fuel2_fv);
    let applied = d.apply(proof_fn, &[m, n, fuel2]);
    let ty = {
        let body = statement(d, fuel1, m, n, fuel2);
        let with_fuel2 = d.pi_fv(fuel2_fv, nat, body);
        let with_n = d.pi_fv(n_fv, nat, with_fuel2);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel1_fv, nat, with_m)
    };
    let value = {
        let with_fuel2 = d.lam_fv(fuel2_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_fuel2);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel1_fv, nat, with_m)
    };
    d.declare_theorem(p.ldiff_aux_agree_of_fuel, ty, value)
}

/// `ldiff_aux_eq_ldiff_of_le : ∀ fuel m n, Le m fuel → Eq (ldiffAux fuel m
/// n) (ldiff m n)` — [`declare_land_aux_eq_land_of_le`]'s `ldiff` twin.
fn declare_ldiff_aux_eq_ldiff_of_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.ldiff_aux_eq_ldiff_of_le, 3, &|d, values| {
        let fuel = values[0];
        let m = values[1];
        let n = values[2];
        let bound_ty = d.le(m, fuel);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let le_refl_m = d.lemma(p.le_refl, &[m]);
        let agree = d.lemma(p.ldiff_aux_agree_of_fuel, &[fuel, m, n, m]);
        let agree = d.apply(agree, &[bound, le_refl_m]);
        let lhs = d.const_app(p.ldiff_aux, &[fuel, m, n]);
        let rhs = d.const_app(p.ldiff, &[m, n]);
        let stmt = d.eq(lhs, rhs);
        let inner_ty = d.arrow(bound_ty, stmt);
        let value = d.lam_fv(bound_fv, bound_ty, agree);
        (inner_ty, value)
    })?;
    Ok(())
}

/// Declare fuel-irrelevance for `ldiffAux` (see the section doc above).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_ldiff_fuel_irrelevance_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_ldiff_aux_zero_left_any_fuel(d, p)?;
    declare_ldiff_aux_agree_of_fuel(d, p)?;
    declare_ldiff_aux_eq_ldiff_of_le(d, p)?;
    Ok(())
}

// ============================================================================
// `land_comm`, the first of the 7 `natural-bitwise` facts fuel-irrelevance
// was blocking (`F:ml430-nat-land-comm-7e6ad72e`). Fuel-irrelevance alone is
// NOT enough -- `land m n = landAux m m n` and `land n m = landAux n n m`
// put DIFFERENT values (`m` vs `n`) in the fuel slot, so relating them needs
// a SECOND piece: same-fuel commutativity of `landAux` itself
// (`declare_land_aux_comm_of_fuel`), then routing both canonical instances
// through the shared fuel `m + n` via `land_aux_agree_of_fuel`.
// ============================================================================

/// `land_aux_comm_of_fuel : ∀ fuel m n, Eq (landAux fuel m n) (landAux fuel
/// n m)` — see the section doc above. `land`'s guard is symmetric (both
/// `on_n_zero`/`on_m_zero` are the constant `0`), so a 4-way case split on
/// `(m = 0?, n = 0?)` shows the two sides always agree: three of the four
/// cases close via [`declare_land_aux_zero_left_any_fuel`] or by `refl`
/// alone (the outer guard checking a LITERAL `0` never needs the other
/// argument's shape), and the fourth (`m`, `n` both nonzero) needs only the
/// induction hypothesis plus `Nat.mul_comm` for the per-bit product.
fn declare_land_aux_comm_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId| {
        let lhs = d.const_app(p.land_aux, &[fuel, a, b]);
        let rhs = d.const_app(p.land_aux, &[fuel, b, a]);
        d.eq(lhs, rhs)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        // Both sides reduce to the constant `0` regardless of `a`/`b`.
        let zero = d.zero();
        let lhs = d.const_app(p.land_aux, &[zero, a, b]);
        d.refl(lhs)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId| -> ExprId {
        let sk = d.succ(k);

        cases_zero_succ(
            d,
            a,
            &|d, candidate| {
                let lhs = d.const_app(p.land_aux, &[sk, candidate, b]);
                let rhs = d.const_app(p.land_aux, &[sk, b, candidate]);
                d.eq(lhs, rhs)
            },
            &|d| {
                // a = 0: LHS = landAux sk 0 b = 0 (the "any fuel" lemma);
                // RHS = landAux sk b 0 reduces to `0` DIRECTLY by iota -- the
                // outer guard checks the LITERAL `0` in the second position
                // and never needs `b`'s shape.
                let zero = d.zero();
                let lhs = d.const_app(p.land_aux, &[sk, zero, b]);
                let rhs = d.const_app(p.land_aux, &[sk, b, zero]);
                let lhs_is_zero = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, b]);
                let rhs_is_zero = d.refl(zero);
                let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
                d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
            },
            &|d, a_pred| {
                let succ_a = d.succ(a_pred);
                cases_zero_succ(
                    d,
                    b,
                    &|d, candidate| {
                        let lhs = d.const_app(p.land_aux, &[sk, succ_a, candidate]);
                        let rhs = d.const_app(p.land_aux, &[sk, candidate, succ_a]);
                        d.eq(lhs, rhs)
                    },
                    &|d| {
                        // b = 0 (a = succ a_pred): mirror image of the a = 0
                        // case above.
                        let zero = d.zero();
                        let lhs = d.const_app(p.land_aux, &[sk, succ_a, zero]);
                        let rhs = d.const_app(p.land_aux, &[sk, zero, succ_a]);
                        let lhs_is_zero = d.refl(zero);
                        let rhs_is_zero = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, succ_a]);
                        let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
                        d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
                    },
                    &|d, b_pred| {
                        // Both nonzero: the real AND-at-this-bit step. Both
                        // guards resolve to `false` regardless of argument
                        // ORDER (each check is decided by a LITERAL `succ`),
                        // so `guarded(succ_a, succ_b, 0, 0, _, _)` is defeq
                        // to BOTH sides' own reduced row -- only the
                        // recursive/bit VALUES need relating.
                        let succ_b = d.succ(b_pred);
                        let two = d.num(2);
                        let zero = d.zero();
                        let half_a = d.div(succ_a, two);
                        let half_b = d.div(succ_b, two);
                        let bit_a = d.modulo(succ_a, two);
                        let bit_b = d.modulo(succ_b, two);

                        let rec = d.const_app(p.land_aux, &[k, half_a, half_b]);
                        let rec_swapped = d.const_app(p.land_aux, &[k, half_b, half_a]);
                        let ih_at_halves = d.apply(ih, &[half_a, half_b]);
                        // ih_at_halves : Eq (landAux k half_a half_b) (landAux k half_b half_a)

                        let bit_and = d.mul(bit_a, bit_b);
                        let bit_and_swapped = d.mul(bit_b, bit_a);
                        let bit_comm = d.lemma(p.mul_comm, &[bit_a, bit_b]);

                        let start = guarded(d, succ_a, succ_b, zero, zero, rec, bit_and);
                        let mid = guarded(d, succ_a, succ_b, zero, zero, rec_swapped, bit_and);
                        let finish =
                            guarded(d, succ_a, succ_b, zero, zero, rec_swapped, bit_and_swapped);

                        let step1 = d.congr(rec, rec_swapped, ih_at_halves, &|d, hole| {
                            guarded(d, succ_a, succ_b, zero, zero, hole, bit_and)
                        });
                        let step2 = d.congr(bit_and, bit_and_swapped, bit_comm, &|d, hole| {
                            guarded(d, succ_a, succ_b, zero, zero, rec_swapped, hole)
                        });
                        d.trans(start, mid, finish, step1, step2)
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let applied = d.apply(proof_fn, &[a, b]);
    let ty = {
        let body = statement(d, fuel, a, b);
        let with_b = d.pi_fv(b_fv, nat, body);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_b = d.lam_fv(b_fv, nat, applied);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.land_aux_comm_of_fuel, ty, value)
}

/// `land_comm : ∀ m n, Eq (land m n) (land n m)` — see the section doc
/// above. Chain: `land m n = landAux m m n = landAux (m+n) m n =
/// landAux (m+n) n m = landAux n n m = land n m`, where the first and last
/// steps are [`declare_land_aux_agree_of_fuel`] (`Le m (m+n)`/`Le n (m+n)`
/// via `Nat.le_add_right`, transporting the second along `Nat.add_comm`) and
/// the middle step is [`declare_land_aux_comm_of_fuel`] at the shared fuel
/// `m + n`.
pub(super) fn declare_land_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_land_aux_comm_of_fuel(d, p)?;
    let p = *p;
    d.theorem(p.land_comm, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let sum = d.add(m, n);

        let le_refl_m = d.lemma(p.le_refl, &[m]);
        let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
        let step_a = d.lemma(p.land_aux_agree_of_fuel, &[m, m, n, sum]);
        let step_a = d.apply(step_a, &[le_refl_m, m_le_sum]);
        // step_a : Eq (landAux m m n) (landAux sum m n)

        let step_b = d.lemma(p.land_aux_comm_of_fuel, &[sum, m, n]);
        // step_b : Eq (landAux sum m n) (landAux sum n m)

        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let n_le_n_sum = d.lemma(p.le_add_right, &[n, m]);
        // n_le_n_sum : Le n (add n m); transport along `add_comm n m` to
        // get `Le n (add m n)` = `Le n sum`.
        let n_sum = d.add(n, m);
        let add_comm_nm = d.lemma(p.add_comm, &[n, m]);
        let n_le_motive = d.eq_motive(n_sum, &|d, x| d.le(n, x));
        let n_le_sum = d.transport(n_sum, n_le_motive, n_le_n_sum, sum, add_comm_nm);

        let step_c = d.lemma(p.land_aux_agree_of_fuel, &[n, n, m, sum]);
        let step_c = d.apply(step_c, &[le_refl_n, n_le_sum]);
        // step_c : Eq (landAux n n m) (landAux sum n m)

        let landaux_m_m_n = d.const_app(p.land_aux, &[m, m, n]);
        let landaux_sum_m_n = d.const_app(p.land_aux, &[sum, m, n]);
        let landaux_sum_n_m = d.const_app(p.land_aux, &[sum, n, m]);
        let landaux_n_n_m = d.const_app(p.land_aux, &[n, n, m]);
        let step_c_rev = d.symm(landaux_n_n_m, landaux_sum_n_m, step_c);

        let step_ab = d.trans(
            landaux_m_m_n,
            landaux_sum_m_n,
            landaux_sum_n_m,
            step_a,
            step_b,
        );
        let proof = d.trans(
            landaux_m_m_n,
            landaux_sum_n_m,
            landaux_n_n_m,
            step_ab,
            step_c_rev,
        );

        let lhs = d.const_app(p.land, &[m, n]);
        let rhs = d.const_app(p.land, &[n, m]);
        (d.eq(lhs, rhs), proof)
    })?;
    Ok(())
}

// ============================================================================
// `lor_comm`, the `lor` twin of `land_comm`. NOT a mechanical transport:
// `lorAux`'s fuel-exhaustion row returns `n` (pass-through), so unlike
// `landAux`'s constant-`0` row, `lorAux fuel a b = lorAux fuel b a` is FALSE
// at insufficient fuel for `a ≠ b` — `lorAux 0 3 4 = 4` while
// `lorAux 0 4 3 = 3`. So [`declare_lor_aux_comm_of_fuel`]'s statement carries
// TWO hypotheses (`Le a fuel`, `Le b fuel`), where
// [`declare_land_aux_comm_of_fuel`] carries none, and both the base case and
// the both-nonzero step need them (the base case to force `a = b = 0`; the
// step to supply `half_le_predecessor_of_succ` for BOTH halves, not one).
// ============================================================================

/// `Eq (bool_select_nat (ble (mod m 2) (mod n 2)) (mod n 2) (mod m 2))
///     (bool_select_nat (ble (mod n 2) (mod m 2)) (mod m 2) (mod n 2))` —
/// `lorAux`'s per-bit `max`-via-`ble` combine is commutative, the `lor` twin
/// of `Nat.mul_comm`'s role in [`declare_land_aux_comm_of_fuel`]'s
/// both-nonzero case. Both sides are stuck at symbolic `m`, `n` and agree
/// only *given* each `Nat.mod _ 2` is `0` or `1` —
/// [`cases_mod_two`] on each operand in turn, four leaves at concrete
/// numerals, `d.refl` closes every one. Structurally identical to
/// [`bit_agreement`], comparing the combine against itself swapped rather
/// than against `Nat.bitwiseAux`'s general form.
/// Given `bit_n ≤ 1`, `Le (mul bit_m bit_n) bit_m` — monotonicity of `mul`
/// in the right argument at `bit_n ≤ 1`, closed by `mul_one`. Shared by the
/// "both positive" leaf below.
fn bit_product_le_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    bit_m: ExprId,
    bit_n: ExprId,
    bit_n_le_one: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let bit = d.mul(bit_m, bit_n);
    let bit_m_one = d.mul(bit_m, one);
    let mono = d.lemma(p.mul_le_mul_left, &[bit_m, bit_n, one, bit_n_le_one]);
    // mono : Le bit bit_m_one
    let mul_one_eq = d.lemma(p.mul_one, &[bit_m]); // Eq bit_m_one bit_m
    let motive = d.eq_motive(bit_m_one, &|d, x| d.le(bit, x));
    d.transport(bit_m_one, motive, mono, bit_m, mul_one_eq)
}
/// `land_aux_le_left : ∀ fuel m n, Le (landAux fuel m n) m` — see the
/// section doc above.
fn declare_land_aux_le_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, m: ExprId, n: ExprId| {
        let lhs = d.const_app(p.land_aux, &[fuel, m, n]);
        d.le(lhs, m)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, _n: ExprId| -> ExprId { d.lemma(p.zero_le, &[m]) };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, m: ExprId, n: ExprId| -> ExprId {
        let sk = d.succ(k);

        cases_zero_succ(
            d,
            m,
            &|d, candidate| {
                let lhs = d.const_app(p.land_aux, &[sk, candidate, n]);
                d.le(lhs, candidate)
            },
            &|d| {
                // m = 0: landAux sk 0 n = 0 (bool_select_nat_same is needed
                // here too -- n stays symbolic, exactly
                // `land_aux_zero_left_any_fuel`'s own succ branch).
                let zero = d.zero();
                let lhs = d.const_app(p.land_aux, &[sk, zero, n]);
                let eq0 = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, n]); // Eq lhs 0
                let le00 = d.lemma(p.le_refl, &[zero]); // Le 0 0
                let motive = d.eq_motive(zero, &|d, x| d.le(x, zero));
                let eq0_rev = d.symm(lhs, zero, eq0); // Eq 0 lhs
                d.transport(zero, motive, le00, lhs, eq0_rev)
            },
            &|d, m_pred| {
                let succ_m = d.succ(m_pred);
                cases_zero_succ(
                    d,
                    n,
                    &|d, candidate| {
                        let lhs = d.const_app(p.land_aux, &[sk, succ_m, candidate]);
                        d.le(lhs, succ_m)
                    },
                    &|d| {
                        // n = 0 (LITERAL): the outer guard fires directly,
                        // regardless of succ_m's shape.
                        d.lemma(p.zero_le, &[succ_m])
                    },
                    &|d, n_pred| {
                        let succ_n = d.succ(n_pred);
                        let two = d.num(2);
                        let one = d.num(1);
                        let half_m = d.div(succ_m, two);
                        let half_n = d.div(succ_n, two);
                        let bit_m = d.modulo(succ_m, two);
                        let bit_n = d.modulo(succ_n, two);

                        let rec = d.const_app(p.land_aux, &[k, half_m, half_n]);
                        let ih_at = d.apply(ih, &[half_m, half_n]); // Le rec half_m

                        let pos2 = d.zero_lt_succ(one); // Lt 0 2
                        let bit_n_lt_2 = d.lemma(p.mod_lt, &[succ_n, two, pos2]);
                        let bit_n_le_1 = d.lemma(p.le_of_lt_succ, &[bit_n, one, bit_n_lt_2]);
                        let bit_le_bit_m = bit_product_le_left(d, &p, bit_m, bit_n, bit_n_le_1);
                        let bit = d.mul(bit_m, bit_n);

                        let two_rec_le = d.lemma(p.mul_le_mul_left, &[two, rec, half_m, ih_at]);
                        // two_rec_le : Le (2*rec) (2*half_m)

                        let two_rec = d.mul(two, rec);
                        let two_half_m = d.mul(two, half_m);
                        let step_a =
                            d.lemma(p.add_le_add_right, &[bit, two_rec, two_half_m, two_rec_le]);
                        // step_a : Le (2*rec + bit) (2*half_m + bit)
                        let step_b =
                            d.lemma(p.add_le_add_left, &[two_half_m, bit, bit_m, bit_le_bit_m]);
                        // step_b : Le (2*half_m + bit) (2*half_m + bit_m)

                        let value = d.add(two_rec, bit);
                        let mid = d.add(two_half_m, bit);
                        let target = d.add(two_half_m, bit_m);
                        let combined = d.lemma(p.le_trans, &[value, mid, target, step_a, step_b]);
                        // combined : Le value target

                        // target = succ_m, via the executable div/mod identity.
                        let h_exec = d.lemma(p.div_mod_exec, &[one, succ_m]);
                        // h_exec : divMod 2 succ_m half_m bit_m
                        let eq_ty = d.eq(succ_m, target);
                        let bound_ty = d.lt(bit_m, two);
                        let eq1 = and_left(d, eq_ty, bound_ty, h_exec); // Eq succ_m target
                        let eq1_rev = d.symm(succ_m, target, eq1); // Eq target succ_m

                        let final_motive = d.eq_motive(target, &|d, x| d.le(value, x));
                        d.transport(target, final_motive, combined, succ_m, eq1_rev)
                        // : Le value succ_m -- and `landAux sk succ_m succ_n`
                        // is defeq to `value` (both guards resolve `false`
                        // directly, succ_m/succ_n literal), so this closes
                        // the goal `Le (landAux sk succ_m succ_n) succ_m`.
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let applied = d.apply(proof_fn, &[m, n]);
    let ty = {
        let body = statement(d, fuel, m, n);
        let with_n = d.pi_fv(n_fv, nat, body);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel_fv, nat, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, applied);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel_fv, nat, with_m)
    };
    d.declare_theorem(p.land_aux_le_left, ty, value)
}
/// `land_le_left : ∀ a b, Le (land a b) a` — [`declare_land_aux_le_left`] at
/// `fuel := a`, `m := a`: `land a b` and `landAux a a b` are the SAME term
/// by definition, so the kernel accepts the bound directly against this
/// `land`-headed statement via defeq, no extra proof step.
fn declare_land_le_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_le_left, 2, &|d, values| {
        let a = values[0];
        let b = values[1];
        let bound = d.lemma(p.land_aux_le_left, &[a, a, b]);
        let lhs = d.const_app(p.land, &[a, b]);
        (d.le(lhs, a), bound)
    })?;
    Ok(())
}
/// Declare [`declare_land_aux_le_left`] and its `land`-headed corollary.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_le_left_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_aux_le_left(d, p)?;
    declare_land_le_left(d, p)?;
    Ok(())
}

/// `land_le_right : ∀ a b, Le (land a b) b` — the mirror of `land_le_left`,
/// via `land_comm` (`Eq (land a b) (land b a)`) transporting
/// `land_le_left b a : Le (land b a) b` backwards along that equality.
/// Needs no new `landAux` machinery: `land_le_left` already gives the bound
/// on the OTHER operand order, and `land_comm` is already proved.
fn declare_land_le_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_le_right, 2, &|d, values| {
        let a = values[0];
        let b = values[1];
        let land_ab = d.const_app(p.land, &[a, b]);
        let land_ba = d.const_app(p.land, &[b, a]);
        let h_comm = d.lemma(p.land_comm, &[a, b]); // Eq (land a b) (land b a)
        let h_comm_rev = d.symm(land_ab, land_ba, h_comm); // Eq (land b a) (land a b)
        let h_le_ba = d.lemma(p.land_le_left, &[b, a]); // Le (land b a) b
        let motive = d.eq_motive(land_ba, &|d, x| d.le(x, b));
        let proof = d.transport(land_ba, motive, h_le_ba, land_ab, h_comm_rev);
        (d.le(land_ab, b), proof)
    })?;
    Ok(())
}

/// Declare [`declare_land_le_right`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_le_right_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_le_right(d, p)?;
    Ok(())
}

fn lor_bit_comm(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bit_n = d.modulo(n, two);

    let combine = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let lhs = combine(d, x, y);
        let rhs = combine(d, y, x);
        d.eq(lhs, rhs)
    };
    // At concrete `x`, `y` both orderings evaluate to the same literal, so
    // `refl` on the un-swapped side is accepted against the swapped one.
    let leaf = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let lhs = combine(d, x, y);
        d.refl(lhs)
    };
    let inner = |d: &mut NatDev<'_>, x: ExprId| {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = leaf(d, x, zero);
        let at_one = leaf(d, x, one);
        cases_mod_two(d, &p, n, &|d, y| claim(d, x, y), at_zero, at_one)
    };

    let zero = d.zero();
    let one = d.num(1);
    let outer_zero = inner(d, zero);
    let outer_one = inner(d, one);
    cases_mod_two(d, &p, m, &|d, x| claim(d, x, bit_n), outer_zero, outer_one)
}

/// `lor_aux_comm_of_fuel : ∀ fuel m n, Le m fuel → Le n fuel → Eq (lorAux
/// fuel m n) (lorAux fuel n m)` — see the section doc above for why BOTH
/// hypotheses are required here, unlike [`declare_land_aux_comm_of_fuel`].
///
/// Case split on `m` then (in the nonzero branch) on `n` ([`cases_zero_succ`],
/// nested, exactly [`declare_land_aux_comm_of_fuel`]'s shape). The two
/// single-zero cases close by combining [`declare_lor_aux_zero_left_any_fuel`]
/// (for the side whose FIRST value argument is the literal `0`) with a plain
/// `refl` (for the side whose SECOND value argument is the literal `0` —
/// `lorAux`'s outer `n = 0` guard fires immediately on a literal, exactly as
/// `land`'s analogous case does for its absorbing zero). The both-nonzero
/// case needs `half_le_predecessor_of_succ` for BOTH halves (`land`'s
/// analogue needs neither bound at all) to apply the IH, plus
/// [`lor_bit_comm`] in place of `Nat.mul_comm`.
fn declare_lor_aux_comm_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId| {
        let bound_a = d.le(a, fuel);
        let bound_b = d.le(b, fuel);
        let lhs = d.const_app(p.lor_aux, &[fuel, a, b]);
        let rhs = d.const_app(p.lor_aux, &[fuel, b, a]);
        let concl = d.eq(lhs, rhs);
        let inner = d.arrow(bound_b, concl);
        d.arrow(bound_a, inner)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId| -> ExprId {
        let zero = d.zero();
        let bound_a_ty = d.le(a, zero);
        let bound_b_ty = d.le(b, zero);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let zero_le_a = d.lemma(p.zero_le, &[a]);
        let a_eq_zero = d.lemma(p.le_antisymm, &[a, zero, h1, zero_le_a]);
        let zero_le_b = d.lemma(p.zero_le, &[b]);
        let b_eq_zero = d.lemma(p.le_antisymm, &[b, zero, h2, zero_le_b]);

        // `lorAux 0 a b` reduces to `b` and `lorAux 0 b a` to `a` for ANY
        // `a`, `b` (the base row ignores the first argument entirely), so
        // the goal is defeq to `Eq b a` -- derive that directly from
        // `a = 0` and `b = 0` rather than reducing the aux terms by hand.
        let a_eq_zero_rev = d.symm(a, zero, a_eq_zero);
        let body = d.trans(b, zero, a, b_eq_zero, a_eq_zero_rev);

        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
        d.lam_fv(h1_fv, bound_a_ty, with_h2)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId| -> ExprId {
        let sk = d.succ(k);

        let goal_a = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let bound_a = d.le(candidate, sk);
            let bound_b = d.le(b, sk);
            let lhs = d.const_app(p.lor_aux, &[sk, candidate, b]);
            let rhs = d.const_app(p.lor_aux, &[sk, b, candidate]);
            let concl = d.eq(lhs, rhs);
            let inner = d.arrow(bound_b, concl);
            d.arrow(bound_a, inner)
        };

        cases_zero_succ(
            d,
            a,
            &goal_a,
            &|d| {
                let zero = d.zero();
                let bound_a_ty = d.le(zero, sk);
                let bound_b_ty = d.le(b, sk);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();

                let lhs = d.const_app(p.lor_aux, &[sk, zero, b]);
                let rhs = d.const_app(p.lor_aux, &[sk, b, zero]);
                let lhs_is_b = d.lemma(p.lor_aux_zero_left_any_fuel, &[sk, b]);
                let rhs_is_b = d.refl(b);
                let rhs_is_b_rev = d.symm(rhs, b, rhs_is_b);
                let body = d.trans(lhs, b, rhs, lhs_is_b, rhs_is_b_rev);

                let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                d.lam_fv(h1_fv, bound_a_ty, with_h2)
            },
            &|d, a_pred| {
                let succ_a = d.succ(a_pred);

                let goal_b = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
                    let bound_a = d.le(succ_a, sk);
                    let bound_b = d.le(candidate, sk);
                    let lhs = d.const_app(p.lor_aux, &[sk, succ_a, candidate]);
                    let rhs = d.const_app(p.lor_aux, &[sk, candidate, succ_a]);
                    let concl = d.eq(lhs, rhs);
                    let inner = d.arrow(bound_b, concl);
                    d.arrow(bound_a, inner)
                };

                cases_zero_succ(
                    d,
                    b,
                    &goal_b,
                    &|d| {
                        let zero = d.zero();
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(zero, sk);
                        let h1_fv = d.fresh_fvar();
                        let h2_fv = d.fresh_fvar();

                        let lhs = d.const_app(p.lor_aux, &[sk, succ_a, zero]);
                        let rhs = d.const_app(p.lor_aux, &[sk, zero, succ_a]);
                        let lhs_is_succ_a = d.refl(succ_a);
                        let rhs_is_succ_a = d.lemma(p.lor_aux_zero_left_any_fuel, &[sk, succ_a]);
                        let rhs_is_succ_a_rev = d.symm(rhs, succ_a, rhs_is_succ_a);
                        let body = d.trans(lhs, succ_a, rhs, lhs_is_succ_a, rhs_is_succ_a_rev);

                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                    &|d, b_pred| {
                        let succ_b = d.succ(b_pred);
                        let bound_a_ty = d.le(succ_a, sk);
                        let bound_b_ty = d.le(succ_b, sk);
                        let h1_fv = d.fresh_fvar();
                        let h1 = d.kernel().fvar(h1_fv);
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);

                        let two = d.num(2);
                        let half_a = d.div(succ_a, two);
                        let half_b = d.div(succ_b, two);
                        let bit_a = d.modulo(succ_a, two);
                        let bit_b = d.modulo(succ_b, two);

                        // Unlike `land_aux_comm_of_fuel`'s both-nonzero
                        // case, BOTH halves need a fuel bound here -- the
                        // IH itself carries `Le _ k` hypotheses.
                        let half_a_le_k = half_le_predecessor_of_succ(d, &p, a_pred, k, h1);
                        let half_b_le_k = half_le_predecessor_of_succ(d, &p, b_pred, k, h2);

                        let ih_at_halves = d.apply(ih, &[half_a, half_b]);
                        let ih_at_halves = d.apply(ih_at_halves, &[half_a_le_k, half_b_le_k]);
                        // ih_at_halves : Eq (lorAux k half_a half_b) (lorAux k half_b half_a)

                        let rec = d.const_app(p.lor_aux, &[k, half_a, half_b]);
                        let rec_swapped = d.const_app(p.lor_aux, &[k, half_b, half_a]);

                        let bit_a_le_bit_b = d.ble(bit_a, bit_b);
                        let bit_or = d.bool_select_nat(bit_a_le_bit_b, bit_b, bit_a);
                        let bit_b_le_bit_a = d.ble(bit_b, bit_a);
                        let bit_or_swapped = d.bool_select_nat(bit_b_le_bit_a, bit_a, bit_b);
                        let bit_comm = lor_bit_comm(d, &p, succ_a, succ_b);

                        // Both guards resolve to `false` regardless of
                        // argument ORDER (each check is decided by a
                        // LITERAL `succ`), so `guarded(succ_a, succ_b,
                        // succ_a, succ_b, _, _)` is defeq to BOTH sides'
                        // own reduced row -- exactly
                        // `declare_land_aux_comm_of_fuel`'s both-nonzero
                        // argument, unaffected by `lorAux`'s guard values
                        // being pass-through rather than constant (neither
                        // guard ever SELECTS `on_n_zero`/`on_m_zero` here).
                        let start = guarded(d, succ_a, succ_b, succ_a, succ_b, rec, bit_or);
                        let mid = guarded(d, succ_a, succ_b, succ_a, succ_b, rec_swapped, bit_or);
                        let finish = guarded(
                            d,
                            succ_a,
                            succ_b,
                            succ_a,
                            succ_b,
                            rec_swapped,
                            bit_or_swapped,
                        );

                        let step1 = d.congr(rec, rec_swapped, ih_at_halves, &|d, hole| {
                            guarded(d, succ_a, succ_b, succ_a, succ_b, hole, bit_or)
                        });
                        let step2 = d.congr(bit_or, bit_or_swapped, bit_comm, &|d, hole| {
                            guarded(d, succ_a, succ_b, succ_a, succ_b, rec_swapped, hole)
                        });
                        let body = d.trans(start, mid, finish, step1, step2);

                        let with_h2 = d.lam_fv(h2_fv, bound_b_ty, body);
                        d.lam_fv(h1_fv, bound_a_ty, with_h2)
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let applied = d.apply(proof_fn, &[a, b]);
    let ty = {
        let body = statement(d, fuel, a, b);
        let with_b = d.pi_fv(b_fv, nat, body);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_b = d.lam_fv(b_fv, nat, applied);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.lor_aux_comm_of_fuel, ty, value)
}

/// `lor_comm : ∀ m n, Eq (lor m n) (lor n m)` — see [`NatPrelude::lor_comm`].
/// Chain: `lor m n = lorAux m m n = lorAux (m+n) m n = lorAux (m+n) n m =
/// lorAux n n m = lor n m`, the outer two steps via
/// [`declare_lor_aux_agree_of_fuel`] (`Le m (m+n)`/`Le n (m+n)` via
/// `Nat.le_add_right`, transporting the second along `Nat.add_comm`, exactly
/// as [`declare_land_comm`]) and the middle step via
/// [`declare_lor_aux_comm_of_fuel`] at the shared fuel `m + n` -- which here
/// (unlike [`declare_land_aux_comm_of_fuel`]) needs `Le m (m+n)` and
/// `Le n (m+n)` too, already in hand from the outer steps' own derivation.
pub(super) fn declare_lor_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_lor_aux_comm_of_fuel(d, p)?;
    let p = *p;
    d.theorem(p.lor_comm, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let sum = d.add(m, n);

        let le_refl_m = d.lemma(p.le_refl, &[m]);
        let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
        let step_a = d.lemma(p.lor_aux_agree_of_fuel, &[m, m, n, sum]);
        let step_a = d.apply(step_a, &[le_refl_m, m_le_sum]);
        // step_a : Eq (lorAux m m n) (lorAux sum m n)

        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let n_le_n_sum = d.lemma(p.le_add_right, &[n, m]);
        // n_le_n_sum : Le n (add n m); transport along `add_comm n m` to
        // get `Le n (add m n)` = `Le n sum`.
        let n_sum = d.add(n, m);
        let add_comm_nm = d.lemma(p.add_comm, &[n, m]);
        let n_le_motive = d.eq_motive(n_sum, &|d, x| d.le(n, x));
        let n_le_sum = d.transport(n_sum, n_le_motive, n_le_n_sum, sum, add_comm_nm);

        // `lor_aux_comm_of_fuel` (unlike `land_aux_comm_of_fuel`) carries
        // hypotheses -- both bounds are already in hand above.
        let step_b = d.lemma(p.lor_aux_comm_of_fuel, &[sum, m, n]);
        let step_b = d.apply(step_b, &[m_le_sum, n_le_sum]);
        // step_b : Eq (lorAux sum m n) (lorAux sum n m)

        let step_c = d.lemma(p.lor_aux_agree_of_fuel, &[n, n, m, sum]);
        let step_c = d.apply(step_c, &[le_refl_n, n_le_sum]);
        // step_c : Eq (lorAux n n m) (lorAux sum n m)

        let loraux_m_m_n = d.const_app(p.lor_aux, &[m, m, n]);
        let loraux_sum_m_n = d.const_app(p.lor_aux, &[sum, m, n]);
        let loraux_sum_n_m = d.const_app(p.lor_aux, &[sum, n, m]);
        let loraux_n_n_m = d.const_app(p.lor_aux, &[n, n, m]);
        let step_c_rev = d.symm(loraux_n_n_m, loraux_sum_n_m, step_c);

        let step_ab = d.trans(loraux_m_m_n, loraux_sum_m_n, loraux_sum_n_m, step_a, step_b);
        let proof = d.trans(
            loraux_m_m_n,
            loraux_sum_n_m,
            loraux_n_n_m,
            step_ab,
            step_c_rev,
        );

        let lhs = d.const_app(p.lor, &[m, n]);
        let rhs = d.const_app(p.lor, &[n, m]);
        (d.eq(lhs, rhs), proof)
    })?;
    Ok(())
}

// ============================================================================
// `land_aux_eq_zero_of_left_eq_zero` -- "zero propagates through the other
// operand" -- the one theorem `docs/plan/status/252-nat-assoc-dichotomy.md`
// traced by hand (and cross-checked numerically in Python) but did not
// build, because it and `land_aux_assoc_of_fuel` both belong here, under
// active concurrent edit at the time that plan was written. See that file
// for the full case-tree derivation this function follows exactly.
// ============================================================================

/// Non-dependent `Or.rec` (private copy; every other file that needs one
/// carries its own, per the existing convention -- see `fibonacci.rs`'s
/// own `or_elim`).
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// Non-dependent `Exists.rec` over `Nat` (private copy, same convention):
/// given `predicate : Nat -> Prop`, `minor : forall w, predicate w -> goal`,
/// and `proof : Exists Nat predicate`, produce a term of type `goal`.
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

/// `fun pred => Eq target (succ pred)` -- the exact predicate
/// [`NatPrelude::zero_or_succ`]'s right disjunct is stated with, rebuilt
/// here so [`exists_elim`] can be handed a predicate that matches it
/// syntactically.
fn succ_pred_predicate(d: &mut NatDev<'_>, target: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let succ_pred = d.succ(pred);
    let body = d.eq(target, succ_pred);
    d.lam_fv(pred_fv, nat, body)
}

/// `Exists Nat (fun pred => Eq target (succ pred))` -- the type of
/// `zero_or_succ`'s right disjunct at `target`, needed to type a lambda
/// binder that consumes it.
fn succ_pred_exists_ty(d: &mut NatDev<'_>, p: &NatPrelude, predicate: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level_one = d.level_one();
    let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
    d.apply(exists_const, &[nat, predicate])
}

/// Given `rec_zero : Eq rec 0` and `bit_zero : Eq bit 0`, produce
/// `Eq (add (mul 2 rec) bit) 0` -- the reverse direction of `add_eq_zero`,
/// used to close a `landAux` successor row once both halves of its
/// `2 * rec + bit` value are known to vanish.
fn stepped_zero_of_parts(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    rec: ExprId,
    bit: ExprId,
    rec_zero: ExprId,
    bit_zero: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.mul(two, rec);
    let stepped = d.add(doubled, bit);

    let step1 = d.congr(rec, zero, rec_zero, &|d, x| {
        let dd = d.mul(two, x);
        d.add(dd, bit)
    });
    let mul_two_zero = d.mul(two, zero);
    let mid1 = d.add(mul_two_zero, bit);

    let step2 = d.congr(bit, zero, bit_zero, &|d, x| d.add(mul_two_zero, x));
    let mid2 = d.add(mul_two_zero, zero);

    // `mid2 = add mul_two_zero 0` is defeq `mul_two_zero` (add's base row is
    // the constant identity), so `d.refl(mul_two_zero)` retypes directly as
    // `Eq mid2 mul_two_zero`.
    let mul_zero_pf = d.lemma(p.mul_zero, &[two]); // Eq mul_two_zero 0
    let mid2_defeq = d.refl(mul_two_zero);
    let step3 = d.trans(mid2, mul_two_zero, zero, mid2_defeq, mul_zero_pf);

    let (_, proof) = d.chain(stepped, &[(mid1, step1), (mid2, step2), (zero, step3)]);
    proof
}

/// The one genuinely hard leaf of [`declare_land_aux_eq_zero_of_left_eq_zero`]:
/// `a = succ a'`, `b = succ b'`, `c = succ c'`, at fuel `sk = succ k`. Builds
/// a term of type
/// `Arrow(Eq (landAux sk succ_a succ_b) 0, Eq (landAux sk succ_a (landAux sk succ_b succ_c)) 0)`.
///
/// `ih : forall a b c, Eq (landAux k a b) 0 -> Eq (landAux k a (landAux k b c)) 0`
/// is the outer induction's own hypothesis, applied at the halves.
#[allow(clippy::too_many_arguments)]
fn declare_land_aux_eq_zero_hard_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    ih: ExprId,
    succ_a: ExprId,
    succ_b: ExprId,
    succ_c: ExprId,
) -> ExprId {
    let p = *p;
    let sk = d.succ(k);
    let zero = d.zero();
    let two = d.num(2);
    let one = d.num(1);

    let half_a = d.div(succ_a, two);
    let half_b = d.div(succ_b, two);
    let half_c = d.div(succ_c, two);
    let bit_a = d.modulo(succ_a, two);
    let bit_b = d.modulo(succ_b, two);
    let bit_c = d.modulo(succ_c, two);

    let rec_ab = d.const_app(p.land_aux, &[k, half_a, half_b]);
    let bit_ab = d.mul(bit_a, bit_b);
    let doubled_ab = d.mul(two, rec_ab);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let ab = d.const_app(p.land_aux, &[sk, succ_a, succ_b]);
    let hyp_ty = d.eq(ab, zero);

    // `h : Eq (landAux sk succ_a succ_b) 0` is defeq
    // `Eq (add (mul 2 rec_ab) bit_ab) 0` (both guards resolve `false`,
    // succ_a/succ_b literal), so `h` is accepted directly where
    // `add_eq_zero` expects its hypothesis.
    let d_ab = d.lemma(p.add_eq_zero, &[doubled_ab, bit_ab, h]);
    let doubled_ab_zero_ty = d.eq(doubled_ab, zero);
    let bit_ab_zero_ty = d.eq(bit_ab, zero);
    let doubled_ab_zero = and_left(d, doubled_ab_zero_ty, bit_ab_zero_ty, d_ab);
    let bit_ab_zero = and_right(d, doubled_ab_zero_ty, bit_ab_zero_ty, d_ab);

    // `Eq (mul 2 rec_ab) 0 -> Or (Eq 2 0) (Eq rec_ab 0)`, eliminate the
    // left disjunct via `succ_ne_zero` (2 is `succ 1`).
    let mul_disj = d.lemma(p.mul_eq_zero, &[two, rec_ab, doubled_ab_zero]);
    let rec_ab_zero_ty = d.eq(rec_ab, zero);
    let two_zero_ty = d.eq(two, zero);
    let rec_ab_zero = {
        let left_fv = d.fresh_fvar();
        let left_h = d.kernel().fvar(left_fv);
        let contradiction = d.lemma(p.succ_ne_zero, &[one, left_h]);
        let left_body = absurd(d, rec_ab_zero_ty, contradiction);
        let left_case = d.lam_fv(left_fv, two_zero_ty, left_body);
        let right_fv = d.fresh_fvar();
        let right_h = d.kernel().fvar(right_fv);
        let right_case = d.lam_fv(right_fv, rec_ab_zero_ty, right_h);
        or_elim(
            d,
            &p,
            two_zero_ty,
            rec_ab_zero_ty,
            rec_ab_zero_ty,
            left_case,
            right_case,
            mul_disj,
        )
    };

    // Dichotomize the inner value `Y := landAux sk succ_b succ_c`.
    let y = d.const_app(p.land_aux, &[sk, succ_b, succ_c]);
    let dichotomy_y = d.lemma(p.zero_or_succ, &[y]);
    let y_zero_ty = d.eq(y, zero);
    let y_succ_predicate = succ_pred_predicate(d, y);
    let y_succ_exists_ty = succ_pred_exists_ty(d, &p, y_succ_predicate);

    let a_bc = d.const_app(p.land_aux, &[sk, succ_a, y]);
    let goal_ty = d.eq(a_bc, zero);

    let left_case = {
        // Y = 0: RHS transports to landAux sk succ_a 0, defeq 0.
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv);
        let cong = d.congr(y, zero, hy, &|d, x| {
            d.const_app(p.land_aux, &[sk, succ_a, x])
        });
        let goal0 = d.const_app(p.land_aux, &[sk, succ_a, zero]);
        let refl0 = d.refl(zero); // retypes: Eq goal0 zero
        let body = d.trans(a_bc, goal0, zero, cong, refl0);
        d.lam_fv(hy_fv, y_zero_ty, body)
    };

    let right_case = {
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv); // Exists Nat (fun w => Eq y (succ w))

        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let succ_q = d.succ(q);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv); // Eq y (succ q)
        let heq_ty = d.eq(y, succ_q);

        let half_q = d.div(succ_q, two);
        let bit_q = d.modulo(succ_q, two);
        let rec_bc = d.const_app(p.land_aux, &[k, half_b, half_c]);
        let bit_bc = d.mul(bit_b, bit_c);

        // `Lt bit_bc 2`, via `bit_bc <= bit_b` (bit_c <= 1) and `bit_b < 2`.
        let positive2 = d.zero_lt_succ(one);
        let bit_c_lt_2 = d.lemma(p.mod_lt, &[succ_c, two, positive2]);
        let bit_c_le_1 = d.lemma(p.le_of_lt_succ, &[bit_c, one, bit_c_lt_2]);
        let bit_bc_le_bit_b = bit_product_le_left(d, &p, bit_b, bit_c, bit_c_le_1);
        let positive2b = d.zero_lt_succ(one);
        let bit_b_lt_2 = d.lemma(p.mod_lt, &[succ_b, two, positive2b]);
        let bit_bc_lt_2 = d.lemma(
            p.lt_of_le_of_lt,
            &[bit_bc, bit_b, two, bit_bc_le_bit_b, bit_b_lt_2],
        );

        // candidate_divmod : divMod 2 succ_q rec_bc bit_bc
        let doubled_bc = d.mul(two, rec_bc);
        let add_term = d.add(doubled_bc, bit_bc);
        let candidate_eq_ty = d.eq(succ_q, add_term);
        let candidate_bound_ty = d.lt(bit_bc, two);
        // `heq : Eq y (succ q)` is defeq `Eq add_term succ_q` (y unfolds to
        // add_term, both guards resolve false, succ_b/succ_c literal).
        let candidate_eq = d.symm(add_term, succ_q, heq);
        let candidate_divmod = d.const_app(
            p.logic.and_intro,
            &[
                candidate_eq_ty,
                candidate_bound_ty,
                candidate_eq,
                bit_bc_lt_2,
            ],
        );

        // exec_divmod : divMod 2 succ_q half_q bit_q
        let exec_divmod = d.lemma(p.div_mod_exec, &[one, succ_q]);

        let unique = d.lemma(
            p.div_mod_unique,
            &[
                two,
                succ_q,
                half_q,
                bit_q,
                rec_bc,
                bit_bc,
                exec_divmod,
                candidate_divmod,
            ],
        );
        let half_eq_ty = d.eq(half_q, rec_bc);
        let bit_eq_ty = d.eq(bit_q, bit_bc);
        let half_eq = and_left(d, half_eq_ty, bit_eq_ty, unique);
        let bit_eq = and_right(d, half_eq_ty, bit_eq_ty, unique);

        // rec_aY := landAux k half_a half_q; show it is 0.
        let rec_ay = d.const_app(p.land_aux, &[k, half_a, half_q]);
        let cong_rec = d.congr(half_q, rec_bc, half_eq, &|d, x| {
            d.const_app(p.land_aux, &[k, half_a, x])
        });
        let rec_a_bc = d.const_app(p.land_aux, &[k, half_a, rec_bc]);
        let ih_at = d.apply(ih, &[half_a, half_b, half_c]);
        let ih_applied = d.apply(ih_at, &[rec_ab_zero]);
        let rec_ay_zero = d.trans(rec_ay, rec_a_bc, zero, cong_rec, ih_applied);

        // bit_aY := mul bit_a bit_q; show it is 0.
        let bit_ay = d.mul(bit_a, bit_q);
        let cong_bit1 = d.congr(bit_q, bit_bc, bit_eq, &|d, x| d.mul(bit_a, x));
        let mul_a_bc = d.mul(bit_a, bit_bc);
        let assoc = d.lemma(p.mul_assoc, &[bit_a, bit_b, bit_c]);
        // assoc : Eq (mul (mul bit_a bit_b) bit_c) (mul bit_a (mul bit_b bit_c))
        //       = Eq (mul bit_ab bit_c) mul_a_bc
        let mul_ab_c = d.mul(bit_ab, bit_c);
        let assoc_rev = d.symm(mul_ab_c, mul_a_bc, assoc);
        let cong_bit2 = d.congr(bit_ab, zero, bit_ab_zero, &|d, x| d.mul(x, bit_c));
        let mul_zero_c = d.mul(zero, bit_c);
        let zm = d.lemma(p.zero_mul, &[bit_c]);
        let (_, bit_ay_zero) = d.chain(
            bit_ay,
            &[
                (mul_a_bc, cong_bit1),
                (mul_ab_c, assoc_rev),
                (mul_zero_c, cong_bit2),
                (zero, zm),
            ],
        );

        let stepped_zero = stepped_zero_of_parts(d, &p, rec_ay, bit_ay, rec_ay_zero, bit_ay_zero);
        // stepped_zero : Eq (add (mul 2 rec_aY) bit_aY) 0, and
        // `landAux sk succ_a succ_q` is defeq to that sum (both guards
        // resolve false, succ_a/succ_q literal).
        let goal_at_succ_q = d.const_app(p.land_aux, &[sk, succ_a, succ_q]);

        let cong_outer = d.congr(y, succ_q, heq, &|d, x| {
            d.const_app(p.land_aux, &[sk, succ_a, x])
        });
        let minor_body = d.trans(a_bc, goal_at_succ_q, zero, cong_outer, stepped_zero);
        let minor_inner = d.lam_fv(heq_fv, heq_ty, minor_body);
        let nat = d.nat_ty();
        let minor = d.lam_fv(q_fv, nat, minor_inner);

        let body = exists_elim(d, &p, y_succ_predicate, goal_ty, minor, hy);
        d.lam_fv(hy_fv, y_succ_exists_ty, body)
    };

    let dichotomy_proof = or_elim(
        d,
        &p,
        y_zero_ty,
        y_succ_exists_ty,
        goal_ty,
        left_case,
        right_case,
        dichotomy_y,
    );
    d.lam_fv(h_fv, hyp_ty, dichotomy_proof)
}

fn declare_land_aux_eq_zero_of_left_eq_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId, c: ExprId| {
        let zero = d.zero();
        let ab = d.const_app(p.land_aux, &[fuel, a, b]);
        let hyp = d.eq(ab, zero);
        let bc = d.const_app(p.land_aux, &[fuel, b, c]);
        let a_bc = d.const_app(p.land_aux, &[fuel, a, bc]);
        let concl = d.eq(a_bc, zero);
        d.arrow(hyp, concl)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId, _c: ExprId| -> ExprId {
        // fuel = 0: the RHS is `landAux 0 a (landAux 0 b c)`, defeq `0`
        // regardless of the second argument's shape -- the zero-fuel row
        // ignores both of its arguments. Hyp unused.
        let zero = d.zero();
        let h_fv = d.fresh_fvar();
        let ab = d.const_app(p.land_aux, &[zero, a, b]);
        let hyp_ty = d.eq(ab, zero);
        let body = d.refl(zero);
        d.lam_fv(h_fv, hyp_ty, body)
    };

    let step =
        |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId, c: ExprId| -> ExprId {
            let sk = d.succ(k);
            let zero = d.zero();

            cases_zero_succ(
                d,
                a,
                &|d, candidate| {
                    let ab = d.const_app(p.land_aux, &[sk, candidate, b]);
                    let hyp_ty = d.eq(ab, zero);
                    let bc = d.const_app(p.land_aux, &[sk, b, c]);
                    let a_bc = d.const_app(p.land_aux, &[sk, candidate, bc]);
                    let concl = d.eq(a_bc, zero);
                    d.arrow(hyp_ty, concl)
                },
                &|d| {
                    // a = 0: RHS = landAux sk 0 Y = 0 via
                    // `land_aux_zero_left_any_fuel`, for ANY Y. Hyp unused.
                    let h_fv = d.fresh_fvar();
                    let ab = d.const_app(p.land_aux, &[sk, zero, b]);
                    let hyp_ty = d.eq(ab, zero);
                    let y = d.const_app(p.land_aux, &[sk, b, c]);
                    let body = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, y]);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, a_pred| {
                    let succ_a = d.succ(a_pred);
                    cases_zero_succ(
                        d,
                        b,
                        &|d, candidate| {
                            let ab = d.const_app(p.land_aux, &[sk, succ_a, candidate]);
                            let hyp_ty = d.eq(ab, zero);
                            let bc = d.const_app(p.land_aux, &[sk, candidate, c]);
                            let a_bc = d.const_app(p.land_aux, &[sk, succ_a, bc]);
                            let concl = d.eq(a_bc, zero);
                            d.arrow(hyp_ty, concl)
                        },
                        &|d| {
                            // a = succ a', b = 0: Y0 := landAux sk 0 c = 0
                            // via the "any fuel" lemma (n := c is symbolic,
                            // so this is genuinely NOT defeq without it).
                            // Then landAux sk succ_a Y0, transported to
                            // landAux sk succ_a 0, is defeq 0 (literal n
                            // after transport). Hyp unused.
                            let h_fv = d.fresh_fvar();
                            let ab = d.const_app(p.land_aux, &[sk, succ_a, zero]);
                            let hyp_ty = d.eq(ab, zero);
                            let y0 = d.const_app(p.land_aux, &[sk, zero, c]);
                            let y0_zero = d.lemma(p.land_aux_zero_left_any_fuel, &[sk, c]);
                            let target = d.const_app(p.land_aux, &[sk, succ_a, y0]);
                            let goal0 = d.const_app(p.land_aux, &[sk, succ_a, zero]);
                            let cong = d.congr(y0, zero, y0_zero, &|d, x| {
                                d.const_app(p.land_aux, &[sk, succ_a, x])
                            });
                            let refl0 = d.refl(zero); // retypes: Eq goal0 zero (defeq)
                            let body = d.trans(target, goal0, zero, cong, refl0);
                            d.lam_fv(h_fv, hyp_ty, body)
                        },
                        &|d, b_pred| {
                            let succ_b = d.succ(b_pred);
                            cases_zero_succ(
                                d,
                                c,
                                &|d, candidate| {
                                    let ab = d.const_app(p.land_aux, &[sk, succ_a, succ_b]);
                                    let hyp_ty = d.eq(ab, zero);
                                    let bc = d.const_app(p.land_aux, &[sk, succ_b, candidate]);
                                    let a_bc = d.const_app(p.land_aux, &[sk, succ_a, bc]);
                                    let concl = d.eq(a_bc, zero);
                                    d.arrow(hyp_ty, concl)
                                },
                                &|d| {
                                    // c = 0: Y0 := landAux sk succ_b 0 is
                                    // defeq 0 DIRECTLY (n := c = 0 is a
                                    // LITERAL from this case split, so the
                                    // outer guard resolves regardless of
                                    // succ_b's shape) -- so the whole
                                    // target is defeq 0 by pure reduction,
                                    // no lemma at all. Hyp unused.
                                    let h_fv = d.fresh_fvar();
                                    let ab = d.const_app(p.land_aux, &[sk, succ_a, succ_b]);
                                    let hyp_ty = d.eq(ab, zero);
                                    let body = d.refl(zero);
                                    d.lam_fv(h_fv, hyp_ty, body)
                                },
                                &|d, c_pred| {
                                    let succ_c = d.succ(c_pred);
                                    declare_land_aux_eq_zero_hard_leaf(
                                        d, &p, k, ih, succ_a, succ_b, succ_c,
                                    )
                                },
                            )
                        },
                    )
                },
            )
        };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let applied = d.apply(proof_fn, &[a, b, c]);
    let ty = {
        let body = statement(d, fuel, a, b, c);
        let with_c = d.pi_fv(c_fv, nat, body);
        let with_b = d.pi_fv(b_fv, nat, with_c);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_c = d.lam_fv(c_fv, nat, applied);
        let with_b = d.lam_fv(b_fv, nat, with_c);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.land_aux_eq_zero_of_left_eq_zero, ty, value)
}

/// Declare [`declare_land_aux_eq_zero_of_left_eq_zero`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_zero_propagation_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_aux_eq_zero_of_left_eq_zero(d, p)?;
    Ok(())
}

// ============================================================================
// `land_aux_assoc_of_fuel` / `land_assoc` -- see
// `docs/plan/status/257-nat-land-assoc-impl.md` for the fully hand-traced
// derivation this transcribes. The step case is split `c`, then `b`, then
// `a` (corrected from an earlier `a,b,c` plan -- `guarded`'s guard checks
// its SECOND value argument, i.e. the outer application's own `n`-slot,
// OUTERMOST, and splitting `c` first is what makes the outer applications on
// both sides resolve directly in leaves 1-3).
// ============================================================================

/// The hard leaf of [`declare_land_aux_assoc_of_fuel`]: `a = succ_a`,
/// `b = succ_b`, `c = succ_c` (all literal successors), at fuel
/// `sk = succ k`. Builds a term of type
/// `Eq (landAux sk (landAux sk succ_a succ_b) succ_c)
///     (landAux sk succ_a (landAux sk succ_b succ_c))`.
///
/// `ih : forall a b c, Eq (landAux k (landAux k a b) c) (landAux k a (landAux k b c))`
/// is the outer induction's own hypothesis, applied at the halves.
#[allow(clippy::too_many_arguments)]
fn declare_land_aux_assoc_hard_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    ih: ExprId,
    succ_a: ExprId,
    succ_b: ExprId,
    succ_c: ExprId,
) -> ExprId {
    let p = *p;
    let sk = d.succ(k);
    let zero = d.zero();
    let two = d.num(2);
    let one = d.num(1);

    let half_a = d.div(succ_a, two);
    let half_b = d.div(succ_b, two);
    let half_c = d.div(succ_c, two);
    let bit_a = d.modulo(succ_a, two);
    let bit_b = d.modulo(succ_b, two);
    let bit_c = d.modulo(succ_c, two);

    let rec_ab = d.const_app(p.land_aux, &[k, half_a, half_b]);
    let bit_ab = d.mul(bit_a, bit_b);
    let rec_bc = d.const_app(p.land_aux, &[k, half_b, half_c]);
    let bit_bc = d.mul(bit_b, bit_c);

    // X, Y: both stuck compounds (both guards resolve `false`, operands
    // literal `succ`, but the recursive/bit values are opaque).
    let x = d.const_app(p.land_aux, &[sk, succ_a, succ_b]);
    let y = d.const_app(p.land_aux, &[sk, succ_b, succ_c]);

    let lhs = d.const_app(p.land_aux, &[sk, x, succ_c]);
    let rhs = d.const_app(p.land_aux, &[sk, succ_a, y]);
    let goal_ty = d.eq(lhs, rhs);

    // Dichotomize Y first.
    let dichotomy_y = d.lemma(p.zero_or_succ, &[y]);
    let y_zero_ty = d.eq(y, zero);
    let y_succ_predicate = succ_pred_predicate(d, y);
    let y_succ_exists_ty = succ_pred_exists_ty(d, &p, y_succ_predicate);

    let y_zero_case = {
        // Y = 0: mirror the direct propagation lemma via
        // `land_aux_comm_of_fuel`, permuting to (c, b, a).
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv); // Eq y zero

        let comm_bc = d.lemma(p.land_aux_comm_of_fuel, &[sk, succ_b, succ_c]);
        // comm_bc : Eq y (landAux sk succ_c succ_b)
        let cb = d.const_app(p.land_aux, &[sk, succ_c, succ_b]);
        let comm_bc_rev = d.symm(y, cb, comm_bc); // Eq cb y
        let hyp_cb = d.trans(cb, y, zero, comm_bc_rev, hy); // Eq cb zero

        let prop_cba = d.lemma(
            p.land_aux_eq_zero_of_left_eq_zero,
            &[sk, succ_c, succ_b, succ_a, hyp_cb],
        );
        let cb_a = d.const_app(p.land_aux, &[sk, succ_b, succ_a]);
        let c_cba = d.const_app(p.land_aux, &[sk, succ_c, cb_a]);
        // prop_cba : Eq c_cba zero

        let comm_ab = d.lemma(p.land_aux_comm_of_fuel, &[sk, succ_a, succ_b]);
        // comm_ab : Eq x cb_a
        let comm_xc = d.lemma(p.land_aux_comm_of_fuel, &[sk, x, succ_c]);
        let c_x = d.const_app(p.land_aux, &[sk, succ_c, x]);
        // comm_xc : Eq lhs c_x

        let cong_x = d.congr(x, cb_a, comm_ab, &|d, hole| {
            d.const_app(p.land_aux, &[sk, succ_c, hole])
        });
        // cong_x : Eq c_x c_cba

        let (_, lhs_is_zero) = d.chain(lhs, &[(c_x, comm_xc), (c_cba, cong_x), (zero, prop_cba)]);

        let cong_rhs = d.congr(y, zero, hy, &|d, hole| {
            d.const_app(p.land_aux, &[sk, succ_a, hole])
        });
        let rhs_at_zero = d.const_app(p.land_aux, &[sk, succ_a, zero]);
        let rhs_zero_tail = d.refl(zero); // Eq rhs_at_zero zero (defeq: literal n = 0)
        let rhs_is_zero = d.trans(rhs, rhs_at_zero, zero, cong_rhs, rhs_zero_tail);
        let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);

        let body = d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev);
        d.lam_fv(hy_fv, y_zero_ty, body)
    };

    let y_succ_case = {
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv); // Exists Nat (fun w => Eq y (succ w))

        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let succ_q = d.succ(q);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv); // Eq y (succ q)
        let heq_ty = d.eq(y, succ_q);

        let half_q = d.div(succ_q, two);
        let bit_q = d.modulo(succ_q, two);

        // Reconstruct div/mod of succ_q from Y's own decomposition
        // (rec_bc, bit_bc) -- identical to the propagation lemma's
        // `Y = succ q` branch.
        let positive2 = d.zero_lt_succ(one);
        let bit_c_lt_2 = d.lemma(p.mod_lt, &[succ_c, two, positive2]);
        let bit_c_le_1 = d.lemma(p.le_of_lt_succ, &[bit_c, one, bit_c_lt_2]);
        let bit_bc_le_bit_b = bit_product_le_left(d, &p, bit_b, bit_c, bit_c_le_1);
        let positive2b = d.zero_lt_succ(one);
        let bit_b_lt_2 = d.lemma(p.mod_lt, &[succ_b, two, positive2b]);
        let bit_bc_lt_2 = d.lemma(
            p.lt_of_le_of_lt,
            &[bit_bc, bit_b, two, bit_bc_le_bit_b, bit_b_lt_2],
        );

        let doubled_bc = d.mul(two, rec_bc);
        let add_term_bc = d.add(doubled_bc, bit_bc);
        let candidate_eq_ty_bc = d.eq(succ_q, add_term_bc);
        let candidate_bound_ty_bc = d.lt(bit_bc, two);
        let candidate_eq_bc = d.symm(add_term_bc, succ_q, heq);
        let candidate_divmod_bc = d.const_app(
            p.logic.and_intro,
            &[
                candidate_eq_ty_bc,
                candidate_bound_ty_bc,
                candidate_eq_bc,
                bit_bc_lt_2,
            ],
        );
        let exec_divmod_bc = d.lemma(p.div_mod_exec, &[one, succ_q]);
        let unique_bc = d.lemma(
            p.div_mod_unique,
            &[
                two,
                succ_q,
                half_q,
                bit_q,
                rec_bc,
                bit_bc,
                exec_divmod_bc,
                candidate_divmod_bc,
            ],
        );
        let half_eq_ty_bc = d.eq(half_q, rec_bc);
        let bit_eq_ty_bc = d.eq(bit_q, bit_bc);
        let half_q_eq = and_left(d, half_eq_ty_bc, bit_eq_ty_bc, unique_bc);
        let bit_q_eq = and_right(d, half_eq_ty_bc, bit_eq_ty_bc, unique_bc);

        // Dichotomize X.
        let dichotomy_x = d.lemma(p.zero_or_succ, &[x]);
        let x_zero_ty = d.eq(x, zero);
        let x_succ_predicate = succ_pred_predicate(d, x);
        let x_succ_exists_ty = succ_pred_exists_ty(d, &p, x_succ_predicate);

        let x_zero_case = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv); // Eq x zero

            let cong_lhs = d.congr(x, zero, hx, &|d, hole| {
                d.const_app(p.land_aux, &[sk, hole, succ_c])
            });
            let lhs_at_zero = d.const_app(p.land_aux, &[sk, zero, succ_c]);
            let lhs_zero_tail = d.refl(zero); // Eq lhs_at_zero zero (both literal 0/succ_c)
            let lhs_is_zero = d.trans(lhs, lhs_at_zero, zero, cong_lhs, lhs_zero_tail);

            // RHS: hyp X=0 is exactly land_aux_eq_zero_of_left_eq_zero's
            // own hypothesis at (sk, succ_a, succ_b, succ_c).
            let rhs_is_zero = d.lemma(
                p.land_aux_eq_zero_of_left_eq_zero,
                &[sk, succ_a, succ_b, succ_c, hx],
            );
            let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
            let body = d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev);
            d.lam_fv(hx_fv, x_zero_ty, body)
        };

        let x_succ_case = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv); // Exists Nat (fun w => Eq x (succ w))

            let p_fv = d.fresh_fvar();
            let pvar = d.kernel().fvar(p_fv);
            let succ_p = d.succ(pvar);
            let hxp_fv = d.fresh_fvar();
            let hxp = d.kernel().fvar(hxp_fv); // Eq x (succ p)
            let hxp_ty = d.eq(x, succ_p);

            let half_p = d.div(succ_p, two);
            let bit_p = d.modulo(succ_p, two);

            // Reconstruct div/mod of succ_p from X's own decomposition
            // (rec_ab, bit_ab) -- the same technique, mirrored onto the
            // OTHER pair.
            let positive2c = d.zero_lt_succ(one);
            let bit_b_lt_2c = d.lemma(p.mod_lt, &[succ_b, two, positive2c]);
            let bit_b_le_1 = d.lemma(p.le_of_lt_succ, &[bit_b, one, bit_b_lt_2c]);
            let bit_ab_le_bit_a = bit_product_le_left(d, &p, bit_a, bit_b, bit_b_le_1);
            let positive2d = d.zero_lt_succ(one);
            let bit_a_lt_2 = d.lemma(p.mod_lt, &[succ_a, two, positive2d]);
            let bit_ab_lt_2 = d.lemma(
                p.lt_of_le_of_lt,
                &[bit_ab, bit_a, two, bit_ab_le_bit_a, bit_a_lt_2],
            );

            let doubled_ab = d.mul(two, rec_ab);
            let add_term_ab = d.add(doubled_ab, bit_ab);
            let candidate_eq_ty_ab = d.eq(succ_p, add_term_ab);
            let candidate_bound_ty_ab = d.lt(bit_ab, two);
            let candidate_eq_ab = d.symm(add_term_ab, succ_p, hxp);
            let candidate_divmod_ab = d.const_app(
                p.logic.and_intro,
                &[
                    candidate_eq_ty_ab,
                    candidate_bound_ty_ab,
                    candidate_eq_ab,
                    bit_ab_lt_2,
                ],
            );
            let exec_divmod_ab = d.lemma(p.div_mod_exec, &[one, succ_p]);
            let unique_ab = d.lemma(
                p.div_mod_unique,
                &[
                    two,
                    succ_p,
                    half_p,
                    bit_p,
                    rec_ab,
                    bit_ab,
                    exec_divmod_ab,
                    candidate_divmod_ab,
                ],
            );
            let half_eq_ty_ab = d.eq(half_p, rec_ab);
            let bit_eq_ty_ab = d.eq(bit_p, bit_ab);
            let half_p_eq = and_left(d, half_eq_ty_ab, bit_eq_ty_ab, unique_ab);
            let bit_p_eq = and_right(d, half_eq_ty_ab, bit_eq_ty_ab, unique_ab);

            let cong_l = d.congr(x, succ_p, hxp, &|d, hole| {
                d.const_app(p.land_aux, &[sk, hole, succ_c])
            });
            let lhs_at_p = d.const_app(p.land_aux, &[sk, succ_p, succ_c]);

            let cong_r = d.congr(y, succ_q, heq, &|d, hole| {
                d.const_app(p.land_aux, &[sk, succ_a, hole])
            });
            let rhs_at_q = d.const_app(p.land_aux, &[sk, succ_a, succ_q]);

            // landAux sk succ_p succ_c reduces to 2*rec_Xc + bit_Xc;
            // landAux sk succ_a succ_q reduces to 2*rec_aY + bit_aY.
            let rec_xc = d.const_app(p.land_aux, &[k, half_p, half_c]);
            let bit_xc = d.mul(bit_p, bit_c);
            let rec_ay = d.const_app(p.land_aux, &[k, half_a, half_q]);
            let bit_ay = d.mul(bit_a, bit_q);

            // rec_Xc -[congr half_p_eq]-> landAux k rec_ab half_c
            //        -[ih at (half_a,half_b,half_c)]-> landAux k half_a rec_bc
            //        -[congr symm(half_q_eq)]-> rec_aY
            let cong_rec1 = d.congr(half_p, rec_ab, half_p_eq, &|d, hole| {
                d.const_app(p.land_aux, &[k, hole, half_c])
            });
            let rec_ab_c = d.const_app(p.land_aux, &[k, rec_ab, half_c]);
            let ih_at = d.apply(ih, &[half_a, half_b, half_c]);
            // ih_at : Eq (landAux k rec_ab half_c) (landAux k half_a rec_bc)
            let half_a_rec_bc = d.const_app(p.land_aux, &[k, half_a, rec_bc]);
            let rec_bc_eq_half_q = d.symm(half_q, rec_bc, half_q_eq);
            let cong_rec2 = d.congr(rec_bc, half_q, rec_bc_eq_half_q, &|d, hole| {
                d.const_app(p.land_aux, &[k, half_a, hole])
            });
            let (_, rec_xc_eq_rec_ay) = d.chain(
                rec_xc,
                &[
                    (rec_ab_c, cong_rec1),
                    (half_a_rec_bc, ih_at),
                    (rec_ay, cong_rec2),
                ],
            );

            // bit_Xc -[congr bit_p_eq]-> mul bit_ab bit_c
            //        -[mul_assoc]-> mul bit_a bit_bc
            //        -[congr symm(bit_q_eq)]-> bit_aY
            let cong_bit1 = d.congr(bit_p, bit_ab, bit_p_eq, &|d, hole| d.mul(hole, bit_c));
            let mul_ab_c = d.mul(bit_ab, bit_c);
            let assoc = d.lemma(p.mul_assoc, &[bit_a, bit_b, bit_c]);
            // assoc : Eq mul_ab_c (mul bit_a bit_bc)
            let mul_a_bc = d.mul(bit_a, bit_bc);
            let bit_bc_eq_bit_q = d.symm(bit_q, bit_bc, bit_q_eq);
            let cong_bit2 = d.congr(bit_bc, bit_q, bit_bc_eq_bit_q, &|d, hole| {
                d.mul(bit_a, hole)
            });
            let (_, bit_xc_eq_bit_ay) = d.chain(
                bit_xc,
                &[
                    (mul_ab_c, cong_bit1),
                    (mul_a_bc, assoc),
                    (bit_ay, cong_bit2),
                ],
            );

            // Lift both equalities through the shared `2 * rec + bit` shape.
            let doubled_xc = d.mul(two, rec_xc);
            let stepped_xc = d.add(doubled_xc, bit_xc);
            let cong_final1 = d.congr(rec_xc, rec_ay, rec_xc_eq_rec_ay, &|d, hole| {
                let doubled = d.mul(two, hole);
                d.add(doubled, bit_xc)
            });
            let doubled_ay = d.mul(two, rec_ay);
            let mid_stepped = d.add(doubled_ay, bit_xc);
            let cong_final2 = d.congr(bit_xc, bit_ay, bit_xc_eq_bit_ay, &|d, hole| {
                let doubled = d.mul(two, rec_ay);
                d.add(doubled, hole)
            });
            let stepped_ay = d.add(doubled_ay, bit_ay);
            let (_, stepped_eq) = d.chain(
                stepped_xc,
                &[(mid_stepped, cong_final1), (stepped_ay, cong_final2)],
            );
            // stepped_eq : Eq stepped_xc stepped_ay, defeq
            // Eq lhs_at_p rhs_at_q (both are `guarded` reductions of the
            // identical shape).

            let cong_r_rev = d.symm(rhs, rhs_at_q, cong_r);
            let (_, body) = d.chain(
                lhs,
                &[
                    (lhs_at_p, cong_l),
                    (rhs_at_q, stepped_eq),
                    (rhs, cong_r_rev),
                ],
            );

            let minor_inner = d.lam_fv(hxp_fv, hxp_ty, body);
            let nat = d.nat_ty();
            let minor = d.lam_fv(p_fv, nat, minor_inner);
            let x_body = exists_elim(d, &p, x_succ_predicate, goal_ty, minor, hx);
            d.lam_fv(hx_fv, x_succ_exists_ty, x_body)
        };

        let dichotomy_x_proof = or_elim(
            d,
            &p,
            x_zero_ty,
            x_succ_exists_ty,
            goal_ty,
            x_zero_case,
            x_succ_case,
            dichotomy_x,
        );

        let minor_inner = d.lam_fv(heq_fv, heq_ty, dichotomy_x_proof);
        let nat = d.nat_ty();
        let minor = d.lam_fv(q_fv, nat, minor_inner);
        let body = exists_elim(d, &p, y_succ_predicate, goal_ty, minor, hy);
        d.lam_fv(hy_fv, y_succ_exists_ty, body)
    };

    or_elim(
        d,
        &p,
        y_zero_ty,
        y_succ_exists_ty,
        goal_ty,
        y_zero_case,
        y_succ_case,
        dichotomy_y,
    )
}

/// `land_aux_assoc_of_fuel : ∀ fuel a b c,
/// Eq (landAux fuel (landAux fuel a b) c) (landAux fuel a (landAux fuel b c))`
/// — see the section doc above.
fn declare_land_aux_assoc_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId, c: ExprId| {
        let x = d.const_app(p.land_aux, &[fuel, a, b]);
        let lhs = d.const_app(p.land_aux, &[fuel, x, c]);
        let y = d.const_app(p.land_aux, &[fuel, b, c]);
        let rhs = d.const_app(p.land_aux, &[fuel, a, y]);
        d.eq(lhs, rhs)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId, c: ExprId| -> ExprId {
        // fuel = 0: both sides defeq `0` regardless of `a`, `b`, `c`.
        let zero = d.zero();
        let x = d.const_app(p.land_aux, &[zero, a, b]);
        let lhs = d.const_app(p.land_aux, &[zero, x, c]);
        d.refl(lhs)
    };

    let step =
        |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId, c: ExprId| -> ExprId {
            let sk = d.succ(k);
            let zero = d.zero();

            cases_zero_succ(
                d,
                c,
                &|d, candidate| {
                    let x = d.const_app(p.land_aux, &[sk, a, b]);
                    let lhs = d.const_app(p.land_aux, &[sk, x, candidate]);
                    let y = d.const_app(p.land_aux, &[sk, b, candidate]);
                    let rhs = d.const_app(p.land_aux, &[sk, a, y]);
                    d.eq(lhs, rhs)
                },
                &|d| {
                    // Leaf 1: c = 0. Both sides defeq 0 -- the outer `n`
                    // slot on each side is the literal `c = 0`.
                    let x = d.const_app(p.land_aux, &[sk, a, b]);
                    let lhs = d.const_app(p.land_aux, &[sk, x, zero]);
                    d.refl(lhs)
                },
                &|d, c_pred| {
                    let succ_c = d.succ(c_pred);
                    cases_zero_succ(
                        d,
                        b,
                        &|d, candidate| {
                            let x = d.const_app(p.land_aux, &[sk, a, candidate]);
                            let lhs = d.const_app(p.land_aux, &[sk, x, succ_c]);
                            let y = d.const_app(p.land_aux, &[sk, candidate, succ_c]);
                            let rhs = d.const_app(p.land_aux, &[sk, a, y]);
                            d.eq(lhs, rhs)
                        },
                        &|d| {
                            // Leaf 2: c = succ_c, b = 0. X = landAux sk a 0
                            // and Y = landAux sk 0 succ_c both reduce to 0
                            // by pure computation, so both outer
                            // applications reduce to 0 regardless of `a`.
                            let x = d.const_app(p.land_aux, &[sk, a, zero]);
                            let lhs = d.const_app(p.land_aux, &[sk, x, succ_c]);
                            d.refl(lhs)
                        },
                        &|d, b_pred| {
                            let succ_b = d.succ(b_pred);
                            cases_zero_succ(
                                d,
                                a,
                                &|d, candidate| {
                                    let x = d.const_app(p.land_aux, &[sk, candidate, succ_b]);
                                    let lhs = d.const_app(p.land_aux, &[sk, x, succ_c]);
                                    let y = d.const_app(p.land_aux, &[sk, succ_b, succ_c]);
                                    let rhs = d.const_app(p.land_aux, &[sk, candidate, y]);
                                    d.eq(lhs, rhs)
                                },
                                &|d| {
                                    // Leaf 3: c = succ_c, b = succ_b, a = 0.
                                    // X = landAux sk 0 succ_b reduces to 0
                                    // by pure computation (chased through
                                    // LHS), so LHS is a pure `refl`. Y is a
                                    // genuine stuck compound, so RHS needs
                                    // `land_aux_zero_left_any_fuel`.
                                    let x = d.const_app(p.land_aux, &[sk, zero, succ_b]);
                                    let lhs = d.const_app(p.land_aux, &[sk, x, succ_c]);
                                    let lhs_is_zero = d.refl(zero);
                                    let y = d.const_app(p.land_aux, &[sk, succ_b, succ_c]);
                                    let rhs = d.const_app(p.land_aux, &[sk, zero, y]);
                                    let rhs_is_zero =
                                        d.lemma(p.land_aux_zero_left_any_fuel, &[sk, y]);
                                    let rhs_is_zero_rev = d.symm(rhs, zero, rhs_is_zero);
                                    d.trans(lhs, zero, rhs, lhs_is_zero, rhs_is_zero_rev)
                                },
                                &|d, a_pred| {
                                    let succ_a = d.succ(a_pred);
                                    declare_land_aux_assoc_hard_leaf(
                                        d, &p, k, ih, succ_a, succ_b, succ_c,
                                    )
                                },
                            )
                        },
                    )
                },
            )
        };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let applied = d.apply(proof_fn, &[a, b, c]);
    let ty = {
        let body = statement(d, fuel, a, b, c);
        let with_c = d.pi_fv(c_fv, nat, body);
        let with_b = d.pi_fv(b_fv, nat, with_c);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_c = d.lam_fv(c_fv, nat, applied);
        let with_b = d.lam_fv(b_fv, nat, with_c);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.land_aux_assoc_of_fuel, ty, value)
}

/// `land_assoc : ∀ a b c, Eq (land (land a b) c) (land a (land b c))` — see
/// the section doc above. Chain, `land_comm`'s pattern one argument wider:
/// pick the shared fuel `F := add a b` (sufficient for `a`, `b`, and
/// `land a b` via `land_le_left` + `le_trans`; `c` never needs its own
/// bound, since `land_aux_agree_of_fuel`'s hypotheses constrain only the
/// `m` position, never `n`), relate `landAux F a b`/`landAux F b c` back to
/// `land a b`/`land b c` via `land_aux_agree_of_fuel`, invoke
/// `land_aux_assoc_of_fuel` at `F`, then relate the two outer `landAux F …`
/// terms back to `land … …` via `land_aux_agree_of_fuel` again.
pub(super) fn declare_land_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_land_aux_assoc_of_fuel(d, p)?;
    let p = *p;
    d.theorem(p.land_assoc, 3, &|d, values| {
        let a = values[0];
        let b = values[1];
        let c = values[2];

        let fuel = d.add(a, b);

        let le_a_fuel = d.lemma(p.le_add_right, &[a, b]); // Le a fuel
        let le_refl_a = d.lemma(p.le_refl, &[a]);

        let le_b_b_a = d.lemma(p.le_add_right, &[b, a]); // Le b (add b a)
        let b_a = d.add(b, a);
        let add_comm_ba = d.lemma(p.add_comm, &[b, a]); // Eq (add b a) (add a b)
        let le_b_motive = d.eq_motive(b_a, &|d, x| d.le(b, x));
        let le_b_fuel = d.transport(b_a, le_b_motive, le_b_b_a, fuel, add_comm_ba);
        let le_refl_b = d.lemma(p.le_refl, &[b]);

        // Le x1 fuel, where x1 := landAux a a b (defeq `land a b`), via
        // `land_le_left` (Le x1 a, by defeq) + `le_trans`.
        let x1 = d.const_app(p.land_aux, &[a, a, b]);
        let le_x1_a = d.lemma(p.land_le_left, &[a, b]); // Le (land a b) a
        let le_x1_fuel = d.lemma(p.le_trans, &[x1, a, fuel, le_x1_a, le_a_fuel]);
        let le_refl_x1 = d.lemma(p.le_refl, &[x1]);

        // step1 : Eq (landAux fuel a b) (landAux a a b) = Eq x0 x1
        let x0 = d.const_app(p.land_aux, &[fuel, a, b]);
        let step1 = d.lemma(
            p.land_aux_agree_of_fuel,
            &[fuel, a, b, a, le_a_fuel, le_refl_a],
        );
        // step2 : Eq (landAux fuel b c) (landAux b b c) = Eq y0 y1
        let y0 = d.const_app(p.land_aux, &[fuel, b, c]);
        let y1 = d.const_app(p.land_aux, &[b, b, c]);
        let step2 = d.lemma(
            p.land_aux_agree_of_fuel,
            &[fuel, b, c, b, le_b_fuel, le_refl_b],
        );

        // step3 : Eq (landAux fuel x0 c) (landAux fuel a y0)
        let step3 = d.lemma(p.land_aux_assoc_of_fuel, &[fuel, a, b, c]);
        let lhs0 = d.const_app(p.land_aux, &[fuel, x0, c]);
        let rhs0 = d.const_app(p.land_aux, &[fuel, a, y0]);

        let cong_left = d.congr(x0, x1, step1, &|d, hole| {
            d.const_app(p.land_aux, &[fuel, hole, c])
        });
        let mid1 = d.const_app(p.land_aux, &[fuel, x1, c]);
        let cong_right = d.congr(y0, y1, step2, &|d, hole| {
            d.const_app(p.land_aux, &[fuel, a, hole])
        });
        let mid2 = d.const_app(p.land_aux, &[fuel, a, y1]);

        let cong_left_rev = d.symm(lhs0, mid1, cong_left);
        let ab_step = d.trans(mid1, lhs0, rhs0, cong_left_rev, step3);
        let ab_final = d.trans(mid1, rhs0, mid2, ab_step, cong_right);
        // ab_final : Eq mid1 mid2
        //   = Eq (landAux fuel x1 c) (landAux fuel a y1)

        // step5 : Eq (landAux fuel x1 c) (landAux x1 x1 c) = Eq mid1 z1
        let step5 = d.lemma(
            p.land_aux_agree_of_fuel,
            &[fuel, x1, c, x1, le_x1_fuel, le_refl_x1],
        );
        let z1 = d.const_app(p.land_aux, &[x1, x1, c]);

        // step6 : Eq (landAux fuel a y1) (landAux a a y1) = Eq mid2 z2
        let step6 = d.lemma(
            p.land_aux_agree_of_fuel,
            &[fuel, a, y1, a, le_a_fuel, le_refl_a],
        );
        let z2 = d.const_app(p.land_aux, &[a, a, y1]);

        let step5_rev = d.symm(mid1, z1, step5);
        let z1_step = d.trans(z1, mid1, mid2, step5_rev, ab_final);
        let proof = d.trans(z1, mid2, z2, z1_step, step6);
        // proof : Eq z1 z2
        //   = Eq (landAux x1 x1 c) (landAux a a y1)
        //  defeq Eq (land (land a b) c) (land a (land b c))

        let lhs = {
            let land_ab = d.const_app(p.land, &[a, b]);
            d.const_app(p.land, &[land_ab, c])
        };
        let rhs = {
            let land_bc = d.const_app(p.land, &[b, c]);
            d.const_app(p.land, &[a, land_bc])
        };
        (d.eq(lhs, rhs), proof)
    })?;
    Ok(())
}

/// Declare [`declare_land_assoc`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_assoc_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_assoc(d, p)?;
    Ok(())
}

// ============================================================================
// `lor_aux_ne_zero_of_right_ne_zero` -- the invariant that plays
// `land_aux_eq_zero_of_left_eq_zero`'s role for `lor`, and NOT its direct
// transport. See `docs/plan/status/266-nat-lor-assoc.md` for the full
// derivation (numerically cross-checked in Python before any Rust) and for
// why the direct analogue ("`lor` propagates zero") is FALSE, not merely
// harder: `lor a b = 0` forces `a = 0 ∧ b = 0`, so `lor a (lor b c)`
// collapses to `c`, not `0`. What DOES hold: at any fuel `succ _`, a
// POSITIVE RIGHT operand alone forces a positive result, regardless of the
// left operand's shape -- confirmed exhaustively over fuel 0..7, m,n 0..13.
// ============================================================================

/// `Not (Eq (mul 2 x) 0)`, given `x_ne_zero : Not (Eq x 0)`. The
/// `mul_eq_zero`/`succ_ne_zero` contrapositive `land`'s zero-propagation
/// lemma already uses in its hard leaf (`declare_land_aux_eq_zero_hard_leaf`,
/// far above), extracted here as a standalone step.
fn double_ne_zero(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, x_ne_zero: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let two = d.num(2);
    let doubled = d.mul(two, x);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let doubled_eq_zero_ty = d.eq(doubled, zero);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv); // Eq (mul 2 x) 0
    let disj = d.lemma(p.mul_eq_zero, &[two, x, h]); // Or (Eq 2 0) (Eq x 0)
    let two_zero_ty = d.eq(two, zero);
    let x_zero_ty = d.eq(x, zero);
    let one = d.num(1);

    let left_case = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv); // Eq 2 0
        let contra = d.lemma(p.succ_ne_zero, &[one, l]); // False (2 = succ 1)
        d.lam_fv(l_fv, two_zero_ty, contra)
    };
    let right_case = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv); // Eq x 0
        let contra = d.apply(x_ne_zero, &[r]); // False
        d.lam_fv(r_fv, x_zero_ty, contra)
    };
    let false_proof = or_elim(
        d,
        &p,
        two_zero_ty,
        x_zero_ty,
        false_ty,
        left_case,
        right_case,
        disj,
    );
    d.lam_fv(h_fv, doubled_eq_zero_ty, false_proof)
}

/// `Not (Eq half_n 0)`, given `heq : Eq succ_n (add (mul 2 half_n) 0)`
/// where `succ_n` is literally `succ n_pred`. If `half_n` WERE `0`, `heq`
/// would transport (via `mul`'s/`add`'s own base-case defeq) to
/// `Eq (succ n_pred) 0`, refuted directly by `Nat.succ_ne_zero`.
fn half_ne_zero_from_heq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n_pred: ExprId,
    half_n: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let succ_n = d.succ(n_pred);
    let zero = d.zero();
    let two = d.num(2);
    let half_zero_ty = d.eq(half_n, zero);

    let sum0 = {
        let doubled = d.mul(two, half_n);
        d.add(doubled, zero)
    };
    let hz_fv = d.fresh_fvar();
    let hz = d.kernel().fvar(hz_fv); // Eq half_n zero
    let cong = d.congr(half_n, zero, hz, &|d, hole| {
        let doubled = d.mul(two, hole);
        d.add(doubled, zero)
    });
    let sum0p = {
        let doubled = d.mul(two, zero);
        d.add(doubled, zero)
    };
    // transported : Eq succ_n sum0p, defeq Eq (succ n_pred) 0.
    let transported = d.trans(succ_n, sum0, sum0p, heq, cong);
    let contra = d.lemma(p.succ_ne_zero, &[n_pred, transported]);
    d.lam_fv(hz_fv, half_zero_ty, contra)
}

/// The "both positive" branch shared by every step case of
/// [`declare_lor_aux_ne_zero_of_right_ne_zero`]'s induction: given the
/// literal successors `succ_m` (so both zero-guards on `lorAux`'s successor
/// row resolve `false` once paired with the caller's own literal `succ_n`),
/// `rec` (the recursive call's value, `lorAux k half_m half_n` at the
/// caller's own predecessor fuel `k`), and a proof that `rec` is nonzero
/// whenever `half_n` is (`rec_ne_zero_of_half_n_ne_zero` -- `ih` applied at
/// the halves), produces
/// `Not (Eq (add (mul 2 rec) (bool_select_nat (ble bit_m bit_n) bit_n
/// bit_m)) 0)` -- i.e. `Not (Eq (lorAux sk succ_m succ_n) 0)` up to the
/// guard-resolution defeq the caller is responsible for (`sk` never
/// appears here; the caller's `rec` already carries it via its OWN fuel
/// argument).
///
/// Case-splits `Nat.mod succ_n 2` (`cases_mod_two`, folding
/// `Nat.div_mod_exec`'s reconstruction equation into an ARROW-typed motive,
/// since the split does not otherwise expose it as a usable hypothesis):
/// bit 1 closes at either bit of `succ_m` via `Nat.succ_ne_zero` alone
/// (`add x 1` is defeq `succ x`, regardless of which branch `bool_select_nat`
/// picks); bit 0 needs `Nat.div_mod_exec` to show `half_n` itself must be
/// nonzero (else `succ_n` would be `0`), then `rec_ne_zero_of_half_n_ne_zero`
/// plus [`double_ne_zero`].
fn lor_aux_pos_both_positive(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n_pred: ExprId,
    succ_m: ExprId,
    rec: ExprId,
    rec_ne_zero_of_half_n_ne_zero: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let succ_n = d.succ(n_pred);
    let zero = d.zero();
    let two = d.num(2);
    let one = d.num(1);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);

    let half_n = d.div(succ_n, two);
    let bit_m = d.modulo(succ_m, two);
    let bit_n = d.modulo(succ_n, two);

    // div_mod_exec(one, succ_n) : divMod 2 succ_n half_n bit_n
    //   = And (Eq succ_n (add (mul 2 half_n) bit_n)) (Lt bit_n 2)
    let divmod_n = d.lemma(p.div_mod_exec, &[one, succ_n]);
    let eq_ty = {
        let doubled = d.mul(two, half_n);
        let sum = d.add(doubled, bit_n);
        d.eq(succ_n, sum)
    };
    let lt_ty = d.lt(bit_n, two);
    let eq_n_decomp = and_left(d, eq_ty, lt_ty, divmod_n);

    // Outer split on `mod succ_n 2`, folding `eq_n_decomp`'s type
    // (parameterized by the remainder) into an arrow motive -- the only way
    // to carry an equation out of a `cases_mod_two` branch into other terms.
    let outer_motive = |d: &mut NatDev<'_>, r: ExprId| -> ExprId {
        let heq_ty = {
            let doubled = d.mul(two, half_n);
            let sum = d.add(doubled, r);
            d.eq(succ_n, sum)
        };
        let ble_mr = d.ble(bit_m, r);
        let bit_or_r = d.bool_select_nat(ble_mr, r, bit_m);
        let stepped_r = {
            let doubled = d.mul(two, rec);
            d.add(doubled, bit_or_r)
        };
        let concl = {
            let eq0 = d.eq(stepped_r, zero);
            d.arrow(eq0, false_ty)
        };
        d.arrow(heq_ty, concl)
    };

    // r = 1: `bool_select_nat (ble bit_m 1) 1 bit_m` reduces to the literal
    // `1` at EITHER concrete `bit_m` (`ble(0,1)`/`ble(1,1)` both reduce to
    // `true`), so `add (mul 2 rec) 1` is defeq `succ (mul 2 rec)` and
    // `succ_ne_zero` closes it without ever touching `heq` or `rec`'s value.
    let at_one = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = {
            let doubled = d.mul(two, half_n);
            let sum = d.add(doubled, one);
            d.eq(succ_n, sum)
        };
        let succ_ne = {
            let doubled = d.mul(two, rec);
            d.lemma(p.succ_ne_zero, &[doubled])
        };
        let bit_m_motive = |d: &mut NatDev<'_>, s: ExprId| -> ExprId {
            let ble_s1 = d.ble(s, one);
            let bit_or_s = d.bool_select_nat(ble_s1, one, s);
            let stepped_s = {
                let doubled = d.mul(two, rec);
                d.add(doubled, bit_or_s)
            };
            let eq0 = d.eq(stepped_s, zero);
            d.arrow(eq0, false_ty)
        };
        let body = cases_mod_two(d, &p, succ_m, &bit_m_motive, succ_ne, succ_ne);
        d.lam_fv(heq_fv, heq_ty, body)
    };

    // r = 0: `bool_select_nat (ble bit_m 0) 0 bit_m` reduces to `bit_m`
    // itself (`max(bit_m, 0) = bit_m`), split further:
    //   bit_m = 1: same `add x 1` trick as above, `heq` unused.
    //   bit_m = 0: `stepped` is defeq `mul 2 rec`; need `Not (Eq rec 0)`,
    //     from `half_n`'s OWN nonzero-ness (via `heq` + `succ_ne_zero`) and
    //     the caller's `rec_ne_zero_of_half_n_ne_zero`.
    let at_zero = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = {
            let doubled = d.mul(two, half_n);
            let sum = d.add(doubled, zero);
            d.eq(succ_n, sum)
        };
        let at_one_bm = {
            let doubled = d.mul(two, rec);
            d.lemma(p.succ_ne_zero, &[doubled])
        };
        let at_zero_bm = {
            let half_ne_zero = half_ne_zero_from_heq(d, &p, n_pred, half_n, heq);
            let rec_ne_zero = rec_ne_zero_of_half_n_ne_zero(d, half_ne_zero);
            double_ne_zero(d, &p, rec, rec_ne_zero)
        };
        let bit_m_motive = |d: &mut NatDev<'_>, s: ExprId| -> ExprId {
            let ble_s0 = d.ble(s, zero);
            let bit_or_s = d.bool_select_nat(ble_s0, zero, s);
            let stepped_s = {
                let doubled = d.mul(two, rec);
                d.add(doubled, bit_or_s)
            };
            let eq0 = d.eq(stepped_s, zero);
            d.arrow(eq0, false_ty)
        };
        let body = cases_mod_two(d, &p, succ_m, &bit_m_motive, at_zero_bm, at_one_bm);
        d.lam_fv(heq_fv, heq_ty, body)
    };

    let folded = cases_mod_two(d, &p, succ_n, &outer_motive, at_zero, at_one);
    d.apply(folded, &[eq_n_decomp])
}

/// `Nat.lor_aux_ne_zero_of_right_ne_zero : ∀ fuel m n, Not (Eq n 0) →
/// Not (Eq (lorAux fuel m n) 0)`. Unconditional in `fuel` -- at `fuel = 0`,
/// `lorAux 0 m n` is defeq `n` regardless of `m`, so the goal IS the
/// hypothesis. See the section doc above for the both-positive branch.
fn declare_lor_aux_ne_zero_of_right_ne_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, m: ExprId, n: ExprId| -> ExprId {
        let zero = d.zero();
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let n_eq_zero = d.eq(n, zero);
        let hyp = d.arrow(n_eq_zero, false_ty);
        let lor_val = d.const_app(p.lor_aux, &[fuel, m, n]);
        let val_eq_zero = d.eq(lor_val, zero);
        let concl = d.arrow(val_eq_zero, false_ty);
        d.arrow(hyp, concl)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId| -> ExprId {
        let zero = d.zero();
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hn_ty = {
            let eq = d.eq(n, zero);
            d.arrow(eq, false_ty)
        };
        let _ = m; // `lorAux 0 m n` ignores `m` entirely.
        // `lorAux 0 m n` is defeq `n`, so the goal IS the hypothesis.
        d.lam_fv(hn_fv, hn_ty, hn)
    };

    // `step`'s hypothesis about `n` (`Not (Eq n 0)`) must be folded into
    // `cases_zero_succ`'s own ARROW-typed motive, not built separately
    // before the split and wrapped afterward: `Nat.rec`'s branches only
    // substitute the case-split variable through the MOTIVE, never through
    // an independently-built term referencing the original (still-generic)
    // `n` -- a hypothesis built outside the split stays a hypothesis about
    // the ORIGINAL `n` inside every branch, never specializing to the
    // branch's own literal. Matches
    // `declare_land_aux_eq_zero_of_left_eq_zero`'s exact convention.
    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, m: ExprId, n: ExprId| -> ExprId {
        let zero = d.zero();
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let sk = d.succ(k);

        let goal_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let n_eq_zero = d.eq(candidate, zero);
            let hyp = d.arrow(n_eq_zero, false_ty);
            let lor_val = d.const_app(p.lor_aux, &[sk, m, candidate]);
            let eq0 = d.eq(lor_val, zero);
            let concl = d.arrow(eq0, false_ty);
            d.arrow(hyp, concl)
        };

        cases_zero_succ(
            d,
            n,
            &goal_at,
            &|d| {
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);
                let hn_ty = {
                    let eq = d.eq(zero, zero);
                    d.arrow(eq, false_ty)
                };
                let refl0 = d.refl(zero);
                let contradiction = d.apply(hn, &[refl0]);
                let goal = {
                    let lor_val = d.const_app(p.lor_aux, &[sk, m, zero]);
                    let eq0 = d.eq(lor_val, zero);
                    d.arrow(eq0, false_ty)
                };
                let body = absurd(d, goal, contradiction);
                d.lam_fv(hn_fv, hn_ty, body)
            },
            &|d, n_pred| {
                let succ_n = d.succ(n_pred);
                // `hn` is unused here: `succ_n` is already known nonzero via
                // `succ_ne_zero`, without needing this hypothesis.
                let hn_fv = d.fresh_fvar();
                let hn_ty = {
                    let eq = d.eq(succ_n, zero);
                    d.arrow(eq, false_ty)
                };

                let goal_m_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
                    let lor_val = d.const_app(p.lor_aux, &[sk, candidate, succ_n]);
                    let eq0 = d.eq(lor_val, zero);
                    d.arrow(eq0, false_ty)
                };

                let inner = cases_zero_succ(
                    d,
                    m,
                    &goal_m_at,
                    &|d| d.lemma(p.succ_ne_zero, &[n_pred]),
                    &|d, m_pred| {
                        let succ_m = d.succ(m_pred);
                        let two = d.num(2);
                        let half_m = d.div(succ_m, two);
                        let half_n = d.div(succ_n, two);
                        let rec = d.const_app(p.lor_aux, &[k, half_m, half_n]);
                        lor_aux_pos_both_positive(d, &p, n_pred, succ_m, rec, &|d, half_ne_zero| {
                            let applied = d.apply(ih, &[half_m, half_n]);
                            d.apply(applied, &[half_ne_zero])
                        })
                    },
                );
                d.lam_fv(hn_fv, hn_ty, inner)
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let applied = d.apply(proof_fn, &[m, n]);
    let ty = {
        let body = statement(d, fuel, m, n);
        let with_n = d.pi_fv(n_fv, nat, body);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel_fv, nat, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, applied);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel_fv, nat, with_m)
    };
    d.declare_theorem(p.lor_aux_ne_zero_of_right_ne_zero, ty, value)
}

/// Declare [`declare_lor_aux_ne_zero_of_right_ne_zero`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_lor_aux_ne_zero_of_right_ne_zero_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_lor_aux_ne_zero_of_right_ne_zero(d, p)?;
    Ok(())
}

// ============================================================================
// `lor_aux_assoc_of_fuel` / `lor_assoc` / `lor_aux_le_add` -- see
// `docs/plan/status/266-nat-lor-assoc.md` for the fully hand-traced,
// Python-simulated derivation this transcribes (the `land_assoc` counterpart
// is `docs/plan/status/257-nat-land-assoc-impl.md`). SIMPLER than `land`'s
// hard leaf once `lor_aux_ne_zero_of_right_ne_zero` exists: the two stuck
// intermediates are unconditionally positive here, so both dichotomies'
// `= 0` branches close by direct contradiction rather than a mirrored
// propagation argument.
// ============================================================================

/// `Eq (bool_select_nat (ble (mod a 2) (mod b 2)) (mod b 2) (mod a 2))
///     (add (mod a 2) (mod b 2))`? No -- this is `max`, not a helper for
/// `lor_bit_assoc`; see [`lor_bit_le_sum`] below for the sum bound.
///
/// `Eq (bool_select_nat cond bit_b bit_a) 2`-bounded value at either branch,
/// via `Bool.rec` directly (the same recursor [`bool_select_nat_same`]
/// uses): `Lt bit_a 2` closes the `false` branch, `Lt bit_b 2` closes the
/// `true` branch, matching `combine`'s own `on_false`/`on_true` convention
/// (`bool_select_nat(cond, on_true, on_false)` applies `Bool.rec` as
/// `[motive, on_false, on_true, cond]`).
fn lor_bit_lt_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    bit_a: ExprId,
    bit_b: ExprId,
    bit_a_lt_2: ExprId,
    bit_b_lt_2: ExprId,
) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let two = d.num(2);
    let cond = d.ble(bit_a, bit_b);
    let motive = |d: &mut NatDev<'_>, c: ExprId| -> ExprId {
        let sel = d.bool_select_nat(c, bit_b, bit_a);
        d.lt(sel, two)
    };
    let motive_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = motive(d, c);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive_lam, bit_a_lt_2, bit_b_lt_2, cond])
}

/// `Eq (max (max bit_a bit_b) bit_c) (max bit_a (max bit_b bit_c))`, where
/// `bit_a := mod a 2` etc. and `max` is the `bool_select_nat`/`ble` shape
/// `lor`'s own per-bit combine uses (`lor_bit_comm`'s `combine`). Needed by
/// [`declare_lor_aux_assoc_hard_leaf`] in place of `Nat.mul_assoc` for
/// `land`'s analogous step.
///
/// Three nested [`cases_mod_two`] (`a`, then `b`, then `c`), 8 leaves at
/// concrete `{0,1}` triples, each closing by `d.refl` (associativity of
/// `max` over `{0,1}` is trivially true at all 8 combinations, confirmed in
/// Python before any Rust).
fn lor_bit_assoc(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bit_b = d.modulo(b, two);
    let bit_c = d.modulo(c, two);

    let combine = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let xy = combine(d, x, y);
        let lhs = combine(d, xy, z);
        let yz = combine(d, y, z);
        let rhs = combine(d, x, yz);
        d.eq(lhs, rhs)
    };
    let leaf = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let xy = combine(d, x, y);
        let lhs = combine(d, xy, z);
        d.refl(lhs)
    };

    let zero = d.zero();
    let one = d.num(1);

    let inner_at = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let at_zero = leaf(d, x, y, zero);
        let at_one = leaf(d, x, y, one);
        cases_mod_two(d, &p, c, &|d, z| claim(d, x, y, z), at_zero, at_one)
    };

    let middle_at = |d: &mut NatDev<'_>, x: ExprId| {
        let at_zero = inner_at(d, x, zero);
        let at_one = inner_at(d, x, one);
        cases_mod_two(d, &p, b, &|d, y| claim(d, x, y, bit_c), at_zero, at_one)
    };

    let outer_zero = middle_at(d, zero);
    let outer_one = middle_at(d, one);
    cases_mod_two(
        d,
        &p,
        a,
        &|d, x| claim(d, x, bit_b, bit_c),
        outer_zero,
        outer_one,
    )
}

/// The hard leaf of [`declare_lor_aux_assoc_of_fuel`]: `a = succ_a`,
/// `b = succ_b`, `c = succ_c` (all literal successors), at fuel
/// `sk = succ k`. Builds a term of type
/// `Eq (lorAux sk (lorAux sk succ_a succ_b) succ_c)
///     (lorAux sk succ_a (lorAux sk succ_b succ_c))`.
///
/// `ih : forall a b c, Eq (lorAux k (lorAux k a b) c) (lorAux k a (lorAux k b c))`
/// is the outer induction's own hypothesis, applied at the halves.
///
/// SIMPLER than [`declare_land_aux_assoc_hard_leaf`]: `X := lorAux sk succ_a
/// succ_b` and `Y := lorAux sk succ_b succ_c` are UNCONDITIONALLY positive
/// here (via [`declare_lor_aux_ne_zero_of_right_ne_zero`] applied at
/// `succ_b`/`succ_c` respectively), so both dichotomies' `= 0` branches
/// close by direct contradiction rather than a mirrored propagation
/// argument. `b_pred`/`c_pred` are the already-exposed predecessors from the
/// caller's own `cases_zero_succ` chain (`succ_b = succ b_pred`,
/// `succ_c = succ c_pred`), needed to invoke `Nat.succ_ne_zero`.
#[allow(clippy::too_many_arguments)]
fn declare_lor_aux_assoc_hard_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    ih: ExprId,
    succ_a: ExprId,
    succ_b: ExprId,
    succ_c: ExprId,
    b_pred: ExprId,
    c_pred: ExprId,
) -> ExprId {
    let p = *p;
    let sk = d.succ(k);
    let zero = d.zero();
    let two = d.num(2);
    let one = d.num(1);

    let half_a = d.div(succ_a, two);
    let half_b = d.div(succ_b, two);
    let half_c = d.div(succ_c, two);
    let bit_a = d.modulo(succ_a, two);
    let bit_b = d.modulo(succ_b, two);
    let bit_c = d.modulo(succ_c, two);

    let bit_or = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };

    let rec_ab = d.const_app(p.lor_aux, &[k, half_a, half_b]);
    let bit_ab = bit_or(d, bit_a, bit_b);
    let rec_bc = d.const_app(p.lor_aux, &[k, half_b, half_c]);
    let bit_bc = bit_or(d, bit_b, bit_c);

    // X, Y: both stuck compounds (both guards resolve `false`, operands
    // literal `succ`, but the recursive/bit values are opaque) -- and, via
    // `lor_aux_ne_zero_of_right_ne_zero`, both UNCONDITIONALLY positive.
    let x = d.const_app(p.lor_aux, &[sk, succ_a, succ_b]);
    let y = d.const_app(p.lor_aux, &[sk, succ_b, succ_c]);

    let lhs = d.const_app(p.lor_aux, &[sk, x, succ_c]);
    let rhs = d.const_app(p.lor_aux, &[sk, succ_a, y]);
    let goal_ty = d.eq(lhs, rhs);

    let not_succ_b_zero = d.lemma(p.succ_ne_zero, &[b_pred]);
    let not_x_zero = d.lemma(
        p.lor_aux_ne_zero_of_right_ne_zero,
        &[sk, succ_a, succ_b, not_succ_b_zero],
    );
    let not_succ_c_zero = d.lemma(p.succ_ne_zero, &[c_pred]);
    let not_y_zero = d.lemma(
        p.lor_aux_ne_zero_of_right_ne_zero,
        &[sk, succ_b, succ_c, not_succ_c_zero],
    );

    let dichotomy_x = d.lemma(p.zero_or_succ, &[x]);
    let x_zero_ty = d.eq(x, zero);
    let x_succ_predicate = succ_pred_predicate(d, x);
    let x_succ_exists_ty = succ_pred_exists_ty(d, &p, x_succ_predicate);

    let x_zero_case = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv); // Eq x zero
        let contradiction = d.apply(not_x_zero, &[hx]);
        let body = absurd(d, goal_ty, contradiction);
        d.lam_fv(hx_fv, x_zero_ty, body)
    };

    let x_succ_case = {
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv); // Exists Nat (fun w => Eq x (succ w))

        let p_fv = d.fresh_fvar();
        let pvar = d.kernel().fvar(p_fv);
        let succ_p = d.succ(pvar);
        let hxp_fv = d.fresh_fvar();
        let hxp = d.kernel().fvar(hxp_fv); // Eq x (succ p)
        let hxp_ty = d.eq(x, succ_p);

        let half_p = d.div(succ_p, two);
        let bit_p = d.modulo(succ_p, two);

        // Reconstruct div/mod of succ_p from X's own decomposition
        // (rec_ab, bit_ab). The `< 2` bound on `bit_ab = max bit_a bit_b`
        // is direct (it's EITHER bit_a or bit_b, both < 2 via `mod_lt`),
        // via `lor_bit_lt_two` rather than land's `bit_product_le_left` +
        // `lt_of_le_of_lt` chain (that bound is `mul`-specific).
        let positive2a = d.zero_lt_succ(one);
        let bit_a_lt_2 = d.lemma(p.mod_lt, &[succ_a, two, positive2a]);
        let positive2b = d.zero_lt_succ(one);
        let bit_b_lt_2 = d.lemma(p.mod_lt, &[succ_b, two, positive2b]);
        let bit_ab_lt_2 = lor_bit_lt_two(d, &p, bit_a, bit_b, bit_a_lt_2, bit_b_lt_2);

        let doubled_ab = d.mul(two, rec_ab);
        let add_term_ab = d.add(doubled_ab, bit_ab);
        let candidate_eq_ty_ab = d.eq(succ_p, add_term_ab);
        let candidate_bound_ty_ab = d.lt(bit_ab, two);
        let candidate_eq_ab = d.symm(add_term_ab, succ_p, hxp);
        let candidate_divmod_ab = d.const_app(
            p.logic.and_intro,
            &[
                candidate_eq_ty_ab,
                candidate_bound_ty_ab,
                candidate_eq_ab,
                bit_ab_lt_2,
            ],
        );
        let exec_divmod_ab = d.lemma(p.div_mod_exec, &[one, succ_p]);
        let unique_ab = d.lemma(
            p.div_mod_unique,
            &[
                two,
                succ_p,
                half_p,
                bit_p,
                rec_ab,
                bit_ab,
                exec_divmod_ab,
                candidate_divmod_ab,
            ],
        );
        let half_eq_ty_ab = d.eq(half_p, rec_ab);
        let bit_eq_ty_ab = d.eq(bit_p, bit_ab);
        let half_p_eq = and_left(d, half_eq_ty_ab, bit_eq_ty_ab, unique_ab);
        let bit_p_eq = and_right(d, half_eq_ty_ab, bit_eq_ty_ab, unique_ab);

        // Dichotomize Y.
        let dichotomy_y = d.lemma(p.zero_or_succ, &[y]);
        let y_zero_ty = d.eq(y, zero);
        let y_succ_predicate = succ_pred_predicate(d, y);
        let y_succ_exists_ty = succ_pred_exists_ty(d, &p, y_succ_predicate);

        let y_zero_case = {
            let hy_fv = d.fresh_fvar();
            let hy = d.kernel().fvar(hy_fv); // Eq y zero
            let contradiction = d.apply(not_y_zero, &[hy]);
            let body = absurd(d, goal_ty, contradiction);
            d.lam_fv(hy_fv, y_zero_ty, body)
        };

        let y_succ_case = {
            let hy_fv = d.fresh_fvar();
            let hy = d.kernel().fvar(hy_fv); // Exists Nat (fun w => Eq y (succ w))

            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let succ_q = d.succ(q);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv); // Eq y (succ q)
            let heq_ty = d.eq(y, succ_q);

            let half_q = d.div(succ_q, two);
            let bit_q = d.modulo(succ_q, two);

            let positive2c = d.zero_lt_succ(one);
            let bit_b_lt_2c = d.lemma(p.mod_lt, &[succ_b, two, positive2c]);
            let positive2d = d.zero_lt_succ(one);
            let bit_c_lt_2 = d.lemma(p.mod_lt, &[succ_c, two, positive2d]);
            let bit_bc_lt_2 = lor_bit_lt_two(d, &p, bit_b, bit_c, bit_b_lt_2c, bit_c_lt_2);

            let doubled_bc = d.mul(two, rec_bc);
            let add_term_bc = d.add(doubled_bc, bit_bc);
            let candidate_eq_ty_bc = d.eq(succ_q, add_term_bc);
            let candidate_bound_ty_bc = d.lt(bit_bc, two);
            let candidate_eq_bc = d.symm(add_term_bc, succ_q, heq);
            let candidate_divmod_bc = d.const_app(
                p.logic.and_intro,
                &[
                    candidate_eq_ty_bc,
                    candidate_bound_ty_bc,
                    candidate_eq_bc,
                    bit_bc_lt_2,
                ],
            );
            let exec_divmod_bc = d.lemma(p.div_mod_exec, &[one, succ_q]);
            let unique_bc = d.lemma(
                p.div_mod_unique,
                &[
                    two,
                    succ_q,
                    half_q,
                    bit_q,
                    rec_bc,
                    bit_bc,
                    exec_divmod_bc,
                    candidate_divmod_bc,
                ],
            );
            let half_eq_ty_bc = d.eq(half_q, rec_bc);
            let bit_eq_ty_bc = d.eq(bit_q, bit_bc);
            let half_q_eq = and_left(d, half_eq_ty_bc, bit_eq_ty_bc, unique_bc);
            let bit_q_eq = and_right(d, half_eq_ty_bc, bit_eq_ty_bc, unique_bc);

            let cong_l = d.congr(x, succ_p, hxp, &|d, hole| {
                d.const_app(p.lor_aux, &[sk, hole, succ_c])
            });
            let lhs_at_p = d.const_app(p.lor_aux, &[sk, succ_p, succ_c]);

            let cong_r = d.congr(y, succ_q, heq, &|d, hole| {
                d.const_app(p.lor_aux, &[sk, succ_a, hole])
            });
            let rhs_at_q = d.const_app(p.lor_aux, &[sk, succ_a, succ_q]);

            let rec_xc = d.const_app(p.lor_aux, &[k, half_p, half_c]);
            let bit_xc = bit_or(d, bit_p, bit_c);
            let rec_ay = d.const_app(p.lor_aux, &[k, half_a, half_q]);
            let bit_ay = bit_or(d, bit_a, bit_q);

            let cong_rec1 = d.congr(half_p, rec_ab, half_p_eq, &|d, hole| {
                d.const_app(p.lor_aux, &[k, hole, half_c])
            });
            let rec_ab_c = d.const_app(p.lor_aux, &[k, rec_ab, half_c]);
            let ih_at = d.apply(ih, &[half_a, half_b, half_c]);
            // ih_at : Eq (lorAux k rec_ab half_c) (lorAux k half_a rec_bc)
            let half_a_rec_bc = d.const_app(p.lor_aux, &[k, half_a, rec_bc]);
            let rec_bc_eq_half_q = d.symm(half_q, rec_bc, half_q_eq);
            let cong_rec2 = d.congr(rec_bc, half_q, rec_bc_eq_half_q, &|d, hole| {
                d.const_app(p.lor_aux, &[k, half_a, hole])
            });
            let (_, rec_xc_eq_rec_ay) = d.chain(
                rec_xc,
                &[
                    (rec_ab_c, cong_rec1),
                    (half_a_rec_bc, ih_at),
                    (rec_ay, cong_rec2),
                ],
            );

            // bit_Xc -[congr bit_p_eq]-> bit_or bit_ab bit_c
            //        -[lor_bit_assoc]-> bit_or bit_a bit_bc
            //        -[congr symm(bit_q_eq)]-> bit_aY
            let cong_bit1 = d.congr(bit_p, bit_ab, bit_p_eq, &|d, hole| bit_or(d, hole, bit_c));
            let mul_ab_c = bit_or(d, bit_ab, bit_c);
            let assoc = lor_bit_assoc(d, &p, succ_a, succ_b, succ_c);
            // assoc : Eq (bit_or bit_ab bit_c) (bit_or bit_a bit_bc)
            let mul_a_bc = bit_or(d, bit_a, bit_bc);
            let bit_bc_eq_bit_q = d.symm(bit_q, bit_bc, bit_q_eq);
            let cong_bit2 = d.congr(bit_bc, bit_q, bit_bc_eq_bit_q, &|d, hole| {
                bit_or(d, bit_a, hole)
            });
            let (_, bit_xc_eq_bit_ay) = d.chain(
                bit_xc,
                &[
                    (mul_ab_c, cong_bit1),
                    (mul_a_bc, assoc),
                    (bit_ay, cong_bit2),
                ],
            );

            let doubled_xc = d.mul(two, rec_xc);
            let stepped_xc = d.add(doubled_xc, bit_xc);
            let cong_final1 = d.congr(rec_xc, rec_ay, rec_xc_eq_rec_ay, &|d, hole| {
                let doubled = d.mul(two, hole);
                d.add(doubled, bit_xc)
            });
            let doubled_ay = d.mul(two, rec_ay);
            let mid_stepped = d.add(doubled_ay, bit_xc);
            let cong_final2 = d.congr(bit_xc, bit_ay, bit_xc_eq_bit_ay, &|d, hole| {
                let doubled = d.mul(two, rec_ay);
                d.add(doubled, hole)
            });
            let stepped_ay = d.add(doubled_ay, bit_ay);
            let (_, stepped_eq) = d.chain(
                stepped_xc,
                &[(mid_stepped, cong_final1), (stepped_ay, cong_final2)],
            );

            let cong_r_rev = d.symm(rhs, rhs_at_q, cong_r);
            let (_, body) = d.chain(
                lhs,
                &[
                    (lhs_at_p, cong_l),
                    (rhs_at_q, stepped_eq),
                    (rhs, cong_r_rev),
                ],
            );

            let minor_inner = d.lam_fv(heq_fv, heq_ty, body);
            let nat = d.nat_ty();
            let minor = d.lam_fv(q_fv, nat, minor_inner);
            let y_body = exists_elim(d, &p, y_succ_predicate, goal_ty, minor, hy);
            d.lam_fv(hy_fv, y_succ_exists_ty, y_body)
        };

        let dichotomy_y_proof = or_elim(
            d,
            &p,
            y_zero_ty,
            y_succ_exists_ty,
            goal_ty,
            y_zero_case,
            y_succ_case,
            dichotomy_y,
        );

        let minor_inner = d.lam_fv(hxp_fv, hxp_ty, dichotomy_y_proof);
        let nat = d.nat_ty();
        let minor = d.lam_fv(p_fv, nat, minor_inner);
        let body = exists_elim(d, &p, x_succ_predicate, goal_ty, minor, hx);
        d.lam_fv(hx_fv, x_succ_exists_ty, body)
    };

    or_elim(
        d,
        &p,
        x_zero_ty,
        x_succ_exists_ty,
        goal_ty,
        x_zero_case,
        x_succ_case,
        dichotomy_x,
    )
}

/// `lor_aux_assoc_of_fuel : ∀ fuel a b c,
/// Eq (lorAux fuel (lorAux fuel a b) c) (lorAux fuel a (lorAux fuel b c))`
/// — see the section doc above. SIMPLER than
/// [`declare_land_aux_assoc_of_fuel`]'s analogous leaves 1-3: each closes
/// by pure computation (defeq congruence through a reduced subterm), never
/// needing a case split on the third variable or an extra lemma call except
/// leaf 3's `lor_aux_zero_left_any_fuel`.
fn declare_lor_aux_assoc_of_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, a: ExprId, b: ExprId, c: ExprId| {
        let x = d.const_app(p.lor_aux, &[fuel, a, b]);
        let lhs = d.const_app(p.lor_aux, &[fuel, x, c]);
        let y = d.const_app(p.lor_aux, &[fuel, b, c]);
        let rhs = d.const_app(p.lor_aux, &[fuel, a, y]);
        d.eq(lhs, rhs)
    };

    let base = |d: &mut NatDev<'_>, a: ExprId, b: ExprId, c: ExprId| -> ExprId {
        // fuel = 0: lorAux 0 m n is defeq n regardless of m, so X := lorAux
        // 0 a b is defeq b, LHS := lorAux 0 X c is defeq c; Y := lorAux 0 b
        // c is defeq c, RHS := lorAux 0 a Y is defeq c. Both sides defeq
        // `c` directly -- one `refl`, no case split needed at all.
        let zero = d.zero();
        let x = d.const_app(p.lor_aux, &[zero, a, b]);
        let lhs = d.const_app(p.lor_aux, &[zero, x, c]);
        d.refl(lhs)
    };

    let step =
        |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, a: ExprId, b: ExprId, c: ExprId| -> ExprId {
            let sk = d.succ(k);

            cases_zero_succ(
                d,
                c,
                &|d, candidate| {
                    let x = d.const_app(p.lor_aux, &[sk, a, b]);
                    let lhs = d.const_app(p.lor_aux, &[sk, x, candidate]);
                    let y = d.const_app(p.lor_aux, &[sk, b, candidate]);
                    let rhs = d.const_app(p.lor_aux, &[sk, a, y]);
                    d.eq(lhs, rhs)
                },
                &|d| {
                    // Leaf 1: c = 0. X = lorAux sk a b (unsplit). LHS =
                    // lorAux sk X 0 defeq X (literal n=0). Y = lorAux sk b
                    // 0 defeq b (same rule). RHS = lorAux sk a Y is defeq
                    // lorAux sk a b = X via congruence (Y defeq b). Both
                    // sides defeq X -- zero lemmas.
                    let zero = d.zero();
                    let x = d.const_app(p.lor_aux, &[sk, a, b]);
                    let lhs = d.const_app(p.lor_aux, &[sk, x, zero]);
                    d.refl(lhs)
                },
                &|d, c_pred| {
                    let succ_c = d.succ(c_pred);
                    cases_zero_succ(
                        d,
                        b,
                        &|d, candidate| {
                            let x = d.const_app(p.lor_aux, &[sk, a, candidate]);
                            let lhs = d.const_app(p.lor_aux, &[sk, x, succ_c]);
                            let y = d.const_app(p.lor_aux, &[sk, candidate, succ_c]);
                            let rhs = d.const_app(p.lor_aux, &[sk, a, y]);
                            d.eq(lhs, rhs)
                        },
                        &|d| {
                            // Leaf 2: c = succ_c, b = 0. X = lorAux sk a 0
                            // defeq a (literal n=b=0). Y = lorAux sk 0
                            // succ_c defeq succ_c (both checks resolve via
                            // literals: outer n=succ_c fails, inner m=0
                            // succeeds -> on_m_zero = succ_c). LHS and RHS
                            // both defeq lorAux sk a succ_c -- zero
                            // lemmas, `a` never case split.
                            let zero = d.zero();
                            let x = d.const_app(p.lor_aux, &[sk, a, zero]);
                            let lhs = d.const_app(p.lor_aux, &[sk, x, succ_c]);
                            d.refl(lhs)
                        },
                        &|d, b_pred| {
                            let succ_b = d.succ(b_pred);
                            cases_zero_succ(
                                d,
                                a,
                                &|d, candidate| {
                                    let x = d.const_app(p.lor_aux, &[sk, candidate, succ_b]);
                                    let lhs = d.const_app(p.lor_aux, &[sk, x, succ_c]);
                                    let y = d.const_app(p.lor_aux, &[sk, succ_b, succ_c]);
                                    let rhs = d.const_app(p.lor_aux, &[sk, candidate, y]);
                                    d.eq(lhs, rhs)
                                },
                                &|d| {
                                    // Leaf 3: c = succ_c, b = succ_b, a = 0.
                                    // X = lorAux sk 0 succ_b: outer check
                                    // n=succ_b fails (literal succ); inner
                                    // check m=0 succeeds -> X defeq succ_b
                                    // (pure reduction). LHS = lorAux sk X
                                    // succ_c is defeq lorAux sk succ_b
                                    // succ_c = Y via congruence. Y itself
                                    // is a genuine stuck compound. RHS =
                                    // lorAux sk 0 Y: outer check n=Y is
                                    // STUCK (not literal), so needs
                                    // `lor_aux_zero_left_any_fuel`.
                                    let zero = d.zero();
                                    let x = d.const_app(p.lor_aux, &[sk, zero, succ_b]);
                                    let lhs = d.const_app(p.lor_aux, &[sk, x, succ_c]);
                                    let y = d.const_app(p.lor_aux, &[sk, succ_b, succ_c]);
                                    let lhs_is_y = d.refl(y);
                                    let rhs = d.const_app(p.lor_aux, &[sk, zero, y]);
                                    let rhs_is_y = d.lemma(p.lor_aux_zero_left_any_fuel, &[sk, y]);
                                    let rhs_is_y_rev = d.symm(rhs, y, rhs_is_y);
                                    d.trans(lhs, y, rhs, lhs_is_y, rhs_is_y_rev)
                                },
                                &|d, a_pred| {
                                    let succ_a = d.succ(a_pred);
                                    declare_lor_aux_assoc_hard_leaf(
                                        d, &p, k, ih, succ_a, succ_b, succ_c, b_pred, c_pred,
                                    )
                                },
                            )
                        },
                    )
                },
            )
        };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_double_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let applied = d.apply(proof_fn, &[a, b, c]);
    let ty = {
        let body = statement(d, fuel, a, b, c);
        let with_c = d.pi_fv(c_fv, nat, body);
        let with_b = d.pi_fv(b_fv, nat, with_c);
        let with_a = d.pi_fv(a_fv, nat, with_b);
        d.pi_fv(fuel_fv, nat, with_a)
    };
    let value = {
        let with_c = d.lam_fv(c_fv, nat, applied);
        let with_b = d.lam_fv(b_fv, nat, with_c);
        let with_a = d.lam_fv(a_fv, nat, with_b);
        d.lam_fv(fuel_fv, nat, with_a)
    };
    d.declare_theorem(p.lor_aux_assoc_of_fuel, ty, value)
}

/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as a `(target, proof)` chain step,
/// the proof's source being `add(add(a,b),add(c,d))`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`binomial.rs`, `div_mod_lemmas.rs`,
/// `finite_set.rs`, `fibonacci.rs`, `subset_sum.rs`,
/// `count_range_reversal.rs`, `eisenstein_lemma.rs`).
fn add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let target = d.add(ac, bd);
    // Generic-then-apply (`prove_eq_at`): a caller may pass compound
    // arguments outside the ring fragment; `prove_eq` on the literal terms
    // would (correctly) decline `NonRing` on those.
    let proof = crate::ring::nat::prove_eq_at(d, p, &[a, b, c, dd], &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let cd = d.add(c, dd);
        let lhs = d.add(ab, cd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let rhs = d.add(ac, bd);
        (lhs, rhs)
    })
    .unwrap_or_else(|err| panic!("ring declined add_add_add_comm: {err:?}"));
    (target, proof)
}

/// `lor_bit_le_sum : Le (max bit_m bit_n) (add bit_m bit_n)` where
/// `bit_m := mod m 2`, `bit_n := mod n 2` and `max` is the
/// `bool_select_nat`/`ble` shape `lor`'s own per-bit combine uses
/// (`lor_bit_comm`'s `combine`). Needed by [`declare_lor_aux_le_add`]'s
/// both-positive step: the per-bit OR is bounded by the sum of the two
/// bits, at either concrete `{0,1}` pair -- `Le 0 0`/`Le 1 1` via
/// `Nat.le_refl`, `Le 1 2` via `Nat.le_add_right(1,1)`.
fn lor_bit_le_sum(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let bit_n = d.modulo(n, two);

    let combine = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let lhs = combine(d, x, y);
        let sum = d.add(x, y);
        d.le(lhs, sum)
    };

    let zero = d.zero();
    let one = d.num(1);
    let leaf_00 = d.lemma(p.le_refl, &[zero]);
    let leaf_01 = d.lemma(p.le_refl, &[one]);
    let leaf_10 = d.lemma(p.le_refl, &[one]);
    let leaf_11 = d.lemma(p.le_add_right, &[one, one]);

    let outer_zero = cases_mod_two(d, &p, n, &|d, y| claim(d, zero, y), leaf_00, leaf_01);
    let outer_one = cases_mod_two(d, &p, n, &|d, y| claim(d, one, y), leaf_10, leaf_11);

    cases_mod_two(d, &p, m, &|d, x| claim(d, x, bit_n), outer_zero, outer_one)
}

/// `lor_aux_le_add : ∀ fuel m n, Le (lorAux fuel m n) (add m n)` — see the
/// section doc above. Unconditional in `fuel`, confirmed by exhaustive
/// Python simulation (fuel 0..7, m,n 0..13, zero counterexamples).
fn declare_lor_aux_le_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    let statement = |d: &mut NatDev<'_>, fuel: ExprId, m: ExprId, n: ExprId| {
        let lhs = d.const_app(p.lor_aux, &[fuel, m, n]);
        let sum = d.add(m, n);
        d.le(lhs, sum)
    };

    let base = |d: &mut NatDev<'_>, m: ExprId, n: ExprId| -> ExprId {
        // fuel = 0: lorAux 0 m n defeq n; need Le n (add m n).
        let n_le_nm = d.lemma(p.le_add_right, &[n, m]); // Le n (add n m)
        let nm = d.add(n, m);
        let mn = d.add(m, n);
        let comm = d.lemma(p.add_comm, &[n, m]); // Eq (add n m) (add m n)
        let motive = d.eq_motive(nm, &|d, x| d.le(n, x));
        d.transport(nm, motive, n_le_nm, mn, comm)
    };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId, m: ExprId, n: ExprId| -> ExprId {
        let sk = d.succ(k);

        cases_zero_succ(
            d,
            n,
            &|d, candidate| {
                let lhs = d.const_app(p.lor_aux, &[sk, m, candidate]);
                let sum = d.add(m, candidate);
                d.le(lhs, sum)
            },
            &|d| {
                // n = 0 (literal): lorAux sk m 0 defeq m (outer n=0 guard
                // fires by pure computation regardless of m's shape).
                // Need Le m (add m 0).
                let zero = d.zero();
                let le_mm = d.lemma(p.le_refl, &[m]);
                let m0 = d.add(m, zero);
                let add_zero_m = d.lemma(p.add_zero, &[m]); // Eq (add m 0) m
                let add_zero_m_rev = d.symm(m0, m, add_zero_m); // Eq m (add m 0)
                let motive = d.eq_motive(m, &|d, x| d.le(m, x));
                d.transport(m, motive, le_mm, m0, add_zero_m_rev)
            },
            &|d, n_pred| {
                let succ_n = d.succ(n_pred);

                cases_zero_succ(
                    d,
                    m,
                    &|d, candidate| {
                        let lhs = d.const_app(p.lor_aux, &[sk, candidate, succ_n]);
                        let sum = d.add(candidate, succ_n);
                        d.le(lhs, sum)
                    },
                    &|d| {
                        // m = 0 (literal), n = succ_n (literal): both
                        // guards resolve by pure computation, giving
                        // lorAux sk 0 succ_n defeq succ_n. Need
                        // Le succ_n (add 0 succ_n).
                        let zero = d.zero();
                        let le_nn = d.lemma(p.le_refl, &[succ_n]);
                        let zn = d.add(zero, succ_n);
                        let zero_add_n = d.lemma(p.zero_add, &[succ_n]); // Eq (add 0 succ_n) succ_n
                        let zero_add_n_rev = d.symm(zn, succ_n, zero_add_n);
                        let motive = d.eq_motive(succ_n, &|d, x| d.le(succ_n, x));
                        d.transport(succ_n, motive, le_nn, zn, zero_add_n_rev)
                    },
                    &|d, m_pred| {
                        let succ_m = d.succ(m_pred);
                        let two = d.num(2);
                        let one = d.num(1);
                        let half_m = d.div(succ_m, two);
                        let half_n = d.div(succ_n, two);
                        let bit_m = d.modulo(succ_m, two);
                        let bit_n = d.modulo(succ_n, two);

                        let rec = d.const_app(p.lor_aux, &[k, half_m, half_n]);
                        let ih_at = d.apply(ih, &[half_m, half_n]);
                        // ih_at : Le rec (add half_m half_n)

                        let sum_halves = d.add(half_m, half_n);
                        let two_rec_le = d.lemma(p.mul_le_mul_left, &[two, rec, sum_halves, ih_at]);
                        // two_rec_le : Le (mul 2 rec) (mul 2 sum_halves)

                        let dist = d.lemma(p.left_distrib, &[two, half_m, half_n]);
                        // dist : Eq (mul 2 sum_halves) (add two_half_m two_half_n)
                        let two_half_m = d.mul(two, half_m);
                        let two_half_n = d.mul(two, half_n);
                        let sum_doubled = d.add(two_half_m, two_half_n);
                        let mul2sumhalves = d.mul(two, sum_halves);
                        let two_rec = d.mul(two, rec);
                        let motive_dist = d.eq_motive(mul2sumhalves, &|d, x| d.le(two_rec, x));
                        let two_rec_le2 =
                            d.transport(mul2sumhalves, motive_dist, two_rec_le, sum_doubled, dist);
                        // two_rec_le2 : Le two_rec sum_doubled

                        let bit_le_sum = lor_bit_le_sum(d, &p, succ_m, succ_n);
                        // bit_le_sum : Le (max bit_m bit_n) (add bit_m bit_n)
                        let ble_mn = d.ble(bit_m, bit_n);
                        let bit = d.bool_select_nat(ble_mn, bit_n, bit_m);

                        let step_a = d.lemma(
                            p.add_le_add_right,
                            &[bit, two_rec, sum_doubled, two_rec_le2],
                        );
                        // step_a : Le (add two_rec bit) (add sum_doubled bit)
                        let bit_sum = d.add(bit_m, bit_n);
                        let step_b =
                            d.lemma(p.add_le_add_left, &[sum_doubled, bit, bit_sum, bit_le_sum]);
                        // step_b : Le (add sum_doubled bit) (add sum_doubled bit_sum)

                        let value = d.add(two_rec, bit);
                        let mid = d.add(sum_doubled, bit);
                        let target = d.add(sum_doubled, bit_sum);
                        let combined = d.lemma(p.le_trans, &[value, mid, target, step_a, step_b]);
                        // combined : Le value target

                        // target = add(add A B)(add C D); rearrange to
                        // add succ_m succ_n via add_add_add_comm plus the
                        // two div_mod_exec decompositions.
                        let h_exec_m = d.lemma(p.div_mod_exec, &[one, succ_m]);
                        let eq_ty_m = {
                            let sum_m = d.add(two_half_m, bit_m);
                            d.eq(succ_m, sum_m)
                        };
                        let bound_ty_m = d.lt(bit_m, two);
                        let eq_m = and_left(d, eq_ty_m, bound_ty_m, h_exec_m);
                        // eq_m : Eq succ_m (add two_half_m bit_m)

                        let h_exec_n = d.lemma(p.div_mod_exec, &[one, succ_n]);
                        let eq_ty_n = {
                            let sum_n = d.add(two_half_n, bit_n);
                            d.eq(succ_n, sum_n)
                        };
                        let bound_ty_n = d.lt(bit_n, two);
                        let eq_n = and_left(d, eq_ty_n, bound_ty_n, h_exec_n);
                        // eq_n : Eq succ_n (add two_half_n bit_n)

                        let (regrouped, comm_proof) =
                            add_add_add_comm(d, &p, two_half_m, two_half_n, bit_m, bit_n);
                        // comm_proof : Eq target regrouped
                        // regrouped = add (add two_half_m bit_m) (add two_half_n bit_n)

                        let ac = d.add(two_half_m, bit_m);
                        let bd = d.add(two_half_n, bit_n);
                        let eq_m_rev = d.symm(succ_m, ac, eq_m); // Eq ac succ_m
                        let cong1 = d.congr(ac, succ_m, eq_m_rev, &|d, hole| d.add(hole, bd));
                        let mid_r = d.add(succ_m, bd);
                        let eq_n_rev = d.symm(succ_n, bd, eq_n); // Eq bd succ_n
                        let cong2 = d.congr(bd, succ_n, eq_n_rev, &|d, hole| d.add(succ_m, hole));
                        let final_r = d.add(succ_m, succ_n);

                        let (_, target_eq_final) = d.chain(
                            target,
                            &[(regrouped, comm_proof), (mid_r, cong1), (final_r, cong2)],
                        );
                        // target_eq_final : Eq target (add succ_m succ_n)

                        let final_motive = d.eq_motive(target, &|d, x| d.le(value, x));
                        d.transport(target, final_motive, combined, final_r, target_eq_final)
                        // : Le value (add succ_m succ_n) -- and lorAux sk
                        // succ_m succ_n is defeq `value` (both guards
                        // resolve `false` directly, succ_m/succ_n literal).
                    },
                )
            },
        )
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = agree_by_fuel_induction(d, &statement, &base, &step, fuel);

    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let applied = d.apply(proof_fn, &[m, n]);
    let ty = {
        let body = statement(d, fuel, m, n);
        let with_n = d.pi_fv(n_fv, nat, body);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(fuel_fv, nat, with_m)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, applied);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(fuel_fv, nat, with_m)
    };
    d.declare_theorem(p.lor_aux_le_add, ty, value)
}

/// `lor_assoc : ∀ a b c, Eq (lor (lor a b) c) (lor a (lor b c))` — see the
/// section doc above. Chain, `lor_comm`'s pattern one argument wider (the
/// same shape as [`declare_land_assoc`]): pick the shared fuel `F := add a
/// b`, relate `lorAux F a b`/`lorAux F b c` back to `lor a b`/`lor b c` via
/// `lor_aux_agree_of_fuel`, invoke `lor_aux_assoc_of_fuel` at `F`, then
/// relate the two outer `lorAux F …` terms back to `lor … …` via
/// `lor_aux_agree_of_fuel` again. Unlike `land_assoc`, the bound
/// `Le (lor a b) F` comes directly from [`declare_lor_aux_le_add`] at
/// `(a, a, b)` -- the bound already targets `F` exactly, no `Nat.le_trans`
/// chain needed.
fn declare_lor_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_lor_aux_assoc_of_fuel(d, p)?;
    let p = *p;
    d.theorem(p.lor_assoc, 3, &|d, values| {
        let a = values[0];
        let b = values[1];
        let c = values[2];

        let fuel = d.add(a, b);

        let le_a_fuel = d.lemma(p.le_add_right, &[a, b]); // Le a fuel
        let le_refl_a = d.lemma(p.le_refl, &[a]);

        let le_b_b_a = d.lemma(p.le_add_right, &[b, a]); // Le b (add b a)
        let b_a = d.add(b, a);
        let add_comm_ba = d.lemma(p.add_comm, &[b, a]); // Eq (add b a) (add a b)
        let le_b_motive = d.eq_motive(b_a, &|d, x| d.le(b, x));
        let le_b_fuel = d.transport(b_a, le_b_motive, le_b_b_a, fuel, add_comm_ba);
        let le_refl_b = d.lemma(p.le_refl, &[b]);

        // Le x1 fuel, where x1 := lorAux a a b (defeq `lor a b`), directly
        // via `lor_aux_le_add` -- the bound already targets `fuel` exactly
        // (F := add a b), no `le_trans` needed (unlike `land`'s
        // `land_le_left` + `le_trans` chain).
        let x1 = d.const_app(p.lor_aux, &[a, a, b]);
        let le_x1_fuel = d.lemma(p.lor_aux_le_add, &[a, a, b]); // Le (lorAux a a b) (add a b)
        let le_refl_x1 = d.lemma(p.le_refl, &[x1]);

        // step1 : Eq (lorAux fuel a b) (lorAux a a b) = Eq x0 x1
        let x0 = d.const_app(p.lor_aux, &[fuel, a, b]);
        let step1 = d.lemma(
            p.lor_aux_agree_of_fuel,
            &[fuel, a, b, a, le_a_fuel, le_refl_a],
        );
        // step2 : Eq (lorAux fuel b c) (lorAux b b c) = Eq y0 y1
        let y0 = d.const_app(p.lor_aux, &[fuel, b, c]);
        let y1 = d.const_app(p.lor_aux, &[b, b, c]);
        let step2 = d.lemma(
            p.lor_aux_agree_of_fuel,
            &[fuel, b, c, b, le_b_fuel, le_refl_b],
        );

        // step3 : Eq (lorAux fuel x0 c) (lorAux fuel a y0)
        let step3 = d.lemma(p.lor_aux_assoc_of_fuel, &[fuel, a, b, c]);
        let lhs0 = d.const_app(p.lor_aux, &[fuel, x0, c]);
        let rhs0 = d.const_app(p.lor_aux, &[fuel, a, y0]);

        let cong_left = d.congr(x0, x1, step1, &|d, hole| {
            d.const_app(p.lor_aux, &[fuel, hole, c])
        });
        let mid1 = d.const_app(p.lor_aux, &[fuel, x1, c]);
        let cong_right = d.congr(y0, y1, step2, &|d, hole| {
            d.const_app(p.lor_aux, &[fuel, a, hole])
        });
        let mid2 = d.const_app(p.lor_aux, &[fuel, a, y1]);

        let cong_left_rev = d.symm(lhs0, mid1, cong_left);
        let ab_step = d.trans(mid1, lhs0, rhs0, cong_left_rev, step3);
        let ab_final = d.trans(mid1, rhs0, mid2, ab_step, cong_right);
        // ab_final : Eq mid1 mid2

        // step5 : Eq (lorAux fuel x1 c) (lorAux x1 x1 c) = Eq mid1 z1
        let step5 = d.lemma(
            p.lor_aux_agree_of_fuel,
            &[fuel, x1, c, x1, le_x1_fuel, le_refl_x1],
        );
        let z1 = d.const_app(p.lor_aux, &[x1, x1, c]);

        // step6 : Eq (lorAux fuel a y1) (lorAux a a y1) = Eq mid2 z2
        let step6 = d.lemma(
            p.lor_aux_agree_of_fuel,
            &[fuel, a, y1, a, le_a_fuel, le_refl_a],
        );
        let z2 = d.const_app(p.lor_aux, &[a, a, y1]);

        let step5_rev = d.symm(mid1, z1, step5);
        let z1_step = d.trans(z1, mid1, mid2, step5_rev, ab_final);
        let proof = d.trans(z1, mid2, z2, z1_step, step6);
        // proof : Eq z1 z2
        //   = Eq (lorAux x1 x1 c) (lorAux a a y1)
        //  defeq Eq (lor (lor a b) c) (lor a (lor b c))

        let lhs = {
            let lor_ab = d.const_app(p.lor, &[a, b]);
            d.const_app(p.lor, &[lor_ab, c])
        };
        let rhs = {
            let lor_bc = d.const_app(p.lor, &[b, c]);
            d.const_app(p.lor, &[a, lor_bc])
        };
        (d.eq(lhs, rhs), proof)
    })?;
    Ok(())
}

/// Declare [`declare_lor_aux_le_add`] and [`declare_lor_assoc`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_lor_assoc_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_lor_aux_le_add(d, p)?;
    declare_lor_assoc(d, p)?;
    Ok(())
}
