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
use super::ops::{
    NatDev, NatOps, agree_by_double_fuel_induction, agree_by_fuel_induction, bool_select_nat_same,
    cases_lt_bound, cases_mod_two, cases_zero_succ,
};
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
fn guarded(
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
fn half_le_predecessor_of_succ(
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
    let p = *p;
    let zero = d.zero();
    let add_n_zero = d.add(n, zero);
    let add_n_n = d.add(n, n);
    let step1 = d.lemma(p.add_lt_add_left, &[n, zero, n, pos]);
    let eq1 = d.lemma(p.add_zero, &[n]);
    let motive1 = d.eq_motive(add_n_zero, &|d, x| {
        let add_n_n_inner = d.add(n, n);
        d.lt(x, add_n_n_inner)
    });
    let n_lt_add_n_n = d.transport(add_n_zero, motive1, step1, n, eq1);

    let one = d.num(1);
    let succ_one = d.succ(one);
    let mul_succ_one_n = d.mul(succ_one, n);
    let mul_one_n = d.mul(one, n);
    let add_mul_one_n_n = d.add(mul_one_n, n);
    let succ_mul_eq = d.lemma(p.succ_mul, &[one, n]);
    let one_mul_eq = d.lemma(p.one_mul, &[n]);
    let congr_step = d.congr(mul_one_n, n, one_mul_eq, &|d, x| d.add(x, n));
    let (_, mul_two_n_eq_add_n_n) = d.chain(
        mul_succ_one_n,
        &[(add_mul_one_n_n, succ_mul_eq), (add_n_n, congr_step)],
    );
    let rev_eq = d.symm(mul_succ_one_n, add_n_n, mul_two_n_eq_add_n_n);
    let motive2 = d.eq_motive(add_n_n, &|d, x| d.lt(n, x));
    d.transport(add_n_n, motive2, n_lt_add_n_n, mul_succ_one_n, rev_eq)
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
