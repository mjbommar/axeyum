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
use super::ops::{NatDev, NatOps, agree_by_fuel_induction, cases_lt_bound, cases_mod_two};
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
