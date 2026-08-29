//! `Int.Even`/`Int.Odd`: parity over `ℤ`, defined directly through the
//! already-proved `ℕ` predicates rather than through a fresh `ℤ`-level
//! existential.
//!
//! ## Why `Nat.Even (natAbs n)` / `Nat.Odd (natAbs n)`, not `∃ k : Int, …`
//!
//! Mathlib's `Int.Even`/`Int.Odd` are instances of the generic algebraic
//! definitions (`Even n := ∃ r, n = r + r`, `Odd n := ∃ k, n = 2*k + 1`) at
//! the `Int` type. That form is faithful but does not compose with this
//! kernel's actual entry point into an `Int` proof: every case-split here
//! goes through `Int.rec`'s `ofNat`/`negSucc` constructors (`ops.rs`'s
//! `case_split`), and relating an `Int`-witnessed existential to the
//! already-built `Nat.Even`/`Nat.Odd` (`nat_prelude/parity.rs`) needs a
//! sign argument at every use — exactly the "check what composes" warning
//! the brief for this file carries.
//!
//! Negation does not change parity, so magnitude alone decides it:
//! `Int.Odd n := Nat.Odd (natAbs n)`, `Int.Even n := Nat.Even (natAbs n)`.
//! This is not merely convenient, it is *free* at both constructors, because
//! `natAbs` itself reduces purely on each (`nat_abs.rs`'s module doc):
//!
//! ```text
//! Odd (ofNat a)   ≡ Nat.Odd a          -- natAbs (ofNat a)   ≡ a
//! Odd (negSucc m) ≡ Nat.Odd (succ m)   -- natAbs (negSucc m) ≡ succ m
//! ```
//!
//! and `Nat.Odd (succ m)` is exactly the right-hand side of
//! [`NatPrelude::even_iff_odd_succ`](crate::nat_prelude::NatPrelude::even_iff_odd_succ),
//! so the `negSucc` branch of any `Int.Odd`-hypothesis proof (e.g.
//! `Int.fib_of_odd`, `fibonacci.rs`) reaches `Nat.Even m` through that
//! existing bridge with **no** new `Int`-level parity lemma at all — matching
//! the earlier lane's prediction exactly, and confirming it: no `Int`-level
//! parity reasoning is needed to use the predicate once it is stated this
//! way.
//!
//! [`declare_odd_iff_nat_abs_odd`]/[`declare_even_iff_nat_abs_even`] are the
//! two bridge lemmas the brief asks for. Both are near-tautological (`fun h
//! => h` in each direction) precisely *because* the definition above already
//! **is** the bridge; they exist as named, discoverable API surface rather
//! than to do any work a caller could not get by unfolding the definition
//! directly.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::{IntDev, Shape, case_split, exists_elim};

/// `Int.natAbs a`. Module-private mirror of `gcd.rs`'s/`bezout_witnesses.rs`'s
/// own copies (`nat_abs.rs`'s `NatAbsOps` trait is private to that module).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// Height for `Int.Even`/`Int.Odd`: each unfolds through exactly one
/// `Int.natAbs` application (local height 4 within `nat_abs.rs`) to a
/// `Nat.Even`/`Nat.Odd` application (height 4 within `nat_prelude/parity.rs`),
/// so 5 strictly dominates both direct callees.
const EVEN_ODD_HEIGHT: u16 = 5;

/// `Int.Even`, `Int.Odd` — see the module doc for why magnitude alone
/// decides parity.
fn declare_even_odd_defs(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let prop = d.kernel().sort_zero();

    // Even n := Nat.Even (natAbs n)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mag = nat_abs(d, n);
        let body = d.const_app(p.nat.even, &[mag]);
        let value = d.lam_fv(n_fv, int_ty, body);
        let ty = d.arrow(int_ty, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.even,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(EVEN_ODD_HEIGHT),
        })?;
    }

    // Odd n := Nat.Odd (natAbs n)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mag = nat_abs(d, n);
        let body = d.const_app(p.nat.odd, &[mag]);
        let value = d.lam_fv(n_fv, int_ty, body);
        let ty = d.arrow(int_ty, prop);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.odd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(EVEN_ODD_HEIGHT),
        })?;
    }
    Ok(())
}

/// `Int.odd_iff_nat_abs_odd : ∀ n, Iff (Odd n) (Nat.Odd (natAbs n))`. Both
/// directions are the identity function, since the two sides are the SAME
/// term up to one delta unfold of `Int.Odd` — see the module doc.
fn declare_odd_iff_nat_abs_odd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.odd_iff_nat_abs_odd, 1, &|d, v| {
        let n = v[0];
        let odd_n_ty = d.const_app(p.odd, &[n]);
        let mag = nat_abs(d, n);
        let nat_odd_mag_ty = d.const_app(p.nat.odd, &[mag]);
        let stmt = d.const_app(p.logic.iff, &[odd_n_ty, nat_odd_mag_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, odd_n_ty, h)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, nat_odd_mag_ty, h)
        };
        let proof = d.const_app(p.logic.iff_intro, &[odd_n_ty, nat_odd_mag_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.even_iff_nat_abs_even : ∀ n, Iff (Even n) (Nat.Even (natAbs n))` —
/// [`declare_odd_iff_nat_abs_odd`] with `Even`/`Odd` swapped; no new
/// construction.
fn declare_even_iff_nat_abs_even(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.int_theorem(p.even_iff_nat_abs_even, 1, &|d, v| {
        let n = v[0];
        let even_n_ty = d.const_app(p.even, &[n]);
        let mag = nat_abs(d, n);
        let nat_even_mag_ty = d.const_app(p.nat.even, &[mag]);
        let stmt = d.const_app(p.logic.iff, &[even_n_ty, nat_even_mag_ty]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, even_n_ty, h)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, nat_even_mag_ty, h)
        };
        let proof = d.const_app(p.logic.iff_intro, &[even_n_ty, nat_even_mag_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_parity_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_even_odd_defs(d)?;
    declare_odd_iff_nat_abs_odd(d)?;
    declare_even_iff_nat_abs_even(d)?;
    Ok(())
}

// ============================================================================
// The `ml430-int-*` division-by-two family (2026-08-29).
//
// Ten freshly-dispatched mirrors, closed via the sign-general `Int.emod`
// machinery landed the same day (`division.rs`'s `emod_natAbs_bound`,
// `ediv_emod_unique_general`) plus the `Nat`-side parity bridges
// (`Nat.even_iff_mod_two_eq_zero`, `Nat.odd_iff_mod_two_eq_one`,
// `Nat.mod_two_eq_zero_or_one`, `nat_prelude/parity.rs` and
// `nat_prelude/rec_agreement.rs`).
//
// `emod_two_ne_zero`/`emod_two_ne_one` are pure `n % 2` facts (no `Even`/`Odd`
// at all) and are proved directly from [`declare_emod_two_eq_zero_or_one`], an
// internal helper (not itself an `ml430` mirror) built by `Int.rec` on `n`
// plus `Nat.mod_two_eq_zero_or_one` on the bound `Nat` field of each branch.
//
// The `ediv_two_mul_two_*`/`odd_of_mul_*` facts need `Even`/`Odd` connected to
// the additive/multiplicative structure. Two different bridges turned out to
// be the cheap ones for the two families:
//
// - `ediv_two_mul_two_of_even`/`ediv_two_mul_two_add_one_of_odd`/
//   `add_one_ediv_two_mul_two_of_odd` go through the `n % 2` characterisation
//   ([`even_implies_emod_zero`]/[`odd_implies_emod_one`], case-split builders
//   with the same shape as [`declare_emod_two_eq_zero_or_one`]) plus
//   `Int.ediv_add_emod`.
// - `odd_of_mul_left`/`odd_of_mul_right` go through `Int.natAbs` being
//   multiplicative (`nat_abs_mul`, `gcd.rs`) directly — `natAbs` does not care
//   about sign, so this route never needs `Int.rec` at all, unlike the
//   `ediv_two_mul_two_*` family. The Nat-level content
//   (`Nat.Even a → Nat.Even (a*b)`, both sides) is built here from
//   `right_distrib`/`left_distrib` since neither has a home in `nat_prelude`
//   yet and this lane does not touch that crate.
//
// `Int.even_add`/`Int.even_add'` (the two `ml430-int-even-add-*` mirrors) and
// `Int.even_add_one` are NOT attempted here: relating `Even (m+n)` to `Even
// m`/`Even n` needs an additive compatibility law for `emod`
// (`(m+n) % 2` vs `m % 2`, `n % 2`) that does not exist yet in any branch-free
// form, and building it from scratch is a separate-sized task. Left `open`;
// see the lane status file.

/// `Int.ofNat 2` — the literal divisor every lemma below is stated against.
fn two_int(d: &mut IntDev<'_>) -> ExprId {
    let two = d.num(2);
    d.of_nat(two)
}

/// `(Eq (emod n 2) 0, Eq (emod n 2) 1, emod n 2)` — the two disjuncts
/// [`declare_emod_two_eq_zero_or_one`] proves, plus the shared remainder
/// term, all as a function of `n`.
fn emod_two_disjuncts(d: &mut IntDev<'_>, n: ExprId) -> (ExprId, ExprId, ExprId) {
    let two = two_int(d);
    let r = d.iemod(n, two);
    let zero = d.izero();
    let one = d.ione();
    let eq0 = d.ieq(r, zero);
    let eq1 = d.ieq(r, one);
    (eq0, eq1, r)
}

/// `Or (Eq (emod n 2) 0) (Eq (emod n 2) 1)`.
fn emod_two_stmt(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let (eq0, eq1, _r) = emod_two_disjuncts(d, n);
    d.or(eq0, eq1)
}

/// `fun (h_0 : tys[0]) … => body(h_0, …)` — module-private copy of the
/// `with_hypotheses` binder `order.rs`/`algebra.rs` each keep privately to
/// their own file.
fn with_hyps(
    d: &mut IntDev<'_>,
    tys: &[ExprId],
    body: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let fvs: Vec<u64> = (0..tys.len()).map(|_| d.fresh_fvar()).collect();
    let hyps: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut term = body(d, &hyps);
    for (index, &fv) in fvs.iter().enumerate().rev() {
        term = d.lam_fv(fv, tys[index], term);
    }
    term
}

/// `Not (Eq Int zero one)` — `zero_lt_one` rewritten along a hypothetical
/// `zero = one` into `Lt one one`, refuted by `lt_irrefl`.
fn izero_ne_one(d: &mut IntDev<'_>) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let one = d.ione();
    let eq_ty = d.ieq(zero, one);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let lt01 = d.kernel().const_(p.zero_lt_one, vec![]);
    let motive = d.ieq_motive(zero, &|d, x| {
        let one = d.ione();
        d.ilt(x, one)
    });
    let lt11 = d.itransport(zero, motive, lt01, one, h);
    let irrefl = d.const_app(p.lt_irrefl, &[one]);
    let false_proof = d.apply(irrefl, &[lt11]);
    d.lam_fv(h_fv, eq_ty, false_proof)
}

/// From `h0 : Eq Int r 0` and `h1 : Eq Int r 1`, derive `False` — the two
/// disjuncts [`declare_emod_two_eq_zero_or_one`] proves are mutually
/// exclusive.
fn zero_one_disjoint(d: &mut IntDev<'_>, r: ExprId, h0: ExprId, h1: ExprId) -> ExprId {
    let zero = d.izero();
    let one = d.ione();
    let flip0 = d.isymm(r, zero, h0);
    let combined = d.itrans(zero, r, one, flip0, h1);
    let ne = izero_ne_one(d);
    d.apply(ne, &[combined])
}

/// `Int.emod_two_eq_zero_or_one : ∀ n, Or (Eq (emod n 2) 0) (Eq (emod n 2)
/// 1)`. `Int.rec` on `n`, then `Nat.mod_two_eq_zero_or_one` on the bound
/// `Nat` field of whichever branch: in the `ofNat m` branch `emod` computes
/// directly to `ofNat (mod m 2)`, so the two `Nat`-level disjuncts lift
/// straight across via [`super::ops::IntDev::nat_eq_to_int`]; in the `negSucc
/// m` branch `emod` computes to `subNatNat 2 (succ (mod m 2))`, which the
/// SAME lift (through the context `fun x => subNatNat 2 (succ x)`) collapses
/// to `ofNat 1` at `mod m 2 = 0` and `ofNat 0` at `mod m 2 = 1` — the sign
/// flip is exactly `negSucc`'s magnitude being `succ m`, one step out of
/// phase with `m` itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_two_eq_zero_or_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_two_eq_zero_or_one, 1, &|d, v| {
        let n = v[0];
        let stmt = emod_two_stmt(d, n);
        let proof = case_split(
            d,
            &[n],
            &|d, args| emod_two_stmt(d, args[0]),
            &|d, branches| {
                let (shape, m) = branches[0];
                let n_term = d.branch_term(branches[0]);
                let (eq0, eq1, _r) = emod_two_disjuncts(d, n_term);
                let or_ty = d.or(eq0, eq1);
                let two_nat = d.num(2);
                let r = d.modulo(m, two_nat);
                let zero_nat = d.zero();
                let one_nat = d.num(1);
                let nat_eq0 = d.eq(r, zero_nat);
                let nat_eq1 = d.eq(r, one_nat);
                let split = d.const_app(p.nat.mod_two_eq_zero_or_one, &[m]);
                match shape {
                    Shape::OfNat => d.or_elim(
                        nat_eq0,
                        nat_eq1,
                        or_ty,
                        split,
                        &|d, h0| {
                            let lifted = d.nat_eq_to_int(r, zero_nat, h0, &|d, x| d.of_nat(x));
                            d.or_inl(eq0, eq1, lifted)
                        },
                        &|d, h1| {
                            let lifted = d.nat_eq_to_int(r, one_nat, h1, &|d, x| d.of_nat(x));
                            d.or_inr(eq0, eq1, lifted)
                        },
                    ),
                    Shape::NegSucc => d.or_elim(
                        nat_eq0,
                        nat_eq1,
                        or_ty,
                        split,
                        &|d, h0| {
                            let lifted = d.nat_eq_to_int(r, zero_nat, h0, &|d, x| {
                                let sx = d.succ(x);
                                let two = d.num(2);
                                d.sub_nat_nat(two, sx)
                            });
                            d.or_inr(eq0, eq1, lifted)
                        },
                        &|d, h1| {
                            let lifted = d.nat_eq_to_int(r, one_nat, h1, &|d, x| {
                                let sx = d.succ(x);
                                let two = d.num(2);
                                d.sub_nat_nat(two, sx)
                            });
                            d.or_inl(eq0, eq1, lifted)
                        },
                    ),
                }
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.emod_two_ne_zero : ∀ n, Iff (Not (Eq (emod n 2) 0)) (Eq (emod n 2)
/// 1)` — `F:ml430-int-emod-two-ne-zero-d07d008f`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_two_ne_zero(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_two_ne_zero, 1, &|d, v| {
        let n = v[0];
        let (eq0, eq1, r) = emod_two_disjuncts(d, n);
        let not_eq0 = d.not(eq0);
        let stmt = d.const_app(p.logic.iff, &[not_eq0, eq1]);

        let split = d.const_app(p.emod_two_eq_zero_or_one, &[n]);
        let mp = with_hyps(d, &[not_eq0], &|d, h| {
            d.or_elim(
                eq0,
                eq1,
                eq1,
                split,
                &|d, h0| {
                    let f = d.apply(h[0], &[h0]);
                    d.absurd(eq1, f)
                },
                &|_d, h1| h1,
            )
        });
        let mpr = with_hyps(d, &[eq1], &|d, h| {
            with_hyps(d, &[eq0], &|d, hh| {
                let false_proof = zero_one_disjoint(d, r, hh[0], h[0]);
                let false_ty = d.false_ty();
                d.absurd(false_ty, false_proof)
            })
        });
        let proof = d.const_app(p.logic.iff_intro, &[not_eq0, eq1, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.emod_two_ne_one : ∀ n, Iff (Not (Eq (emod n 2) 1)) (Eq (emod n 2)
/// 0)` — `F:ml430-int-emod-two-ne-one-5b930333`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_two_ne_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_two_ne_one, 1, &|d, v| {
        let n = v[0];
        let (eq0, eq1, r) = emod_two_disjuncts(d, n);
        let not_eq1 = d.not(eq1);
        let stmt = d.const_app(p.logic.iff, &[not_eq1, eq0]);

        let split = d.const_app(p.emod_two_eq_zero_or_one, &[n]);
        let mp = with_hyps(d, &[not_eq1], &|d, h| {
            d.or_elim(eq0, eq1, eq0, split, &|_d, h0| h0, &|d, h1| {
                let f = d.apply(h[0], &[h1]);
                d.absurd(eq0, f)
            })
        });
        let mpr = with_hyps(d, &[eq0], &|d, h| {
            with_hyps(d, &[eq1], &|d, hh| {
                let false_proof = zero_one_disjoint(d, r, h[0], hh[0]);
                let false_ty = d.false_ty();
                d.absurd(false_ty, false_proof)
            })
        });
        let proof = d.const_app(p.logic.iff_intro, &[not_eq1, eq0, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Even n ⊢ Eq Int (emod n 2) 0` — the `mp` direction of `Int.even_iff`
/// (never given a name of its own: nothing else in this lane needs the `mpr`
/// direction, and the two `emod_two_ne_*` facts above already cover the pure
/// `n % 2` content).
///
/// `ofNat m` branch: `Even (ofNat m) ≡ Nat.Even m` unfolds straight through
/// `Nat.even_iff_mod_two_eq_zero`. `negSucc m` branch: `Even (negSucc m) ≡
/// Nat.Even (succ m)`, which is NOT `Nat.even_iff_mod_two_eq_zero`'s own
/// shape (that relates `Even m` to `mod m 2`, not `Even (succ m)`) — bridged
/// through [`nat_even_succ_implies_odd`] to `Nat.Odd m` first.
fn even_implies_emod_zero(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let p = d.int();
    let stmt_at = |d: &mut IntDev<'_>, nn: ExprId| -> ExprId {
        let even_ty = d.const_app(p.even, &[nn]);
        let (eq0, _eq1, _r) = emod_two_disjuncts(d, nn);
        d.arrow(even_ty, eq0)
    };
    case_split(d, &[n], &|d, args| stmt_at(d, args[0]), &|d, branches| {
        let (shape, m) = branches[0];
        let n_term = d.branch_term(branches[0]);
        let even_ty = d.const_app(p.even, &[n_term]);
        let two_nat = d.num(2);
        match shape {
            Shape::OfNat => {
                let r = d.modulo(m, two_nat);
                let zero_nat = d.zero();
                let even_m_ty = d.const_app(p.nat.even, &[m]);
                let eq0_nat = d.eq(r, zero_nat);
                let iff_ty = d.const_app(p.nat.even_iff_mod_two_eq_zero, &[m]);
                let mp = d.const_app(p.logic.iff_mp, &[even_m_ty, eq0_nat, iff_ty]);
                with_hyps(d, &[even_ty], &|d, h| {
                    let nat_eq = d.apply(mp, &[h[0]]);
                    d.nat_eq_to_int(r, zero_nat, nat_eq, &|d, x| d.of_nat(x))
                })
            }
            Shape::NegSucc => {
                let r = d.modulo(m, two_nat);
                let one_nat = d.num(1);
                let odd_m_ty = d.const_app(p.nat.odd, &[m]);
                let eq1_nat = d.eq(r, one_nat);
                let iff_ty = d.const_app(p.nat.odd_iff_mod_two_eq_one, &[m]);
                let mp = d.const_app(p.logic.iff_mp, &[odd_m_ty, eq1_nat, iff_ty]);
                with_hyps(d, &[even_ty], &|d, h| {
                    let odd_m = nat_even_succ_implies_odd(d, m, h[0]);
                    let nat_eq = d.apply(mp, &[odd_m]);
                    d.nat_eq_to_int(r, one_nat, nat_eq, &|d, x| {
                        let sx = d.succ(x);
                        let two = d.num(2);
                        d.sub_nat_nat(two, sx)
                    })
                })
            }
        }
    })
}

/// `Odd n ⊢ Eq Int (emod n 2) 1` — [`even_implies_emod_zero`]'s twin.
///
/// `ofNat m` branch: `Odd (ofNat m) ≡ Nat.Odd m`, straight through
/// `Nat.odd_iff_mod_two_eq_one`. `negSucc m` branch: `Odd (negSucc m) ≡
/// Nat.Odd (succ m)`, which IS `Nat.even_iff_odd_succ`'s own shape (`Even m
/// ↔ Odd (succ m)`) read backwards — no contrapositive needed here, unlike
/// [`even_implies_emod_zero`]'s `negSucc` branch.
fn odd_implies_emod_one(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let p = d.int();
    let stmt_at = |d: &mut IntDev<'_>, nn: ExprId| -> ExprId {
        let odd_ty = d.const_app(p.odd, &[nn]);
        let (_eq0, eq1, _r) = emod_two_disjuncts(d, nn);
        d.arrow(odd_ty, eq1)
    };
    case_split(d, &[n], &|d, args| stmt_at(d, args[0]), &|d, branches| {
        let (shape, m) = branches[0];
        let n_term = d.branch_term(branches[0]);
        let odd_ty = d.const_app(p.odd, &[n_term]);
        let two_nat = d.num(2);
        match shape {
            Shape::OfNat => {
                let r = d.modulo(m, two_nat);
                let one_nat = d.num(1);
                let odd_m_ty = d.const_app(p.nat.odd, &[m]);
                let eq1_nat = d.eq(r, one_nat);
                let iff_ty = d.const_app(p.nat.odd_iff_mod_two_eq_one, &[m]);
                let mp = d.const_app(p.logic.iff_mp, &[odd_m_ty, eq1_nat, iff_ty]);
                with_hyps(d, &[odd_ty], &|d, h| {
                    let nat_eq = d.apply(mp, &[h[0]]);
                    d.nat_eq_to_int(r, one_nat, nat_eq, &|d, x| d.of_nat(x))
                })
            }
            Shape::NegSucc => {
                let r = d.modulo(m, two_nat);
                let zero_nat = d.zero();
                let succ_m = d.succ(m);
                let even_m_ty = d.const_app(p.nat.even, &[m]);
                let odd_succ_ty = d.const_app(p.nat.odd, &[succ_m]);
                let iff_es = d.const_app(p.nat.even_iff_odd_succ, &[m]);
                let mpr_es = d.const_app(p.logic.iff_mpr, &[even_m_ty, odd_succ_ty, iff_es]);
                let eq0_nat = d.eq(r, zero_nat);
                let iff_em = d.const_app(p.nat.even_iff_mod_two_eq_zero, &[m]);
                let mp_em = d.const_app(p.logic.iff_mp, &[even_m_ty, eq0_nat, iff_em]);
                with_hyps(d, &[odd_ty], &|d, h| {
                    let even_m = d.apply(mpr_es, &[h[0]]);
                    let nat_eq = d.apply(mp_em, &[even_m]);
                    d.nat_eq_to_int(r, zero_nat, nat_eq, &|d, x| {
                        let sx = d.succ(x);
                        let two = d.num(2);
                        d.sub_nat_nat(two, sx)
                    })
                })
            }
        }
    })
}

/// `Int.ediv_two_mul_two_of_even : ∀ n, Even n → Eq (mul (ediv n 2) 2) n` —
/// `F:ml430-int-ediv-two-mul-two-of-even-0095e2a6`. From `Int.ediv_add_emod`
/// at `b := 2`, rewriting `emod n 2` to `0` via [`even_implies_emod_zero`],
/// `add_zero`, then `mul_comm` to swap `2*(n/2)` into `(n/2)*2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv_two_mul_two_of_even(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ediv_two_mul_two_of_even, 1, &|d, v| {
        let n = v[0];
        let even_ty = d.const_app(p.even, &[n]);
        let two = two_int(d);
        let ediv_n2 = d.iediv(n, two);
        let lhs = d.imul(ediv_n2, two);
        let eq = d.ieq(lhs, n);
        let stmt = d.arrow(even_ty, eq);

        let mp = even_implies_emod_zero(d, n);
        let ident = d.const_app(p.ediv_add_emod, &[n, two]);
        let mul_two_ediv = d.imul(two, ediv_n2);
        let emod_n2 = d.iemod(n, two);
        let zero = d.izero();
        let lhs0 = d.iadd(mul_two_ediv, emod_n2);
        let add_mul_zero = d.iadd(mul_two_ediv, zero);
        let add_zero_eq = d.const_app(p.add_zero, &[mul_two_ediv]);
        let mul_comm_eq = d.const_app(p.mul_comm, &[two, ediv_n2]);

        let proof = with_hyps(d, &[even_ty], &|d, h| {
            let hn0 = d.apply(mp, &[h[0]]);
            let rewritten = d.icongr(emod_n2, zero, hn0, &|d, x| d.iadd(mul_two_ediv, x));
            let (_final, chain_proof) = d.ichain(
                lhs0,
                &[
                    (add_mul_zero, rewritten),
                    (mul_two_ediv, add_zero_eq),
                    (lhs, mul_comm_eq),
                ],
            );
            let flip = d.isymm(lhs0, lhs, chain_proof);
            d.itrans(lhs, lhs0, n, flip, ident)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Odd n ⊢ Eq Int (add (mul (ediv n 2) 2) one) n` — shared by
/// [`declare_ediv_two_mul_two_add_one_of_odd`] and
/// [`declare_add_one_ediv_two_mul_two_of_odd`]. Same route as
/// [`declare_ediv_two_mul_two_of_even`], rewriting `emod n 2` to `1` instead
/// of `0` (so no `add_zero` step) and then `mul_comm`-swapping under the
/// `+1` rather than in isolation.
fn odd_ediv_two_mul_two_add_one(d: &mut IntDev<'_>, n: ExprId, h_odd: ExprId) -> (ExprId, ExprId) {
    let p = d.int();
    let two = two_int(d);
    let one = d.ione();
    let ediv_n2 = d.iediv(n, two);
    let lhs = d.imul(ediv_n2, two);
    let target_lhs = d.iadd(lhs, one);

    let mp = odd_implies_emod_one(d, n);
    let hn1 = d.apply(mp, &[h_odd]);
    let mul_two_ediv = d.imul(two, ediv_n2);
    let emod_n2 = d.iemod(n, two);
    let lhs0 = d.iadd(mul_two_ediv, emod_n2);
    let ident = d.const_app(p.ediv_add_emod, &[n, two]);

    let step1_target = d.iadd(mul_two_ediv, one);
    let rewritten = d.icongr(emod_n2, one, hn1, &|d, x| d.iadd(mul_two_ediv, x));
    let mul_comm_eq = d.const_app(p.mul_comm, &[two, ediv_n2]);
    let step2 = d.icongr(mul_two_ediv, lhs, mul_comm_eq, &|d, x| d.iadd(x, one));

    let (_final, chain_proof) = d.ichain(lhs0, &[(step1_target, rewritten), (target_lhs, step2)]);
    let flip = d.isymm(lhs0, target_lhs, chain_proof);
    let proof = d.itrans(target_lhs, lhs0, n, flip, ident);
    (target_lhs, proof)
}

/// `Int.ediv_two_mul_two_add_one_of_odd : ∀ n, Odd n → Eq (add (mul (ediv n
/// 2) 2) one) n` — `F:ml430-int-ediv-two-mul-two-add-one-of-odd-a7ec30d7`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_ediv_two_mul_two_add_one_of_odd(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.ediv_two_mul_two_add_one_of_odd, 1, &|d, v| {
        let n = v[0];
        let odd_ty = d.const_app(p.odd, &[n]);
        let two = two_int(d);
        let one = d.ione();
        let ediv_n2 = d.iediv(n, two);
        let lhs = d.imul(ediv_n2, two);
        let target_lhs = d.iadd(lhs, one);
        let eq = d.ieq(target_lhs, n);
        let stmt = d.arrow(odd_ty, eq);

        let proof = with_hyps(d, &[odd_ty], &|d, h| {
            let (_lhs, proof) = odd_ediv_two_mul_two_add_one(d, n, h[0]);
            proof
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.add_one_ediv_two_mul_two_of_odd : ∀ n, Odd n → Eq (add one (mul
/// (ediv n 2) 2)) n` — `F:ml430-int-add-one-ediv-two-mul-two-of-odd-3c9ef32f`.
/// [`odd_ediv_two_mul_two_add_one`]'s conclusion, flipped via `add_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_add_one_ediv_two_mul_two_of_odd(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_one_ediv_two_mul_two_of_odd, 1, &|d, v| {
        let n = v[0];
        let odd_ty = d.const_app(p.odd, &[n]);
        let two = two_int(d);
        let one = d.ione();
        let ediv_n2 = d.iediv(n, two);
        let lhs = d.imul(ediv_n2, two);
        let flipped_lhs = d.iadd(one, lhs);
        let eq = d.ieq(flipped_lhs, n);
        let stmt = d.arrow(odd_ty, eq);

        let proof = with_hyps(d, &[odd_ty], &|d, h| {
            let (target_lhs, p2) = odd_ediv_two_mul_two_add_one(d, n, h[0]);
            let comm_eq = d.const_app(p.add_comm, &[one, lhs]);
            d.itrans(flipped_lhs, target_lhs, n, comm_eq, p2)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `fun k : Nat => Eq x (add k k)` — module-private copy of
/// `nat_prelude/parity.rs`'s `even_predicate` (that one is `pub(super)` to
/// `nat_prelude`, not visible here).
fn nat_even_predicate(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let body = d.eq(x, kk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Nat.Even a ⊢ Nat.Even (mul a b)` — `a = k+k ⊢ a*b = k*b + k*b`
/// (`right_distrib`).
fn nat_even_mul_of_even_left(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.mul(a, b);
    let target = d.const_app(p.nat.even, &[ab]);
    let pred = nat_even_predicate(d, a);
    let nat_ty = d.nat_ty();
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let kk = d.add(k, k);
        let hk_ty = d.eq(a, kk);

        let kkb = d.mul(kk, b);
        let kb = d.mul(k, b);
        let kbkb = d.add(kb, kb);
        let ab_eq_kkb = d.congr(a, kk, hk, &|d, x| d.mul(x, b));
        let dist = d.const_app(p.nat.right_distrib, &[k, k, b]);
        let (_final, chain_proof) = d.chain(ab, &[(kkb, ab_eq_kkb), (kbkb, dist)]);

        let ev_pred = nat_even_predicate(d, ab);
        let one = d.level_one();
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let ev_proof = d.apply(intro, &[nat_ty, ev_pred, kb, chain_proof]);

        let inner = d.lam_fv(hk_fv, hk_ty, ev_proof);
        d.lam_fv(k_fv, nat_ty, inner)
    };
    exists_elim(d, pred, target, h, minor)
}

/// `Nat.Even b ⊢ Nat.Even (mul a b)` — `b = k+k ⊢ a*b = a*k + a*k`
/// (`left_distrib`), [`nat_even_mul_of_even_left`]'s mirror.
fn nat_even_mul_of_even_right(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.mul(a, b);
    let target = d.const_app(p.nat.even, &[ab]);
    let pred = nat_even_predicate(d, b);
    let nat_ty = d.nat_ty();
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let kk = d.add(k, k);
        let hk_ty = d.eq(b, kk);

        let akk = d.mul(a, kk);
        let ak = d.mul(a, k);
        let akak = d.add(ak, ak);
        let ab_eq_akk = d.congr(b, kk, hk, &|d, x| d.mul(a, x));
        let dist = d.const_app(p.nat.left_distrib, &[a, k, k]);
        let (_final, chain_proof) = d.chain(ab, &[(akk, ab_eq_akk), (akak, dist)]);

        let ev_pred = nat_even_predicate(d, ab);
        let one = d.level_one();
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let ev_proof = d.apply(intro, &[nat_ty, ev_pred, ak, chain_proof]);

        let inner = d.lam_fv(hk_fv, hk_ty, ev_proof);
        d.lam_fv(k_fv, nat_ty, inner)
    };
    exists_elim(d, pred, target, h, minor)
}

/// `Not (Nat.Even x) ⊢ Nat.Odd x` — contrapositive of `even_or_odd_exists`.
fn nat_not_even_implies_odd(d: &mut IntDev<'_>, x: ExprId, h_not_even: ExprId) -> ExprId {
    let p = d.int();
    let even_ty = d.const_app(p.nat.even, &[x]);
    let odd_ty = d.const_app(p.nat.odd, &[x]);
    let disj = d.const_app(p.nat.even_or_odd_exists, &[x]);
    d.or_elim(
        even_ty,
        odd_ty,
        odd_ty,
        disj,
        &|d, h_even| {
            let f = d.apply(h_not_even, &[h_even]);
            d.absurd(odd_ty, f)
        },
        &|_d, h_odd| h_odd,
    )
}

/// `Nat.Even (succ m) ⊢ Nat.Odd m` — `Nat.even_iff_odd_succ` relates `Even
/// m` to `Odd (succ m)`, not `Even (succ m)` to `Odd m`, so this direction is
/// the contrapositive: `Even m ⊢ Odd (succ m) ⊢ Not (Even (succ m))`,
/// refuting the hypothesis; combined with [`nat_not_even_implies_odd`].
fn nat_even_succ_implies_odd(d: &mut IntDev<'_>, m: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let succ_m = d.succ(m);
    let not_even_m = {
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let even_m_ty = d.const_app(p.nat.even, &[m]);
        let odd_succ_ty = d.const_app(p.nat.odd, &[succ_m]);
        let iff_ty = d.const_app(p.nat.even_iff_odd_succ, &[m]);
        let mp = d.const_app(p.logic.iff_mp, &[even_m_ty, odd_succ_ty, iff_ty]);
        let odd_succ_proof = d.apply(mp, &[hm]);
        let not_even_succ = d.const_app(p.nat.odd_not_even, &[succ_m]);
        let refuter = d.apply(not_even_succ, &[odd_succ_proof]);
        let false_proof = d.apply(refuter, &[h]);
        d.lam_fv(hm_fv, even_m_ty, false_proof)
    };
    nat_not_even_implies_odd(d, m, not_even_m)
}

/// `Int.odd_of_mul_left : ∀ m n, Odd (mul m n) → Odd m` —
/// `F:ml430-int-odd-of-mul-left-b580971e`. Routes entirely through
/// `Int.natAbs` being multiplicative (`nat_abs_mul`) — sign plays no role, so
/// unlike the `ediv_two_mul_two_*` family this needs no `Int.rec` at all.
/// Contrapositive: `Even (natAbs m) ⊢ Even (natAbs m * natAbs n)` (via
/// [`nat_even_mul_of_even_left`]) `⊢ Not (Odd (natAbs m * natAbs n))` (via
/// `Nat.even_not_odd`), refuting the rewritten hypothesis.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_odd_of_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.odd_of_mul_left, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let mn = d.imul(m, n);
        let odd_mn_ty = d.const_app(p.odd, &[mn]);
        let odd_m_ty = d.const_app(p.odd, &[m]);
        let stmt = d.arrow(odd_mn_ty, odd_m_ty);

        let a = nat_abs(d, m);
        let b = nat_abs(d, n);
        let nat_abs_mul_eq = d.const_app(p.nat_abs_mul, &[m, n]);
        let ab = d.mul(a, b);

        let proof = with_hyps(d, &[odd_mn_ty], &|d, h| {
            let natabs_mn = nat_abs(d, mn);
            let motive = |d: &mut IntDev<'_>, x: ExprId| d.const_app(p.nat.odd, &[x]);
            let odd_ab = d.nat_rewrite(natabs_mn, ab, nat_abs_mul_eq, h[0], &motive);
            let not_even_a = {
                let ha_fv = d.fresh_fvar();
                let ha = d.kernel().fvar(ha_fv);
                let even_a_ty = d.const_app(p.nat.even, &[a]);
                let even_ab = nat_even_mul_of_even_left(d, a, b, ha);
                let not_odd_of_even_ab = d.const_app(p.nat.even_not_odd, &[ab]);
                let refuter = d.apply(not_odd_of_even_ab, &[even_ab]);
                let false_proof = d.apply(refuter, &[odd_ab]);
                d.lam_fv(ha_fv, even_a_ty, false_proof)
            };
            nat_not_even_implies_odd(d, a, not_even_a)
        });
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.odd_of_mul_right : ∀ m n, Odd (mul m n) → Odd n` —
/// `F:ml430-int-odd-of-mul-right-d6d1fc1d`. [`declare_odd_of_mul_left`]'s
/// mirror, via [`nat_even_mul_of_even_right`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_odd_of_mul_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.odd_of_mul_right, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let mn = d.imul(m, n);
        let odd_mn_ty = d.const_app(p.odd, &[mn]);
        let odd_n_ty = d.const_app(p.odd, &[n]);
        let stmt = d.arrow(odd_mn_ty, odd_n_ty);

        let a = nat_abs(d, m);
        let b = nat_abs(d, n);
        let nat_abs_mul_eq = d.const_app(p.nat_abs_mul, &[m, n]);
        let ab = d.mul(a, b);

        let proof = with_hyps(d, &[odd_mn_ty], &|d, h| {
            let natabs_mn = nat_abs(d, mn);
            let motive = |d: &mut IntDev<'_>, x: ExprId| d.const_app(p.nat.odd, &[x]);
            let odd_ab = d.nat_rewrite(natabs_mn, ab, nat_abs_mul_eq, h[0], &motive);
            let not_even_b = {
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);
                let even_b_ty = d.const_app(p.nat.even, &[b]);
                let even_ab = nat_even_mul_of_even_right(d, a, b, hb);
                let not_odd_of_even_ab = d.const_app(p.nat.even_not_odd, &[ab]);
                let refuter = d.apply(not_odd_of_even_ab, &[even_ab]);
                let false_proof = d.apply(refuter, &[odd_ab]);
                d.lam_fv(hb_fv, even_b_ty, false_proof)
            };
            nat_not_even_implies_odd(d, b, not_even_b)
        });
        (stmt, proof)
    })?;
    Ok(())
}
