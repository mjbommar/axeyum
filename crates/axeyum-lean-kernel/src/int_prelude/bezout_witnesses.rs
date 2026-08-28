//! Bézout's identity **at named computable witnesses** — `Nat.gcdA`/`Nat.gcdB`
//! and `Int.gcdA`/`Int.gcdB`, the extended Euclidean coefficients as
//! `Definition`s that return data.
//!
//! # Why this module exists at all
//!
//! [`super::gcd::declare_gcd_eq_gcd_ab`] already proves Bézout, but in the
//! **existential** form
//!
//! ```text
//! Int.gcd_eq_gcd_ab : ∀ a b, ∃ u v, ofNat (Int.gcd a b) = a*u + b*v
//! ```
//!
//! and Mathlib v4.30 states it at *named* coefficients:
//!
//! ```text
//! theorem Int.gcd_eq_gcd_ab : ∀ x y : ℤ, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
//! ```
//!
//! The two are not a rearrangement of each other, and the gap is exactly the
//! gap between a `Prop` and a program. The existential form's witnesses come
//! from `Nat.gcd_bezout`, a **`Theorem`** whose four naturals live inside a
//! `Prop`, so they cannot be projected out without choice; and its sign
//! handling is a `Prop`-typed `Or`-elimination, not a computable branch. A
//! witness buried in a `Prop` is gone. So the coefficients have to be *built*,
//! by a genuine extended Euclidean algorithm, and Bézout re-derived for it.
//!
//! # The recursion, and why it is fuel-structural
//!
//! Extended Euclid recurses at `n % m`, which is not a constructor predecessor
//! of anything, so the equation compiler would reach for `WellFounded` and drag
//! `propext`/`Quot.sound` in with it — fatal to this project's axiom-freedom
//! metric. This module uses the device `nat_prelude::log`, `sqrt`, `clog` and
//! `defs::declare_executable_division` all use: **structural recursion on a
//! fuel argument**, instantiated at a value large enough to reach the base
//! case.
//!
//! ```text
//! Nat.xgcdAux 0        m        n sel ≡ if sel then 0 else 1
//! Nat.xgcdAux (succ f) 0        n sel ≡ if sel then 0 else 1
//! Nat.xgcdAux (succ f) (succ k) n sel ≡
//!     let r := n % succ k;  q := n / succ k
//!     let a' := Nat.xgcdAux f r (succ k) true
//!     let b' := Nat.xgcdAux f r (succ k) false
//!     if sel then b' - ofNat q * a' else a'
//! Nat.gcdA m n := Nat.xgcdAux m m n true
//! Nat.gcdB m n := Nat.xgcdAux m m n false
//! ```
//!
//! All three equations hold **definitionally** (β/δ/ι): no equation lemmas, and
//! nothing here appeals to an axiom.
//!
//! Two design points are load-bearing.
//!
//! *The pair is `Bool`-selected, not a `Prod`.* `Nat.xgcdAux`'s last argument
//! picks which coefficient to return, exactly as
//! `declare_executable_division`'s `Nat.divModState` selects quotient from
//! remainder with a `Bool`. That keeps one recursion (so one induction proves
//! both coefficients at once) without this kernel needing a product type, and
//! it keeps the motive of the fuel `Nat.rec` a plain non-dependent row
//! `fun _ => Nat → Nat → Bool → Int`.
//!
//! *The orientation matches this prelude's `Nat.gcd`, not Mathlib's `xgcdAux`.*
//! `Nat.gcd` here recurses on its **first** argument
//! (`gcd_zero_left : gcd 0 n = n`, `gcd_succ : gcd (succ k) n = gcd (n % succ
//! k) (succ k)`), so the recursion above shrinks `m` and the step's recursive
//! call is at `(n % succ k, succ k)` — precisely `gcd_succ`'s right-hand side.
//! That is what makes the induction's step a two-line appeal to `gcd_succ`
//! rather than a re-derivation of Euclid.
//!
//! # The fuel bound, and why `m` suffices
//!
//! The invariant is `m ≤ fuel`, and [`declare_xgcd_aux_sound`] carries it as an
//! explicit hypothesis. It is preserved: in the step `fuel = succ f` and
//! `m = succ k`, so `succ k ≤ succ f` gives `k ≤ f`, while
//! `Nat.mod_lt n (succ k) (zero_lt_succ k)` gives `n % succ k < succ k`, i.e.
//! `n % succ k ≤ k`; `le_trans` closes `n % succ k ≤ f`. Instantiating at
//! `fuel := m` needs only `m ≤ m`, so `Nat.gcdA`/`Nat.gcdB` never run short —
//! and note the bound is on the *proof*, not the definition: with too little
//! fuel the function still computes, it just answers for a truncated recursion.
//!
//! # The identity
//!
//! [`declare_xgcd_aux_sound`] proves, by induction on the fuel with **both**
//! `m` and `n` generalized in the motive,
//!
//! ```text
//! ∀ f m n, m ≤ f → ofNat (Nat.gcd m n) = ofNat m * xgcdAux f m n true
//!                                       + ofNat n * xgcdAux f m n false
//! ```
//!
//! The step's algebra is the one line of real content. Writing `S = ofNat (succ
//! k)`, `Q = ofNat (n / succ k)`, `R = ofNat (n % succ k)` and `a'`, `b'` for
//! the recursive coefficients, `Nat.div_mod_exec` gives `n = succ k * q + r`,
//! which casts into `ℤ` for free (`Int.add`/`Int.mul` of two `ofNat`s ι-reduce
//! to `ofNat` of the `Nat` operation), and then
//!
//! ```text
//!   S * (b' - Q*a') + (S*Q + R) * a'
//! = (S*b' - S*(Q*a')) + ((S*Q)*a' + R*a')      distributivity
//! = (S*b' + neg T) + (T + R*a')                T := S*(Q*a'), by mul_assoc
//! = S*b' + R*a'                                the two `T`s cancel
//! = R*a' + S*b'                                add_comm
//! ```
//!
//! and the last line is the induction hypothesis at `(n % succ k, succ k)`,
//! after `gcd_succ` moves the goal's `gcd (succ k) n` onto `gcd (n % succ k)
//! (succ k)`.
//!
//! # Sign bookkeeping at `ℤ`
//!
//! `Int.gcdA`/`Int.gcdB` are Mathlib's definitions verbatim — a computable
//! `Int.rec` on the *first* argument for `gcdA` and the *second* for `gcdB`,
//! negating the `Nat` coefficient on the `negSucc` branch. The four-branch
//! lift is then a `case_split` in which each branch is the `Nat` theorem plus
//! `mul_neg`-shaped rewriting, mirroring what
//! [`super::gcd::declare_gcd_eq_gcd_ab`] already does for the existential form.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// Delta height for `Nat.xgcdAux`: above every `Int` and `Nat` definition it
/// calls (`Int.sub`/`Int.mul`/`Int.ofNat`, `Nat.div`/`Nat.mod`).
const XGCD_AUX_HEIGHT: u16 = 30;
/// `Nat.gcdA`/`Nat.gcdB` call `Nat.xgcdAux`.
const NAT_GCD_AB_HEIGHT: u16 = 31;
/// `Int.gcdA`/`Int.gcdB` call `Nat.gcdA`/`Nat.gcdB` and `Int.natAbs`.
const INT_GCD_AB_HEIGHT: u16 = 32;

/// Computational `if condition then on_true else on_false` at `Int` — the
/// `Int`-typed twin of `NatOps::bool_select_nat`, which is `Nat`-only.
fn bool_select_int(
    d: &mut IntDev<'_>,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, int_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `Nat.xgcdAux fuel m n selector`.
fn xgcd_aux(d: &mut IntDev<'_>, fuel: ExprId, m: ExprId, n: ExprId, selector: ExprId) -> ExprId {
    let f = d.int().xgcd_aux;
    d.const_app(f, &[fuel, m, n, selector])
}

/// `Nat.gcdA m n` — the coefficient of `m`.
fn nat_gcd_a(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let f = d.int().nat_gcd_a;
    d.const_app(f, &[m, n])
}

/// `Nat.gcdB m n` — the coefficient of `n`.
fn nat_gcd_b(d: &mut IntDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let f = d.int().nat_gcd_b;
    d.const_app(f, &[m, n])
}

/// `Int.natAbs a`.
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().nat_abs;
    d.const_app(f, &[a])
}

/// Declare `Nat.xgcdAux`, the fuel-structural extended Euclidean recursion,
/// and its two projections `Nat.gcdA` / `Nat.gcdB`.
///
/// See the module doc for the three definitional equations and the fuel
/// argument's role; nothing here is a `Theorem`, so nothing here needs a proof.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_xgcd_aux(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    // The row a single fuel step produces: `Nat -> Nat -> Bool -> Int`.
    let sel_to_int = d.arrow(bool_ty, int_ty);
    let n_to_row = d.arrow(nat, sel_to_int);
    let row_ty = d.arrow(nat, n_to_row);

    // Shared base answer: the pair `(0, 1)`, i.e. `gcd 0 n = n = 0*0 + n*1`.
    fn base_pair(d: &mut IntDev<'_>, selector: ExprId) -> ExprId {
        let zero = d.izero();
        let one_i = d.ione();
        bool_select_int(d, selector, zero, one_i)
    }

    // fuel = zero: answer as if `m` were already zero.
    let zero_minor = {
        let m_fv = d.fresh_fvar();
        let n_fv = d.fresh_fvar();
        let sel_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(sel_fv);
        let body = base_pair(d, selector);
        let with_sel = d.lam_fv(sel_fv, bool_ty, body);
        let with_n = d.lam_fv(n_fv, nat, with_sel);
        d.lam_fv(m_fv, nat, with_n)
    };

    // fuel = succ f: case-split on `m`'s own constructor. The inner `Nat.rec`
    // is at the plain motive `fun _ : Nat => Int` because `selector` is already
    // bound outside it, which keeps both recursors non-dependent.
    let succ_minor = {
        let f_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let n_fv = d.fresh_fvar();
        let sel_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let m = d.kernel().fvar(m_fv);
        let n = d.kernel().fvar(n_fv);
        let selector = d.kernel().fvar(sel_fv);

        let m_zero_minor = base_pair(d, selector);
        let m_succ_minor = {
            let k_fv = d.fresh_fvar();
            let unused_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let divisor = d.succ(k);
            let remainder = d.modulo(n, divisor);
            let quotient = d.div(n, divisor);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let coeff_a = d.apply(ih, &[remainder, divisor, true_]);
            let coeff_b = d.apply(ih, &[remainder, divisor, false_]);
            let quotient_i = d.of_nat(quotient);
            let scaled = d.imul(quotient_i, coeff_a);
            let next_a = d.isub(coeff_b, scaled);
            let selected = bool_select_int(d, selector, next_a, coeff_a);
            let with_unused = d.lam_fv(unused_fv, int_ty, selected);
            d.lam_fv(k_fv, nat, with_unused)
        };
        let m_motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
        let nat_rec = d.int().nat.rec;
        let rec = d.kernel().const_(nat_rec, vec![one]);
        let body = d.apply(rec, &[m_motive, m_zero_minor, m_succ_minor, m]);

        let with_sel = d.lam_fv(sel_fv, bool_ty, body);
        let with_n = d.lam_fv(n_fv, nat, with_sel);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        let with_ih = d.lam_fv(ih_fv, row_ty, with_m);
        d.lam_fv(f_fv, nat, with_ih)
    };

    let value = {
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let fuel_motive = d.kernel().lam(anon, nat, row_ty, BinderInfo::Default);
        let nat_rec = d.int().nat.rec;
        let rec = d.kernel().const_(nat_rec, vec![one]);
        let body = d.apply(rec, &[fuel_motive, zero_minor, succ_minor, fuel]);
        d.lam_fv(fuel_fv, nat, body)
    };
    let ty = d.arrow(nat, row_ty);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.xgcd_aux,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(XGCD_AUX_HEIGHT),
    })?;

    // `Nat.gcdA m n := xgcdAux m m n true`, `Nat.gcdB` the `false` selector.
    // The fuel is `m` itself; see the module doc for why that always suffices.
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    for (name, selector) in [(p.nat_gcd_a, true_), (p.nat_gcd_b, false_)] {
        let m_fv = d.fresh_fvar();
        let n_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n = d.kernel().fvar(n_fv);
        let body = xgcd_aux(d, m, m, n, selector);
        let with_n = d.lam_fv(n_fv, nat, body);
        let value = d.lam_fv(m_fv, nat, with_n);
        let inner = d.arrow(nat, int_ty);
        let ty = d.arrow(nat, inner);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(NAT_GCD_AB_HEIGHT),
        })?;
    }
    Ok(())
}

/// Declare `Int.gcdA` and `Int.gcdB`, Mathlib's signed coefficients.
///
/// `gcdA` matches on its **first** argument and `gcdB` on its **second**, each
/// negating the `Nat` coefficient under `negSucc` — because `negSucc k` is
/// `-(succ k)` while `natAbs (negSucc k)` is `succ k`, so the coefficient has
/// to flip to keep `x * gcdA x y` unchanged.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_int_gcd_ab(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();

    for on_first in [true, false] {
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);

        // The argument NOT being split contributes only its magnitude.
        let fixed_magnitude = if on_first {
            nat_abs(d, y)
        } else {
            nat_abs(d, x)
        };

        let of_nat_minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = if on_first {
                nat_gcd_a(d, k, fixed_magnitude)
            } else {
                nat_gcd_b(d, fixed_magnitude, k)
            };
            d.lam_fv(k_fv, nat, body)
        };
        let neg_succ_minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let magnitude = d.succ(k);
            let coeff = if on_first {
                nat_gcd_a(d, magnitude, fixed_magnitude)
            } else {
                nat_gcd_b(d, fixed_magnitude, magnitude)
            };
            let body = d.ineg(coeff);
            d.lam_fv(k_fv, nat, body)
        };

        let motive = d.kernel().lam(anon, int_ty, int_ty, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let target = if on_first { x } else { y };
        let body = d.apply(rec, &[motive, of_nat_minor, neg_succ_minor, target]);
        let value = {
            let with_y = d.lam_fv(y_fv, int_ty, body);
            d.lam_fv(x_fv, int_ty, with_y)
        };
        let inner = d.arrow(int_ty, int_ty);
        let ty = d.arrow(int_ty, inner);
        d.kernel().add_declaration(Declaration::Definition {
            name: if on_first { p.gcd_a } else { p.gcd_b },
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(INT_GCD_AB_HEIGHT),
        })?;
    }
    Ok(())
}
