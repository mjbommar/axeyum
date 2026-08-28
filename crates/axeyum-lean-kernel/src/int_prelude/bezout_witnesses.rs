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

use super::gcd::{neg_mul, neg_neg};
use super::ops::{Branch, IntDev, Shape, case_split};

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

// ---------------------------------------------------------------------------
// The identity.
// ---------------------------------------------------------------------------

/// `Eq Int (ofNat (Nat.gcd m n))
///         (ofNat m * xgcdAux fuel m n true + ofNat n * xgcdAux fuel m n false)`
/// — the statement [`declare_xgcd_aux_sound`] proves, at explicit arguments.
fn sound_statement(d: &mut IntDev<'_>, fuel: ExprId, m: ExprId, n: ExprId) -> ExprId {
    let common = NatOps::gcd(d, m, n);
    let lhs = d.of_nat(common);
    let m_i = d.of_nat(m);
    let n_i = d.of_nat(n);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let coeff_a = xgcd_aux(d, fuel, m, n, true_);
    let coeff_b = xgcd_aux(d, fuel, m, n, false_);
    let left = d.imul(m_i, coeff_a);
    let right = d.imul(n_i, coeff_b);
    let rhs = d.iadd(left, right);
    d.ieq(lhs, rhs)
}

/// [`sound_statement`] when the recursion has bottomed out — either because the
/// fuel is `zero` or because `m` is, both of which ι-reduce `xgcdAux` to the
/// base pair `(0, 1)`.
///
/// The whole content is `gcd 0 n = n` plus `0*0 + n*1 = n`; the algebra runs on
/// the right-hand side and is then reversed, because `ichain` composes forwards
/// from the goal's left-hand side.
fn zero_row_proof(d: &mut IntDev<'_>, fuel: ExprId, n: ExprId) -> ExprId {
    let p = d.int();
    let np = p.nat;
    let zero = d.zero();
    let zero_i = d.of_nat(zero);
    let n_i = d.of_nat(n);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let coeff_a = xgcd_aux(d, fuel, zero, n, true_);
    let coeff_b = xgcd_aux(d, fuel, zero, n, false_);
    let left = d.imul(zero_i, coeff_a);
    let right = d.imul(n_i, coeff_b);
    let rhs = d.iadd(left, right);
    let izero = d.izero();

    // `coeff_a` reduces to `Int.zero` and `coeff_b` to `Int.one`, so
    // `mul_zero`/`mul_one` apply up to defeq with no rewriting of the selector.
    let mul_zero_proof = d.lemma(p.mul_zero, &[zero_i]);
    let target_one = d.iadd(izero, right);
    let step_one = d.icongr(left, izero, mul_zero_proof, &|d, x| d.iadd(x, right));

    let mul_one_proof = d.lemma(p.mul_one, &[n_i]);
    let target_two = d.iadd(izero, n_i);
    let step_two = d.icongr(right, n_i, mul_one_proof, &|d, x| d.iadd(izero, x));

    let target_three = d.iadd(n_i, izero);
    let step_three = d.lemma(p.add_comm, &[izero, n_i]);
    let step_four = d.lemma(p.add_zero, &[n_i]);

    let (_, rhs_to_n) = d.ichain(
        rhs,
        &[
            (target_one, step_one),
            (target_two, step_two),
            (target_three, step_three),
            (n_i, step_four),
        ],
    );
    let n_to_rhs = d.isymm(rhs, n_i, rhs_to_n);

    let common = NatOps::gcd(d, zero, n);
    let gcd_zero = d.lemma(np.gcd_zero_left, &[n]);
    let lhs_to_n = d.nat_eq_to_int(common, n, gcd_zero, &|d, x| d.of_nat(x));
    let lhs = d.of_nat(common);
    d.itrans(lhs, n_i, rhs, lhs_to_n, n_to_rhs)
}

/// The inductive step at `fuel = succ pred_fuel`, `m = succ k`: a proof of
/// `Nat.le (succ k) (succ pred_fuel) → sound_statement (succ pred_fuel) (succ k) n`.
///
/// `induction_hypothesis` is the fuel induction's own hypothesis, already
/// generalized over both `m` and `n` — the generalization is what makes this
/// step possible at all, since it is applied at the *different* pair
/// `(n % succ k, succ k)`.
fn step_case(
    d: &mut IntDev<'_>,
    pred_fuel: ExprId,
    induction_hypothesis: ExprId,
    k: ExprId,
    n: ExprId,
) -> ExprId {
    let p = d.int();
    let np = p.nat;
    let fuel = d.succ(pred_fuel);
    let divisor = d.succ(k);
    let hypothesis = d.le(divisor, fuel);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let quotient = d.div(n, divisor);
    let remainder = d.modulo(n, divisor);

    // The fuel bound is preserved: `succ k <= succ f` gives `k <= f`, and
    // `mod_lt` gives `n % succ k < succ k`, hence `n % succ k <= k <= f`.
    let h_k = d.lemma(np.le_of_succ_le_succ, &[k, pred_fuel, h]);
    let h_pos = d.lemma(np.zero_lt_succ, &[k]);
    let h_lt = d.lemma(np.mod_lt, &[n, divisor, h_pos]);
    let h_rk = d.lemma(np.le_of_lt_succ, &[remainder, k, h_lt]);
    let h_le = d.lemma(np.le_trans, &[remainder, k, pred_fuel, h_rk, h_k]);

    let recursive = d.apply(induction_hypothesis, &[remainder, divisor, h_le]);

    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let coeff_a = xgcd_aux(d, pred_fuel, remainder, divisor, true_);
    let coeff_b = xgcd_aux(d, pred_fuel, remainder, divisor, false_);

    let s = d.of_nat(divisor);
    let q = d.of_nat(quotient);
    let r = d.of_nat(remainder);
    let n_i = d.of_nat(n);

    let r_a = d.imul(r, coeff_a);
    let s_b = d.imul(s, coeff_b);
    let recursive_rhs = d.iadd(r_a, s_b);
    let swapped = d.iadd(s_b, r_a);

    // Left-hand side: `gcd (succ k) n = gcd (n % succ k) (succ k)` is exactly
    // `gcd_succ`, which is why this orientation was chosen.
    let common_left = NatOps::gcd(d, divisor, n);
    let common_right = NatOps::gcd(d, remainder, divisor);
    let lhs = d.of_nat(common_left);
    let gcd_succ_proof = d.lemma(np.gcd_succ, &[k, n]);
    let unfold = d.nat_eq_to_int(common_left, common_right, gcd_succ_proof, &|d, x| {
        d.of_nat(x)
    });
    let recursed = d.of_nat(common_right);
    let commute = d.lemma(p.add_comm, &[r_a, s_b]);
    let (_, lhs_to_swapped) = d.ichain(
        lhs,
        &[
            (recursed, unfold),
            (recursive_rhs, recursive),
            (swapped, commute),
        ],
    );

    // Right-hand side: the goal's `xgcdAux (succ f) (succ k) n true` ι-reduces
    // to `coeff_b - ofNat q * coeff_a` and the `false` selector to `coeff_a`,
    // so the goal is stated here at those reducts.
    let q_a = d.imul(q, coeff_a);
    let difference = d.isub(coeff_b, q_a);
    let scaled = d.imul(s, difference);
    let n_a = d.imul(n_i, coeff_a);
    let goal_rhs = d.iadd(scaled, n_a);

    // `T`, the term that appears once negatively and once positively and whose
    // cancellation is the whole point of the algebra.
    let t = d.imul(s, q_a);

    let mul_sub_proof = d.lemma(p.mul_sub, &[s, coeff_b, q_a]);
    let head = d.isub(s_b, t);
    let after_a = d.iadd(head, n_a);
    let step_a = d.icongr(scaled, head, mul_sub_proof, &|d, x| d.iadd(x, n_a));

    // `n = succ k * q + r`, cast into `ℤ` for free: `ofNat` of a `Nat` sum of
    // products is *definitionally* the `Int` sum of products of `ofNat`s.
    let product_nat = d.mul(divisor, quotient);
    let reconstructed = d.add(product_nat, remainder);
    let equation_ty = d.eq(n, reconstructed);
    let bound_ty = d.lt(remainder, divisor);
    let relation = d.lemma(np.div_mod_exec, &[k, n]);
    let h_n = d.and_left(equation_ty, bound_ty, relation);
    let s_q = d.imul(s, q);
    let expanded = d.iadd(s_q, r);
    let expanded_a = d.imul(expanded, coeff_a);
    let after_b = d.iadd(head, expanded_a);
    let step_b = d.nat_eq_to_int(n, reconstructed, h_n, &|d, x| {
        let x_i = d.of_nat(x);
        let product = d.imul(x_i, coeff_a);
        d.iadd(head, product)
    });

    let comm_one = d.lemma(p.mul_comm, &[expanded, coeff_a]);
    let a_expanded = d.imul(coeff_a, expanded);
    let after_c = d.iadd(head, a_expanded);
    let step_c = d.icongr(expanded_a, a_expanded, comm_one, &|d, x| d.iadd(head, x));

    let distrib = d.lemma(p.left_distrib, &[coeff_a, s_q, r]);
    let a_sq = d.imul(coeff_a, s_q);
    let a_r = d.imul(coeff_a, r);
    let distributed = d.iadd(a_sq, a_r);
    let after_d = d.iadd(head, distributed);
    let step_d = d.icongr(a_expanded, distributed, distrib, &|d, x| d.iadd(head, x));

    let comm_two = d.lemma(p.mul_comm, &[coeff_a, s_q]);
    let sq_a = d.imul(s_q, coeff_a);
    let sum_e = d.iadd(sq_a, a_r);
    let after_e = d.iadd(head, sum_e);
    let step_e = d.icongr(a_sq, sq_a, comm_two, &|d, x| {
        let inner = d.iadd(x, a_r);
        d.iadd(head, inner)
    });

    let assoc = d.lemma(p.mul_assoc, &[s, q, coeff_a]);
    let sum_f = d.iadd(t, a_r);
    let after_f = d.iadd(head, sum_f);
    let step_f = d.icongr(sq_a, t, assoc, &|d, x| {
        let inner = d.iadd(x, a_r);
        d.iadd(head, inner)
    });

    let comm_three = d.lemma(p.mul_comm, &[coeff_a, r]);
    let sum_g = d.iadd(t, r_a);
    let after_g = d.iadd(head, sum_g);
    let step_g = d.icongr(a_r, r_a, comm_three, &|d, x| {
        let inner = d.iadd(t, x);
        d.iadd(head, inner)
    });

    // `Int.sub x y` is *defined* as `add x (neg y)`, so `head` needs no
    // rewriting to become the left operand `add_assoc` expects.
    let neg_t = d.ineg(t);
    let step_h = d.lemma(p.add_assoc, &[s_b, neg_t, sum_g]);
    let regrouped = d.iadd(neg_t, sum_g);
    let after_h = d.iadd(s_b, regrouped);

    let cancel_pair = d.iadd(neg_t, t);
    let assoc_inner = d.lemma(p.add_assoc, &[neg_t, t, r_a]);
    let left_grouped = d.iadd(cancel_pair, r_a);
    let assoc_reversed = d.isymm(left_grouped, regrouped, assoc_inner);
    let after_i = d.iadd(s_b, left_grouped);
    let step_i = d.icongr(regrouped, left_grouped, assoc_reversed, &|d, x| {
        d.iadd(s_b, x)
    });

    let comm_neg = d.lemma(p.add_comm, &[neg_t, t]);
    let t_neg_t = d.iadd(t, neg_t);
    let add_neg_proof = d.lemma(p.add_neg, &[t]);
    let izero = d.izero();
    let cancels = d.itrans(cancel_pair, t_neg_t, izero, comm_neg, add_neg_proof);
    let zero_plus = d.iadd(izero, r_a);
    let after_j = d.iadd(s_b, zero_plus);
    let step_j = d.icongr(cancel_pair, izero, cancels, &|d, x| {
        let inner = d.iadd(x, r_a);
        d.iadd(s_b, inner)
    });

    let comm_zero = d.lemma(p.add_comm, &[izero, r_a]);
    let plus_zero = d.iadd(r_a, izero);
    let drop_zero = d.lemma(p.add_zero, &[r_a]);
    let identity = d.itrans(zero_plus, plus_zero, r_a, comm_zero, drop_zero);
    let after_k = d.iadd(s_b, r_a);
    let step_k = d.icongr(zero_plus, r_a, identity, &|d, x| d.iadd(s_b, x));

    let (_, rhs_to_swapped) = d.ichain(
        goal_rhs,
        &[
            (after_a, step_a),
            (after_b, step_b),
            (after_c, step_c),
            (after_d, step_d),
            (after_e, step_e),
            (after_f, step_f),
            (after_g, step_g),
            (after_h, step_h),
            (after_i, step_i),
            (after_j, step_j),
            (after_k, step_k),
        ],
    );
    let swapped_to_rhs = d.isymm(goal_rhs, after_k, rhs_to_swapped);
    let full = d.itrans(lhs, swapped, goal_rhs, lhs_to_swapped, swapped_to_rhs);
    d.lam_fv(h_fv, hypothesis, full)
}

/// `Nat.xgcdAux_sound : ∀ f m n, Nat.le m f → ofNat (gcd m n) =
/// ofNat m * xgcdAux f m n true + ofNat n * xgcdAux f m n false`.
///
/// Induction on the **fuel**, with `m` and `n` both generalized in the motive
/// — the recursive call is at `(n % succ k, succ k)`, a different pair in both
/// coordinates, so a motive that fixed either one could not be applied at it.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_xgcd_aux_sound(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let np = p.nat;
    let nat = d.nat_ty();

    d.theorem(p.xgcd_aux_sound, 3, &|d, values| {
        let (fuel, m, n) = (values[0], values[1], values[2]);
        let hypothesis = d.le(m, fuel);
        let conclusion = sound_statement(d, fuel, m, n);
        let statement = d.arrow(hypothesis, conclusion);

        let motive = |d: &mut IntDev<'_>, f: ExprId| {
            let m_fv = d.fresh_fvar();
            let inner_m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let inner_n = d.kernel().fvar(n_fv);
            let bound = d.le(inner_m, f);
            let concl = sound_statement(d, f, inner_m, inner_n);
            let body = d.arrow(bound, concl);
            let with_n = d.pi_fv(n_fv, nat, body);
            d.pi_fv(m_fv, nat, with_n)
        };
        let base = |d: &mut IntDev<'_>| {
            let m_fv = d.fresh_fvar();
            let inner_m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let inner_n = d.kernel().fvar(n_fv);
            let zero = d.zero();
            let bound = d.le(inner_m, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // `m <= 0` forces `m = 0`, and the whole statement transports.
            let zero_le = d.lemma(np.zero_le, &[inner_m]);
            let m_is_zero = d.lemma(np.le_antisymm, &[inner_m, zero, h, zero_le]);
            let zero_is_m = d.symm(inner_m, zero, m_is_zero);
            let at_zero = zero_row_proof(d, zero, inner_n);
            let eq_motive = d.eq_motive(zero, &|d, x| sound_statement(d, zero, x, inner_n));
            let moved = d.transport(zero, eq_motive, at_zero, inner_m, zero_is_m);
            let with_h = d.lam_fv(h_fv, bound, moved);
            let with_n = d.lam_fv(n_fv, nat, with_h);
            d.lam_fv(m_fv, nat, with_n)
        };
        let step = |d: &mut IntDev<'_>, pred_fuel: ExprId, ih: ExprId| {
            let m_fv = d.fresh_fvar();
            let inner_m = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let inner_n = d.kernel().fvar(n_fv);
            let fuel = d.succ(pred_fuel);
            let case_motive = |d: &mut IntDev<'_>, x: ExprId| {
                let bound = d.le(x, fuel);
                let concl = sound_statement(d, fuel, x, inner_n);
                d.arrow(bound, concl)
            };
            let case_zero = |d: &mut IntDev<'_>| {
                let zero = d.zero();
                let bound = d.le(zero, fuel);
                let h_fv = d.fresh_fvar();
                let body = zero_row_proof(d, fuel, inner_n);
                d.lam_fv(h_fv, bound, body)
            };
            let case_succ = |d: &mut IntDev<'_>, k: ExprId, _unused: ExprId| {
                step_case(d, pred_fuel, ih, k, inner_n)
            };
            let split = d.induct(&case_motive, &case_zero, &case_succ, inner_m);
            let bound = d.le(inner_m, fuel);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let applied = d.apply(split, &[h]);
            let with_h = d.lam_fv(h_fv, bound, applied);
            let with_n = d.lam_fv(n_fv, nat, with_h);
            d.lam_fv(m_fv, nat, with_n)
        };
        let induction = d.induct(&motive, &base, &step, fuel);
        let proof = d.apply(induction, &[m, n]);
        (statement, proof)
    })?;
    Ok(())
}

/// `Nat.gcd_eq_gcd_ab : ∀ m n, ofNat (gcd m n) = ofNat m * gcdA m n + ofNat n * gcdB m n`.
///
/// [`declare_xgcd_aux_sound`] at `fuel := m`, whose hypothesis is then just
/// `Nat.le_refl`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_nat_gcd_eq_gcd_ab(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let np = p.nat;
    d.theorem(p.nat_gcd_eq_gcd_ab, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = NatOps::gcd(d, m, n);
        let lhs = d.of_nat(common);
        let m_i = d.of_nat(m);
        let n_i = d.of_nat(n);
        let coeff_a = nat_gcd_a(d, m, n);
        let coeff_b = nat_gcd_b(d, m, n);
        let left = d.imul(m_i, coeff_a);
        let right = d.imul(n_i, coeff_b);
        let rhs = d.iadd(left, right);
        let statement = d.ieq(lhs, rhs);

        let reflexive = d.lemma(np.le_refl_thm, &[m]);
        let sound = d.lemma(p.xgcd_aux_sound, &[m, m, n]);
        let proof = d.apply(sound, &[reflexive]);
        (statement, proof)
    })?;
    Ok(())
}

/// `Eq Int (mul (neg a) (neg b)) (mul a b)`.
///
/// Built from `gcd.rs`'s already-derived `neg_mul` / `neg_neg` plus the public
/// `Int.mul_neg`, rather than re-derived: the two lemmas were private helpers
/// there and are now `pub(super)`, so this is an extraction, not a second proof
/// of the same fact.
fn neg_mul_neg(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let neg_b = d.ineg(b);
    let product = d.imul(a, b);
    let neg_product = d.ineg(product);
    let a_neg_b = d.imul(a, neg_b);
    let neg_a_neg_b = d.imul(neg_a, neg_b);

    let step_one = neg_mul(d, a, neg_b);
    let neg_a_neg_b_folded = d.ineg(a_neg_b);
    let mul_neg_proof = d.lemma(p.mul_neg, &[a, b]);
    let double_neg = d.ineg(neg_product);
    let step_two = d.icongr(a_neg_b, neg_product, mul_neg_proof, &|d, x| d.ineg(x));
    let step_three = neg_neg(d, product);

    let (_, chained) = d.ichain(
        neg_a_neg_b,
        &[
            (neg_a_neg_b_folded, step_one),
            (double_neg, step_two),
            (product, step_three),
        ],
    );
    chained
}

/// One side of the `Int` lift: `Eq Int (mul x coefficient) (mul (ofNat magnitude) base)`
/// where `x` is the branch's constructor application and `coefficient` its
/// (possibly negated) `Nat` coefficient.
///
/// On `ofNat` both sides are literally the same term. On `negSucc` the value is
/// `neg (ofNat magnitude)` and the coefficient is `neg base`, and the two
/// negations cancel — which is exactly why [`declare_int_gcd_ab`] negates.
fn branch_factor(d: &mut IntDev<'_>, branch: Branch, base: ExprId) -> ExprId {
    match branch.0 {
        Shape::OfNat => {
            let value = d.of_nat(branch.1);
            let product = d.imul(value, base);
            d.irefl(product)
        }
        Shape::NegSucc => {
            let magnitude = d.succ(branch.1);
            let value = d.of_nat(magnitude);
            neg_mul_neg(d, value, base)
        }
    }
}

/// `Int.gcd_eq_gcd_ab_witnesses : ∀ x y,
/// Eq Int (ofNat (Int.gcd x y)) (add (mul x (gcdA x y)) (mul y (gcdB x y)))`
/// — Mathlib v4.30's `Int.gcd_eq_gcd_ab`, at the named computable witnesses.
///
/// Four branches, and in each one `Int.gcd`, `Int.gcdA` and `Int.gcdB` all
/// ι-reduce to their `Nat` counterparts at the branch's magnitudes, so the
/// content is [`declare_nat_gcd_eq_gcd_ab`] plus one `neg_mul_neg` per negative
/// argument.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_gcd_eq_gcd_ab_witnesses(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.gcd_eq_gcd_ab_witnesses, 2, &|d, values| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let (x, y) = (args[0], args[1]);
            let common = d.const_app(p.gcd, &[x, y]);
            let lhs = d.of_nat(common);
            let coeff_a = d.const_app(p.gcd_a, &[x, y]);
            let coeff_b = d.const_app(p.gcd_b, &[x, y]);
            let left = d.imul(x, coeff_a);
            let right = d.imul(y, coeff_b);
            let rhs = d.iadd(left, right);
            d.ieq(lhs, rhs)
        };
        let stmt = statement(d, values);
        let proof = case_split(d, values, &statement, &|d, branches| {
            let magnitude = |d: &mut IntDev<'_>, branch: Branch| match branch.0 {
                Shape::OfNat => branch.1,
                Shape::NegSucc => d.succ(branch.1),
            };
            let mx = magnitude(d, branches[0]);
            let my = magnitude(d, branches[1]);
            let base_a = nat_gcd_a(d, mx, my);
            let base_b = nat_gcd_b(d, mx, my);

            // `ofNat (gcd mx my) = ofNat mx * A + ofNat my * B`.
            let over_nat = d.lemma(p.nat_gcd_eq_gcd_ab, &[mx, my]);
            let mx_i = d.of_nat(mx);
            let my_i = d.of_nat(my);
            let nat_left = d.imul(mx_i, base_a);
            let nat_right = d.imul(my_i, base_b);
            let nat_rhs = d.iadd(nat_left, nat_right);

            // Each side's `x * gcdA x y` equals the `Nat` product it reduces
            // from, up to the two cancelling negations on a `negSucc` branch.
            let left_factor = branch_factor(d, branches[0], base_a);
            let right_factor = branch_factor(d, branches[1], base_b);
            let x = d.branch_term(branches[0]);
            let y = d.branch_term(branches[1]);
            // The goal's coefficients are the `Int`-level ones, which ι-reduce
            // to `base_a`/`base_b` on an `ofNat` branch and to their NEGATIONS
            // on a `negSucc` one. Writing `base_a` here instead was this
            // module's one kernel rejection: the two differ by exactly the sign
            // flip `declare_int_gcd_ab` exists to apply.
            let goal_coeff_a = d.const_app(p.gcd_a, &[x, y]);
            let goal_coeff_b = d.const_app(p.gcd_b, &[x, y]);
            let goal_left = d.imul(x, goal_coeff_a);
            let goal_right = d.imul(y, goal_coeff_b);
            // `left_factor : goal_left = nat_left`, so reverse both to rebuild
            // the goal's right-hand side from the `Nat` theorem's.
            let left_reversed = d.isymm(goal_left, nat_left, left_factor);
            let right_reversed = d.isymm(goal_right, nat_right, right_factor);
            let after_left = d.iadd(goal_left, nat_right);
            let step_left = d.icongr(nat_left, goal_left, left_reversed, &|d, z| {
                d.iadd(z, nat_right)
            });
            let after_right = d.iadd(goal_left, goal_right);
            let step_right = d.icongr(nat_right, goal_right, right_reversed, &|d, z| {
                d.iadd(goal_left, z)
            });

            let common = NatOps::gcd(d, mx, my);
            let lhs = d.of_nat(common);
            let (_, chained) = d.ichain(
                lhs,
                &[
                    (nat_rhs, over_nat),
                    (after_left, step_left),
                    (after_right, step_right),
                ],
            );
            chained
        });
        (stmt, proof)
    })?;
    Ok(())
}
