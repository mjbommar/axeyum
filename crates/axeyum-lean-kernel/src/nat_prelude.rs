//! The **natural-number prelude**: arithmetic over the logic prelude's
//! *inductive* `Nat`, together with the `Eq`-combinator and induction machinery
//! a development needs to use it.
//!
//! Unlike [`build_arith_prelude`](crate::build_arith_prelude) (an axiomatized
//! linear ordered field, for Farkas/LRA reconstruction) and
//! [`build_int_prelude`](crate::build_int_prelude) (an axiomatized discretely
//! ordered ring, for integer-cut reconstruction), **this prelude declares no
//! axioms at all**. [`build_logic_prelude`] admits `Nat` as a real inductive
//! with a real, ι-computing `Nat.rec`, so `add`/`mul`/`pow` are *definitions* by
//! structural recursion and every algebraic law below is a *theorem* the kernel
//! type-checks at admission through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration).
//! `nat_prelude_tests::the_nat_prelude_declares_no_axioms` enforces that claim
//! mechanically by walking the resulting environment.
//!
//! ## What is declared (all under the `Nat` namespace)
//!
//! **Recursive arithmetic definitions** — each by `Nat.rec` on its **second**
//! argument, so the defining equations hold *definitionally* (β/δ/ι) and need
//! no equation lemmas:
//!
//! | name      | zero case            | successor case                       |
//! |-----------|----------------------|--------------------------------------|
//! | `Nat.add` | `add x zero ≡ x`     | `add x (succ j) ≡ succ (add x j)`    |
//! | `Nat.mul` | `mul x zero ≡ zero`  | `mul x (succ j) ≡ add (mul x j) x`   |
//! | `Nat.pow` | `pow x zero ≡ 1`     | `pow x (succ j) ≡ mul (pow x j) x`   |
//!
//! **Finite ranges**: `Nat.sumRange f n` recursively sums `f 0` through
//! `f (n-1)`. Its empty and successor equations are checked theorems backed by
//! definitional reduction.
//!
//! **Defining-equation theorems** (`add_zero`, `add_succ`, `mul_zero`,
//! `mul_succ`, `pow_zero`, `pow_succ`) — each proved by `Eq.refl`; they exist so
//! callers can rewrite by name without knowing the recursion scheme.
//!
//! **Additive theorems**: `zero_add`, `succ_add`, `add_comm`, `add_assoc`,
//! `add_right_comm`.
//!
//! **Multiplicative theorems**: `zero_mul`, `succ_mul`, `mul_comm`,
//! `left_distrib`, `mul_assoc`, `one_mul`, `mul_one`.
//!
//! **Order** (`Nat.le`): an *indexed* `Prop`-valued inductive relation with the
//! same shape as Lean's own `Nat.le` — `Nat.le.refl : Le n n` and
//! `Nat.le.step : Le n m → Le n (succ m)` — admitted through the same trusted
//! inductive gate, so its recursor `Nat.le.rec` (induction on the *derivation*)
//! is kernel-generated. `Nat.lt n m := Nat.le (Nat.succ n) m`. Theorems:
//! `zero_le`, `le_succ_succ`, `le_of_succ_le_succ`, `le_trans`, and
//! `le_add_right`.
//!
//! **Divisibility**: `Nat.dvd a n := Exists (fun q => n = a * q)`, together
//! with checked theorems `dvd_mul` (witness introduction) and `dvd_add`
//! (closure under addition by two `Exists.rec` eliminations).
//!
//! ## What is **not** here
//!
//! No subtraction/predecessor, no antisymmetry, totality, `min`, or
//! decidability of order, no quotient/remainder division, no
//! `n ≠ succ n`-style discrimination.
//! Adding those is ordinary work on top of this prelude, not a kernel question:
//! the order fragment is deliberately minimal (see [`NatPrelude::le`]).
//!
//! ## Building proofs on top
//!
//! [`NatOps`] is the reusable proof-construction layer: `Eq` combinators
//! (`symm`, `trans`, `congr`, `chain`, `transport`, `eq_motive`), a `Nat.rec`
//! [`induct`](NatOps::induct) helper for `Prop`-valued motives, and the
//! [`define_binary`](NatOps::define_binary) /
//! [`theorem`](NatOps::theorem) declaration plumbing. Implement its two required
//! methods on your own development struct (so your own operators stay ordinary
//! methods and every closure keeps taking `&mut YourDev`), or use the ready-made
//! [`NatDev`] over a borrowed kernel.

// Proof scripts are long, straight-line term constructions with short
// mathematical names; splitting them would obscure the derivation they mirror.
// `type_complexity`: the higher-order declaration helpers take
// `&dyn Fn(&mut Self, …) -> …` builders; a type alias mentioning `Self` is not
// expressible, and naming them per-implementor would hide the signature.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{
    BinderInfo, Kernel, KernelError, LogicPrelude, PreludeKey, PreludeValue, build_logic_prelude,
};

/// The interned names produced by [`build_nat_prelude`]: the inductive `Nat`
/// and its constructors/recursor (re-exported from the [`LogicPrelude`] for
/// convenience), the arithmetic definitions, and every theorem name.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms
/// (`k.const_(nat.add, vec![])`) directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatPrelude {
    /// The embedded logical prelude (`False`, `Not`, `Eq`, `Exists`, `Nat`, …).
    pub logic: LogicPrelude,

    // --- the inductive Nat (from the logic prelude) --------------------------
    /// `Nat : Type` — the inductive unary naturals.
    pub nat: NameId,
    /// `Nat.zero : Nat`.
    pub zero: NameId,
    /// `Nat.succ : Nat → Nat`.
    pub succ: NameId,
    /// `Nat.rec` — the generated, ι-computing recursor.
    pub rec: NameId,

    // --- definitions ---------------------------------------------------------
    /// `Nat.add : Nat → Nat → Nat`, by recursion on the second argument.
    pub add: NameId,
    /// `Nat.mul : Nat → Nat → Nat`, by recursion on the second argument.
    pub mul: NameId,
    /// `Nat.pow : Nat → Nat → Nat`, by recursion on the exponent.
    pub pow: NameId,
    /// `Nat.sumRange : (Nat → Nat) → Nat → Nat`.
    pub sum_range: NameId,

    // --- defining equations (each proved by `Eq.refl`) -----------------------
    /// `add_zero : ∀ (n : Nat), Eq Nat (add n zero) n`.
    pub add_zero: NameId,
    /// `add_succ : ∀ (n m : Nat), Eq Nat (add n (succ m)) (succ (add n m))`.
    pub add_succ: NameId,
    /// `mul_zero : ∀ (n : Nat), Eq Nat (mul n zero) zero`.
    pub mul_zero: NameId,
    /// `mul_succ : ∀ (n m : Nat), Eq Nat (mul n (succ m)) (add (mul n m) n)`.
    pub mul_succ: NameId,
    /// `pow_zero : ∀ (n : Nat), Eq Nat (pow n zero) (succ zero)`.
    pub pow_zero: NameId,
    /// `pow_succ : ∀ (n m : Nat), Eq Nat (pow n (succ m)) (mul (pow n m) n)`.
    pub pow_succ: NameId,
    /// `sumRange_zero : ∀ f, sumRange f zero = zero`.
    pub sum_range_zero: NameId,
    /// `sumRange_succ : ∀ f n, sumRange f (succ n) = sumRange f n + f n`.
    pub sum_range_succ: NameId,
    /// `mul_sumRange_pow : ∀ a n, a * sumRange (a^·) n = sumRange (a^(·+1)) n`.
    pub mul_sum_range_pow: NameId,

    // --- additive theorems ---------------------------------------------------
    /// `zero_add : ∀ (n : Nat), Eq Nat (add zero n) n`.
    pub zero_add: NameId,
    /// `succ_add : ∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m))`.
    pub succ_add: NameId,
    /// `add_comm : ∀ (n m : Nat), Eq Nat (add n m) (add m n)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_right_comm : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add (add a c) b)`.
    pub add_right_comm: NameId,

    // --- multiplicative theorems --------------------------------------------
    /// `zero_mul : ∀ (n : Nat), Eq Nat (mul zero n) zero`.
    pub zero_mul: NameId,
    /// `succ_mul : ∀ (n m : Nat), Eq Nat (mul (succ n) m) (add (mul n m) m)`.
    pub succ_mul: NameId,
    /// `mul_comm : ∀ (n m : Nat), Eq Nat (mul n m) (mul m n)`.
    pub mul_comm: NameId,
    /// `left_distrib : ∀ (a b c : Nat), Eq Nat (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `mul_assoc : ∀ (a b c : Nat), Eq Nat (mul (mul a b) c) (mul a (mul b c))`.
    pub mul_assoc: NameId,
    /// `one_mul : ∀ (a : Nat), Eq Nat (mul (succ zero) a) a`.
    pub one_mul: NameId,
    /// `mul_one : ∀ (a : Nat), Eq Nat (mul a (succ zero)) a`.
    pub mul_one: NameId,

    // --- the order relation --------------------------------------------------
    /// `Nat.le : Nat → Nat → Prop` — an indexed inductive relation with the
    /// shape of Lean's own `Nat.le` (the first argument is a *parameter*, the
    /// second an *index*).
    ///
    /// This fragment is deliberately minimal: it carries reflexivity/step
    /// (the constructors), `zero_le`, successor monotonicity/inversion,
    /// transitivity, and `le_add_right` — enough to *state and derive* bounds,
    /// but **not** a complete order library. There is no antisymmetry,
    /// totality, `min`, or decidability. The constructor shape matches Lean's,
    /// so those are extensions rather than redesigns.
    pub le: NameId,
    /// `Nat.lt n m := Nat.le (Nat.succ n) m`.
    pub lt: NameId,
    /// `Nat.le.refl : ∀ (n : Nat), Le n n`.
    pub le_refl: NameId,
    /// `Nat.le.step : ∀ (n m : Nat), Le n m → Le n (succ m)`.
    pub le_step: NameId,
    /// `Nat.le.rec` — the generated recursor (induction on the derivation).
    pub le_rec: NameId,
    /// `zero_le : ∀ (n : Nat), Le zero n`.
    pub zero_le: NameId,
    /// `le_succ_succ : ∀ (n m : Nat), Le n m → Le (succ n) (succ m)`.
    pub le_succ_succ: NameId,
    /// `le_of_succ_le_succ : ∀ (n m : Nat), Le (succ n) (succ m) → Le n m`.
    pub le_of_succ_le_succ: NameId,
    /// `le_trans : ∀ (a b c : Nat), Le a b → Le b c → Le a c`.
    pub le_trans: NameId,
    /// `le_add_right : ∀ (n k : Nat), Le n (add n k)`.
    pub le_add_right: NameId,

    // --- divisibility -------------------------------------------------------
    /// `Nat.dvd : Nat → Nat → Prop`, where `dvd a n := ∃ q, n = a * q`.
    pub dvd: NameId,
    /// `Nat.dvd_mul : ∀ a q, dvd a (a * q)`.
    pub dvd_mul: NameId,
    /// `Nat.dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)`.
    pub dvd_add: NameId,
}

/// Declare the natural-number prelude into `kernel`'s environment, returning the
/// [`NatPrelude`] of interned names.
///
/// The shared logical prelude is built or exact-validated first (as
/// [`build_int_prelude`](crate::build_int_prelude) does).
/// Every definition and theorem is admitted through the **trusted**
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate and `Nat.le`
/// through [`Kernel::add_inductive`](crate::Kernel::add_inductive) — the kernel
/// re-checks each proof term against its stated proposition, so a green build of
/// this function *is* a machine-checked proof of every theorem it declares.
///
/// Repeated construction validates and returns the exact registered package.
/// Any trusted-gate rejection is returned as [`KernelError`] and rolls back all
/// Nat declarations admitted by this invocation.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A failed
/// Nat build leaves the pre-call environment unchanged.
pub fn build_nat_prelude(kernel: &mut Kernel) -> Result<NatPrelude, KernelError> {
    let logic = build_logic_prelude(kernel)?;
    if let Some(PreludeValue::Nat(prelude)) = kernel.cached_prelude(PreludeKey::Nat)? {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<NatPrelude, KernelError> {
        let nat = logic.nat;

        // Intern every name up front so the `NatPrelude` (which the proof scripts
        // below consult for lemma handles) exists before anything is declared.
        let le = kernel.name_str(nat, "le");
        let p = NatPrelude {
            logic,
            nat,
            zero: logic.nat_zero,
            succ: logic.nat_succ,
            rec: logic.nat_rec,
            add: kernel.name_str(nat, "add"),
            mul: kernel.name_str(nat, "mul"),
            pow: kernel.name_str(nat, "pow"),
            sum_range: kernel.name_str(nat, "sumRange"),
            add_zero: kernel.name_str(nat, "add_zero"),
            add_succ: kernel.name_str(nat, "add_succ"),
            mul_zero: kernel.name_str(nat, "mul_zero"),
            mul_succ: kernel.name_str(nat, "mul_succ"),
            pow_zero: kernel.name_str(nat, "pow_zero"),
            pow_succ: kernel.name_str(nat, "pow_succ"),
            sum_range_zero: kernel.name_str(nat, "sumRange_zero"),
            sum_range_succ: kernel.name_str(nat, "sumRange_succ"),
            mul_sum_range_pow: kernel.name_str(nat, "mul_sumRange_pow"),
            zero_add: kernel.name_str(nat, "zero_add"),
            succ_add: kernel.name_str(nat, "succ_add"),
            add_comm: kernel.name_str(nat, "add_comm"),
            add_assoc: kernel.name_str(nat, "add_assoc"),
            add_right_comm: kernel.name_str(nat, "add_right_comm"),
            zero_mul: kernel.name_str(nat, "zero_mul"),
            succ_mul: kernel.name_str(nat, "succ_mul"),
            mul_comm: kernel.name_str(nat, "mul_comm"),
            left_distrib: kernel.name_str(nat, "left_distrib"),
            mul_assoc: kernel.name_str(nat, "mul_assoc"),
            one_mul: kernel.name_str(nat, "one_mul"),
            mul_one: kernel.name_str(nat, "mul_one"),
            le,
            lt: kernel.name_str(nat, "lt"),
            le_refl: kernel.name_str(le, "refl"),
            le_step: kernel.name_str(le, "step"),
            le_rec: kernel.name_str(le, "rec"),
            zero_le: kernel.name_str(nat, "zero_le"),
            le_succ_succ: kernel.name_str(nat, "le_succ_succ"),
            le_of_succ_le_succ: kernel.name_str(nat, "le_of_succ_le_succ"),
            le_trans: kernel.name_str(nat, "le_trans"),
            le_add_right: kernel.name_str(nat, "le_add_right"),
            dvd: kernel.name_str(nat, "dvd"),
            dvd_mul: kernel.name_str(nat, "dvd_mul"),
            dvd_add: kernel.name_str(nat, "dvd_add"),
        };

        let mut d = NatDev::new(kernel, p);
        declare_arithmetic(&mut d, &p)?;
        declare_finite_ranges(&mut d, &p)?;
        declare_defining_equations(&mut d, &p)?;
        declare_additive_theorems(&mut d, &p)?;
        declare_multiplicative_theorems(&mut d, &p)?;
        declare_finite_sum_theorems(&mut d, &p)?;
        declare_order(&mut d, &p)?;
        declare_divisibility(&mut d, &p)?;
        Ok(p)
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(PreludeKey::Nat, PreludeValue::Nat(prelude), checkpoint);
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

/// `add`, `mul`, `pow` — structural recursion on the second argument.
fn declare_arithmetic(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // add x zero ≡ x ; add x (succ j) ≡ succ (add x j)
    d.define_binary(p.add, 1, &|_d, x| x, &|d, _x, _j, ih| d.succ(ih))?;
    // mul x zero ≡ zero ; mul x (succ j) ≡ add (mul x j) x
    d.define_binary(p.mul, 2, &|d, _x| d.zero(), &|d, x, _j, ih| d.add(ih, x))?;
    // pow x zero ≡ 1 ; pow x (succ j) ≡ mul (pow x j) x
    d.define_binary(p.pow, 3, &|d, _x| d.num(1), &|d, x, _j, ih| d.mul(ih, x))?;
    Ok(())
}

/// `sumRange f n = f 0 + ... + f (n-1)`, by structural recursion on `n`.
fn declare_finite_ranges(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
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
    Ok(())
}

/// The defining equations, each a one-line `Eq.refl` proof: they hold by β/δ/ι,
/// so the kernel accepts `refl` against the stated equation.
fn declare_defining_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
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
    Ok(())
}

/// `zero_add`, `succ_add`, `add_comm`, `add_assoc`, `add_right_comm`.
fn declare_additive_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // zero_add : ∀ n, add zero n = n   (induction on n)
    d.theorem(p.zero_add, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.add(z, x);
            d.eq(lhs, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                let z = d.zero();
                let lhs = d.add(z, j);
                d.congr(lhs, j, ih, &|d, x| d.succ(x))
            },
            n,
        );
        (stmt, proof)
    })?;

    // succ_add : ∀ n m, add (succ n) m = succ (add n m)   (induction on m)
    d.theorem(p.succ_add, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.add(sn, x);
            let inner = d.add(n, x);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let sn = d.succ(n);
                d.refl(sn)
            },
            &|d, j, ih| {
                let sn = d.succ(n);
                let lhs = d.add(sn, j);
                let inner = d.add(n, j);
                let rhs = d.succ(inner);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_comm : ∀ n m, add n m = add m n   (induction on m)
    d.theorem(p.add_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.add(n, x);
            let rhs = d.add(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let za = d.add(z, n);
                let h = d.lemma(p.zero_add, &[n]);
                d.symm(za, n, h)
            },
            &|d, j, ih| {
                let lhs = d.add(n, j);
                let rhs = d.add(j, n);
                let h1 = d.congr(lhs, rhs, ih, &|d, x| d.succ(x));
                let s_lhs = d.succ(lhs);
                let s_rhs = d.succ(rhs);
                let sj = d.succ(j);
                let sj_n = d.add(sj, n);
                let h_sa = d.lemma(p.succ_add, &[j, n]);
                let h2 = d.symm(sj_n, s_rhs, h_sa);
                d.trans(s_lhs, s_rhs, sj_n, h1, h2)
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_assoc : ∀ a b c, add (add a b) c = add a (add b c)   (induction on c)
    d.theorem(p.add_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.add(a, b);
            let lhs = d.add(ab, x);
            let bx = d.add(b, x);
            let rhs = d.add(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.add(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                let ab = d.add(a, b);
                let lhs = d.add(ab, j);
                let bj = d.add(b, j);
                let rhs = d.add(a, bj);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            c,
        );
        (stmt, proof)
    })?;

    // add_right_comm : ∀ x y z, add (add x y) z = add (add x z) y   (no induction)
    d.theorem(p.add_right_comm, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let xy = d.add(x, y);
        let start = d.add(xy, z);
        let yz = d.add(y, z);
        let s1 = d.add(x, yz);
        let h1 = d.lemma(p.add_assoc, &[x, y, z]);
        let zy = d.add(z, y);
        let s2 = d.add(x, zy);
        let h_comm = d.lemma(p.add_comm, &[y, z]);
        let h2 = d.congr(yz, zy, h_comm, &|d, t| d.add(x, t));
        let xz = d.add(x, z);
        let s3 = d.add(xz, y);
        let h_assoc2 = d.lemma(p.add_assoc, &[x, z, y]);
        let h3 = d.symm(s3, s2, h_assoc2);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    })?;
    Ok(())
}

/// `zero_mul`, `succ_mul`, `mul_comm`, `mul_one`, `one_mul`, `left_distrib`,
/// `mul_assoc`.
fn declare_multiplicative_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // zero_mul : ∀ n, mul zero n = zero   (induction on n)
    d.theorem(p.zero_mul, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.mul(z, x);
            d.eq(lhs, z)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            // mul zero (succ j) ≡ add (mul zero j) zero ≡ mul zero j, so the
            // induction hypothesis *is* the step, up to definitional equality.
            &|_d, _j, ih| ih,
            n,
        );
        (stmt, proof)
    })?;

    // succ_mul : ∀ n m, mul (succ n) m = add (mul n m) m   (induction on m)
    d.theorem(p.succ_mul, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.mul(sn, x);
            let nm = d.mul(n, x);
            let rhs = d.add(nm, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ succ (add (mul (succ n) j) n) = succ (add (add (mul n j) n) j)
                let sn = d.succ(n);
                let snj = d.mul(sn, j);
                let start = d.add(snj, n);
                let nj = d.mul(n, j);
                let nj_j = d.add(nj, j);
                let s1 = d.add(nj_j, n);
                let h1 = d.congr(snj, nj_j, ih, &|d, t| d.add(t, n));
                let nj_n = d.add(nj, n);
                let s2 = d.add(nj_n, j);
                let h2 = d.lemma(p.add_right_comm, &[nj, j, n]);
                let (end, inner) = d.chain(start, &[(s1, h1), (s2, h2)]);
                d.congr(start, end, inner, &|d, t| d.succ(t))
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_comm : ∀ n m, mul n m = mul m n   (induction on m)
    d.theorem(p.mul_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.mul(n, x);
            let rhs = d.mul(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let zn = d.mul(z, n);
                let h = d.lemma(p.zero_mul, &[n]);
                d.symm(zn, z, h)
            },
            &|d, j, ih| {
                // goal ≡ add (mul n j) n = mul (succ j) n
                let nj = d.mul(n, j);
                let start = d.add(nj, n);
                let jn = d.mul(j, n);
                let s1 = d.add(jn, n);
                let h1 = d.congr(nj, jn, ih, &|d, t| d.add(t, n));
                let sj = d.succ(j);
                let s2 = d.mul(sj, n);
                let h_sm = d.lemma(p.succ_mul, &[j, n]);
                let h2 = d.symm(s2, s1, h_sm);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_one : ∀ a, mul a 1 = a
    // mul a (succ zero) ≡ add (mul a zero) a ≡ add zero a, so `zero_add a`
    // already has this type up to definitional equality.
    d.theorem(p.mul_one, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let lhs = d.mul(a, one);
        let stmt = d.eq(lhs, a);
        let proof = d.lemma(p.zero_add, &[a]);
        (stmt, proof)
    })?;

    // one_mul : ∀ a, mul 1 a = a
    d.theorem(p.one_mul, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let z = d.zero();
        let start = d.mul(one, a);
        let za = d.mul(z, a);
        let s1 = d.add(za, a);
        let h1 = d.lemma(p.succ_mul, &[z, a]);
        let s2 = d.add(z, a);
        let h_zm = d.lemma(p.zero_mul, &[a]);
        let h2 = d.congr(za, z, h_zm, &|d, t| d.add(t, a));
        let h3 = d.lemma(p.zero_add, &[a]);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (a, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    })?;

    // left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)  (ind. on c)
    d.theorem(p.left_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let bx = d.add(b, x);
            let lhs = d.mul(a, bx);
            let ab = d.mul(a, b);
            let ax = d.mul(a, x);
            let rhs = d.add(ab, ax);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.mul(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                // goal ≡ add (mul a (add b j)) a = add (mul a b) (add (mul a j) a)
                let bj = d.add(b, j);
                let a_bj = d.mul(a, bj);
                let start = d.add(a_bj, a);
                let ab = d.mul(a, b);
                let aj = d.mul(a, j);
                let ab_aj = d.add(ab, aj);
                let s1 = d.add(ab_aj, a);
                let h1 = d.congr(a_bj, ab_aj, ih, &|d, t| d.add(t, a));
                let aj_a = d.add(aj, a);
                let s2 = d.add(ab, aj_a);
                let h2 = d.lemma(p.add_assoc, &[ab, aj, a]);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;

    // mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)   (induction on c)
    d.theorem(p.mul_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.mul(a, b);
            let lhs = d.mul(ab, x);
            let bx = d.mul(b, x);
            let rhs = d.mul(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ add (mul (mul a b) j) (mul a b) = mul a (add (mul b j) b)
                let ab = d.mul(a, b);
                let abj = d.mul(ab, j);
                let start = d.add(abj, ab);
                let bj = d.mul(b, j);
                let a_bj = d.mul(a, bj);
                let s1 = d.add(a_bj, ab);
                let h1 = d.congr(abj, a_bj, ih, &|d, t| d.add(t, ab));
                let bj_b = d.add(bj, b);
                let s2 = d.mul(a, bj_b);
                let h_ld = d.lemma(p.left_distrib, &[a, bj, b]);
                let h2 = d.symm(s2, s1, h_ld);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// The first reusable finite-sum algebra needed by the Rado sharpness proof.
/// This is a checked theorem over [`NatPrelude::sum_range`], not a specialized
/// test-only recurrence.
fn declare_finite_sum_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mul_sum_range_pow, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let power_fn = |d: &mut NatDev<'_>, shifted: bool| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let exponent = if shifted { d.succ(i) } else { i };
            let body = d.pow(a, exponent);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let unshifted = power_fn(d, false);
            let shifted = power_fn(d, true);
            let sum = d.sum_range(unshifted, x);
            let lhs = d.mul(a, sum);
            let rhs = d.sum_range(shifted, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let unshifted = power_fn(d, false);
                let shifted = power_fn(d, true);
                let sum = d.sum_range(unshifted, j);
                let shifted_sum = d.sum_range(shifted, j);
                let power = d.pow(a, j);
                let start = {
                    let extended = d.add(sum, power);
                    d.mul(a, extended)
                };
                let a_sum = d.mul(a, sum);
                let a_power = d.mul(a, power);
                let distributed = d.add(a_sum, a_power);
                let h1 = d.lemma(p.left_distrib, &[a, sum, power]);
                let with_ih = d.add(shifted_sum, a_power);
                let h2 = d.congr(a_sum, shifted_sum, ih, &|d, t| d.add(t, a_power));
                let power_a = d.mul(power, a);
                let commuted = d.add(shifted_sum, power_a);
                let h_comm = d.lemma(p.mul_comm, &[a, power]);
                let h3 = d.congr(a_power, power_a, h_comm, &|d, t| d.add(shifted_sum, t));
                let successor_power = {
                    let sj = d.succ(j);
                    d.pow(a, sj)
                };
                let end = d.add(shifted_sum, successor_power);
                let h_pow = d.lemma(p.pow_succ, &[a, j]);
                let h_pow_rev = d.symm(successor_power, power_a, h_pow);
                let h4 = d.congr(power_a, successor_power, h_pow_rev, &|d, t| {
                    d.add(shifted_sum, t)
                });
                let (_, proof) = d.chain(
                    start,
                    &[(distributed, h1), (with_ih, h2), (commuted, h3), (end, h4)],
                );
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.le`, reducible strict order, and the checked order theorems.
fn declare_order(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    // Le : Nat → Nat → Prop, with the first argument a PARAMETER and the second
    // an INDEX (Lean's own `Nat.le` has exactly this shape).
    let le_ty = {
        let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        d.kernel().pi(anon, nat, inner, BinderInfo::Default)
    };
    // Le.refl : Π (n : Nat), Le n n
    let refl_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.le(n, n);
        d.pi_fv(n_fv, nat, body)
    };
    // Le.step : Π (n m : Nat), Le n m → Le n (succ m)
    let step_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let hyp = d.le(n, m);
        let sm = d.succ(m);
        let concl = d.le(n, sm);
        let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
        let over_m = d.pi_fv(m_fv, nat, arrow);
        d.pi_fv(n_fv, nat, over_m)
    };
    d.kernel().add_inductive(
        p.le,
        &[],
        1,
        le_ty,
        &[(p.le_refl, refl_ty), (p.le_step, step_ty)],
    )?;

    // lt n m := Le (succ n) m
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let body = d.le(sn, m);
        let value = {
            let inner = d.lam_fv(m_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lt,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // zero_le : ∀ n, Le zero n   (induction on n, using only the constructors)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            d.le(z, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.const_app(p.le_refl, &[z])
            },
            &|d, j, ih| {
                let z = d.zero();
                d.const_app(p.le_step, &[z, j, ih])
            },
            n,
        );
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.zero_le, ty, value)?;
    }

    // le_succ_succ : ∀ n m, Le n m → Le (succ n) (succ m)
    // — induction on the DERIVATION, i.e. elimination with the generated Le.rec.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(n, m);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let concl = d.le(sn, sm);

        // motive := fun (x : Nat) (_ : Le n x) => Le (succ n) (succ x)
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let body = d.le(sn, sx);
            let dom = d.le(n, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // minor for Le.refl : motive n (Le.refl n) = Le (succ n) (succ n)
        let minor_refl = d.const_app(p.le_refl, &[sn]);
        // minor for Le.step : Π (x : Nat) (hx : Le n x), motive x hx → motive (succ x) …
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(n, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let sx = d.succ(x);
            let ih_ty = d.le(sn, sx);
            let body = d.const_app(p.le_step, &[sn, sx, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[n, motive, minor_refl, minor_step, m, h]);

        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let l_h = d.lam_fv(h_fv, hyp, applied);
            let l_m = d.lam_fv(m_fv, nat, l_h);
            d.lam_fv(n_fv, nat, l_m)
        };
        d.declare_theorem(p.le_succ_succ, ty, value)?;
    }

    // le_trans : ∀ a b c, Le a b → Le b c → Le a c
    // — elimination on the SECOND derivation, with `b` as the recursor's parameter.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.le(a, b);
        let h2_ty = d.le(b, c);
        let concl = d.le(a, c);

        // motive := fun (x : Nat) (_ : Le b x) => Le a x
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = d.le(a, x);
            let dom = d.le(b, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // refl case: motive b (Le.refl b) = Le a b, which is exactly `h1`.
        let minor_refl = h1;
        // step case: fun x hx ih => Le.step a x ih
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(b, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let ih_ty = d.le(a, x);
            let body = d.const_app(p.le_step, &[a, x, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[b, motive, minor_refl, minor_step, c, h2]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, concl, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(c_fv, nat, t);
            let t = d.pi_fv(b_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, applied);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(c_fv, nat, v);
            let v = d.lam_fv(b_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.le_trans, ty, value)?;
    }

    // le_of_succ_le_succ : ∀ n m, Le (succ n) (succ m) → Le n m
    //
    // Eliminate the derivation with the predecessor-style family
    //   P 0        = False
    //   P (succ x) = Le n x.
    // The step case can ignore its induction hypothesis: from
    // `Le (succ n) x`, transitivity with `Le n (succ n)` gives `Le n x`.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(sn, sm);
        let concl = d.le(n, m);

        let predecessor_family = |d: &mut NatDev<'_>, x: ExprId| {
            let type_motive = d.kernel().lam(anon, nat, prop, BinderInfo::Default);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let step = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let ignored_fv = d.fresh_fvar();
                let body = d.le(n, j);
                let inner = d.lam_fv(ignored_fv, prop, body);
                d.lam_fv(j_fv, nat, inner)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.rec, vec![one]);
            d.apply(rec, &[type_motive, false_ty, step, x])
        };

        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(sn, x);
            let body = predecessor_family(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[n]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(sn, x);
            let hx = d.kernel().fvar(hx_fv);
            let ih_fv = d.fresh_fvar();
            let ih_ty = predecessor_family(d, x);
            let n_refl = d.const_app(p.le_refl, &[n]);
            let n_le_sn = d.const_app(p.le_step, &[n, n, n_refl]);
            let body = d.lemma(p.le_trans, &[n, sn, x, n_le_sn, hx]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let proof = d.const_app(p.le_rec, &[sn, motive, minor_refl, minor_step, sm, h]);
        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp, proof);
            let with_m = d.lam_fv(m_fv, nat, with_h);
            d.lam_fv(n_fv, nat, with_m)
        };
        d.declare_theorem(p.le_of_succ_le_succ, ty, value)?;
    }

    // le_add_right : ∀ n k, Le n (add n k)   (induction on k; both cases are
    // definitional, since `add n zero ≡ n` and `add n (succ j) ≡ succ (add n j)`)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let nx = d.add(n, x);
            d.le(n, nx)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| d.const_app(p.le_refl, &[n]),
            &|d, j, ih| {
                let nj = d.add(n, j);
                d.const_app(p.le_step, &[n, nj, ih])
            },
            k,
        );
        let ty = {
            let t = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(n_fv, nat, v)
        };
        d.declare_theorem(p.le_add_right, ty, value)?;
    }
    Ok(())
}

/// `Nat.dvd`, `dvd_mul`, and `dvd_add`, all constructed from the logic
/// prelude's checked `Exists` eliminator and the proved Nat multiplication
/// laws. No proposition is admitted as an axiom.
fn declare_divisibility(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // dvd a n := Exists Nat (fun q => Eq Nat n (a * q))
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pred = d.dvd_predicate(a, n);
        let exists = d.kernel().const_(p.logic.exists_, vec![one]);
        let body = d.apply(exists, &[nat, pred]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(a_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.dvd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // dvd_mul : ∀ a q, dvd a (a * q)
    d.theorem(p.dvd_mul, 2, &|d, v| {
        let (a, q) = (v[0], v[1]);
        let aq = d.mul(a, q);
        let stmt = d.dvd(a, aq);
        let pred = d.dvd_predicate(a, aq);
        let witness_proof = d.refl(aq);
        let one = d.level_one();
        let intro_name = d.prelude().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        let nat = d.nat_ty();
        let proof = d.apply(intro, &[nat, pred, q, witness_proof]);
        (stmt, proof)
    })?;

    // dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.dvd(a, m);
        let h2_ty = d.dvd(a, n);
        let mn = d.add(m, n);
        let goal = d.dvd(a, mn);
        let p1 = d.dvd_predicate(a, m);
        let p2 = d.dvd_predicate(a, n);
        let one = d.level_one();

        let motive_for = |d: &mut NatDev<'_>, pred: ExprId| {
            let exists_name = d.prelude().logic.exists_;
            let exists = d.kernel().const_(exists_name, vec![one]);
            let nat = d.nat_ty();
            let dom = d.apply(exists, &[nat, pred]);
            let anon = d.anon_name();
            d.kernel().lam(anon, dom, goal, BinderInfo::Default)
        };

        let minor1 = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor2 = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.eq(n, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                // m+n = a*q1+n = a*q1+a*q2 = a*(q1+q2)
                let s1 = d.add(aq1, n);
                let c1 = d.congr(m, aq1, e1, &|d, t| d.add(t, n));
                let s2 = d.add(aq1, aq2);
                let c2 = d.congr(n, aq2, e2, &|d, t| d.add(aq1, t));
                let q12 = d.add(q1, q2);
                let aq12 = d.mul(a, q12);
                let h_distrib = d.lemma(p.left_distrib, &[a, q1, q2]);
                let c3 = d.symm(aq12, s2, h_distrib);
                let (_, witness_proof) = d.chain(mn, &[(s1, c1), (s2, c2), (aq12, c3)]);
                let pred = d.dvd_predicate(a, mn);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let nat = d.nat_ty();
                let body = d.apply(intro, &[nat, pred, q12, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, nat, with_e2)
            };
            let motive2 = motive_for(d, p2);
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let nat = d.nat_ty();
            let inner = d.apply(rec, &[nat, p2, motive2, minor2, h2]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, with_e1)
        };
        let motive1 = motive_for(d, p1);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let proof = d.apply(rec, &[nat, p1, motive1, minor1, h1]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, goal, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(n_fv, nat, t);
            let t = d.pi_fv(m_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, proof);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(n_fv, nat, v);
            let v = d.lam_fv(m_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.dvd_add, ty, value)?;
    }
    Ok(())
}

/// The non-kernel state a [`NatOps`] development carries: the interned prelude
/// names, the cached `Nat` type expression, the anonymous name root, and a
/// monotone free-variable counter.
///
/// The counter starts well above anything the type-checker's own
/// [`LocalContext`](crate::LocalContext) mints while descending the *closed*
/// terms a declaration hands it, so a development's free variables can never
/// collide with the kernel's.
#[derive(Debug)]
pub struct NatState {
    prelude: NatPrelude,
    anon: NameId,
    nat_ty: ExprId,
    next_fvar: u64,
}

/// The first free-variable id a [`NatState`] mints.
const FVAR_BASE: u64 = 1_000;

impl NatState {
    /// The state for a development over `prelude` in `kernel`.
    pub fn new(kernel: &mut Kernel, prelude: NatPrelude) -> Self {
        let anon = kernel.anon();
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        Self {
            prelude,
            anon,
            nat_ty,
            next_fvar: FVAR_BASE,
        }
    }

    /// The interned names this development builds on.
    pub fn prelude(&self) -> NatPrelude {
        self.prelude
    }

    /// The expression `Nat` (the carrier type).
    pub fn nat_ty(&self) -> ExprId {
        self.nat_ty
    }

    /// The anonymous name root.
    pub fn anon(&self) -> NameId {
        self.anon
    }

    /// Mint a fresh free-variable id.
    pub fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }
}

/// The reusable proof-construction layer over [`NatPrelude`].
///
/// Implement the two required methods on your own development struct — then all
/// of `Nat` arithmetic, the `Eq` combinators, induction, and the declaration
/// plumbing become methods on it, and your own operators can stay ordinary
/// inherent methods (so every closure below keeps taking `&mut YourDev`). For a
/// development that needs nothing of its own, [`NatDev`] is a ready-made
/// implementor over a borrowed kernel.
///
/// Every method here only *builds* terms except the three declaration helpers
/// ([`define_binary`](Self::define_binary), [`declare_theorem`](Self::declare_theorem),
/// [`try_theorem`](Self::try_theorem)/[`theorem`](Self::theorem)), which push
/// through the kernel's trusted gate and therefore re-type-check what they were
/// given.
pub trait NatOps {
    /// The kernel this development declares into.
    fn kernel(&mut self) -> &mut Kernel;

    /// The interned names and free-variable counter of this development.
    fn nat_state(&mut self) -> &mut NatState;

    // --- interned handles ---------------------------------------------------

    /// The prelude names (a `Copy` snapshot).
    fn prelude(&mut self) -> NatPrelude {
        self.nat_state().prelude()
    }

    /// The expression `Nat`.
    fn nat_ty(&mut self) -> ExprId {
        self.nat_state().nat_ty()
    }

    /// The anonymous name root (the binder name used for every generated
    /// binder — binder names are cosmetic, de Bruijn indices carry the meaning).
    fn anon_name(&mut self) -> NameId {
        self.nat_state().anon()
    }

    /// Mint a fresh free-variable id.
    fn fresh_fvar(&mut self) -> u64 {
        self.nat_state().fresh_fvar()
    }

    /// The universe level `1` (the level `Nat : Sort 1` lives at, and the `Eq`
    /// universe argument for equations between naturals).
    fn level_one(&mut self) -> LevelId {
        let z = self.kernel().level_zero();
        self.kernel().level_succ(z)
    }

    // --- term builders ------------------------------------------------------

    /// Left-associated application `head a1 a2 …`.
    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.kernel().app(e, a);
        }
        e
    }

    /// A universe-monomorphic constant applied to `args`.
    fn const_app(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel().const_(name, vec![]);
        self.apply(c, args)
    }

    /// Apply a previously declared lemma to arguments (an alias of
    /// [`const_app`](Self::const_app) that reads as the proof step it is).
    fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        self.const_app(name, args)
    }

    /// `Nat.zero`.
    fn zero(&mut self) -> ExprId {
        let n = self.prelude().zero;
        self.kernel().const_(n, vec![])
    }

    /// `Nat.succ x`.
    fn succ(&mut self, x: ExprId) -> ExprId {
        let n = self.prelude().succ;
        let s = self.kernel().const_(n, vec![]);
        self.kernel().app(s, x)
    }

    /// The unary numeral `succ^n zero`.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.zero();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }

    /// `Nat.add x y`.
    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().add;
        self.const_app(f, &[x, y])
    }

    /// `Nat.mul x y`.
    fn mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().mul;
        self.const_app(f, &[x, y])
    }

    /// `Nat.pow x y`.
    fn pow(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().pow;
        self.const_app(f, &[x, y])
    }

    /// `Nat.sumRange f n`.
    fn sum_range(&mut self, f: ExprId, n: ExprId) -> ExprId {
        let name = self.prelude().sum_range;
        self.const_app(name, &[f, n])
    }

    /// `Nat.le x y` (the `Prop` `x ≤ y`).
    fn le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().le;
        self.const_app(f, &[x, y])
    }

    /// `Nat.lt x y` (definitionally `Nat.le (Nat.succ x) y`).
    fn lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let f = self.prelude().lt;
        self.const_app(f, &[x, y])
    }

    /// `Nat.dvd a n` (the proposition `a ∣ n`).
    fn dvd(&mut self, a: ExprId, n: ExprId) -> ExprId {
        let f = self.prelude().dvd;
        self.const_app(f, &[a, n])
    }

    /// `fun q : Nat => Eq Nat n (a * q)`, the witness predicate defining
    /// [`NatPrelude::dvd`].
    fn dvd_predicate(&mut self, a: ExprId, n: ExprId) -> ExprId {
        let q_fv = self.fresh_fvar();
        let q = self.kernel().fvar(q_fv);
        let aq = self.mul(a, q);
        let body = self.eq(n, aq);
        let nat = self.nat_ty();
        self.lam_fv(q_fv, nat, body)
    }

    // --- binders ------------------------------------------------------------

    /// `fun (_ : ty) => body`, abstracting the free variable `fv` in `body`.
    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel().abstract_fvars(body, &[fv]);
        let anon = self.anon_name();
        self.kernel().lam(anon, ty, b, BinderInfo::Default)
    }

    /// `∀ (_ : ty), body`, abstracting the free variable `fv` in `body`.
    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel().abstract_fvars(body, &[fv]);
        let anon = self.anon_name();
        self.kernel().pi(anon, ty, b, BinderInfo::Default)
    }

    /// The non-dependent arrow `dom → cod`.
    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        let anon = self.anon_name();
        self.kernel().pi(anon, dom, cod, BinderInfo::Default)
    }

    // --- Eq -----------------------------------------------------------------

    /// `Eq.{1} Nat x y`.
    fn eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq;
        let eq = self.kernel().const_(name, vec![one]);
        let nat = self.nat_ty();
        self.apply(eq, &[nat, x, y])
    }

    /// `Eq.refl.{1} Nat a : Eq Nat a a`.
    fn refl(&mut self, a: ExprId) -> ExprId {
        let one = self.level_one();
        let name = self.prelude().logic.eq_refl;
        let refl = self.kernel().const_(name, vec![one]);
        let nat = self.nat_ty();
        self.apply(refl, &[nat, a])
    }

    /// `Eq.rec.{0,1} Nat p motive refl_case q h : motive q h`.
    fn transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel().level_zero();
        let one = self.level_one();
        let name = self.prelude().logic.eq_rec;
        let rec = self.kernel().const_(name, vec![z, one]);
        let nat = self.nat_ty();
        self.apply(rec, &[nat, p, motive, refl_case, q, h])
    }

    /// Build the `Eq.rec` motive `fun (x : Nat) (_ : Eq Nat a x) => body(x)`.
    fn eq_motive(&mut self, a: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId
    where
        Self: Sized,
    {
        let x_fv = self.fresh_fvar();
        let x = self.kernel().fvar(x_fv);
        let concl = body(self, x);
        let hyp = self.eq(a, x);
        let anon = self.anon_name();
        let inner = self.kernel().lam(anon, hyp, concl, BinderInfo::Default);
        let nat = self.nat_ty();
        self.lam_fv(x_fv, nat, inner)
    }

    /// `h : Eq Nat a b  ⊢  Eq Nat b a`.
    fn symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.eq_motive(a, &|d, x| d.eq(x, a));
        let refl_case = self.refl(a);
        self.transport(a, motive, refl_case, b, h)
    }

    /// `h1 : Eq Nat a b`, `h2 : Eq Nat b c  ⊢  Eq Nat a c`.
    fn trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId
    where
        Self: Sized,
    {
        let motive = self.eq_motive(b, &|d, x| d.eq(a, x));
        self.transport(b, motive, h1, c, h2)
    }

    /// Chain `a = x1 = x2 = … = z` from `(rhs, proof)` steps, returning the last
    /// right-hand side and a proof of `Eq Nat start last`.
    fn chain(&mut self, start: ExprId, steps: &[(ExprId, ExprId)]) -> (ExprId, ExprId)
    where
        Self: Sized,
    {
        let mut current = start;
        let mut proof = self.refl(start);
        for &(next, step) in steps {
            proof = self.trans(start, current, next, proof, step);
            current = next;
        }
        (current, proof)
    }

    /// Congruence in an arbitrary one-hole context: `h : Eq Nat a b` gives
    /// `Eq Nat (f a) (f b)`.
    fn congr(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId
    where
        Self: Sized,
    {
        let fa = f(self, a);
        let motive = self.eq_motive(a, &|d, x| {
            let fx = f(d, x);
            d.eq(fa, fx)
        });
        let refl_case = self.refl(fa);
        self.transport(a, motive, refl_case, b, h)
    }

    // --- induction ----------------------------------------------------------

    /// `Nat.rec.{0} (fun x => p x) base (fun j ih => step j ih) target`, a proof
    /// of `p target` for a `Prop`-valued motive.
    fn induct(
        &mut self,
        p: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let motive = {
            let x_fv = self.fresh_fvar();
            let x = self.kernel().fvar(x_fv);
            let body = p(self, x);
            self.lam_fv(x_fv, nat, body)
        };
        let base_term = base(self);
        let step_term = {
            let j_fv = self.fresh_fvar();
            let j = self.kernel().fvar(j_fv);
            let ih_fv = self.fresh_fvar();
            let ih = self.kernel().fvar(ih_fv);
            let hyp_ty = p(self, j);
            let body = step(self, j, ih);
            let inner = self.lam_fv(ih_fv, hyp_ty, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let z = self.kernel().level_zero();
        let name = self.prelude().rec;
        let rec = self.kernel().const_(name, vec![z]);
        self.apply(rec, &[motive, base_term, step_term, target])
    }

    // --- declarations -------------------------------------------------------

    /// `def name : Nat → Nat → Nat := fun x y => Nat.rec (fun _ => Nat) (base x) (fun j ih => step x j ih) y`
    ///
    /// i.e. structural recursion on the **second** argument, so
    /// `name x zero ≡ base x` and `name x (succ j) ≡ step x j (name x j)` hold
    /// definitionally (β/δ/ι) and no equation lemmas are needed. `height` is the
    /// [`ReducibilityHint::Regular`] delta height: give a definition a strictly
    /// greater height than every definition it calls.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection if the generated definition does not
    /// type-check or the name is already taken.
    fn define_binary(
        &mut self,
        name: NameId,
        height: u16,
        base: &dyn Fn(&mut Self, ExprId) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId, ExprId) -> ExprId,
    ) -> Result<NameId, KernelError>
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let x_fv = self.fresh_fvar();
        let x = self.kernel().fvar(x_fv);
        let motive = self.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let minor_zero = base(self, x);
        let minor_succ = {
            let j_fv = self.fresh_fvar();
            let j = self.kernel().fvar(j_fv);
            let ih_fv = self.fresh_fvar();
            let ih = self.kernel().fvar(ih_fv);
            let body = step(self, x, j, ih);
            let inner = self.lam_fv(ih_fv, nat, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let y_fv = self.fresh_fvar();
        let y = self.kernel().fvar(y_fv);
        let one = self.level_one();
        let rec_name = self.prelude().rec;
        let rec = self.kernel().const_(rec_name, vec![one]);
        let body = self.apply(rec, &[motive, minor_zero, minor_succ, y]);
        let value = {
            let inner = self.lam_fv(y_fv, nat, body);
            self.lam_fv(x_fv, nat, inner)
        };
        let ty = {
            let inner = self.arrow(nat, nat);
            self.arrow(nat, inner)
        };
        self.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(height),
        })?;
        Ok(name)
    }

    /// Admit `theorem name : ty := value` through the kernel's trusted gate.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection — i.e. the kernel **refused** the proof.
    fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    }

    /// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Nat), stmt := fun … => proof`,
    /// where `build` receives the `arity` universally quantified variables and
    /// returns `(statement, proof)`.
    ///
    /// # Errors
    ///
    /// Returns the kernel's rejection — the kernel re-checks `proof` against
    /// `stmt` inside `add_declaration`, so an `Err` here means the proof was
    /// **rejected**.
    fn try_theorem(
        &mut self,
        name: NameId,
        arity: usize,
        build: &dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<ExprId, KernelError>
    where
        Self: Sized,
    {
        let nat = self.nat_ty();
        let fvs: Vec<u64> = (0..arity).map(|_| self.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| self.kernel().fvar(f)).collect();
        let (stmt, proof) = build(self, &vars);
        let mut ty = stmt;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = self.pi_fv(fv, nat, ty);
            value = self.lam_fv(fv, nat, value);
        }
        self.declare_theorem(name, ty, value)?;
        Ok(ty)
    }

    /// [`try_theorem`](Self::try_theorem), returning the declared statement or
    /// the trusted gate's typed rejection.
    ///
    /// # Errors
    ///
    /// Returns the trusted kernel gate's typed rejection.
    fn theorem(
        &mut self,
        name: NameId,
        arity: usize,
        build: &dyn Fn(&mut Self, &[ExprId]) -> (ExprId, ExprId),
    ) -> Result<ExprId, KernelError>
    where
        Self: Sized,
    {
        self.try_theorem(name, arity, build)
    }

    /// A readable rendering of a kernel rejection (the payloads are [`ExprId`]s,
    /// which say nothing on their own).
    fn explain(&mut self, e: &KernelError) -> String {
        match e {
            KernelError::DeclarationValueMismatch { declared, inferred } => {
                let declared = self.kernel().render_lean(*declared);
                let inferred = self.kernel().render_lean(*inferred);
                format!(
                    "DeclarationValueMismatch\n    declared : {declared}\n    inferred : {inferred}"
                )
            }
            KernelError::TypeMismatch { expected, got } => {
                let expected = self.kernel().render_lean(*expected);
                let got = self.kernel().render_lean(*got);
                format!("TypeMismatch\n    expected : {expected}\n    got      : {got}")
            }
            other => format!("{other:?}"),
        }
    }
}

/// A ready-made [`NatOps`] development over a borrowed kernel, for callers with
/// no development struct of their own. [`build_nat_prelude`] uses it to prove
/// the prelude's own theorems.
pub struct NatDev<'k> {
    kernel: &'k mut Kernel,
    state: NatState,
}

impl<'k> NatDev<'k> {
    /// A development over `kernel` using the already-built `prelude`.
    pub fn new(kernel: &'k mut Kernel, prelude: NatPrelude) -> Self {
        let state = NatState::new(kernel, prelude);
        Self { kernel, state }
    }
}

impl NatOps for NatDev<'_> {
    fn kernel(&mut self) -> &mut Kernel {
        self.kernel
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.state
    }
}

#[cfg(test)]
mod nat_prelude_tests;
