//! The **arithmetic prelude** (ADR-0036, the P3.7 / LRA-reconstruction
//! foundation): an axiomatized **linear ordered field**, declared into a
//! [`Kernel`]'s environment through the trusted
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate.
//!
//! This is the trusted base for reconstructing **LRA `la_generic` (Farkas)**
//! proofs into kernel-checked Lean terms. A Farkas refutation is, at bottom, a
//! chain of order/monotonicity steps over an ordered field deriving `False`;
//! the axioms here are exactly the (sound, mathlib-faithful) rules such a chain
//! invokes. The kernel type-checks every axiom's **type** at admission (a
//! malformed axiom set is rejected by [`Kernel::add_declaration`]), and the
//! accompanying tests then build real refutation **proof terms** on top of the
//! axioms and `infer`-check them — so the kernel genuinely verifies the
//! reasoning.
//!
//! ## What is declared
//!
//! The carrier lives in `Type = Sort 1`; the relations land in `Prop = Sort 0`:
//!
//! - **Carrier** `R : Type` (an opaque [`Declaration::Axiom`] of type
//!   `Sort 1`).
//! - **Operations** (each an `axiom`): `add : R → R → R`, `mul : R → R → R`,
//!   `neg : R → R`, `zero : R`, `one : R`.
//! - **Relations** (each an `axiom`): `le : R → R → Prop`, `lt : R → R → Prop`.
//! - **Order axioms**: `le_refl`, `le_trans`, `lt_irrefl` (via `Not`),
//!   `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`.
//! - **Additive axioms**: `add_le_add`, `add_comm`, `add_assoc`, `add_zero`
//!   (via `Eq` at the `R` level), `add_neg` (via `Eq`).
//! - **Scaling axiom**: `mul_le_mul_of_nonneg_left`.
//! - **Constant axiom**: `zero_lt_one : lt zero one`.
//!
//! Each axiom's exact type is documented on the corresponding [`ArithPrelude`]
//! field. The propositional connectives (`Not`, `And`, `Eq`, `False`) come from
//! [`build_logic_prelude`](crate::build_logic_prelude); `Eq` is used at universe
//! `u := 1` because the carrier is `Sort 1`.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, LogicPrelude, build_logic_prelude};

/// The interned names produced by [`build_arith_prelude`]: the carrier, the
/// field/order operations, and every axiom of the linear ordered field, plus the
/// embedded [`LogicPrelude`] (so callers can build `False`/`Not`/`Eq` terms).
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so tests and callers can build `Const` terms
/// (`k.const_(arith.le, vec![])`, `k.const_(arith.le_trans, vec![])`, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArithPrelude {
    /// The embedded logical prelude (`False`, `Not`, `Eq`, …).
    pub logic: LogicPrelude,

    // --- carrier + operations ------------------------------------------------
    /// `R : Type` (i.e. `R : Sort 1`) — the ordered field's carrier.
    pub r: NameId,
    /// `add : R → R → R`.
    pub add: NameId,
    /// `mul : R → R → R`.
    pub mul: NameId,
    /// `neg : R → R`.
    pub neg: NameId,
    /// `zero : R`.
    pub zero: NameId,
    /// `one : R`.
    pub one: NameId,
    /// `le : R → R → Prop`.
    pub le: NameId,
    /// `lt : R → R → Prop`.
    pub lt: NameId,

    // --- order axioms --------------------------------------------------------
    /// `le_refl : ∀ (a : R), le a a`.
    pub le_refl: NameId,
    /// `le_trans : ∀ (a b c : R), le a b → le b c → le a c`.
    pub le_trans: NameId,
    /// `lt_irrefl : ∀ (a : R), Not (lt a a)`.
    pub lt_irrefl: NameId,
    /// `lt_trans : ∀ (a b c : R), lt a b → lt b c → lt a c`.
    pub lt_trans: NameId,
    /// `lt_of_lt_of_le : ∀ (a b c : R), lt a b → le b c → lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ (a b c : R), le a b → lt b c → lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `le_of_lt : ∀ (a b : R), lt a b → le a b`.
    pub le_of_lt: NameId,

    // --- additive axioms -----------------------------------------------------
    /// `add_le_add : ∀ (a b c d : R), le a b → le c d → le (add a c) (add b d)`.
    pub add_le_add: NameId,
    /// `add_comm : ∀ (a b : R), Eq R (add a b) (add b a)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : R), Eq R (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_zero : ∀ (a : R), Eq R (add a zero) a`.
    pub add_zero: NameId,
    /// `add_neg : ∀ (a : R), Eq R (add a (neg a)) zero`.
    pub add_neg: NameId,

    // --- scaling axiom -------------------------------------------------------
    /// `mul_le_mul_of_nonneg_left :
    /// ∀ (c a b : R), le zero c → le a b → le (mul c a) (mul c b)`.
    pub mul_le_mul_of_nonneg_left: NameId,

    // --- constant axiom ------------------------------------------------------
    /// `zero_lt_one : lt zero one`.
    pub zero_lt_one: NameId,

    // --- mixed strict/non-strict additive axiom (Task #16) -------------------
    /// `add_lt_add_of_le_of_lt :
    /// ∀ (a b c d : R), le a b → lt c d → lt (add a c) (add b d)`.
    ///
    /// Summing a non-strict inequality with a strict one yields a strict result.
    /// This is the single combinator the mixed-Farkas reconstruction needs; the
    /// pure-strict variant `lt a b → lt c d → lt (add a c)(add b d)` is *derived*
    /// from it via [`Self::le_of_lt`], so no further axiom is added.
    pub add_lt_add_of_le_of_lt: NameId,
}

/// Declare the axiomatized **linear ordered field** into `kernel`'s environment,
/// returning the [`ArithPrelude`] of interned names. The logical prelude is built
/// first (if not already present, `build_logic_prelude` is idempotent only on a
/// fresh kernel, so this expects a kernel without those names — see Panics).
///
/// Every axiom is admitted through the **trusted**
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate, which
/// type-checks the axiom's type (it must itself be a `Sort`); a malformed axiom
/// type would be rejected (and panic here, since a well-formed prelude is a
/// precondition). A green build of this function therefore *is* a proof that the
/// axiom set is well-formed.
///
/// # Panics
///
/// Panics if any declaration fails to type-check or if a name collides with an
/// already-present declaration — both indicate the prelude was built into a
/// non-fresh kernel or a kernel regression, not a recoverable caller error.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn build_arith_prelude(kernel: &mut Kernel) -> ArithPrelude {
    let logic = build_logic_prelude(kernel);
    let anon = kernel.anon();

    // --- carrier R : Type (= Sort 1) -----------------------------------------
    let r = kernel.name_str(anon, "R");
    {
        let one_lvl = {
            let z = kernel.level_zero();
            kernel.level_succ(z)
        };
        let type1 = kernel.sort(one_lvl);
        kernel
            .add_declaration(Declaration::Axiom {
                name: r,
                uparams: vec![],
                ty: type1,
            })
            .expect("R : Type should admit");
    }

    // `R` as a type expression, and `Prop`.
    let r_ty = kernel.const_(r, vec![]);
    // Helper: the arrow `dom → cod` (a non-dependent Pi).
    let arrow = |kernel: &mut Kernel, dom: ExprId, cod: ExprId| -> ExprId {
        let anon = kernel.anon();
        kernel.pi(anon, dom, cod, BinderInfo::Default)
    };

    // --- operations ----------------------------------------------------------
    // add, mul : R → R → R.
    let bin_op_ty = {
        let inner = arrow(kernel, r_ty, r_ty);
        arrow(kernel, r_ty, inner)
    };
    let add = declare_axiom(kernel, anon, "add", bin_op_ty);
    let mul = declare_axiom(kernel, anon, "mul", bin_op_ty);
    // neg : R → R.
    let neg = {
        let ty = arrow(kernel, r_ty, r_ty);
        declare_axiom(kernel, anon, "neg", ty)
    };
    // zero, one : R.
    let zero = declare_axiom(kernel, anon, "zero", r_ty);
    let one = declare_axiom(kernel, anon, "one", r_ty);
    // le, lt : R → R → Prop.
    let rel_ty = {
        let prop = kernel.sort_zero();
        let inner = arrow(kernel, r_ty, prop);
        arrow(kernel, r_ty, inner)
    };
    let le = declare_axiom(kernel, anon, "le", rel_ty);
    let lt = declare_axiom(kernel, anon, "lt", rel_ty);

    // ----- small term builders over the now-declared symbols -----------------
    // We build axiom *types* as Pi-telescopes over `R`. Inside a telescope of
    // `n` binders, the binder introduced `k`-th from the outside is at de Bruijn
    // index `n - 1 - k` when referenced at the *innermost* point. We always
    // reference variables at the innermost (result) position of each axiom, so
    // the helpers below take explicit `BVar` ids the caller computes.

    // `le x y` and `lt x y` (relation applications) as Prop terms.
    let app2 = |kernel: &mut Kernel, f: NameId, x: ExprId, y: ExprId| -> ExprId {
        let fc = kernel.const_(f, vec![]);
        let e = kernel.app(fc, x);
        kernel.app(e, y)
    };

    // The Pi `∀ (a : R), body` etc. are built directly with `kernel.pi`.

    // --- le_refl : ∀ (a : R), le a a -----------------------------------------
    let le_refl = {
        let a0 = kernel.bvar(0);
        let a0b = kernel.bvar(0);
        let body = app2(kernel, le, a0, a0b);
        let ty = kernel.pi(anon, r_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "le_refl", ty)
    };

    // --- le_trans : ∀ (a b c : R), le a b → le b c → le a c ------------------
    // Telescope a,b,c then two hyp arrows. At the result (under a,b,c,h1,h2):
    //   a = BVar 4, b = BVar 3, c = BVar 2. (Indices computed per binder depth.)
    let le_trans = {
        // Build innermost-out. Names: a,b,c are params; h1: le a b; h2: le b c;
        // result: le a c.
        // Depths from the result position (under a,b,c,h1,h2): a=4,b=3,c=2.
        let a4 = kernel.bvar(4);
        let c2 = kernel.bvar(2);
        let result = app2(kernel, le, a4, c2);
        // h2 : le b c  — under a,b,c,h1 → b=2, c=1.
        let b2 = kernel.bvar(2);
        let c1 = kernel.bvar(1);
        let h2_dom = app2(kernel, le, b2, c1);
        let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
        // h1 : le a b — under a,b,c → a=2, b=1.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let h1_dom = app2(kernel, le, a2, b1);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        // ∀ a b c.
        let ty = telescope_r(kernel, anon, r_ty, 3, after_h1);
        declare_axiom(kernel, anon, "le_trans", ty)
    };

    // --- lt_irrefl : ∀ (a : R), Not (lt a a) ---------------------------------
    let lt_irrefl = {
        let a0 = kernel.bvar(0);
        let a0b = kernel.bvar(0);
        let lt_aa = app2(kernel, lt, a0, a0b);
        let not_c = kernel.const_(logic.not, vec![]);
        let not_lt = kernel.app(not_c, lt_aa);
        let ty = kernel.pi(anon, r_ty, not_lt, BinderInfo::Default);
        declare_axiom(kernel, anon, "lt_irrefl", ty)
    };

    // --- lt_trans : ∀ (a b c : R), lt a b → lt b c → lt a c ------------------
    let lt_trans = {
        let ty = trans_axiom_ty(kernel, anon, r_ty, lt, lt, lt);
        declare_axiom(kernel, anon, "lt_trans", ty)
    };

    // --- lt_of_lt_of_le : ∀ (a b c : R), lt a b → le b c → lt a c ------------
    let lt_of_lt_of_le = {
        let ty = trans_axiom_ty(kernel, anon, r_ty, lt, le, lt);
        declare_axiom(kernel, anon, "lt_of_lt_of_le", ty)
    };

    // --- lt_of_le_of_lt : ∀ (a b c : R), le a b → lt b c → lt a c ------------
    let lt_of_le_of_lt = {
        let ty = trans_axiom_ty(kernel, anon, r_ty, le, lt, lt);
        declare_axiom(kernel, anon, "lt_of_le_of_lt", ty)
    };

    // --- le_of_lt : ∀ (a b : R), lt a b → le a b -----------------------------
    let le_of_lt = {
        // Under a,b,h: a=2,b=1 (result le a b); h: lt a b under a,b → a=1,b=0.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let result = app2(kernel, le, a2, b1);
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let h_dom = app2(kernel, lt, a1, b0);
        let after_h = kernel.pi(anon, h_dom, result, BinderInfo::Default);
        let ty = telescope_r(kernel, anon, r_ty, 2, after_h);
        declare_axiom(kernel, anon, "le_of_lt", ty)
    };

    // --- add_le_add : ∀ (a b c d : R), le a b → le c d → le (add a c)(add b d) -
    let add_le_add = {
        // Under a,b,c,d,h1,h2 the result references: a=5,b=4,c=3,d=2.
        let a5 = kernel.bvar(5);
        let b4 = kernel.bvar(4);
        let c3 = kernel.bvar(3);
        let d2 = kernel.bvar(2);
        let add_ac = app2(kernel, add, a5, c3);
        let add_bd = app2(kernel, add, b4, d2);
        let result = app2(kernel, le, add_ac, add_bd);
        // h2 : le c d — under a,b,c,d,h1 → c=2,d=1.
        let c2 = kernel.bvar(2);
        let d1 = kernel.bvar(1);
        let h2_dom = app2(kernel, le, c2, d1);
        let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
        // h1 : le a b — under a,b,c,d → a=3,b=2.
        let a3 = kernel.bvar(3);
        let b2 = kernel.bvar(2);
        let h1_dom = app2(kernel, le, a3, b2);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        let ty = telescope_r(kernel, anon, r_ty, 4, after_h1);
        declare_axiom(kernel, anon, "add_le_add", ty)
    };

    // Equality builder `Eq.{1} R x y` (carrier is Sort 1 ⇒ u := 1).
    let one_lvl = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };
    let eq_r = |kernel: &mut Kernel, x: ExprId, y: ExprId| -> ExprId {
        let eqc = kernel.const_(logic.eq, vec![one_lvl]);
        let r_ty = kernel.const_(r, vec![]);
        let e = kernel.app(eqc, r_ty);
        let e = kernel.app(e, x);
        kernel.app(e, y)
    };

    // --- add_comm : ∀ (a b : R), Eq R (add a b) (add b a) --------------------
    let add_comm = {
        // Under a,b: a=1,b=0.
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let add_ab = app2(kernel, add, a1, b0);
        let a1b = kernel.bvar(1);
        let b0b = kernel.bvar(0);
        let add_ba = app2(kernel, add, b0b, a1b);
        let body = eq_r(kernel, add_ab, add_ba);
        let ty = telescope_r(kernel, anon, r_ty, 2, body);
        declare_axiom(kernel, anon, "add_comm", ty)
    };

    // --- add_assoc : ∀ (a b c : R), Eq R (add (add a b) c) (add a (add b c)) -
    let add_assoc = {
        // Under a,b,c: a=2,b=1,c=0.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let c0 = kernel.bvar(0);
        let add_ab = app2(kernel, add, a2, b1);
        let lhs = app2(kernel, add, add_ab, c0);
        let a2b = kernel.bvar(2);
        let b1b = kernel.bvar(1);
        let c0b = kernel.bvar(0);
        let add_bc = app2(kernel, add, b1b, c0b);
        let rhs = app2(kernel, add, a2b, add_bc);
        let body = eq_r(kernel, lhs, rhs);
        let ty = telescope_r(kernel, anon, r_ty, 3, body);
        declare_axiom(kernel, anon, "add_assoc", ty)
    };

    // --- add_zero : ∀ (a : R), Eq R (add a zero) a ---------------------------
    let add_zero = {
        let a0 = kernel.bvar(0);
        let zero_c = kernel.const_(zero, vec![]);
        let add_az = app2(kernel, add, a0, zero_c);
        let a0b = kernel.bvar(0);
        let body = eq_r(kernel, add_az, a0b);
        let ty = kernel.pi(anon, r_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "add_zero", ty)
    };

    // --- add_neg : ∀ (a : R), Eq R (add a (neg a)) zero ----------------------
    let add_neg = {
        let a0 = kernel.bvar(0);
        let neg_c = kernel.const_(neg, vec![]);
        let a0b = kernel.bvar(0);
        let neg_a = kernel.app(neg_c, a0b);
        let add_an = app2(kernel, add, a0, neg_a);
        let zero_c = kernel.const_(zero, vec![]);
        let body = eq_r(kernel, add_an, zero_c);
        let ty = kernel.pi(anon, r_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "add_neg", ty)
    };

    // --- mul_le_mul_of_nonneg_left :
    //       ∀ (c a b : R), le zero c → le a b → le (mul c a) (mul c b) --------
    let mul_le_mul_of_nonneg_left = {
        // Binder order c,a,b then h1: le zero c, h2: le a b. Result under
        // c,a,b,h1,h2: c=4,a=3,b=2.
        let c4 = kernel.bvar(4);
        let a3 = kernel.bvar(3);
        let b2 = kernel.bvar(2);
        let c4b = kernel.bvar(4);
        let mul_ca = app2(kernel, mul, c4, a3);
        let mul_cb = app2(kernel, mul, c4b, b2);
        let result = app2(kernel, le, mul_ca, mul_cb);
        // h2 : le a b — under c,a,b,h1 → a=2,b=1.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let h2_dom = app2(kernel, le, a2, b1);
        let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
        // h1 : le zero c — under c,a,b → c=2.
        let zero_c = kernel.const_(zero, vec![]);
        let c2 = kernel.bvar(2);
        let h1_dom = app2(kernel, le, zero_c, c2);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        let ty = telescope_r(kernel, anon, r_ty, 3, after_h1);
        declare_axiom(kernel, anon, "mul_le_mul_of_nonneg_left", ty)
    };

    // --- zero_lt_one : lt zero one -------------------------------------------
    let zero_lt_one = {
        let zero_c = kernel.const_(zero, vec![]);
        let one_c = kernel.const_(one, vec![]);
        let ty = app2(kernel, lt, zero_c, one_c);
        declare_axiom(kernel, anon, "zero_lt_one", ty)
    };

    // --- add_lt_add_of_le_of_lt (Task #16) -----------------------------------
    //   ∀ (a b c d : R), le a b → lt c d → lt (add a c)(add b d).
    // Same telescope/de-Bruijn shape as `add_le_add`, but the second hypothesis
    // and the conclusion are `lt`.
    let add_lt_add_of_le_of_lt = {
        // Under a,b,c,d,h1,h2 the result references: a=5,b=4,c=3,d=2.
        let a5 = kernel.bvar(5);
        let b4 = kernel.bvar(4);
        let c3 = kernel.bvar(3);
        let d2 = kernel.bvar(2);
        let add_ac = app2(kernel, add, a5, c3);
        let add_bd = app2(kernel, add, b4, d2);
        let result = app2(kernel, lt, add_ac, add_bd);
        // h2 : lt c d — under a,b,c,d,h1 → c=2,d=1.
        let c2 = kernel.bvar(2);
        let d1 = kernel.bvar(1);
        let h2_dom = app2(kernel, lt, c2, d1);
        let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
        // h1 : le a b — under a,b,c,d → a=3,b=2.
        let a3 = kernel.bvar(3);
        let b2 = kernel.bvar(2);
        let h1_dom = app2(kernel, le, a3, b2);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        let ty = telescope_r(kernel, anon, r_ty, 4, after_h1);
        declare_axiom(kernel, anon, "add_lt_add_of_le_of_lt", ty)
    };

    ArithPrelude {
        logic,
        r,
        add,
        mul,
        neg,
        zero,
        one,
        le,
        lt,
        le_refl,
        le_trans,
        lt_irrefl,
        lt_trans,
        lt_of_lt_of_le,
        lt_of_le_of_lt,
        le_of_lt,
        add_le_add,
        add_comm,
        add_assoc,
        add_zero,
        add_neg,
        mul_le_mul_of_nonneg_left,
        zero_lt_one,
        add_lt_add_of_le_of_lt,
    }
}

/// Wrap `body` in `n` `∀ (_ : R)` binders, returning `Π (R)^n, body`.
fn telescope_r(
    kernel: &mut Kernel,
    anon: NameId,
    r_ty: ExprId,
    n: usize,
    mut body: ExprId,
) -> ExprId {
    for _ in 0..n {
        body = kernel.pi(anon, r_ty, body, BinderInfo::Default);
    }
    body
}

/// Build the shared 3-place "transitivity" axiom type
/// `∀ (a b c : R), rel1 a b → rel2 b c → rel3 a c` for relation symbols
/// `rel1`/`rel2`/`rel3`.
fn trans_axiom_ty(
    kernel: &mut Kernel,
    anon: NameId,
    r_ty: ExprId,
    rel1: NameId,
    rel2: NameId,
    rel3: NameId,
) -> ExprId {
    let app2 = |kernel: &mut Kernel, f: NameId, x: ExprId, y: ExprId| -> ExprId {
        let fc = kernel.const_(f, vec![]);
        let e = kernel.app(fc, x);
        kernel.app(e, y)
    };
    // Result under a,b,c,h1,h2: a=4,c=2.
    let a4 = kernel.bvar(4);
    let c2 = kernel.bvar(2);
    let result = app2(kernel, rel3, a4, c2);
    // h2 : rel2 b c — under a,b,c,h1 → b=2,c=1.
    let b2 = kernel.bvar(2);
    let c1 = kernel.bvar(1);
    let h2_dom = app2(kernel, rel2, b2, c1);
    let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
    // h1 : rel1 a b — under a,b,c → a=2,b=1.
    let a2 = kernel.bvar(2);
    let b1 = kernel.bvar(1);
    let h1_dom = app2(kernel, rel1, a2, b1);
    let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
    telescope_r(kernel, anon, r_ty, 3, after_h1)
}

/// Declare an axiom `name : ty` through the trusted gate and return its name.
fn declare_axiom(kernel: &mut Kernel, anon: NameId, name: &str, ty: ExprId) -> NameId {
    let nm = kernel.name_str(anon, name);
    kernel
        .add_declaration(Declaration::Axiom {
            name: nm,
            uparams: vec![],
            ty,
        })
        .unwrap_or_else(|e| panic!("arith axiom `{name}` should admit: {e:?}"));
    nm
}

#[cfg(test)]
mod arith_prelude_tests;
