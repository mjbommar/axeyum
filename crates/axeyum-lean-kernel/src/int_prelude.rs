//! The **integer prelude** (ADR-0042, the integer-arithmetic / Diophantine
//! reconstruction foundation): an axiomatized **discretely-ordered commutative
//! ring**, declared into a [`Kernel`]'s environment through the trusted
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate.
//!
//! This is the trusted base for reconstructing **integer-cut / Diophantine
//! `QF_LIA`** refutations into kernel-checked Lean terms. An integer-infeasibility
//! proof is, at bottom, a chain of order/ring steps over `ℤ` that — unlike the
//! ordered field `R` — can invoke **discreteness** (`no_int_between`: there is no
//! integer strictly between `0` and `1`) to refute a residue `g·m = r` with
//! `0 < r < g`. The axioms here are exactly the (sound, ℤ-faithful) rules such a
//! chain invokes. The kernel type-checks every axiom's **type** at admission (a
//! malformed axiom set is rejected by [`Kernel::add_declaration`]), and the
//! accompanying tests then build real proof **terms** on top of the axioms and
//! `infer`-check them — so the kernel genuinely verifies the reasoning.
//!
//! ## What is declared
//!
//! The carrier lives in `Type = Sort 1`; the relations land in `Prop = Sort 0`:
//!
//! - **Carrier** `Z : Type` (an opaque [`Declaration::Axiom`] of type
//!   `Sort 1`).
//! - **Operations** (each an `axiom`): `add : Z → Z → Z`, `mul : Z → Z → Z`,
//!   `neg : Z → Z`, `zero : Z`, `one : Z`.
//! - **Relations** (each an `axiom`): `le : Z → Z → Prop`, `lt : Z → Z → Prop`.
//! - **Order axioms**: `le_refl`, `le_trans`, `lt_irrefl` (via `Not`),
//!   `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`.
//! - **Additive axioms**: `add_le_add`, `add_comm`, `add_assoc`, `add_zero`
//!   (via `Eq` at the `Z` level), `add_neg` (via `Eq`),
//!   `add_lt_add_of_le_of_lt`.
//! - **Multiplicative/ring axioms**: `mul_comm`, `mul_assoc`, `mul_one`,
//!   `mul_zero`, `left_distrib`, `mul_le_mul_of_nonneg_left`, `mul_nonneg`.
//! - **Constant axiom**: `zero_lt_one : lt zero one`.
//! - **Discreteness axiom** (the integer-specific fact the field `R` lacks):
//!   `no_int_between : ∀ (x : Z), Not (And (lt zero x) (lt x one))`.
//! - **Linear-order / antisymmetry axioms** (genuine ℤ theorems):
//!   `le_total : ∀ (a b : Z), Or (le a b) (le b a)` and
//!   `lt_of_le_of_ne : ∀ (a b : Z), le a b → Not (Eq Z a b) → lt a b`.
//! - **Euclidean decomposition** (ADR-0104):
//!   `euclidean_decomposition : ∀ t k, 0 < k → ∃ q r,
//!   t = k*q+r ∧ 0≤r ∧ r<k`. This states the integer theorem needed by
//!   quotient/remainder proofs without adding division or modulo operations.
//! - **Decidable integer equality** (ADR-0106):
//!   `eq_em : ∀ a b, Or (Eq Z a b) (Not (Eq Z a b))`. This is the
//!   integer-specific decision theorem needed by equality partitions, not
//!   unrestricted propositional excluded middle.
//!
//! Each axiom's exact type is documented on the corresponding [`IntPrelude`]
//! field. The propositional connectives (`Not`, `And`, `Eq`, `False`) come from
//! [`build_logic_prelude`](crate::build_logic_prelude); `Eq` is used at universe
//! `u := 1` because the carrier is `Sort 1`.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, LogicPrelude, build_logic_prelude};

/// The interned names produced by [`build_int_prelude`]: the carrier, the
/// ring/order operations, and every axiom of the discretely-ordered commutative
/// ring, plus the embedded [`LogicPrelude`] (so callers can build
/// `False`/`Not`/`And`/`Eq` terms).
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so tests and callers can build `Const` terms
/// (`k.const_(int.le, vec![])`, `k.const_(int.no_int_between, vec![])`, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntPrelude {
    /// The embedded logical prelude (`False`, `Not`, `And`, `Eq`, …).
    pub logic: LogicPrelude,

    // --- carrier + operations ------------------------------------------------
    /// `Z : Type` (i.e. `Z : Sort 1`) — the discretely-ordered ring's carrier.
    pub z: NameId,
    /// `add : Z → Z → Z`.
    pub add: NameId,
    /// `mul : Z → Z → Z`.
    pub mul: NameId,
    /// `neg : Z → Z`.
    pub neg: NameId,
    /// `zero : Z`.
    pub zero: NameId,
    /// `one : Z`.
    pub one: NameId,
    /// `le : Z → Z → Prop`.
    pub le: NameId,
    /// `lt : Z → Z → Prop`.
    pub lt: NameId,

    // --- order axioms --------------------------------------------------------
    /// `le_refl : ∀ (a : Z), le a a`.
    pub le_refl: NameId,
    /// `le_trans : ∀ (a b c : Z), le a b → le b c → le a c`.
    pub le_trans: NameId,
    /// `lt_irrefl : ∀ (a : Z), Not (lt a a)`.
    pub lt_irrefl: NameId,
    /// `lt_trans : ∀ (a b c : Z), lt a b → lt b c → lt a c`.
    pub lt_trans: NameId,
    /// `lt_of_lt_of_le : ∀ (a b c : Z), lt a b → le b c → lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ (a b c : Z), le a b → lt b c → lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `le_of_lt : ∀ (a b : Z), lt a b → le a b`.
    pub le_of_lt: NameId,

    // --- additive axioms -----------------------------------------------------
    /// `add_le_add : ∀ (a b c d : Z), le a b → le c d → le (add a c) (add b d)`.
    pub add_le_add: NameId,
    /// `add_comm : ∀ (a b : Z), Eq Z (add a b) (add b a)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : Z), Eq Z (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_zero : ∀ (a : Z), Eq Z (add a zero) a`.
    pub add_zero: NameId,
    /// `add_neg : ∀ (a : Z), Eq Z (add a (neg a)) zero`.
    pub add_neg: NameId,
    /// `add_lt_add_of_le_of_lt :
    /// ∀ (a b c d : Z), le a b → lt c d → lt (add a c) (add b d)`.
    ///
    /// Summing a non-strict inequality with a strict one yields a strict result.
    pub add_lt_add_of_le_of_lt: NameId,

    // --- scaling axiom -------------------------------------------------------
    /// `mul_le_mul_of_nonneg_left :
    /// ∀ (c a b : Z), le zero c → le a b → le (mul c a) (mul c b)`.
    pub mul_le_mul_of_nonneg_left: NameId,

    // --- constant axiom ------------------------------------------------------
    /// `zero_lt_one : lt zero one`.
    pub zero_lt_one: NameId,

    // --- multiplicative commutative ring axioms ------------------------------
    // Each is a standard theorem of a commutative ordered ring (true in ℤ), and
    // completes the multiplicative fragment. Each axiom's type is type-checked at
    // admission.
    /// `mul_comm : ∀ (a b : Z), Eq Z (mul a b) (mul b a)`.
    pub mul_comm: NameId,
    /// `mul_assoc : ∀ (a b c : Z), Eq Z (mul (mul a b) c) (mul a (mul b c))`.
    pub mul_assoc: NameId,
    /// `mul_one : ∀ (a : Z), Eq Z (mul a one) a`.
    pub mul_one: NameId,
    /// `mul_zero : ∀ (a : Z), Eq Z (mul a zero) zero`.
    pub mul_zero: NameId,
    /// `left_distrib :
    /// ∀ (a b c : Z), Eq Z (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `mul_nonneg : ∀ (a b : Z), le zero a → le zero b → le zero (mul a b)`.
    /// The product of nonnegatives is nonnegative.
    pub mul_nonneg: NameId,

    // --- discreteness axiom (ADR-0042, the integer-specific fact) ------------
    /// `no_int_between : ∀ (x : Z), Not (And (lt zero x) (lt x one))` — there is
    /// no integer strictly between `0` and `1`. This is the single axiom the
    /// field `R` lacks, and the crux of every integer-infeasibility proof.
    pub no_int_between: NameId,

    // --- linear-order / antisymmetry axioms (genuine ℤ theorems) -------------
    /// `le_total : ∀ (a b : Z), Or (le a b) (le b a)` — `ℤ` is a **total**
    /// (linear) order: any two integers are comparable. A standard theorem of
    /// `ℤ`; used to case-split `m' ≤ 1` vs `1 ≤ m'` in the discreteness close.
    pub le_total: NameId,
    /// `lt_of_le_of_ne : ∀ (a b : Z), le a b → Not (Eq Z a b) → lt a b` — a
    /// non-strict inequality that is **not** an equality is strict. A standard
    /// theorem of any partial order (`le` antisymmetric); used to strengthen
    /// `m' ≤ 1` to `m' < 1` (and `0 ≤ m'` to `0 < m'`) once equality is excluded.
    pub lt_of_le_of_ne: NameId,

    // --- Euclidean decomposition (ADR-0104) ---------------------------------
    /// `euclidean_decomposition : ∀ (t k : Z), lt zero k →
    /// Exists Z (fun q => Exists Z (fun r =>
    /// And (Eq Z t (add (mul k q) r)) (And (le zero r) (lt r k))))`.
    ///
    /// This is the standard Euclidean division theorem for positive integer
    /// moduli. It deliberately exposes only quotient/remainder existence and
    /// bounds, not `div` or `mod` operations or their zero-divisor semantics.
    pub euclidean_decomposition: NameId,

    // --- decidable equality (ADR-0106) --------------------------------------
    /// `eq_em : ∀ (a b : Z), Or (Eq Z a b) (Not (Eq Z a b))`.
    ///
    /// Integer equality is decidable. Keeping this theorem on `Z` avoids adding
    /// unrestricted classical excluded middle to the logic prelude.
    pub eq_em: NameId,
}

/// Declare the axiomatized **discretely-ordered commutative ring** into
/// `kernel`'s environment, returning the [`IntPrelude`] of interned names. The
/// logical prelude is built first (if not already present,
/// `build_logic_prelude` is idempotent only on a fresh kernel, so this expects a
/// kernel without those names — see Panics).
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
pub fn build_int_prelude(kernel: &mut Kernel) -> IntPrelude {
    let logic = build_logic_prelude(kernel);
    let anon = kernel.anon();

    // --- carrier Z : Type (= Sort 1) -----------------------------------------
    let z = kernel.name_str(anon, "Z");
    {
        let one_lvl = {
            let zl = kernel.level_zero();
            kernel.level_succ(zl)
        };
        let type1 = kernel.sort(one_lvl);
        kernel
            .add_declaration(Declaration::Axiom {
                name: z,
                uparams: vec![],
                ty: type1,
            })
            .expect("Z : Type should admit");
    }

    // `Z` as a type expression.
    let z_ty = kernel.const_(z, vec![]);
    // Helper: the arrow `dom → cod` (a non-dependent Pi).
    let arrow = |kernel: &mut Kernel, dom: ExprId, cod: ExprId| -> ExprId {
        let anon = kernel.anon();
        kernel.pi(anon, dom, cod, BinderInfo::Default)
    };

    // --- operations ----------------------------------------------------------
    // add, mul : Z → Z → Z.
    let bin_op_ty = {
        let inner = arrow(kernel, z_ty, z_ty);
        arrow(kernel, z_ty, inner)
    };
    let add = declare_axiom(kernel, anon, "add", bin_op_ty);
    let mul = declare_axiom(kernel, anon, "mul", bin_op_ty);
    // neg : Z → Z.
    let neg = {
        let ty = arrow(kernel, z_ty, z_ty);
        declare_axiom(kernel, anon, "neg", ty)
    };
    // zero, one : Z.
    let zero = declare_axiom(kernel, anon, "zero", z_ty);
    let one = declare_axiom(kernel, anon, "one", z_ty);
    // le, lt : Z → Z → Prop.
    let rel_ty = {
        let prop = kernel.sort_zero();
        let inner = arrow(kernel, z_ty, prop);
        arrow(kernel, z_ty, inner)
    };
    let le = declare_axiom(kernel, anon, "le", rel_ty);
    let lt = declare_axiom(kernel, anon, "lt", rel_ty);

    // ----- small term builders over the now-declared symbols -----------------
    // We build axiom *types* as Pi-telescopes over `Z`. Inside a telescope of
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

    // --- le_refl : ∀ (a : Z), le a a -----------------------------------------
    let le_refl = {
        let a0 = kernel.bvar(0);
        let a0b = kernel.bvar(0);
        let body = app2(kernel, le, a0, a0b);
        let ty = kernel.pi(anon, z_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "le_refl", ty)
    };

    // --- le_trans : ∀ (a b c : Z), le a b → le b c → le a c ------------------
    let le_trans = {
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
        let ty = telescope_z(kernel, anon, z_ty, 3, after_h1);
        declare_axiom(kernel, anon, "le_trans", ty)
    };

    // --- lt_irrefl : ∀ (a : Z), Not (lt a a) ---------------------------------
    let lt_irrefl = {
        let a0 = kernel.bvar(0);
        let a0b = kernel.bvar(0);
        let lt_aa = app2(kernel, lt, a0, a0b);
        let not_c = kernel.const_(logic.not, vec![]);
        let not_lt = kernel.app(not_c, lt_aa);
        let ty = kernel.pi(anon, z_ty, not_lt, BinderInfo::Default);
        declare_axiom(kernel, anon, "lt_irrefl", ty)
    };

    // --- lt_trans : ∀ (a b c : Z), lt a b → lt b c → lt a c ------------------
    let lt_trans = {
        let ty = trans_axiom_ty(kernel, anon, z_ty, lt, lt, lt);
        declare_axiom(kernel, anon, "lt_trans", ty)
    };

    // --- lt_of_lt_of_le : ∀ (a b c : Z), lt a b → le b c → lt a c ------------
    let lt_of_lt_of_le = {
        let ty = trans_axiom_ty(kernel, anon, z_ty, lt, le, lt);
        declare_axiom(kernel, anon, "lt_of_lt_of_le", ty)
    };

    // --- lt_of_le_of_lt : ∀ (a b c : Z), le a b → lt b c → lt a c ------------
    let lt_of_le_of_lt = {
        let ty = trans_axiom_ty(kernel, anon, z_ty, le, lt, lt);
        declare_axiom(kernel, anon, "lt_of_le_of_lt", ty)
    };

    // --- le_of_lt : ∀ (a b : Z), lt a b → le a b -----------------------------
    let le_of_lt = {
        // Under a,b,h: a=2,b=1 (result le a b); h: lt a b under a,b → a=1,b=0.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let result = app2(kernel, le, a2, b1);
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let h_dom = app2(kernel, lt, a1, b0);
        let after_h = kernel.pi(anon, h_dom, result, BinderInfo::Default);
        let ty = telescope_z(kernel, anon, z_ty, 2, after_h);
        declare_axiom(kernel, anon, "le_of_lt", ty)
    };

    // --- add_le_add : ∀ (a b c d : Z), le a b → le c d → le (add a c)(add b d) -
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
        let ty = telescope_z(kernel, anon, z_ty, 4, after_h1);
        declare_axiom(kernel, anon, "add_le_add", ty)
    };

    // Equality builder `Eq.{1} Z x y` (carrier is Sort 1 ⇒ u := 1).
    let one_lvl = {
        let zl = kernel.level_zero();
        kernel.level_succ(zl)
    };
    let eq_z = |kernel: &mut Kernel, x: ExprId, y: ExprId| -> ExprId {
        let eqc = kernel.const_(logic.eq, vec![one_lvl]);
        let z_ty = kernel.const_(z, vec![]);
        let e = kernel.app(eqc, z_ty);
        let e = kernel.app(e, x);
        kernel.app(e, y)
    };

    // --- add_comm : ∀ (a b : Z), Eq Z (add a b) (add b a) --------------------
    let add_comm = {
        // Under a,b: a=1,b=0.
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let add_ab = app2(kernel, add, a1, b0);
        let a1b = kernel.bvar(1);
        let b0b = kernel.bvar(0);
        let add_ba = app2(kernel, add, b0b, a1b);
        let body = eq_z(kernel, add_ab, add_ba);
        let ty = telescope_z(kernel, anon, z_ty, 2, body);
        declare_axiom(kernel, anon, "add_comm", ty)
    };

    // --- add_assoc : ∀ (a b c : Z), Eq Z (add (add a b) c) (add a (add b c)) -
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
        let body = eq_z(kernel, lhs, rhs);
        let ty = telescope_z(kernel, anon, z_ty, 3, body);
        declare_axiom(kernel, anon, "add_assoc", ty)
    };

    // --- add_zero : ∀ (a : Z), Eq Z (add a zero) a ---------------------------
    let add_zero = {
        let a0 = kernel.bvar(0);
        let zero_c = kernel.const_(zero, vec![]);
        let add_az = app2(kernel, add, a0, zero_c);
        let a0b = kernel.bvar(0);
        let body = eq_z(kernel, add_az, a0b);
        let ty = kernel.pi(anon, z_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "add_zero", ty)
    };

    // --- add_neg : ∀ (a : Z), Eq Z (add a (neg a)) zero ----------------------
    let add_neg = {
        let a0 = kernel.bvar(0);
        let neg_c = kernel.const_(neg, vec![]);
        let a0b = kernel.bvar(0);
        let neg_a = kernel.app(neg_c, a0b);
        let add_an = app2(kernel, add, a0, neg_a);
        let zero_c = kernel.const_(zero, vec![]);
        let body = eq_z(kernel, add_an, zero_c);
        let ty = kernel.pi(anon, z_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "add_neg", ty)
    };

    // --- add_lt_add_of_le_of_lt :
    //   ∀ (a b c d : Z), le a b → lt c d → lt (add a c)(add b d).
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
        let ty = telescope_z(kernel, anon, z_ty, 4, after_h1);
        declare_axiom(kernel, anon, "add_lt_add_of_le_of_lt", ty)
    };

    // --- mul_le_mul_of_nonneg_left :
    //       ∀ (c a b : Z), le zero c → le a b → le (mul c a) (mul c b) --------
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
        let ty = telescope_z(kernel, anon, z_ty, 3, after_h1);
        declare_axiom(kernel, anon, "mul_le_mul_of_nonneg_left", ty)
    };

    // --- zero_lt_one : lt zero one -------------------------------------------
    let zero_lt_one = {
        let zero_c = kernel.const_(zero, vec![]);
        let one_c = kernel.const_(one, vec![]);
        let ty = app2(kernel, lt, zero_c, one_c);
        declare_axiom(kernel, anon, "zero_lt_one", ty)
    };

    // --- mul_comm : ∀ (a b : Z), Eq Z (mul a b) (mul b a) --------------------
    // (Same shape as `add_comm`, with `mul` for `add`.) Under a,b: a=1,b=0.
    let mul_comm = {
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let mul_ab = app2(kernel, mul, a1, b0);
        let a1b = kernel.bvar(1);
        let b0b = kernel.bvar(0);
        let mul_ba = app2(kernel, mul, b0b, a1b);
        let body = eq_z(kernel, mul_ab, mul_ba);
        let ty = telescope_z(kernel, anon, z_ty, 2, body);
        declare_axiom(kernel, anon, "mul_comm", ty)
    };

    // --- mul_assoc : ∀ (a b c : Z), Eq Z (mul (mul a b) c)(mul a (mul b c)) --
    // (Same shape as `add_assoc`.) Under a,b,c: a=2,b=1,c=0.
    let mul_assoc = {
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let c0 = kernel.bvar(0);
        let mul_ab = app2(kernel, mul, a2, b1);
        let lhs = app2(kernel, mul, mul_ab, c0);
        let a2b = kernel.bvar(2);
        let b1b = kernel.bvar(1);
        let c0b = kernel.bvar(0);
        let mul_bc = app2(kernel, mul, b1b, c0b);
        let rhs = app2(kernel, mul, a2b, mul_bc);
        let body = eq_z(kernel, lhs, rhs);
        let ty = telescope_z(kernel, anon, z_ty, 3, body);
        declare_axiom(kernel, anon, "mul_assoc", ty)
    };

    // --- mul_one : ∀ (a : Z), Eq Z (mul a one) a -----------------------------
    // (Same shape as `add_zero`, with `mul`/`one` for `add`/`zero`.)
    let mul_one = {
        let a0 = kernel.bvar(0);
        let one_c = kernel.const_(one, vec![]);
        let mul_ao = app2(kernel, mul, a0, one_c);
        let a0b = kernel.bvar(0);
        let body = eq_z(kernel, mul_ao, a0b);
        let ty = kernel.pi(anon, z_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "mul_one", ty)
    };

    // --- mul_zero : ∀ (a : Z), Eq Z (mul a zero) zero ------------------------
    let mul_zero = {
        let a0 = kernel.bvar(0);
        let zero_c = kernel.const_(zero, vec![]);
        let mul_az = app2(kernel, mul, a0, zero_c);
        let zero_cb = kernel.const_(zero, vec![]);
        let body = eq_z(kernel, mul_az, zero_cb);
        let ty = kernel.pi(anon, z_ty, body, BinderInfo::Default);
        declare_axiom(kernel, anon, "mul_zero", ty)
    };

    // --- left_distrib :
    //       ∀ (a b c : Z), Eq Z (mul a (add b c)) (add (mul a b)(mul a c)) ----
    // Under a,b,c: a=2,b=1,c=0.
    let left_distrib = {
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let c0 = kernel.bvar(0);
        let add_bc = app2(kernel, add, b1, c0);
        let lhs = app2(kernel, mul, a2, add_bc);
        let a2b = kernel.bvar(2);
        let b1b = kernel.bvar(1);
        let mul_ab = app2(kernel, mul, a2b, b1b);
        let a2c = kernel.bvar(2);
        let c0b = kernel.bvar(0);
        let mul_ac = app2(kernel, mul, a2c, c0b);
        let rhs = app2(kernel, add, mul_ab, mul_ac);
        let body = eq_z(kernel, lhs, rhs);
        let ty = telescope_z(kernel, anon, z_ty, 3, body);
        declare_axiom(kernel, anon, "left_distrib", ty)
    };

    // --- mul_nonneg : ∀ (a b : Z), le zero a → le zero b → le zero (mul a b) -
    // Telescope a,b then h1,h2. Result under a,b,h1,h2: a=3,b=2; h2 under
    // a,b,h1: b=1; h1 under a,b: a=1.
    let mul_nonneg = {
        let zero_res = kernel.const_(zero, vec![]);
        let a3 = kernel.bvar(3);
        let b2 = kernel.bvar(2);
        let mul_ab = app2(kernel, mul, a3, b2);
        let result = app2(kernel, le, zero_res, mul_ab);
        // h2 : le zero b — under a,b,h1 → b=1.
        let zero_h2 = kernel.const_(zero, vec![]);
        let b1 = kernel.bvar(1);
        let h2_dom = app2(kernel, le, zero_h2, b1);
        let after_h2 = kernel.pi(anon, h2_dom, result, BinderInfo::Default);
        // h1 : le zero a — under a,b → a=1.
        let zero_h1 = kernel.const_(zero, vec![]);
        let a1 = kernel.bvar(1);
        let h1_dom = app2(kernel, le, zero_h1, a1);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        let ty = telescope_z(kernel, anon, z_ty, 2, after_h1);
        declare_axiom(kernel, anon, "mul_nonneg", ty)
    };

    // --- no_int_between : ∀ (x : Z), Not (And (lt zero x) (lt x one)) --------
    // The discreteness axiom (ADR-0042): there is no integer strictly between
    // `0` and `1`. Under the single binder `x` (de Bruijn 0):
    //   lt zero x = app2(lt, zero, x);  lt x one = app2(lt, x, one);
    //   And P Q   = (And P) Q  (the logic prelude's `And`, two explicit Props);
    //   Not R     = (Not) R    (the logic prelude's `Not`, one explicit Prop).
    let no_int_between = {
        let zero_c = kernel.const_(zero, vec![]);
        let x0 = kernel.bvar(0);
        let lt_0x = app2(kernel, lt, zero_c, x0);
        let x0b = kernel.bvar(0);
        let one_c = kernel.const_(one, vec![]);
        let lt_x1 = app2(kernel, lt, x0b, one_c);
        // And (lt zero x) (lt x one) = (And (lt zero x)) (lt x one).
        let and_c = kernel.const_(logic.and, vec![]);
        let and_p = kernel.app(and_c, lt_0x);
        let and_pq = kernel.app(and_p, lt_x1);
        // Not (And …) = Not applied to the conjunction.
        let not_c = kernel.const_(logic.not, vec![]);
        let not_and = kernel.app(not_c, and_pq);
        let ty = kernel.pi(anon, z_ty, not_and, BinderInfo::Default);
        declare_axiom(kernel, anon, "no_int_between", ty)
    };

    // --- le_total : ∀ (a b : Z), Or (le a b) (le b a) ------------------------
    // `ℤ` is a total order. Under binders a,b (de Bruijn a=1, b=0):
    //   Or (le a b) (le b a) = (Or (le a b)) (le b a)  (the logic prelude's `Or`,
    //   two explicit Props).
    let le_total = {
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let le_ab = app2(kernel, le, a1, b0);
        let a1b = kernel.bvar(1);
        let b0b = kernel.bvar(0);
        let le_ba = app2(kernel, le, b0b, a1b);
        let or_c = kernel.const_(logic.or, vec![]);
        let or_p = kernel.app(or_c, le_ab);
        let or_pq = kernel.app(or_p, le_ba);
        let ty = telescope_z(kernel, anon, z_ty, 2, or_pq);
        declare_axiom(kernel, anon, "le_total", ty)
    };

    // --- lt_of_le_of_ne : ∀ (a b : Z), le a b → Not (Eq Z a b) → lt a b ------
    // A non-strict inequality that is not an equality is strict.
    // Binder order a,b then h1 : le a b, h2 : Not (Eq Z a b). Result under
    // a,b,h1,h2: a=3,b=2; h2 (Not(Eq a b)) under a,b,h1: a=2,b=1; h1 (le a b)
    // under a,b: a=1,b=0.
    let lt_of_le_of_ne = {
        let a3 = kernel.bvar(3);
        let b2 = kernel.bvar(2);
        let result = app2(kernel, lt, a3, b2);
        // h2 : Not (Eq Z a b) — under a,b,h1 → a=2,b=1.
        let a2 = kernel.bvar(2);
        let b1 = kernel.bvar(1);
        let eq_ab = eq_z(kernel, a2, b1);
        let not_c = kernel.const_(logic.not, vec![]);
        let not_eq = kernel.app(not_c, eq_ab);
        let after_h2 = kernel.pi(anon, not_eq, result, BinderInfo::Default);
        // h1 : le a b — under a,b → a=1,b=0.
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let h1_dom = app2(kernel, le, a1, b0);
        let after_h1 = kernel.pi(anon, h1_dom, after_h2, BinderInfo::Default);
        let ty = telescope_z(kernel, anon, z_ty, 2, after_h1);
        declare_axiom(kernel, anon, "lt_of_le_of_ne", ty)
    };

    // --- euclidean_decomposition :
    //       ∀ t k, lt zero k → ∃ q r, t = k*q+r ∧ 0≤r ∧ r<k ------------
    // Free variables keep this dependent type readable; `abstract_fvars`
    // performs the required de-Bruijn shifting under each predicate/telescope.
    let euclidean_decomposition = {
        let t_id = 10_000;
        let k_id = 10_001;
        let q_id = 10_002;
        let r_id = 10_003;
        let t = kernel.fvar(t_id);
        let k = kernel.fvar(k_id);
        let q = kernel.fvar(q_id);
        let r = kernel.fvar(r_id);
        let kq = app2(kernel, mul, k, q);
        let kq_r = app2(kernel, add, kq, r);
        let recomposition = eq_z(kernel, t, kq_r);
        let zero_c = kernel.const_(zero, vec![]);
        let nonnegative = app2(kernel, le, zero_c, r);
        let below_modulus = app2(kernel, lt, r, k);
        let and_c = kernel.const_(logic.and, vec![]);
        let bounds = {
            let e = kernel.app(and_c, nonnegative);
            kernel.app(e, below_modulus)
        };
        let facts = {
            let and_c = kernel.const_(logic.and, vec![]);
            let e = kernel.app(and_c, recomposition);
            kernel.app(e, bounds)
        };

        let r_body = kernel.abstract_fvars(facts, &[r_id]);
        let r_pred = kernel.lam(anon, z_ty, r_body, BinderInfo::Default);
        let one_lvl = {
            let zero_lvl = kernel.level_zero();
            kernel.level_succ(zero_lvl)
        };
        let exists_c = kernel.const_(logic.exists_, vec![one_lvl]);
        let exists_r = {
            let e = kernel.app(exists_c, z_ty);
            kernel.app(e, r_pred)
        };
        let q_body = kernel.abstract_fvars(exists_r, &[q_id]);
        let q_pred = kernel.lam(anon, z_ty, q_body, BinderInfo::Default);
        let exists_q = {
            let exists_c = kernel.const_(logic.exists_, vec![one_lvl]);
            let e = kernel.app(exists_c, z_ty);
            kernel.app(e, q_pred)
        };
        let zero_c = kernel.const_(zero, vec![]);
        let positive = app2(kernel, lt, zero_c, k);
        let after_positive = kernel.pi(anon, positive, exists_q, BinderInfo::Default);
        let k_body = kernel.abstract_fvars(after_positive, &[k_id]);
        let after_k = kernel.pi(anon, z_ty, k_body, BinderInfo::Default);
        let t_body = kernel.abstract_fvars(after_k, &[t_id]);
        let ty = kernel.pi(anon, z_ty, t_body, BinderInfo::Default);
        declare_axiom(kernel, anon, "euclidean_decomposition", ty)
    };

    // --- eq_em : ∀ a b, Or (Eq Z a b) (Not (Eq Z a b)) ---------------------
    let eq_em = {
        let a1 = kernel.bvar(1);
        let b0 = kernel.bvar(0);
        let equality = eq_z(kernel, a1, b0);
        let not_c = kernel.const_(logic.not, vec![]);
        let not_equality = kernel.app(not_c, equality);
        let or_c = kernel.const_(logic.or, vec![]);
        let disjunction = kernel.app(or_c, equality);
        let disjunction = kernel.app(disjunction, not_equality);
        let ty = telescope_z(kernel, anon, z_ty, 2, disjunction);
        declare_axiom(kernel, anon, "eq_em", ty)
    };

    IntPrelude {
        logic,
        z,
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
        add_lt_add_of_le_of_lt,
        mul_le_mul_of_nonneg_left,
        zero_lt_one,
        mul_comm,
        mul_assoc,
        mul_one,
        mul_zero,
        left_distrib,
        mul_nonneg,
        no_int_between,
        le_total,
        lt_of_le_of_ne,
        euclidean_decomposition,
        eq_em,
    }
}

/// Wrap `body` in `n` `∀ (_ : Z)` binders, returning `Π (Z)^n, body`.
fn telescope_z(
    kernel: &mut Kernel,
    anon: NameId,
    z_ty: ExprId,
    n: usize,
    mut body: ExprId,
) -> ExprId {
    for _ in 0..n {
        body = kernel.pi(anon, z_ty, body, BinderInfo::Default);
    }
    body
}

/// Build the shared 3-place "transitivity" axiom type
/// `∀ (a b c : Z), rel1 a b → rel2 b c → rel3 a c` for relation symbols
/// `rel1`/`rel2`/`rel3`.
fn trans_axiom_ty(
    kernel: &mut Kernel,
    anon: NameId,
    z_ty: ExprId,
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
    telescope_z(kernel, anon, z_ty, 3, after_h1)
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
        .unwrap_or_else(|e| panic!("int axiom `{name}` should admit: {e:?}"));
    nm
}

#[cfg(test)]
mod int_prelude_tests;
