//! Integer-infeasibility (**Diophantine**) refutation → kernel-checked Lean
//! `False` (ADR-0042, the integer-proof payoff).
//!
//! The in-tree [`DiophantineCertificate`](crate::DiophantineCertificate) (P2.4)
//! refutes an integer system `A x = b` that is *rational*-feasible yet
//! *integer*-infeasible (the canonical case `x + y = 0 ∧ x − y = 1 ⇒ 2x = 1`). It
//! certifies an integer combination `Σ_i λ_i·E_i` equal to a row
//! `Σ_j combined_j·x_j = constant` with `g = gcd(|combined_j|) ∤ constant`.
//!
//! This module reconstructs that refutation over the **integer prelude**
//! ([`IntPrelude`], the discretely-ordered commutative ring `Z`): it encodes each
//! `E_i` as a hypothesis `h_i : Eq Z lhs_i rhs_i`, derives the combined equality
//! `Eq Z combined_expr (intlit constant)` (scale + sum via `Eq Z` congruence and an
//! integer ring normalizer), reduces it to `g·m' = r` with `0 < r < g` (Euclidean
//! `constant = g·q + r`, `m' = m − q`, `m = combined/g`), and closes with the
//! **discreteness** axiom `no_int_between m' (And.intro (0<m') (m'<1))` to `False`.
//!
//! ## Soundness — the kernel is the checker
//!
//! Every assembled term is `infer`-checked and [`Kernel::def_eq`]-compared to the
//! prelude's `False`. A wrong reconstruction makes the final `infer`/`def_eq` fail,
//! so this returns a [`ReconstructError`], never a wrong `False`. The integer ring
//! normalizer is a port of the LRA/SOS additive normalizer over `R`; the only new
//! trusted base is [`IntPrelude`]'s axioms (every one a genuine ℤ theorem,
//! type-checked at admission).
//!
//! ## Scope
//!
//! Handles the main case `g > 0` (gcd divides every combined coefficient, as the
//! certificate guarantees). The degenerate `g = 0` row (`0 = constant ≠ 0`, an
//! empty `combined`) is **declined** here (no order machinery is needed for it, but
//! it is a distinct shape; it falls through to the linear/Farkas path). The
//! reconstruction also declines on any `i128` overflow or a normalizer mismatch —
//! never fabricating an identity.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::BTreeMap;

use axeyum_ir::{SymbolId, TermArena, TermId};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, IntPrelude, Kernel, NameId, build_int_prelude,
};

use crate::lia_gcd::{DiophantineCertificate, Equality, prove_lia_unsat_by_diophantine_certified};
use crate::reconstruct::ReconstructError;

/// A signed unit **generator** of the integer additive normal form: a bare
/// variable `±xⱼ` (dense index) or the unit `±1`. The canonical form of a linear
/// integer expression is a right-nested `add` over a flat list of these
/// (terminated by `zero`), variables ascending by index and the constant last;
/// repeated generators model integer coefficients (`coeff = 3` ⇒ three `+xⱼ`).
///
/// The degree-2 multiplicative engine ([`IntReconstructCtx::mul_lists_eq`]) only
/// ever produces `Const`/`Lin` products in the Diophantine reduction (`const ×
/// linear`), so the quadratic [`IGen::Quad`] case appears in the type for the
/// generic distribution but never in a successful Diophantine proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IGen {
    mono: IMono,
    /// `true` ⇒ `neg (mono_expr)`, `false` ⇒ `mono_expr`.
    neg: bool,
}

/// A base monomial of degree ≤ 2 over canonical variable indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IMono {
    /// The constant `1`.
    Const,
    /// The linear monomial `xᵢ`.
    Lin(usize),
    /// The quadratic monomial `xᵢ·xⱼ` with `i ≤ j` (kernel term `mul xᵢ xⱼ`).
    Quad(usize, usize),
}

impl IMono {
    fn quad(i: usize, j: usize) -> Self {
        if i <= j {
            IMono::Quad(i, j)
        } else {
            IMono::Quad(j, i)
        }
    }

    /// Total sort key: linear (ascending index), then quadratic, then constant.
    fn sort_key(self) -> (u8, usize, usize) {
        match self {
            IMono::Lin(i) => (0, i, 0),
            IMono::Quad(i, j) => (1, i, j),
            IMono::Const => (2, usize::MAX, usize::MAX),
        }
    }
}

impl IGen {
    fn pos(mono: IMono) -> Self {
        IGen { mono, neg: false }
    }

    fn negate(self) -> Self {
        IGen {
            mono: self.mono,
            neg: !self.neg,
        }
    }

    /// Sort key keeping a generator adjacent to its negation after bubbling.
    fn sort_key(self) -> (u8, usize, usize, u8) {
        let (a, b, c) = self.mono.sort_key();
        (a, b, c, u8::from(self.neg))
    }
}

/// A small owned degree-≤2 integer expression AST over canonical variable indices,
/// the input to the ring normalizer ([`IntReconstructCtx::normalize`]). Built from
/// `var`/`neg`/`add`/`mul`/`one`; the normalizer emits its faithful kernel
/// `Z`-encoding and proves it equals the canonical signed-monomial sum.
#[derive(Debug, Clone)]
enum ZExpr {
    Var(usize),
    Neg(Box<ZExpr>),
    Add(Box<ZExpr>, Box<ZExpr>),
    Mul(Box<ZExpr>, Box<ZExpr>),
    One,
    /// The constant `zero` (the additive identity; canonicalizes to the empty
    /// generator list). Appears when an encoded literal is `0`.
    Zero,
}

/// The reconstruction context for integer Diophantine proofs: a [`Kernel`] seeded
/// with the integer prelude ([`build_int_prelude`]) plus a deterministic map from a
/// dense variable index to its opaque `Z`-typed [`NameId`].
pub struct IntReconstructCtx {
    kernel: Kernel,
    int: IntPrelude,
    /// Dense variable index → opaque `Z`-typed constant `NameId`.
    vars: BTreeMap<usize, NameId>,
    next_id: u64,
}

impl core::fmt::Debug for IntReconstructCtx {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IntReconstructCtx")
            .field("vars", &self.vars.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl Default for IntReconstructCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl IntReconstructCtx {
    /// A fresh context: a kernel with the integer prelude declared.
    #[must_use]
    pub fn new() -> Self {
        let mut kernel = Kernel::new();
        let int = build_int_prelude(&mut kernel);
        Self {
            kernel,
            int,
            vars: BTreeMap::new(),
            next_id: 0,
        }
    }

    /// A shared reference to the underlying kernel.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// A mutable reference to the underlying kernel.
    pub fn kernel_mut(&mut self) -> &mut Kernel {
        &mut self.kernel
    }

    /// The integer prelude names.
    #[must_use]
    pub fn int(&self) -> &IntPrelude {
        &self.int
    }

    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.dio");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Get (declaring lazily) the opaque `Z`-typed constant for variable `index`.
    fn var_const(&mut self, index: usize) -> NameId {
        if let Some(&id) = self.vars.get(&index) {
            return id;
        }
        let z_ty = self.kernel.const_(self.int.z, vec![]);
        let decl_name = self.fresh_name("x");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: z_ty,
            })
            .expect("integer variable axiom (_ : Z) should admit");
        self.vars.insert(index, decl_name);
        decl_name
    }

    // ---- term builders over Z ----------------------------------------------

    fn mk_add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let add = self.kernel.const_(self.int.add, vec![]);
        let e = self.kernel.app(add, x);
        self.kernel.app(e, y)
    }

    fn mk_mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let mul = self.kernel.const_(self.int.mul, vec![]);
        let e = self.kernel.app(mul, x);
        self.kernel.app(e, y)
    }

    fn mk_neg(&mut self, x: ExprId) -> ExprId {
        let neg = self.kernel.const_(self.int.neg, vec![]);
        self.kernel.app(neg, x)
    }

    fn mk_zero(&mut self) -> ExprId {
        self.kernel.const_(self.int.zero, vec![])
    }

    fn mk_one(&mut self) -> ExprId {
        self.kernel.const_(self.int.one, vec![])
    }

    fn mk_le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let le = self.kernel.const_(self.int.le, vec![]);
        let e = self.kernel.app(le, x);
        self.kernel.app(e, y)
    }

    fn mk_lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let lt = self.kernel.const_(self.int.lt, vec![]);
        let e = self.kernel.app(lt, x);
        self.kernel.app(e, y)
    }

    /// The `Z`-term for an integer constant `n`: `zero` for `0`, else a left-nested
    /// `add` of `|n|` copies of `one` (negated when `n < 0`).
    fn mk_intlit(&mut self, n: i128) -> ExprId {
        if n == 0 {
            return self.mk_zero();
        }
        let count = n.unsigned_abs();
        let unit = if n < 0 {
            let one = self.mk_one();
            self.mk_neg(one)
        } else {
            self.mk_one()
        };
        let mut acc = unit;
        for _ in 1..count {
            acc = self.mk_add(acc, unit);
        }
        acc
    }

    /// `Eq Z x y` (carrier is `Sort 1` ⇒ universe `u := 1`).
    fn mk_eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let eq = self.kernel.const_(self.int.logic.eq, vec![one_lvl]);
        let z_ty = self.kernel.const_(self.int.z, vec![]);
        let e = self.kernel.app(eq, z_ty);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    fn eq_refl(&mut self, a: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let refl = self.kernel.const_(self.int.logic.eq_refl, vec![one_lvl]);
        let z_ty = self.kernel.const_(self.int.z, vec![]);
        let e = self.kernel.app(refl, z_ty);
        self.kernel.app(e, a)
    }

    /// `Eq.rec`-based transport over the `Z` carrier (`Sort 1`).
    fn eq_rec_transport(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        let one_lvl = self.kernel.level_succ(z);
        let rec = self.kernel.const_(self.int.logic.eq_rec, vec![z, one_lvl]);
        let z_ty = self.kernel.const_(self.int.z, vec![]);
        let e = self.kernel.app(rec, z_ty);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, q);
        self.kernel.app(e, h)
    }

    /// `Eq.symm`: `h : Eq Z a b` ⇒ `Eq Z b a`.
    fn eq_symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_x_a = self.mk_eq(x1, a);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = self.eq_refl(a);
        self.eq_rec_transport(a, motive, refl_case, b, h)
    }

    /// `Eq.trans`: `h1 : Eq Z a b`, `h2 : Eq Z b c` ⇒ `Eq Z a c`.
    fn eq_trans(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_a_x = self.mk_eq(a, x1);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport(b, motive, h1, c, h2)
    }

    // ---- ring-axiom wrappers -----------------------------------------------

    fn add_assoc_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.add_assoc, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    fn add_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.add_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    fn add_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.add_zero, vec![]);
        self.kernel.app(ax, a)
    }

    fn add_neg_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.add_neg, vec![]);
        self.kernel.app(ax, a)
    }

    fn mul_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.mul_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    fn mul_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.mul_zero, vec![]);
        self.kernel.app(ax, a)
    }

    fn mul_one_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.mul_one, vec![]);
        self.kernel.app(ax, a)
    }

    fn left_distrib_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.left_distrib, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    // ---- Eq congruence (Eq.rec transport) ----------------------------------

    fn congr_add_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_add(x1, b);
            let eq_body = self.mk_eq(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl(a_b)
        };
        self.eq_rec_transport(a, motive, refl_case, ap, h)
    }

    fn congr_add_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_add(a, x1);
            let eq_body = self.mk_eq(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl(a_b)
        };
        self.eq_rec_transport(b, motive, refl_case, bp, h)
    }

    fn congr_mul_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_mul(x1, b);
            let eq_body = self.mk_eq(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl(a_b)
        };
        self.eq_rec_transport(a, motive, refl_case, ap, h)
    }

    fn congr_mul_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_mul(a, x1);
            let eq_body = self.mk_eq(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl(a_b)
        };
        self.eq_rec_transport(b, motive, refl_case, bp, h)
    }

    fn congr_neg(&mut self, a: ExprId, ap: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let neg_a = self.mk_neg(a);
            let x1 = self.kernel.bvar(1);
            let neg_x = self.mk_neg(x1);
            let eq_body = self.mk_eq(neg_a, neg_x);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let neg_a = self.mk_neg(a);
            self.eq_refl(neg_a)
        };
        self.eq_rec_transport(a, motive, refl_case, ap, h)
    }

    // ---- derived neg/mul bridge lemmas (no new axiom) ----------------------

    /// Inverse-uniqueness: `h1 : Eq Z (add c u) zero`, `h2 : Eq Z (add c v) zero`
    /// ⇒ `Eq Z u v`. Pure additive-axiom chain.
    fn add_left_cancel_eq(
        &mut self,
        c: ExprId,
        u: ExprId,
        v: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let zero = self.mk_zero();
        let cv = self.mk_add(c, v);
        let cu = self.mk_add(c, u);
        let u_zero = self.mk_add(u, zero);
        let s0 = {
            let az = self.add_zero_eq(u);
            self.eq_symm(u_zero, u, az)
        };
        let h2_sym = self.eq_symm(cv, zero, h2);
        let s1 = self.congr_add_right(u, zero, cv, h2_sym);
        let u_cv = self.mk_add(u, cv);
        let uc = self.mk_add(u, c);
        let uc_v = self.mk_add(uc, v);
        let s2 = {
            let assoc = self.add_assoc_eq(u, c, v);
            self.eq_symm(uc_v, u_cv, assoc)
        };
        let comm_uc = self.add_comm_eq(u, c);
        let s3 = self.congr_add_left(uc, cu, v, comm_uc);
        let cu_v = self.mk_add(cu, v);
        let s4 = self.congr_add_left(cu, zero, v, h1);
        let zero_v = self.mk_add(zero, v);
        let v_zero = self.mk_add(v, zero);
        let s5 = self.add_comm_eq(zero, v);
        let s6 = self.add_zero_eq(v);
        let t01 = self.eq_trans(u, u_zero, u_cv, s0, s1);
        let t02 = self.eq_trans(u, u_cv, uc_v, t01, s2);
        let t03 = self.eq_trans(u, uc_v, cu_v, t02, s3);
        let t04 = self.eq_trans(u, cu_v, zero_v, t03, s4);
        let t05 = self.eq_trans(u, zero_v, v_zero, t04, s5);
        self.eq_trans(u, v_zero, v, t05, s6)
    }

    /// `neg_neg z : Eq Z (neg (neg z)) z`.
    fn neg_neg_eq(&mut self, z: ExprId) -> ExprId {
        let nz = self.mk_neg(z);
        let nnz = self.mk_neg(nz);
        let zero = self.mk_zero();
        let add_z_nz = self.mk_add(z, nz);
        let add_nz_z = self.mk_add(nz, z);
        let h1 = {
            let comm = self.add_comm_eq(nz, z);
            let an = self.add_neg_eq(z);
            self.eq_trans(add_nz_z, add_z_nz, zero, comm, an)
        };
        let h2 = self.add_neg_eq(nz);
        let z_eq_nnz = self.add_left_cancel_eq(nz, z, nnz, h1, h2);
        self.eq_symm(z, nnz, z_eq_nnz)
    }

    /// `neg_add a b : Eq Z (neg (add a b)) (add (neg a)(neg b))`. Derived:
    /// `add (neg a)(neg b)` and `neg (add a b)` are both additive inverses of
    /// `add a b`; inverse-uniqueness identifies them.
    fn neg_add_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let nb = self.mk_neg(b);
        let ab = self.mk_add(a, b);
        let na_nb = self.mk_add(na, nb); // (-a)+(-b)
        let zero = self.mk_zero();
        // inv1 : add (add a b) (add (neg a)(neg b)) = zero.
        let inv1 = {
            let assoc0 = self.add_assoc_eq(a, b, na_nb); // (a+b)+T = a+(b+T)
            let ab_t = self.mk_add(ab, na_nb); // (a+b)+T
            let b_t = self.mk_add(b, na_nb); // b+T
            let a_bt = self.mk_add(a, b_t); // a+(b+T)
            // inner: b+T = -a.
            let assoc1 = self.add_assoc_eq(b, na, nb); // (b+(-a))+(-b) = b+((-a)+(-b))
            let b_na = self.mk_add(b, na); // b+(-a)
            let bna_nb = self.mk_add(b_na, nb); // (b+(-a))+(-b)
            let s1 = self.eq_symm(bna_nb, b_t, assoc1); // b+T = (b+(-a))+(-b)
            let na_b = self.mk_add(na, b); // (-a)+b
            let comm1 = self.add_comm_eq(b, na); // b+(-a) = (-a)+b
            let s2 = self.congr_add_left(b_na, na_b, nb, comm1); // (b+(-a))+(-b) = ((-a)+b)+(-b)
            let nab_nb = self.mk_add(na_b, nb); // ((-a)+b)+(-b)
            let assoc2 = self.add_assoc_eq(na, b, nb); // ((-a)+b)+(-b) = (-a)+(b+(-b))
            let b_nb = self.mk_add(b, nb); // b+(-b)
            let na_bnb = self.mk_add(na, b_nb); // (-a)+(b+(-b))
            let an_b = self.add_neg_eq(b); // b+(-b) = zero
            let na_zero = self.mk_add(na, zero); // (-a)+zero
            let s3 = self.congr_add_right(na, b_nb, zero, an_b); // (-a)+(b+(-b)) = (-a)+zero
            let s4 = self.add_zero_eq(na); // (-a)+zero = -a
            let i01 = self.eq_trans(b_t, bna_nb, nab_nb, s1, s2);
            let i02 = self.eq_trans(b_t, nab_nb, na_bnb, i01, assoc2);
            let i03 = self.eq_trans(b_t, na_bnb, na_zero, i02, s3);
            let inner = self.eq_trans(b_t, na_zero, na, i03, s4); // b+T = -a
            let a_na = self.mk_add(a, na); // a+(-a)
            let lift = self.congr_add_right(a, b_t, na, inner); // a+(b+T) = a+(-a)
            let an_a = self.add_neg_eq(a); // a+(-a) = zero
            let c01 = self.eq_trans(ab_t, a_bt, a_na, assoc0, lift);
            self.eq_trans(ab_t, a_na, zero, c01, an_a)
        };
        // inv2 : add (add a b) (neg (add a b)) = zero.
        let inv2 = self.add_neg_eq(ab);
        let neg_ab = self.mk_neg(ab);
        let u_eq_v = self.add_left_cancel_eq(ab, na_nb, neg_ab, inv1, inv2); // (-a)+(-b) = neg(a+b)
        self.eq_symm(na_nb, neg_ab, u_eq_v) // neg(a+b) = (-a)+(-b)
    }

    /// `mul_neg_right a b : Eq Z (mul a (neg b)) (neg (mul a b))`.
    fn mul_neg_right_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let nb = self.mk_neg(b);
        let ab = self.mk_mul(a, b);
        let a_nb = self.mk_mul(a, nb);
        let zero = self.mk_zero();
        let b_nb = self.mk_add(b, nb);
        let a_bnb = self.mk_mul(a, b_nb);
        let sum = self.mk_add(ab, a_nb);
        let inv1 = {
            let ld = self.left_distrib_eq(a, b, nb);
            let an = self.add_neg_eq(b);
            let cong = self.congr_mul_right(a, b_nb, zero, an);
            let mz = self.mul_zero_eq(a);
            let a_zero = self.mk_mul(a, zero);
            let lhs_zero = self.eq_trans(a_bnb, a_zero, zero, cong, mz);
            let sum_to_lhs = self.eq_symm(a_bnb, sum, ld);
            self.eq_trans(sum, a_bnb, zero, sum_to_lhs, lhs_zero)
        };
        let inv2 = self.add_neg_eq(ab);
        let neg_ab = self.mk_neg(ab);
        self.add_left_cancel_eq(ab, a_nb, neg_ab, inv1, inv2)
    }

    /// `mul_neg_left a b : Eq Z (mul (neg a) b) (neg (mul a b))`.
    fn mul_neg_left_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let na_b = self.mk_mul(na, b);
        let b_na = self.mk_mul(b, na);
        let ba = self.mk_mul(b, a);
        let ab = self.mk_mul(a, b);
        let comm1 = self.mul_comm_eq(na, b);
        let mnr = self.mul_neg_right_eq(b, a);
        let neg_ba = self.mk_neg(ba);
        let comm2 = self.mul_comm_eq(b, a);
        let neg_ab = self.mk_neg(ab);
        let neg_cong = self.congr_neg(ba, ab, comm2);
        let t01 = self.eq_trans(na_b, b_na, neg_ba, comm1, mnr);
        self.eq_trans(na_b, neg_ba, neg_ab, t01, neg_cong)
    }

    /// `neg_mul_neg a b : Eq Z (mul (neg a)(neg b)) (mul a b)`.
    fn neg_mul_neg_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let na_nb = {
            let nb = self.mk_neg(b);
            self.mk_mul(na, nb)
        };
        let na_b = self.mk_mul(na, b);
        let ab = self.mk_mul(a, b);
        let mnr = self.mul_neg_right_eq(na, b);
        let neg_na_b = self.mk_neg(na_b);
        let mnl = self.mul_neg_left_eq(a, b);
        let neg_ab = self.mk_neg(ab);
        let neg_neg_ab = self.mk_neg(neg_ab);
        let cong = self.congr_neg(na_b, neg_ab, mnl);
        let nn = self.neg_neg_eq(ab);
        let t01 = self.eq_trans(na_nb, neg_na_b, neg_neg_ab, mnr, cong);
        self.eq_trans(na_nb, neg_neg_ab, ab, t01, nn)
    }

    // ---- monomial / generator kernel encodings -----------------------------

    fn mono_expr(&mut self, m: IMono) -> ExprId {
        match m {
            IMono::Const => self.mk_one(),
            IMono::Lin(i) => {
                let name = self.var_const(i);
                self.kernel.const_(name, vec![])
            }
            IMono::Quad(i, j) => {
                let ni = self.var_const(i);
                let xi = self.kernel.const_(ni, vec![]);
                let nj = self.var_const(j);
                let xj = self.kernel.const_(nj, vec![]);
                self.mk_mul(xi, xj)
            }
        }
    }

    fn gen_expr(&mut self, g: IGen) -> ExprId {
        let m = self.mono_expr(g.mono);
        if g.neg { self.mk_neg(m) } else { m }
    }

    /// The canonical right-nested sum `g0 + (g1 + … + (g_{k-1} + zero))`; empty ⇒
    /// `zero`.
    fn gens_to_expr(&mut self, gens: &[IGen]) -> ExprId {
        let mut acc = self.mk_zero();
        for &g in gens.iter().rev() {
            let ge = self.gen_expr(g);
            acc = self.mk_add(ge, acc);
        }
        acc
    }

    // ---- additive normalizer (sort + cancel) -------------------------------

    fn lift_tail_rewrite(
        &mut self,
        prefix: &[IGen],
        tail: &[IGen],
        tail2: &[IGen],
        mut proof: ExprId,
    ) -> ExprId {
        for k in (0..prefix.len()).rev() {
            let g = self.gen_expr(prefix[k]);
            let mut sub_tail: Vec<IGen> = prefix[k + 1..].to_vec();
            sub_tail.extend_from_slice(tail);
            let mut sub_tail2: Vec<IGen> = prefix[k + 1..].to_vec();
            sub_tail2.extend_from_slice(tail2);
            let t = self.gens_to_expr(&sub_tail);
            let t2 = self.gens_to_expr(&sub_tail2);
            proof = self.congr_add_right(g, t, t2, proof);
        }
        proof
    }

    fn swap_head_eq(&mut self, g0: IGen, g1: IGen, tail: &[IGen]) -> ExprId {
        let e0 = self.gen_expr(g0);
        let e1 = self.gen_expr(g1);
        let t = self.gens_to_expr(tail);
        let assoc1 = self.add_assoc_eq(e0, e1, t);
        let lhs = {
            let inner = self.mk_add(e1, t);
            self.mk_add(e0, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e0, e1);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm(mid1, lhs, assoc1);
        let comm = self.add_comm_eq(e0, e1);
        let e0e1 = self.mk_add(e0, e1);
        let e1e0 = self.mk_add(e1, e0);
        let step2 = self.congr_add_left(e0e1, e1e0, t, comm);
        let step3 = self.add_assoc_eq(e1, e0, t);
        let mid2 = self.mk_add(e1e0, t);
        let rhs = {
            let inner = self.mk_add(e0, t);
            self.mk_add(e1, inner)
        };
        let t01 = self.eq_trans(lhs, mid1, mid2, step1, step2);
        self.eq_trans(lhs, mid2, rhs, t01, step3)
    }

    fn cancel_head_eq(&mut self, g: IGen, tail: &[IGen]) -> ExprId {
        let gn = g.negate();
        let e = self.gen_expr(g);
        let en = self.gen_expr(gn);
        let t = self.gens_to_expr(tail);
        let assoc = self.add_assoc_eq(e, en, t);
        let lhs = {
            let inner = self.mk_add(en, t);
            self.mk_add(e, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e, en);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm(mid1, lhs, assoc);
        let e_en = self.mk_add(e, en);
        let e_e_en_zero = if g.neg {
            let p = en;
            let np = e;
            let comm = self.add_comm_eq(np, p);
            let an = self.add_neg_eq(p);
            let lhs_c = self.mk_add(np, p);
            let mid_c = self.mk_add(p, np);
            let zero = self.mk_zero();
            self.eq_trans(lhs_c, mid_c, zero, comm, an)
        } else {
            self.add_neg_eq(e)
        };
        let zero = self.mk_zero();
        let step2 = self.congr_add_left(e_en, zero, t, e_e_en_zero);
        let comm0 = self.add_comm_eq(zero, t);
        let addz = self.add_zero_eq(t);
        let zt = self.mk_add(zero, t);
        let tz = self.mk_add(t, zero);
        let step3 = self.eq_trans(zt, tz, t, comm0, addz);
        let t01 = self.eq_trans(lhs, mid1, zt, step1, step2);
        self.eq_trans(lhs, zt, t, t01, step3)
    }

    /// Normalize a generator list to canonical (sorted + cancelled) form, with a
    /// proof `Eq Z (gens_to_expr gens) (gens_to_expr canonical)`.
    fn normalize_gens(&mut self, gens: &[IGen]) -> (Vec<IGen>, ExprId) {
        let mut cur: Vec<IGen> = gens.to_vec();
        let start = self.gens_to_expr(&cur);
        let mut proof = self.eq_refl(start);
        loop {
            let mut action: Option<(usize, bool)> = None;
            for i in 0..cur.len().saturating_sub(1) {
                if cur[i].negate() == cur[i + 1] {
                    action = Some((i, true));
                    break;
                }
                if cur[i].sort_key() > cur[i + 1].sort_key() {
                    action = Some((i, false));
                    break;
                }
            }
            let Some((i, is_cancel)) = action else {
                break;
            };
            let prefix = cur[..i].to_vec();
            let before = self.gens_to_expr(&cur);
            if is_cancel {
                let g = cur[i];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.cancel_head_eq(g, &tail);
                let mut from_tail = vec![g, g.negate()];
                from_tail.extend_from_slice(&tail);
                let lifted = self.lift_tail_rewrite(&prefix, &from_tail, &tail, head_proof);
                let mut next = prefix.clone();
                next.extend_from_slice(&tail);
                let after = self.gens_to_expr(&next);
                proof = self.eq_trans(start, before, after, proof, lifted);
                cur = next;
            } else {
                let g0 = cur[i];
                let g1 = cur[i + 1];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.swap_head_eq(g0, g1, &tail);
                let mut from_tail = vec![g0, g1];
                from_tail.extend_from_slice(&tail);
                let mut to_tail = vec![g1, g0];
                to_tail.extend_from_slice(&tail);
                let lifted = self.lift_tail_rewrite(&prefix, &from_tail, &to_tail, head_proof);
                let mut next = prefix.clone();
                next.push(g1);
                next.push(g0);
                next.extend_from_slice(&tail);
                let after = self.gens_to_expr(&next);
                proof = self.eq_trans(start, before, after, proof, lifted);
                cur = next;
            }
        }
        (cur, proof)
    }

    /// Prove `Eq Z (add canonA canonB) (gens_to_expr(gensA ++ gensB))`.
    fn append_eq(&mut self, gens_a: &[IGen], gens_b: &[IGen]) -> ExprId {
        let canon_b = self.gens_to_expr(gens_b);
        if gens_a.is_empty() {
            let zero = self.mk_zero();
            let comm = self.add_comm_eq(zero, canon_b);
            let addz = self.add_zero_eq(canon_b);
            let zt = self.mk_add(zero, canon_b);
            let tz = self.mk_add(canon_b, zero);
            return self.eq_trans(zt, tz, canon_b, comm, addz);
        }
        let g = self.gen_expr(gens_a[0]);
        let rest = gens_a[1..].to_vec();
        let canon_rest = self.gens_to_expr(&rest);
        let assoc = self.add_assoc_eq(g, canon_rest, canon_b);
        let lhs = {
            let ca = self.mk_add(g, canon_rest);
            self.mk_add(ca, canon_b)
        };
        let mid = {
            let inner = self.mk_add(canon_rest, canon_b);
            self.mk_add(g, inner)
        };
        let rec = self.append_eq(&rest, gens_b);
        let mut rest_b: Vec<IGen> = rest.clone();
        rest_b.extend_from_slice(gens_b);
        let rest_b_expr = self.gens_to_expr(&rest_b);
        let inner_from = self.mk_add(canon_rest, canon_b);
        let step2 = self.congr_add_right(g, inner_from, rest_b_expr, rec);
        let rhs = self.mk_add(g, rest_b_expr);
        self.eq_trans(lhs, mid, rhs, assoc, step2)
    }

    /// Prove `Eq Z (neg (gens_to_expr gens)) (gens_to_expr neg_gens)`.
    fn neg_gens_eq(&mut self, gens: &[IGen]) -> ExprId {
        let inner = self.gens_to_expr(gens);
        let neg_inner = self.mk_neg(inner);
        let Some((&head, tail)) = gens.split_first() else {
            // neg zero = zero.
            let zero = self.mk_zero();
            let nz = self.mk_neg(zero);
            let an = self.add_neg_eq(zero);
            let z_nz = self.mk_add(zero, nz);
            let comm = self.add_comm_eq(zero, nz);
            let nz_z = self.mk_add(nz, zero);
            let addz = self.add_zero_eq(nz);
            let s0 = self.eq_symm(nz_z, nz, addz);
            let comm_sym = self.eq_symm(z_nz, nz_z, comm);
            let t01 = self.eq_trans(nz, nz_z, z_nz, s0, comm_sym);
            return self.eq_trans(nz, z_nz, zero, t01, an);
        };
        let head_e = self.gen_expr(head);
        let canon_tail = self.gens_to_expr(tail);
        let na = self.neg_add_eq(head_e, canon_tail);
        let neg_head = self.mk_neg(head_e);
        let neg_tail = self.mk_neg(canon_tail);
        let na_nt = self.mk_add(neg_head, neg_tail);
        let head_neg_gen = head.negate();
        let head_neg_e = self.gen_expr(head_neg_gen);
        let neg_head_eq = if head.neg {
            self.neg_neg_eq(head_neg_e)
        } else {
            self.eq_refl(neg_head)
        };
        let rec = self.neg_gens_eq(tail);
        let neg_tail_gens: Vec<IGen> = tail.iter().map(|g| g.negate()).collect();
        let neg_tail_canon = self.gens_to_expr(&neg_tail_gens);
        let cong_l = self.congr_add_left(neg_head, head_neg_e, neg_tail, neg_head_eq);
        let mid = self.mk_add(head_neg_e, neg_tail);
        let cong_r = self.congr_add_right(head_neg_e, neg_tail, neg_tail_canon, rec);
        let target = self.mk_add(head_neg_e, neg_tail_canon);
        let cong = self.eq_trans(na_nt, mid, target, cong_l, cong_r);
        self.eq_trans(neg_inner, na_nt, target, na, cong)
    }

    // ---- multiplicative distribution ---------------------------------------

    /// `Eq Z (mul (mono_expr a)(mono_expr b)) (mono_expr out)`. `None` if either
    /// factor is quadratic (product degree ≥ 3 — out of scope).
    fn mul_base_mono_eq(&mut self, a: IMono, b: IMono) -> Option<(IMono, ExprId)> {
        match (a, b) {
            (IMono::Quad(..), _) | (_, IMono::Quad(..)) => None,
            (IMono::Const, IMono::Const) => {
                let one = self.mk_one();
                let mo = self.mul_one_eq(one);
                Some((IMono::Const, mo))
            }
            (IMono::Const, other) | (other, IMono::Const) => {
                let one = self.mk_one();
                let ve = self.mono_expr(other);
                let (le, re, is_one_left) = if matches!(a, IMono::Const) {
                    (one, ve, true)
                } else {
                    (ve, one, false)
                };
                let lhs = self.mk_mul(le, re);
                let eq = if is_one_left {
                    let comm = self.mul_comm_eq(one, ve);
                    let v_one = self.mk_mul(ve, one);
                    let mo = self.mul_one_eq(ve);
                    self.eq_trans(lhs, v_one, ve, comm, mo)
                } else {
                    self.mul_one_eq(ve)
                };
                Some((other, eq))
            }
            (IMono::Lin(i), IMono::Lin(j)) => {
                let xi = self.mono_expr(IMono::Lin(i));
                let xj = self.mono_expr(IMono::Lin(j));
                let lhs = self.mk_mul(xi, xj);
                let out = IMono::quad(i, j);
                if i <= j {
                    Some((out, self.eq_refl(lhs)))
                } else {
                    let comm = self.mul_comm_eq(xi, xj);
                    Some((out, comm))
                }
            }
        }
    }

    /// `Eq Z (mul (gen_expr a)(gen_expr b)) (gen_expr out)`. `None` on a quadratic
    /// product.
    fn mul_gen_eq(&mut self, a: IGen, b: IGen) -> Option<(IGen, ExprId)> {
        let (out_mono, base_eq) = self.mul_base_mono_eq(a.mono, b.mono)?;
        let ae = self.mono_expr(a.mono);
        let be = self.mono_expr(b.mono);
        let out_e = self.mono_expr(out_mono);
        let out_neg = a.neg ^ b.neg;
        let out_gen = IGen {
            mono: out_mono,
            neg: out_neg,
        };
        let lhs_a = if a.neg { self.mk_neg(ae) } else { ae };
        let lhs_b = if b.neg { self.mk_neg(be) } else { be };
        let lhs = self.mk_mul(lhs_a, lhs_b);
        let ab = self.mk_mul(ae, be);
        let proof = match (a.neg, b.neg) {
            (false, false) => base_eq,
            (true, false) => {
                let mnl = self.mul_neg_left_eq(ae, be);
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq);
                self.eq_trans(lhs, neg_ab, neg_out, mnl, cong)
            }
            (false, true) => {
                let mnr = self.mul_neg_right_eq(ae, be);
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq);
                self.eq_trans(lhs, neg_ab, neg_out, mnr, cong)
            }
            (true, true) => {
                let nmn = self.neg_mul_neg_eq(ae, be);
                self.eq_trans(lhs, ab, out_e, nmn, base_eq)
            }
        };
        Some((out_gen, proof))
    }

    /// `Eq Z (mul (gen_expr g)(gens_to_expr bs)) (gens_to_expr out)`.
    fn mul_gen_into_list_eq(&mut self, g: IGen, bs: &[IGen]) -> Option<(Vec<IGen>, ExprId)> {
        let ge = self.gen_expr(g);
        let bs_canon = self.gens_to_expr(bs);
        let lhs = self.mk_mul(ge, bs_canon);
        let Some((&b0, rest)) = bs.split_first() else {
            let mz = self.mul_zero_eq(ge);
            return Some((Vec::new(), mz));
        };
        let b0e = self.gen_expr(b0);
        let rest_canon = self.gens_to_expr(rest);
        let ld = self.left_distrib_eq(ge, b0e, rest_canon);
        let ge_b0 = self.mk_mul(ge, b0e);
        let ge_rest = self.mk_mul(ge, rest_canon);
        let sum = self.mk_add(ge_b0, ge_rest);
        let (prod0, head_eq) = self.mul_gen_eq(g, b0)?;
        let prod0_e = self.gen_expr(prod0);
        let (out_rest, rest_eq) = self.mul_gen_into_list_eq(g, rest)?;
        let out_rest_canon = self.gens_to_expr(&out_rest);
        let cong_l = self.congr_add_left(ge_b0, prod0_e, ge_rest, head_eq);
        let mid = self.mk_add(prod0_e, ge_rest);
        let cong_r = self.congr_add_right(prod0_e, ge_rest, out_rest_canon, rest_eq);
        let target = self.mk_add(prod0_e, out_rest_canon);
        let cong = self.eq_trans(sum, mid, target, cong_l, cong_r);
        let full = self.eq_trans(lhs, sum, target, ld, cong);
        let mut out = vec![prod0];
        out.extend_from_slice(&out_rest);
        Some((out, full))
    }

    /// `Eq Z (mul as_canon bs_canon) (gens_to_expr out)` — full distribution.
    fn mul_lists_eq(&mut self, a_gens: &[IGen], b_gens: &[IGen]) -> Option<(Vec<IGen>, ExprId)> {
        let a_canon = self.gens_to_expr(a_gens);
        let b_canon = self.gens_to_expr(b_gens);
        let lhs = self.mk_mul(a_canon, b_canon);
        let Some((&a0, rest)) = a_gens.split_first() else {
            let comm = self.mul_comm_eq(a_canon, b_canon);
            let b_zero = self.mk_mul(b_canon, a_canon);
            let mz = self.mul_zero_eq(b_canon);
            let zero = self.mk_zero();
            let eq = self.eq_trans(lhs, b_zero, zero, comm, mz);
            return Some((Vec::new(), eq));
        };
        let a0e = self.gen_expr(a0);
        let rest_canon = self.gens_to_expr(rest);
        let add_a = self.mk_add(a0e, rest_canon);
        let comm0 = self.mul_comm_eq(add_a, b_canon);
        let b_adda = self.mk_mul(b_canon, add_a);
        let ld = self.left_distrib_eq(b_canon, a0e, rest_canon);
        let b_a0 = self.mk_mul(b_canon, a0e);
        let b_rest = self.mk_mul(b_canon, rest_canon);
        let sum_b = self.mk_add(b_a0, b_rest);
        let comm_h = self.mul_comm_eq(b_canon, a0e);
        let a0_b = self.mk_mul(a0e, b_canon);
        let (head_out, head_dist) = self.mul_gen_into_list_eq(a0, b_gens)?;
        let head_out_canon = self.gens_to_expr(&head_out);
        let head_eq = self.eq_trans(b_a0, a0_b, head_out_canon, comm_h, head_dist);
        let (tail_out, tail_inner_eq) = self.mul_lists_eq(rest, b_gens)?;
        let tail_out_canon = self.gens_to_expr(&tail_out);
        let comm_t = self.mul_comm_eq(b_canon, rest_canon);
        let rest_b = self.mk_mul(rest_canon, b_canon);
        let tail_eq = self.eq_trans(b_rest, rest_b, tail_out_canon, comm_t, tail_inner_eq);
        let cong_l = self.congr_add_left(b_a0, head_out_canon, b_rest, head_eq);
        let mid = self.mk_add(head_out_canon, b_rest);
        let cong_r = self.congr_add_right(head_out_canon, b_rest, tail_out_canon, tail_eq);
        let appended = self.append_eq(&head_out, &tail_out);
        let mut out: Vec<IGen> = head_out.clone();
        out.extend_from_slice(&tail_out);
        let out_canon = self.gens_to_expr(&out);
        let pre_target = self.mk_add(head_out_canon, tail_out_canon);
        let cong = self.eq_trans(sum_b, mid, pre_target, cong_l, cong_r);
        let t01 = self.eq_trans(lhs, b_adda, sum_b, comm0, ld);
        let t02 = self.eq_trans(lhs, sum_b, pre_target, t01, cong);
        let full = self.eq_trans(lhs, pre_target, out_canon, t02, appended);
        Some((out, full))
    }

    // ---- the ring normalizer (the public entry into the engine) ------------

    /// Normalize a [`ZExpr`] into a canonical signed-generator sum: returns
    /// `(gens, kernel_expr, proof)` with `proof : Eq Z kernel_expr (gens_to_expr
    /// gens)` and `gens` SORTED-AND-CANCELLED. `None` (decline) on a degree-≥3
    /// subproduct.
    fn normalize(&mut self, expr: &ZExpr) -> Option<(Vec<IGen>, ExprId, ExprId)> {
        let (raw_gens, kernel_expr, raw_proof) = self.normalize_raw(expr)?;
        let (canon_gens, sort_proof) = self.normalize_gens(&raw_gens);
        let raw_canon = self.gens_to_expr(&raw_gens);
        let canon = self.gens_to_expr(&canon_gens);
        let proof = self.eq_trans(kernel_expr, raw_canon, canon, raw_proof, sort_proof);
        Some((canon_gens, kernel_expr, proof))
    }

    fn normalize_raw(&mut self, expr: &ZExpr) -> Option<(Vec<IGen>, ExprId, ExprId)> {
        match expr {
            ZExpr::Var(i) => {
                let name = self.var_const(*i);
                let xe = self.kernel.const_(name, vec![]);
                let zero = self.mk_zero();
                let xz = self.mk_add(xe, zero);
                let az = self.add_zero_eq(xe);
                let proof = self.eq_symm(xz, xe, az);
                Some((vec![IGen::pos(IMono::Lin(*i))], xe, proof))
            }
            ZExpr::One => {
                let one_e = self.mk_one();
                let zero = self.mk_zero();
                let oz = self.mk_add(one_e, zero);
                let az = self.add_zero_eq(one_e);
                let proof = self.eq_symm(oz, one_e, az);
                Some((vec![IGen::pos(IMono::Const)], one_e, proof))
            }
            ZExpr::Zero => {
                // zero canonicalizes to the empty gen list; gens_to_expr([]) = zero,
                // so the proof is refl.
                let zero = self.mk_zero();
                let proof = self.eq_refl(zero);
                Some((Vec::new(), zero, proof))
            }
            ZExpr::Neg(a) => {
                let (a_gens, a_e, a_proof) = self.normalize_raw(a)?;
                let neg_e = self.mk_neg(a_e);
                let a_canon = self.gens_to_expr(&a_gens);
                let cong = self.congr_neg(a_e, a_canon, a_proof);
                let neg_a_canon = self.mk_neg(a_canon);
                let neg_gens: Vec<IGen> = a_gens.iter().map(|g| g.negate()).collect();
                let neg_gens_eq = self.neg_gens_eq(&a_gens);
                let out_canon = self.gens_to_expr(&neg_gens);
                let proof = self.eq_trans(neg_e, neg_a_canon, out_canon, cong, neg_gens_eq);
                Some((neg_gens, neg_e, proof))
            }
            ZExpr::Add(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_raw(b)?;
                let add_e = self.mk_add(a_e, b_e);
                let a_canon = self.gens_to_expr(&a_gens);
                let b_canon = self.gens_to_expr(&b_gens);
                let cong_l = self.congr_add_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_add(a_canon, b_e);
                let cong_r = self.congr_add_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_add(a_canon, b_canon);
                let cong = self.eq_trans(add_e, mid, ab_canon, cong_l, cong_r);
                let appended = self.append_eq(&a_gens, &b_gens);
                let mut out: Vec<IGen> = a_gens.clone();
                out.extend_from_slice(&b_gens);
                let out_canon = self.gens_to_expr(&out);
                let proof = self.eq_trans(add_e, ab_canon, out_canon, cong, appended);
                Some((out, add_e, proof))
            }
            ZExpr::Mul(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_raw(b)?;
                let mul_e = self.mk_mul(a_e, b_e);
                let a_canon = self.gens_to_expr(&a_gens);
                let b_canon = self.gens_to_expr(&b_gens);
                let cong_l = self.congr_mul_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_mul(a_canon, b_e);
                let cong_r = self.congr_mul_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_mul(a_canon, b_canon);
                let cong = self.eq_trans(mul_e, mid, ab_canon, cong_l, cong_r);
                let (out, dist) = self.mul_lists_eq(&a_gens, &b_gens)?;
                let out_canon = self.gens_to_expr(&out);
                let proof = self.eq_trans(mul_e, ab_canon, out_canon, cong, dist);
                Some((out, mul_e, proof))
            }
        }
    }

    // ---- order helpers over Z ----------------------------------------------

    /// `le_refl a : le a a`.
    fn le_refl_app(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.le_refl, vec![]);
        self.kernel.app(ax, a)
    }

    /// `mul_le_mul_of_nonneg_left c a b h1 h2 : le (mul c a)(mul c b)` from
    /// `h1 : le zero c`, `h2 : le a b`.
    fn mul_le_mul_left_app(
        &mut self,
        c: ExprId,
        a: ExprId,
        b: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self
            .kernel
            .const_(self.int.mul_le_mul_of_nonneg_left, vec![]);
        let e = self.kernel.app(ax, c);
        let e = self.kernel.app(e, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `le_of_lt a b h : le a b` from `h : lt a b`.
    fn le_of_lt_app(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, h)
    }

    /// `lt_of_le_of_lt a b c h1 h2 : lt a c` from `h1 : le a b`, `h2 : lt b c`.
    fn lt_of_le_of_lt_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.int.lt_of_le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `lt_of_lt_of_le a b c h1 h2 : lt a c` from `h1 : lt a b`, `h2 : le b c`.
    fn lt_of_lt_of_le_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.int.lt_of_lt_of_le, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `lt_of_le_of_ne a b h_le h_ne : lt a b` from `h_le : le a b`,
    /// `h_ne : Not (Eq Z a b)`.
    fn lt_of_le_of_ne_app(&mut self, a: ExprId, b: ExprId, h_le: ExprId, h_ne: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.lt_of_le_of_ne, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, h_le);
        self.kernel.app(e, h_ne)
    }

    /// Cast the left operand of an `le`: `h_le : le l r`, `h_eq : Eq Z l l'` ⇒
    /// `le l' r`.
    fn le_cast_left(
        &mut self,
        l: ExprId,
        lp: ExprId,
        r: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_x_r = self.mk_le(x1, r);
            let x0 = self.kernel.bvar(0);
            let eq_l_x = self.mk_eq(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, le_x_r, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport(l, motive, h_le, lp, h_eq)
    }

    /// Cast the right operand of an `le`: `h_le : le l r`, `h_eq : Eq Z r r'` ⇒
    /// `le l r'`.
    fn le_cast_right(
        &mut self,
        l: ExprId,
        r: ExprId,
        rp: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_l_x = self.mk_le(l, x1);
            let x0 = self.kernel.bvar(0);
            let eq_r_x = self.mk_eq(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, le_l_x, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport(r, motive, h_le, rp, h_eq)
    }

    /// `And.intro P Q hp hq : And P Q` (the logic prelude's explicit-Prop form).
    fn and_intro(&mut self, p: ExprId, q: ExprId, hp: ExprId, hq: ExprId) -> ExprId {
        let intro = self.kernel.const_(self.int.logic.and_intro, vec![]);
        let e = self.kernel.app(intro, p);
        let e = self.kernel.app(e, q);
        let e = self.kernel.app(e, hp);
        self.kernel.app(e, hq)
    }

    /// `no_int_between m (And.intro …) : False`.
    fn no_int_between_app(&mut self, m: ExprId, and_proof: ExprId) -> ExprId {
        let nib = self.kernel.const_(self.int.no_int_between, vec![]);
        let e = self.kernel.app(nib, m);
        self.kernel.app(e, and_proof)
    }
}

/// Encode an integer linear form `Σ_j c_j·x_j + k` (coefficients keyed by dense
/// variable index, plus a constant) as a [`ZExpr`]: a left-nested `add` over `|c_j|`
/// signed copies of each variable, then `|k|` signed `One`s. The empty form is
/// `intlit 0`. `None` if no atoms (a `0` constant with no vars) — handled by the
/// caller via [`IntReconstructCtx::mk_intlit`].
fn lin_to_zexpr(coeffs: &[(usize, i128)], constant: i128) -> Option<ZExpr> {
    let mut atoms: Vec<ZExpr> = Vec::new();
    for &(idx, c) in coeffs {
        if c == 0 {
            continue;
        }
        let count = c.unsigned_abs();
        for _ in 0..count {
            let atom = if c < 0 {
                ZExpr::Neg(Box::new(ZExpr::Var(idx)))
            } else {
                ZExpr::Var(idx)
            };
            atoms.push(atom);
        }
    }
    if constant != 0 {
        let count = constant.unsigned_abs();
        for _ in 0..count {
            let atom = if constant < 0 {
                ZExpr::Neg(Box::new(ZExpr::One))
            } else {
                ZExpr::One
            };
            atoms.push(atom);
        }
    }
    let mut iter = atoms.into_iter();
    let first = iter.next()?;
    let mut acc = first;
    for t in iter {
        acc = ZExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// The faithful [`ZExpr`] for an integer literal `n`: [`ZExpr::Zero`] for `0`, else
/// the `lin_to_zexpr` unit expansion. (Total: always `Some`-like, returns a value.)
fn intlit_zexpr(n: i128) -> ZExpr {
    if n == 0 {
        ZExpr::Zero
    } else {
        lin_to_zexpr(&[], n).expect("nonzero literal has atoms")
    }
}

/// The canonical generator list of a linear form `Σ c_j·x_j + k` (no proof): the
/// expected normal form (`|c_j|` signed `Lin(j)` per variable plus `|k|` signed
/// `Const`), sorted. Used to *check* a normalizer result agrees with the
/// certificate's claim.
fn lin_to_canon_gens(coeffs: &[(usize, i128)], constant: i128) -> Vec<IGen> {
    let mut gens: Vec<IGen> = Vec::new();
    // `coeffs` arrives ascending by index from the certificate (a BTreeMap-derived
    // Vec), so emitting variables then the constant yields the sorted canonical form.
    for &(idx, c) in coeffs {
        if c == 0 {
            continue;
        }
        let g = if c < 0 {
            IGen::pos(IMono::Lin(idx)).negate()
        } else {
            IGen::pos(IMono::Lin(idx))
        };
        for _ in 0..c.unsigned_abs() {
            gens.push(g);
        }
    }
    if constant != 0 {
        let g = if constant < 0 {
            IGen::pos(IMono::Const).negate()
        } else {
            IGen::pos(IMono::Const)
        };
        for _ in 0..constant.unsigned_abs() {
            gens.push(g);
        }
    }
    gens
}

/// A bound on coefficient magnitudes/repetition expanded into unit generators. The
/// reconstruction declines above this to keep the proof term bounded (the cap also
/// guards against pathological certificates blowing up the kernel term).
const DIO_UNIT_MAX: i128 = 4096;

/// **Reconstruct an integer Diophantine refutation to a kernel-checked Lean
/// `False`.** Runs the in-tree [`DiophantineCertificate`] decision on `assertions`;
/// on a refutation, reconstructs the integer-infeasibility argument over
/// [`IntPrelude`] and returns the assembled `False` proof term (already `infer` +
/// `def_eq False`-gated through the kernel).
///
/// Handles the main case `g = gcd(|combined_j|) > 0` (the certificate guarantees `g
/// ∤ constant`). The degenerate empty-`combined` row (`g = 0`, `0 = constant ≠ 0`)
/// is declined here.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when there is no Diophantine refutation,
/// the degenerate `g = 0` case, a coefficient/bound overflow, or a normalizer
/// mismatch (the certificate's claimed combined row does not canonicalize as
/// expected — never fabricated); [`ReconstructError::KernelRejected`] when the
/// assembled term does not kernel-check to `False`.
pub fn reconstruct_diophantine_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let (_, proof) = build_and_gate_diophantine(arena, assertions)?;
    Ok(proof)
}

/// The theorem name used for the exported Diophantine refutation Lean module.
const DIO_LEAN_THEOREM: &str = "axeyum_refutation";

/// **Like [`reconstruct_diophantine_proof`], but also renders a self-contained Lean
/// module** (`render_lean_module`) re-proving the refutation. A successful return
/// means the proof was emitted, kernel-checked to `False`, and rendered to
/// externally-checkable Lean source.
///
/// # Errors
///
/// Same as [`reconstruct_diophantine_proof`].
pub fn reconstruct_diophantine_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let (mut ctx, proof) = build_and_gate_diophantine(arena, assertions)?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    Ok(ctx
        .kernel()
        .render_lean_module(DIO_LEAN_THEOREM, false_, proof))
}

/// Shared core: run the Diophantine decision, build the `False` proof over a fresh
/// [`IntReconstructCtx`], and gate it through the kernel (`infer` + `def_eq False`).
/// Returns the context (carrying the full environment) and the gated proof term.
fn build_and_gate_diophantine(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<(IntReconstructCtx, ExprId), ReconstructError> {
    let Some((equalities, cert)) = prove_lia_unsat_by_diophantine_certified(arena, assertions)
    else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no Diophantine (integer-infeasibility) refutation for these assertions"
                .to_owned(),
        });
    };
    let mut ctx = IntReconstructCtx::new();
    let proof = ctx.build_diophantine_false(&equalities, &cert)?;
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "diophantine".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok((ctx, proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "diophantine".to_owned(),
            detail: "Diophantine refutation did not infer to False".to_owned(),
        })
    }
}

/// Map the certificate's [`SymbolId`] keys to dense `0..n` variable indices in a
/// deterministic (sorted) order, so the kernel encoding is stable.
fn dense_index_map(
    equalities: &[Equality],
    cert: &DiophantineCertificate,
) -> BTreeMap<SymbolId, usize> {
    let mut syms: std::collections::BTreeSet<SymbolId> = std::collections::BTreeSet::new();
    for eq in equalities {
        for &s in eq.coeffs.keys() {
            syms.insert(s);
        }
    }
    for &(s, _) in &cert.combined {
        syms.insert(s);
    }
    syms.into_iter().enumerate().map(|(i, s)| (s, i)).collect()
}

impl IntReconstructCtx {
    /// Declare a fresh hypothesis axiom `h : prop` and return its const proof.
    fn hyp_axiom(&mut self, prop: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name("hyp");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: prop,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "diophantine".to_owned(),
                detail: format!("hypothesis axiom did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    /// Emit the faithful kernel `Z`-encoding of a [`ZExpr`] (no proof). The kernel
    /// hash-conses, so this is the SAME `ExprId` [`Self::normalize`] carries as its
    /// `kernel_expr` for the same `ZExpr`.
    fn emit_zexpr(&mut self, expr: &ZExpr) -> ExprId {
        match expr {
            ZExpr::Var(i) => {
                let name = self.var_const(*i);
                self.kernel.const_(name, vec![])
            }
            ZExpr::One => self.mk_one(),
            ZExpr::Zero => self.mk_zero(),
            ZExpr::Neg(a) => {
                let ae = self.emit_zexpr(a);
                self.mk_neg(ae)
            }
            ZExpr::Add(a, b) => {
                let ae = self.emit_zexpr(a);
                let be = self.emit_zexpr(b);
                self.mk_add(ae, be)
            }
            ZExpr::Mul(a, b) => {
                let ae = self.emit_zexpr(a);
                let be = self.emit_zexpr(b);
                self.mk_mul(ae, be)
            }
        }
    }

    /// `Eq Z (intlit n) (gens_to_expr (canonical gens of n))` — bridge `mk_intlit`'s
    /// LEFT-nested encoding to the normalizer's RIGHT-nested canonical form, via the
    /// normalizer over the faithful `lin_to_zexpr` of `n` (which is the SAME
    /// left-nested term `mk_intlit` builds). For `n = 0` both sides are `zero` and
    /// the bridge is `refl`.
    fn intlit_eq_canon(&mut self, n: i128) -> ExprId {
        let lit = self.mk_intlit(n);
        if n == 0 {
            return self.eq_refl(lit);
        }
        let z = lin_to_zexpr(&[], n).expect("nonzero constant has atoms");
        let (gens, kexpr, proof) = self
            .normalize(&z)
            .expect("constant normalizer never declines (degree 0)");
        debug_assert_eq!(kexpr, lit, "mk_intlit and lin_to_zexpr must coincide");
        let canon = self.gens_to_expr(&gens);
        // proof : Eq Z kexpr canon ; kexpr == lit (hash-cons), so this is the bridge.
        let _ = canon;
        proof
    }

    /// Build a proof `lt zero K` where `K = gens_to_expr` of `n ≥ 1` `Const`
    /// generators (`one + (one + … + (one + zero))`). Partial-sum induction from
    /// `zero_lt_one`.
    fn lt_zero_ones(&mut self, n: i128) -> Result<ExprId, ReconstructError> {
        if n < 1 {
            return Err(ReconstructError::UnsupportedTerm {
                term: "lt_zero_ones requires n ≥ 1".to_owned(),
            });
        }
        let one = self.mk_one();
        let zero = self.mk_zero();
        let one_zero = self.mk_add(one, zero); // gens_to_expr([Const])
        let zlo = self.kernel.const_(self.int.zero_lt_one, vec![]); // lt zero one
        // cast rhs one → one+zero via symm(add_zero one).
        let addz = self.add_zero_eq(one); // add one zero = one
        let eq_one_onezero = self.eq_symm(one_zero, one, addz); // one = one+zero
        let mut acc = self.lt_cast_right(zero, one, one_zero, zlo, eq_one_onezero);
        let mut s_gens = vec![IGen::pos(IMono::Const)];
        for _ in 1..n {
            let s = self.gens_to_expr(&s_gens);
            let mut new_gens = vec![IGen::pos(IMono::Const)];
            new_gens.extend_from_slice(&s_gens);
            let _new_s = self.gens_to_expr(&new_gens); // one + S
            // le zero one (le_of_lt zero_lt_one).
            let le_zero_one = {
                let zlo2 = self.kernel.const_(self.int.zero_lt_one, vec![]);
                self.le_of_lt_app(zero, one, zlo2)
            };
            let le_s_s = self.le_refl_app(s); // le S S
            // add_le_add zero one S S : le (add zero S)(add one S).
            let combined = self.add_le_add_app(zero, one, s, s, le_zero_one, le_s_s);
            // cast lhs (add zero S) → S via add_comm + add_zero.
            let zs = self.mk_add(zero, s);
            let comm = self.add_comm_eq(zero, s); // add zero S = add S zero
            let sz = self.mk_add(s, zero);
            let addz2 = self.add_zero_eq(s); // add S zero = S
            let eq_zs_s = self.eq_trans(zs, sz, s, comm, addz2); // add zero S = S
            let one_s = self.mk_add(one, s); // add one S = one+S
            let le_s_one_s = self.le_cast_left(zs, s, one_s, combined, eq_zs_s); // le S (one+S)
            // lt zero S and le S (one+S) ⇒ lt zero (one+S).
            acc = self.lt_of_lt_of_le_app(zero, s, one_s, acc, le_s_one_s);
            s_gens = new_gens;
        }
        Ok(acc)
    }

    /// `add_le_add a b c d h1 h2 : le (add a c)(add b d)`.
    fn add_le_add_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.int.add_le_add, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// Cast the right operand of an `lt`: `h_lt : lt l r`, `h_eq : Eq Z r r'` ⇒
    /// `lt l r'`.
    fn lt_cast_right(
        &mut self,
        l: ExprId,
        r: ExprId,
        rp: ExprId,
        h_lt: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let lt_l_x = self.mk_lt(l, x1);
            let x0 = self.kernel.bvar(0);
            let eq_r_x = self.mk_eq(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, lt_l_x, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport(r, motive, h_lt, rp, h_eq)
    }

    /// `lt zero (intlit n)` for `n ≥ 1`. Bridges the canonical `one+…+zero` form of
    /// [`Self::lt_zero_ones`] back to the `mk_intlit` term.
    fn lt_zero_intlit(&mut self, n: i128) -> Result<ExprId, ReconstructError> {
        let lt_zero_canon = self.lt_zero_ones(n)?; // lt zero (gens_to_expr ones)
        let canon = {
            let gens: Vec<IGen> = (0..n).map(|_| IGen::pos(IMono::Const)).collect();
            self.gens_to_expr(&gens)
        };
        let lit = self.mk_intlit(n);
        let zero = self.mk_zero();
        // bridge : Eq Z (intlit n) canon ; cast lt zero canon → lt zero (intlit n).
        let bridge = self.intlit_eq_canon(n); // Eq Z lit canon
        let bridge_sym = self.eq_symm(lit, canon, bridge); // canon = lit
        Ok(self.lt_cast_right(zero, canon, lit, lt_zero_canon, bridge_sym))
    }

    /// `lt (intlit a)(intlit b)` for `0 ≤ a < b`. Derived: `b − a ≥ 1`, so
    /// `lt zero (intlit (b−a))`; add `intlit a` on the left of both sides
    /// (`add_lt_add_of_le_of_lt` with `le (intlit a)(intlit a)`), then renormalize
    /// `a + 0 → a` and `a + (b−a) → b`. To keep the proof small we instead use the
    /// ring fact directly: `lt a b ⇐ lt zero (b−a)` via casting.
    fn lt_intlit_intlit(&mut self, a: i128, b: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(a >= 0 && b > a);
        let diff = b - a;
        // h0 : lt zero (intlit diff).
        let h0 = self.lt_zero_intlit(diff)?;
        let zero = self.mk_zero();
        let a_lit = self.mk_intlit(a);
        let diff_lit = self.mk_intlit(diff);
        // h_le : le (intlit a)(intlit a)  (le_refl).
        let h_le = self.le_refl_app(a_lit);
        // add_lt_add_of_le_of_lt a a zero diff h_le h0 : lt (add a zero)(add a diff).
        let combined = self.add_lt_add_of_le_of_lt_app(a_lit, a_lit, zero, diff_lit, h_le, h0);
        // cast lhs (add a zero) → a via add_zero.
        let a_zero = self.mk_add(a_lit, zero);
        let a_diff = self.mk_add(a_lit, diff_lit);
        let addz = self.add_zero_eq(a_lit); // add a zero = a
        let lt_a_adiff = self.lt_cast_left(a_zero, a_lit, a_diff, combined, addz);
        // cast rhs (add a diff) → b : prove Eq Z (add (intlit a)(intlit diff)) (intlit b).
        let sum_eq_b = self.intlit_add_eq(a, diff, b)?; // Eq Z (add a diff) (intlit b)
        let b_lit = self.mk_intlit(b);
        Ok(self.lt_cast_right(a_lit, a_diff, b_lit, lt_a_adiff, sum_eq_b))
    }

    /// `add_lt_add_of_le_of_lt a b c d h1 h2 : lt (add a c)(add b d)`.
    fn add_lt_add_of_le_of_lt_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.int.add_lt_add_of_le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// Cast the left operand of an `lt`: `h_lt : lt l r`, `h_eq : Eq Z l l'` ⇒
    /// `lt l' r`.
    fn lt_cast_left(
        &mut self,
        l: ExprId,
        lp: ExprId,
        r: ExprId,
        h_lt: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let lt_x_r = self.mk_lt(x1, r);
            let x0 = self.kernel.bvar(0);
            let eq_l_x = self.mk_eq(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, lt_x_r, BinderInfo::Default);
            let z_ty = self.kernel.const_(self.int.z, vec![]);
            self.kernel.lam(anon, z_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport(l, motive, h_lt, lp, h_eq)
    }

    /// `lt_irrefl a : Not (lt a a)`.
    fn lt_irrefl_app(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.lt_irrefl, vec![]);
        self.kernel.app(ax, a)
    }

    /// `mul_one a : Eq Z (mul a one) a` already exists; this multiplies the literal
    /// `g·1` shape: prove `Eq Z (add (intlit a)(intlit b)) (intlit s)` when
    /// `a + b = s` (all ≥ 0 or the relevant signs), via the ring normalizer.
    fn intlit_add_eq(&mut self, a: i128, b: i128, s: i128) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, s);
        // Faithful ZExpr `add (intlit a)(intlit b)` and its normalized canonical. Both
        // operands are required nonzero by the only caller (`lt_intlit_intlit` with
        // `a = r ≥ 1`, `b = diff ≥ 1`); a zero operand is out of scope here.
        let (Some(za), Some(zb)) = (lin_to_zexpr(&[], a), lin_to_zexpr(&[], b)) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_add requires both operands nonzero".to_owned(),
            });
        };
        let sum_zexpr = ZExpr::Add(Box::new(za), Box::new(zb));
        let (gens, kexpr, proof) =
            self.normalize(&sum_zexpr)
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: "intlit_add normalizer declined".to_owned(),
                })?;
        let expected = lin_to_canon_gens(&[], s);
        if gens != expected {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_add did not canonicalize to the expected sum".to_owned(),
            });
        }
        // kexpr is the faithful `add (intlit a)(intlit b)` term (or the single literal
        // when one operand is 0 — those branches return the literal's faithful form).
        let canon = self.gens_to_expr(&gens);
        let s_lit = self.mk_intlit(s);
        let bridge = self.intlit_eq_canon(s); // Eq Z (intlit s) canon
        let bridge_sym = self.eq_symm(s_lit, canon, bridge); // canon = intlit s
        Ok(self.eq_trans(kexpr, canon, s_lit, proof, bridge_sym))
    }

    /// Sum the scaled hypotheses into `h_comb : Eq Z combined_expr (intlit constant)`.
    ///
    /// `combined_expr = Σ_j combined_j x_j` (canonical gens of `combined_dense`). The
    /// proof scales each `h_i : Eq Z L_i (intlit b_i)` by `λ_i` (signed repetition,
    /// via `congr_add` over copies and `congr_neg`), sums them (`congr_add`), and
    /// normalizes both sides; the normalizer's canonical forms must match
    /// `combined_dense` (LHS) and `intlit constant` (RHS), else we decline.
    #[allow(clippy::type_complexity, clippy::too_many_lines)]
    fn combine_equalities(
        &mut self,
        hyps: &[(ExprId, Vec<IGen>, ExprId, i128, ExprId)],
        multipliers: &[i128],
        combined_dense: &[(usize, i128)],
        constant: i128,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine combine declined: {d}"),
        };
        if hyps.len() != multipliers.len() {
            return Err(decline("multiplier/hyp count mismatch"));
        }
        // Build the scaled LHS / RHS ZExprs and a single Eq proof for the whole sum.
        // We accumulate `acc : Eq Z lhs_acc rhs_acc` where lhs_acc/rhs_acc are
        // right-built sums of the scaled terms.
        let mut acc: Option<(ExprId, ExprId, ExprId)> = None; // (lhs, rhs, proof)
        for (eq_idx, (l_expr, _l_gens, r_expr, _b_i, h)) in hyps.iter().enumerate() {
            let (l_expr, r_expr, h) = (*l_expr, *r_expr, *h);
            let lambda = multipliers[eq_idx];
            if lambda == 0 {
                continue;
            }
            // Scaled equality: Eq Z (λ·L_i)(λ·R_i). Build by repeating `h` |λ| times
            // under add, then negating if λ < 0.
            let (mut s_lhs, mut s_rhs, mut s_proof) = (l_expr, r_expr, h);
            let count = lambda.unsigned_abs();
            for _ in 1..count {
                // acc' = add acc base : Eq Z (add s_lhs L_i)(add s_rhs R_i).
                let new_lhs = self.mk_add(s_lhs, l_expr);
                let new_rhs = self.mk_add(s_rhs, r_expr);
                // congr: add s_lhs L_i = add s_rhs L_i (congr_add_left s_proof) then
                //        add s_rhs L_i = add s_rhs R_i (congr_add_right h).
                let mid = self.mk_add(s_rhs, l_expr);
                let cong_l = self.congr_add_left(s_lhs, s_rhs, l_expr, s_proof);
                let cong_r = self.congr_add_right(s_rhs, l_expr, r_expr, h);
                let p = self.eq_trans(new_lhs, mid, new_rhs, cong_l, cong_r);
                s_lhs = new_lhs;
                s_rhs = new_rhs;
                s_proof = p;
            }
            if lambda < 0 {
                let neg_lhs = self.mk_neg(s_lhs);
                let neg_rhs = self.mk_neg(s_rhs);
                let p = self.congr_neg(s_lhs, s_rhs, s_proof);
                s_lhs = neg_lhs;
                s_rhs = neg_rhs;
                s_proof = p;
            }
            acc = Some(match acc {
                None => (s_lhs, s_rhs, s_proof),
                Some((a_lhs, a_rhs, a_proof)) => {
                    let new_lhs = self.mk_add(a_lhs, s_lhs);
                    let new_rhs = self.mk_add(a_rhs, s_rhs);
                    let mid = self.mk_add(a_rhs, s_lhs);
                    let cong_l = self.congr_add_left(a_lhs, a_rhs, s_lhs, a_proof);
                    let cong_r = self.congr_add_right(a_rhs, s_lhs, s_rhs, s_proof);
                    let p = self.eq_trans(new_lhs, mid, new_rhs, cong_l, cong_r);
                    (new_lhs, new_rhs, p)
                }
            });
        }
        let Some((lhs_acc, rhs_acc, proof_acc)) = acc else {
            return Err(decline("all multipliers zero"));
        };
        // Normalize lhs_acc and rhs_acc; check they canonicalize to combined / constant.
        let (lhs_gens, _lhs_k, lhs_norm) = self
            .normalize_kernel(lhs_acc)
            .ok_or_else(|| decline("lhs normalizer declined"))?;
        let (rhs_gens, _rhs_k, rhs_norm) = self
            .normalize_kernel(rhs_acc)
            .ok_or_else(|| decline("rhs normalizer declined"))?;
        let expected_lhs = lin_to_canon_gens(combined_dense, 0);
        let expected_rhs = lin_to_canon_gens(&[], constant);
        if lhs_gens != expected_lhs {
            return Err(decline(
                "combined LHS did not canonicalize to Σ combined_j x_j",
            ));
        }
        if rhs_gens != expected_rhs {
            return Err(decline("combined RHS did not canonicalize to the constant"));
        }
        // We want `h_comb : Eq Z combined_faithful (intlit constant)`, where
        // `combined_faithful` is the FAITHFUL `lin_to_zexpr(combined_dense, 0)` form
        // (the same operand the step-3 reduction uses), NOT the right-nested canonical
        // form. We have:
        //   proof_acc           : Eq Z lhs_acc rhs_acc
        //   lhs_norm            : Eq Z lhs_acc lhs_canon
        //   rhs_norm            : Eq Z rhs_acc rhs_canon
        // and both lhs_acc and combined_faithful canonicalize to the SAME `lhs_gens`.
        let lhs_canon = self.gens_to_expr(&lhs_gens);
        let rhs_canon = self.gens_to_expr(&rhs_gens);
        // Faithful combined form and its own normalization to `lhs_canon`.
        let combined_faithful = match lin_to_zexpr(combined_dense, 0) {
            Some(z) => self.emit_zexpr(&z),
            None => return Err(decline("combined row empty")),
        };
        let (cf_gens, cf_kexpr, cf_norm) = self
            .normalize_kernel(combined_faithful)
            .ok_or_else(|| decline("combined faithful normalizer declined"))?;
        if cf_gens != expected_lhs {
            return Err(decline(
                "combined faithful did not canonicalize as expected",
            ));
        }
        debug_assert_eq!(cf_kexpr, combined_faithful);
        // cf_norm : Eq Z combined_faithful lhs_canon.
        // chain: combined_faithful = lhs_canon = lhs_acc = rhs_acc = rhs_canon = const.
        let lhs_canon_to_acc = self.eq_symm(lhs_acc, lhs_canon, lhs_norm); // lhs_canon = lhs_acc
        let cf_to_acc = self.eq_trans(
            combined_faithful,
            lhs_canon,
            lhs_acc,
            cf_norm,
            lhs_canon_to_acc,
        );
        let cf_to_rhs = self.eq_trans(combined_faithful, lhs_acc, rhs_acc, cf_to_acc, proof_acc);
        let cf_to_rcanon =
            self.eq_trans(combined_faithful, rhs_acc, rhs_canon, cf_to_rhs, rhs_norm);
        let const_lit = self.mk_intlit(constant);
        let const_bridge = self.intlit_eq_canon(constant); // Eq Z const_lit rhs_canon
        let rcanon_to_lit = self.eq_symm(const_lit, rhs_canon, const_bridge); // rhs_canon = const_lit
        Ok(self.eq_trans(
            combined_faithful,
            rhs_canon,
            const_lit,
            cf_to_rcanon,
            rcanon_to_lit,
        ))
    }

    /// Normalize a kernel `Z`-expression that is already a faithful `add`/`neg`/
    /// `var`/`one` tree (no `Mul` beyond what the gens encode), by reading it back
    /// into a [`ZExpr`] then calling [`Self::normalize`]. Returns the canonical gens,
    /// the (same) kernel expr, and the proof. We reconstruct the `ZExpr` from the
    /// kernel term's structure.
    fn normalize_kernel(&mut self, e: ExprId) -> Option<(Vec<IGen>, ExprId, ExprId)> {
        let z = self.kernel_expr_to_zexpr(e)?;
        let (gens, kexpr, proof) = self.normalize(&z)?;
        debug_assert_eq!(kexpr, e);
        Some((gens, kexpr, proof))
    }

    /// Read a faithful kernel `Z`-term back into a [`ZExpr`]. Recognizes `add`/`neg`/
    /// `mul` applications, the `one`/`zero` constants, and variable constants (mapped
    /// back through the `vars` table). `zero` becomes the empty-equivalent — but since
    /// our built terms never contain a bare `zero` leaf (intlit 0 only appears as the
    /// whole expr, handled by callers), a `zero` leaf is mapped to `add one (neg one)`
    /// would be wrong; instead we map `zero` to a degenerate that the normalizer
    /// handles: we never emit `zero` inside these accumulators, so `None` on `zero`.
    fn kernel_expr_to_zexpr(&self, e: ExprId) -> Option<ZExpr> {
        use axeyum_lean_kernel::ExprNode;
        match *self.kernel.expr_node(e) {
            ExprNode::Const(name, _) => {
                if name == self.int.one {
                    Some(ZExpr::One)
                } else if name == self.int.zero {
                    Some(ZExpr::Zero)
                } else {
                    self.vars
                        .iter()
                        .find_map(|(&i, &n)| if n == name { Some(ZExpr::Var(i)) } else { None })
                }
            }
            ExprNode::App(_, _) => {
                let (head, args) = self.app_spine(e);
                let ExprNode::Const(name, _) = *self.kernel.expr_node(head) else {
                    return None;
                };
                if name == self.int.add && args.len() == 2 {
                    let a = self.kernel_expr_to_zexpr(args[0])?;
                    let b = self.kernel_expr_to_zexpr(args[1])?;
                    Some(ZExpr::Add(Box::new(a), Box::new(b)))
                } else if name == self.int.mul && args.len() == 2 {
                    let a = self.kernel_expr_to_zexpr(args[0])?;
                    let b = self.kernel_expr_to_zexpr(args[1])?;
                    Some(ZExpr::Mul(Box::new(a), Box::new(b)))
                } else if name == self.int.neg && args.len() == 1 {
                    let a = self.kernel_expr_to_zexpr(args[0])?;
                    Some(ZExpr::Neg(Box::new(a)))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Collect an application spine `f a1 a2 … an` into `(f, [a1, …, an])`.
    fn app_spine(&self, e: ExprId) -> (ExprId, Vec<ExprId>) {
        use axeyum_lean_kernel::ExprNode;
        let mut args = Vec::new();
        let mut cur = e;
        while let ExprNode::App(f, a) = *self.kernel.expr_node(cur) {
            args.push(a);
            cur = f;
        }
        args.reverse();
        (cur, args)
    }

    /// Prove `m' < 1` from `gm : Eq Z (mul g_lit m') r_lit`, `h_g_pos : lt zero
    /// g_lit`, `h_r_lt_g : lt r_lit g_lit`.
    ///
    /// `le_total m' 1 → Or (le m' 1)(le 1 m')`; the `le 1 m'` branch contradicts
    /// (`g = g·1 ≤ g·m' = r < g`). After `Or.rec` we have `le m' 1`, strengthened to
    /// `lt m' 1` by `lt_of_le_of_ne` with `m' ≠ 1` (else `g·m' = g·1 = g ≠ r`).
    fn prove_m_prime_lt_one(
        &mut self,
        g_lit: ExprId,
        m_prime: ExprId,
        r_lit: ExprId,
        gm: ExprId,
        h_g_pos: ExprId,
        h_r_lt_g: ExprId,
    ) -> ExprId {
        let one = self.mk_one();
        let zero = self.mk_zero();
        // le_total m' one : Or (le m' one)(le one m').
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, m_prime);
            self.kernel.app(e, one)
        };
        let a_prop = self.mk_le(m_prime, one); // le m' one
        let b_prop = self.mk_le(one, m_prime); // le one m'
        // h_g_nonneg : le zero g_lit  (le_of_lt h_g_pos).
        let h_g_nonneg = self.le_of_lt_app(zero, g_lit, h_g_pos);
        // minor_inl : (le m' one) → le m' one  (identity lambda).
        let target = self.mk_le(m_prime, one);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        // minor_inr : (le one m') → le m' one  (derive le m' one from a contradiction).
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_one_mp = self.kernel.fvar(fid); // le one m'
            // mul_le_mul_of_nonneg_left g one m' h_g_nonneg h_le_one_mp : le (mul g one)(mul g m').
            let le_gone_gmp =
                self.mul_le_mul_left_app(g_lit, one, m_prime, h_g_nonneg, h_le_one_mp);
            // cast (mul g one) → g via mul_one.
            let g_one = self.mk_mul(g_lit, one);
            let mul_one = self.mul_one_eq(g_lit); // mul g one = g
            let gmp = self.mk_mul(g_lit, m_prime);
            let le_g_gmp = self.le_cast_left(g_one, g_lit, gmp, le_gone_gmp, mul_one); // le g (g·m')
            // cast (mul g m') → r via gm : Eq Z (mul g m') r.
            let le_g_r = self.le_cast_right(g_lit, gmp, r_lit, le_g_gmp, gm); // le g r
            // lt_of_le_of_lt g r g  (le g r, lt r g) : lt g g.
            let lt_g_g = self.lt_of_le_of_lt_app(g_lit, r_lit, g_lit, le_g_r, h_r_lt_g);
            // lt_irrefl g lt_g_g : False.
            let irr = self.lt_irrefl_app(g_lit);
            let false_proof = self.kernel.app(irr, lt_g_g);
            // ex falso into `le m' one`.
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        // Or.rec.{0} A B (fun _ => target) minor_inl minor_inr or_proof : le m' one.
        let le_mp_one = {
            let anon = self.kernel.anon();
            let or_ab = {
                let or_c = self.kernel.const_(self.int.logic.or, vec![]);
                let e = self.kernel.app(or_c, a_prop);
                self.kernel.app(e, b_prop)
            };
            let motive = self.kernel.lam(anon, or_ab, target, BinderInfo::Default);
            let zlvl = self.kernel.level_zero();
            let rec = self.kernel.const_(self.int.logic.or_rec, vec![zlvl]);
            let e = self.kernel.app(rec, a_prop);
            let e = self.kernel.app(e, b_prop);
            let e = self.kernel.app(e, motive);
            let e = self.kernel.app(e, minor_inl);
            let e = self.kernel.app(e, minor_inr);
            self.kernel.app(e, or_proof)
        };
        // m' ≠ one : Not (Eq Z m' one) = fun (h : Eq Z m' one) => False.
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z m' one
            // congr: Eq Z (mul g m')(mul g one).
            let gmp = self.mk_mul(g_lit, m_prime);
            let g_one = self.mk_mul(g_lit, one);
            let cong = self.congr_mul_right(g_lit, m_prime, one, h_eq); // mul g m' = mul g one
            let mul_one = self.mul_one_eq(g_lit); // mul g one = g
            // mul g m' = g : trans cong mul_one.
            let gmp_eq_g = self.eq_trans(gmp, g_one, g_lit, cong, mul_one); // mul g m' = g
            // r = g : trans (symm gm) (mul g m' = g).
            let r_eq_gmp = self.eq_symm(gmp, r_lit, gm); // gm: Eq (mul g m') r ⇒ Eq r (mul g m')
            let r_eq_g = self.eq_trans(r_lit, gmp, g_lit, r_eq_gmp, gmp_eq_g); // Eq Z r g
            // cast lt r g (h_r_lt_g) along r = g on the LEFT ⇒ lt g g.
            let lt_g_g = self.lt_cast_left(r_lit, g_lit, g_lit, h_r_lt_g, r_eq_g);
            let irr = self.lt_irrefl_app(g_lit);
            let false_proof = self.kernel.app(irr, lt_g_g);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_m_one = self.mk_eq(m_prime, one);
            self.kernel.lam(anon, eq_m_one, body, BinderInfo::Default)
        };
        // lt_of_le_of_ne m' one (le m' one) (m' ≠ one) : lt m' one.
        self.lt_of_le_of_ne_app(m_prime, one, le_mp_one, not_eq)
    }

    /// Prove `0 < m'` from `gm : Eq Z (mul g_lit m') r_lit`, `h_g_pos : lt zero
    /// g_lit`, `h_r_pos : lt zero r_lit`.
    ///
    /// Symmetric to [`Self::prove_m_prime_lt_one`] with `0`: `le_total m' 0`; the
    /// `le m' 0` branch gives `g·m' ≤ g·0 = 0`, i.e. `r ≤ 0`, contradicting `0 < r`.
    /// After `Or.rec` we have `le 0 m'`; `m' ≠ 0` (else `g·m' = 0 ≠ r`) strengthens
    /// to `0 < m'`.
    fn prove_zero_lt_m_prime(
        &mut self,
        g_lit: ExprId,
        m_prime: ExprId,
        r_lit: ExprId,
        gm: ExprId,
        h_g_pos: ExprId,
        h_r_pos: ExprId,
    ) -> ExprId {
        let zero = self.mk_zero();
        // le_total zero m' : Or (le zero m')(le m' zero).
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, zero);
            self.kernel.app(e, m_prime)
        };
        let a_prop = self.mk_le(zero, m_prime); // le zero m'
        let b_prop = self.mk_le(m_prime, zero); // le m' zero
        let h_g_nonneg = self.le_of_lt_app(zero, g_lit, h_g_pos);
        let target = self.mk_le(zero, m_prime);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_mp_zero = self.kernel.fvar(fid); // le m' zero
            // mul_le_mul_of_nonneg_left g m' zero h_g_nonneg h_le_mp_zero : le (mul g m')(mul g zero).
            let le_gmp_gzero =
                self.mul_le_mul_left_app(g_lit, m_prime, zero, h_g_nonneg, h_le_mp_zero);
            // cast (mul g zero) → zero via mul_zero.
            let g_zero = self.mk_mul(g_lit, zero);
            let mul_zero = self.mul_zero_eq(g_lit); // mul g zero = zero
            let gmp = self.mk_mul(g_lit, m_prime);
            let le_gmp_zero = self.le_cast_right(gmp, g_zero, zero, le_gmp_gzero, mul_zero); // le (g·m') zero
            // cast (mul g m') → r via gm on the LEFT.
            let le_r_zero = self.le_cast_left(gmp, r_lit, zero, le_gmp_zero, gm); // le r zero
            // lt_of_lt_of_le zero r zero (lt zero r)(le r zero) : lt zero zero.
            let lt_zero_zero = self.lt_of_lt_of_le_app(zero, r_lit, zero, h_r_pos, le_r_zero);
            let irr = self.lt_irrefl_app(zero);
            let false_proof = self.kernel.app(irr, lt_zero_zero);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_zero_mp = {
            let anon = self.kernel.anon();
            let or_ab = {
                let or_c = self.kernel.const_(self.int.logic.or, vec![]);
                let e = self.kernel.app(or_c, a_prop);
                self.kernel.app(e, b_prop)
            };
            let motive = self.kernel.lam(anon, or_ab, target, BinderInfo::Default);
            let zlvl = self.kernel.level_zero();
            let rec = self.kernel.const_(self.int.logic.or_rec, vec![zlvl]);
            let e = self.kernel.app(rec, a_prop);
            let e = self.kernel.app(e, b_prop);
            let e = self.kernel.app(e, motive);
            let e = self.kernel.app(e, minor_inl);
            let e = self.kernel.app(e, minor_inr);
            self.kernel.app(e, or_proof)
        };
        // zero ≠ m' : Not (Eq Z zero m') = fun (h : Eq Z zero m') => False.
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z zero m'
            // h_eq_sym : Eq Z m' zero.
            let gmp = self.mk_mul(g_lit, m_prime);
            let g_zero = self.mk_mul(g_lit, zero);
            let h_eq_sym = self.eq_symm(zero, m_prime, h_eq); // m' = zero
            // congr: mul g m' = mul g zero.
            let cong = self.congr_mul_right(g_lit, m_prime, zero, h_eq_sym);
            let mul_zero = self.mul_zero_eq(g_lit); // mul g zero = zero
            let gmp_eq_zero = self.eq_trans(gmp, g_zero, zero, cong, mul_zero); // mul g m' = zero
            // r = mul g m' = zero ⇒ Eq Z r zero.
            let r_eq_gmp = self.eq_symm(gmp, r_lit, gm); // r = mul g m'
            let r_eq_zero = self.eq_trans(r_lit, gmp, zero, r_eq_gmp, gmp_eq_zero); // r = zero
            // cast lt zero r (h_r_pos) along r = zero on the RIGHT ⇒ lt zero zero.
            let lt_zero_zero = self.lt_cast_right(zero, r_lit, zero, h_r_pos, r_eq_zero);
            let irr = self.lt_irrefl_app(zero);
            let false_proof = self.kernel.app(irr, lt_zero_zero);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_zero_m = self.mk_eq(zero, m_prime);
            self.kernel.lam(anon, eq_zero_m, body, BinderInfo::Default)
        };
        // lt_of_le_of_ne zero m' (le zero m')(zero ≠ m') : lt zero m'.
        self.lt_of_le_of_ne_app(zero, m_prime, le_zero_mp, not_eq)
    }

    /// `False.rec.{0} (fun _ => target) h_false : target`.
    fn ex_falso(&mut self, target: ExprId, h_false: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let false_const = self.kernel.const_(self.int.logic.false_, vec![]);
        let motive = self
            .kernel
            .lam(anon, false_const, target, BinderInfo::Default);
        let z = self.kernel.level_zero();
        let rec = self.kernel.const_(self.int.logic.false_rec, vec![z]);
        let e = self.kernel.app(rec, motive);
        self.kernel.app(e, h_false)
    }

    /// A fresh free-variable id (for open `Or.rec` / `Not`-lambda bodies).
    fn fresh_fvar(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Assemble the `False` proof term for the Diophantine certificate. Returns a
    /// [`ReconstructError`] (decline) on the degenerate `g = 0` case, a bound
    /// overflow, or a normalizer/identity mismatch; the caller gates the result
    /// through `infer`/`def_eq False`.
    #[allow(clippy::too_many_lines)]
    fn build_diophantine_false(
        &mut self,
        equalities: &[Equality],
        cert: &DiophantineCertificate,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };

        // --- gcd g and Euclidean (q, r): constant = g·q + r, 0 < r < g ---------
        let mut g: i128 = 0;
        for &(_, c) in &cert.combined {
            g = gcd_i128(g, c);
        }
        if g == 0 {
            return Err(decline("degenerate 0 = constant row (g = 0); not handled"));
        }
        let mut r = cert.constant % g;
        let mut q = cert.constant / g;
        if r < 0 {
            r += g;
            q -= 1;
        }
        if !(r > 0 && r < g) {
            return Err(decline("certificate not gcd-infeasible (0 < r < g failed)"));
        }
        if g > DIO_UNIT_MAX || r > DIO_UNIT_MAX || q.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("g / r / q exceed the unit-expansion bound"));
        }
        let gq = g.checked_mul(q).ok_or_else(|| decline("g·q overflow"))?;
        if gq.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("g·q exceeds the unit-expansion bound"));
        }

        // --- dense variable indices -------------------------------------------
        let index_of = dense_index_map(equalities, cert);
        let mut combined_dense: Vec<(usize, i128)> = cert
            .combined
            .iter()
            .map(|&(s, c)| (index_of[&s], c))
            .collect();
        combined_dense.sort_by_key(|&(i, _)| i);
        // m = combined / g.
        let mut m_coeffs: Vec<(usize, i128)> = Vec::with_capacity(combined_dense.len());
        for &(i, c) in &combined_dense {
            if c % g != 0 {
                return Err(decline("combined coefficient not divisible by gcd"));
            }
            let cq = c / g;
            if cq.unsigned_abs() > DIO_UNIT_MAX as u128 {
                return Err(decline("m coefficient exceeds the unit-expansion bound"));
            }
            m_coeffs.push((i, cq));
        }
        if m_coeffs.is_empty() {
            return Err(decline("m is empty (no variables); not handled"));
        }

        // === 1. Hypotheses h_i : Eq Z L_i (intlit b_i). =======================
        let mut hyps: Vec<(ExprId, Vec<IGen>, ExprId, i128, ExprId)> =
            Vec::with_capacity(equalities.len());
        for eq in equalities {
            let dense: Vec<(usize, i128)> =
                eq.coeffs.iter().map(|(&s, &c)| (index_of[&s], c)).collect();
            for &(_, c) in &dense {
                if c.unsigned_abs() > DIO_UNIT_MAX as u128 {
                    return Err(decline("equality coefficient exceeds the bound"));
                }
            }
            if eq.rhs.unsigned_abs() > DIO_UNIT_MAX as u128 {
                return Err(decline("equality rhs exceeds the bound"));
            }
            let l_gens = lin_to_canon_gens(&dense, 0);
            // Encode L_i as the faithful ZExpr (so it hash-conses with later uses).
            let l_expr = match lin_to_zexpr(&dense, 0) {
                Some(z) => self.emit_zexpr(&z),
                None => self.mk_zero(), // L_i ≡ 0 (no variables) — a 0 = b_i row
            };
            let r_expr = self.mk_intlit(eq.rhs);
            let prop = self.mk_eq(l_expr, r_expr);
            let h = self.hyp_axiom(prop)?;
            hyps.push((l_expr, l_gens, r_expr, eq.rhs, h));
        }

        // === 2. Combined: h_comb : Eq Z combined_expr (intlit constant). ======
        let h_comb =
            self.combine_equalities(&hyps, &cert.multipliers, &combined_dense, cert.constant)?;
        let combined_kexpr = match lin_to_zexpr(&combined_dense, 0) {
            Some(z) => self.emit_zexpr(&z),
            None => return Err(decline("combined row empty")),
        };
        let const_expr = self.mk_intlit(cert.constant);

        // === 3. gm : Eq Z (mul g_lit m') (intlit r). ==========================
        // 3a. ring_id1 : Eq Z (mul g_lit m') (add combined_expr (neg (intlit gq))).
        let g_zexpr = lin_to_zexpr(&[], g).ok_or_else(|| decline("g zero (unreachable)"))?;
        let m_prime_zexpr =
            lin_to_zexpr(&m_coeffs, -q).ok_or_else(|| decline("m' has no atoms"))?;
        let prod_zexpr = ZExpr::Mul(Box::new(g_zexpr), Box::new(m_prime_zexpr.clone()));
        let (prod_gens, prod_kexpr, prod_norm) = self
            .normalize(&prod_zexpr)
            .ok_or_else(|| decline("mul(g,m') normalizer declined"))?;
        let expected_prod_gens = lin_to_canon_gens(&combined_dense, -gq);
        if prod_gens != expected_prod_gens {
            return Err(decline("g·m' did not canonicalize to combined − g·q"));
        }
        // rhs1 = add combined (neg (intlit gq)) as a ZExpr, normalized.
        let rhs1_zexpr = ZExpr::Add(
            Box::new(lin_to_zexpr(&combined_dense, 0).ok_or_else(|| decline("combined empty"))?),
            Box::new(ZExpr::Neg(Box::new(intlit_zexpr(gq)))),
        );
        let (rhs1_gens, rhs1_kexpr, rhs1_norm) = self
            .normalize(&rhs1_zexpr)
            .ok_or_else(|| decline("combined − g·q normalizer declined"))?;
        if rhs1_gens != expected_prod_gens {
            return Err(decline("combined − g·q did not canonicalize as expected"));
        }
        let canon_prod = self.gens_to_expr(&prod_gens);
        let rhs1_norm_sym = self.eq_symm(rhs1_kexpr, canon_prod, rhs1_norm); // rhs1_kexpr ← canon? no
        // rhs1_norm : Eq Z rhs1_kexpr canon  ⇒ symm : Eq Z canon rhs1_kexpr.
        let ring_id1 = self.eq_trans(prod_kexpr, canon_prod, rhs1_kexpr, prod_norm, rhs1_norm_sym);

        // 3b. rewrite combined → const inside rhs1, then normalize (const − gq) → r.
        // rhs1_kexpr = add combined_kexpr (neg (intlit gq)).
        let neg_gq_kexpr = {
            let gq_k = self.emit_zexpr(&intlit_zexpr(gq));
            self.mk_neg(gq_k)
        };
        let rhs_after = self.mk_add(const_expr, neg_gq_kexpr);
        let cong = self.congr_add_left(combined_kexpr, const_expr, neg_gq_kexpr, h_comb);
        // const − gq normalizer.
        let after_zexpr = ZExpr::Add(
            Box::new(intlit_zexpr(cert.constant)),
            Box::new(ZExpr::Neg(Box::new(intlit_zexpr(gq)))),
        );
        let (after_gens, after_kexpr, after_norm) = self
            .normalize(&after_zexpr)
            .ok_or_else(|| decline("constant − g·q normalizer declined"))?;
        let expected_r_gens = lin_to_canon_gens(&[], r);
        if after_gens != expected_r_gens {
            return Err(decline("constant − g·q did not canonicalize to r"));
        }
        // after_kexpr is `add (intlit const)(neg (intlit gq))` = rhs_after (hash-cons).
        let r_lit = self.mk_intlit(r);
        let canon_r = self.gens_to_expr(&after_gens);
        let r_bridge = self.intlit_eq_canon(r); // Eq Z r_lit canon_r
        let r_bridge_sym = self.eq_symm(r_lit, canon_r, r_bridge); // canon_r = r_lit
        let after_to_r = self.eq_trans(after_kexpr, canon_r, r_lit, after_norm, r_bridge_sym);
        // rhs1_kexpr =[cong] rhs_after(=after_kexpr) =[after_to_r] r_lit.
        let rhs1_to_r = self.eq_trans(rhs1_kexpr, rhs_after, r_lit, cong, after_to_r);

        // 3c. gm : Eq Z (mul g_lit m') r_lit.
        let gm = self.eq_trans(prod_kexpr, rhs1_kexpr, r_lit, ring_id1, rhs1_to_r);

        // === 4. Discreteness close. ===========================================
        let g_lit = self.mk_intlit(g);
        let m_prime_expr = self.emit_zexpr(&m_prime_zexpr);
        debug_assert_eq!(prod_kexpr, self.mk_mul(g_lit, m_prime_expr));
        let zero = self.mk_zero();
        let one = self.mk_one();

        let h_g_pos = self.lt_zero_intlit(g)?; // lt zero g
        let h_r_pos = self.lt_zero_intlit(r)?; // lt zero r
        let h_r_lt_g = self.lt_intlit_intlit(r, g)?; // lt r g

        let lt_mp_one =
            self.prove_m_prime_lt_one(g_lit, m_prime_expr, r_lit, gm, h_g_pos, h_r_lt_g);
        let lt_zero_mp =
            self.prove_zero_lt_m_prime(g_lit, m_prime_expr, r_lit, gm, h_g_pos, h_r_pos);

        let p_prop = self.mk_lt(zero, m_prime_expr);
        let q_prop = self.mk_lt(m_prime_expr, one);
        let and_proof = self.and_intro(p_prop, q_prop, lt_zero_mp, lt_mp_one);
        Ok(self.no_int_between_app(m_prime_expr, and_proof))
    }
}

/// `gcd(a, b)` as a nonnegative `i128`.
fn gcd_i128(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    i128::try_from(a).unwrap_or(i128::MAX)
}
