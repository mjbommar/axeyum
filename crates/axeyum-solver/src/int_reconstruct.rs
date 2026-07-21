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
//! certificate guarantees) via discreteness, AND the degenerate `g = 0` row
//! (`0 = constant ≠ 0`, an empty `combined`, all variables cancelled): the latter is
//! a contradiction in any ordered ring — `0 = c` with `c ≠ 0` is false — closed by
//! `ne_c h_comb` where `ne_c : Not (Eq Z zero (intlit constant))` is built from the
//! SIGN of `constant` (no discreteness needed). The reconstruction declines on any
//! `i128`/bound overflow or a normalizer mismatch — never fabricating an identity.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, IntPrelude, Kernel, NameId, build_int_prelude,
};
use axeyum_rewrite::replace_subterms;

use crate::quant_closed_counterexample_cert::{
    ClosedUniversalCounterexampleCertificate, check_closed_universal_counterexample,
};
use crate::quant_nested_xor_cert::{IntNestedXorRefutationCertificate, int_nested_xor_refutation};
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

    /// `le_trans a b c h1 h2 : le a c`.
    fn le_trans_app(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.le_trans, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `lt_trans a b c h1 h2 : lt a c`.
    fn lt_trans_app(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.int.lt_trans, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
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

fn int_values_fit_proof_unit_budget(values: impl IntoIterator<Item = i128>) -> bool {
    let mut remaining = DIO_UNIT_MAX as u128;
    for value in values {
        let Some(next) = remaining.checked_sub(value.unsigned_abs()) else {
            return false;
        };
        remaining = next;
    }
    true
}

fn source_int_literals_fit_proof_unit_budget(
    arena: &TermArena,
    roots: impl IntoIterator<Item = TermId>,
) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = roots.into_iter().collect::<Vec<_>>();
    let mut values = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::IntConst(value) => values.push(*value),
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    int_values_fit_proof_unit_budget(values)
}

fn zexpr_fits_proof_unit_budget(expr: &ZExpr) -> bool {
    fn units(expr: &ZExpr) -> Option<u128> {
        match expr {
            ZExpr::Var(_) | ZExpr::One => Some(1),
            ZExpr::Zero => Some(0),
            ZExpr::Neg(inner) => units(inner),
            ZExpr::Add(left, right) => units(left)?.checked_add(units(right)?),
            ZExpr::Mul(left, right) => units(left)?.checked_mul(units(right)?),
        }
    }
    units(expr).is_some_and(|units| units <= DIO_UNIT_MAX as u128)
}

fn ground_int_term_fits_proof_unit_budget(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
) -> bool {
    fn units(arena: &TermArena, term: TermId, assignment: &Assignment) -> Option<u128> {
        match arena.node(term) {
            TermNode::IntConst(value) => Some(value.unsigned_abs()),
            TermNode::Symbol(symbol) => assignment.get(*symbol)?.as_int().map(i128::unsigned_abs),
            TermNode::App { op, args } => {
                match (op, &**args) {
                    (Op::IntNeg, [argument]) => units(arena, *argument, assignment),
                    (Op::IntAdd | Op::IntSub, [left, right]) => units(arena, *left, assignment)?
                        .checked_add(units(arena, *right, assignment)?),
                    (Op::IntMul, [left, right]) => units(arena, *left, assignment)?
                        .checked_mul(units(arena, *right, assignment)?),
                    (Op::Ite, [condition, then_term, else_term]) => {
                        match eval(arena, *condition, assignment).ok()? {
                            Value::Bool(true) => units(arena, *then_term, assignment),
                            Value::Bool(false) => units(arena, *else_term, assignment),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    units(arena, term, assignment).is_some_and(|units| units <= DIO_UNIT_MAX as u128)
}

/// Returns whether `assertions` has the closed-universal equality shape whose
/// ADR-0100 certificate can be reconstructed over [`IntPrelude`]. This is only a
/// cheap router predicate; the certificate checker and the kernel proof remain
/// the acceptance gates.
pub(crate) fn closed_universal_counterexample_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    let [assertion] = assertions else {
        return false;
    };
    let Some((binders, body)) = peel_closed_foralls(arena, *assertion) else {
        return false;
    };
    binders
        .iter()
        .all(|&binder| matches!(arena.symbol(binder).1, Sort::Int | Sort::Bool))
        && match_closed_int_equality_body(arena, body).is_some()
}

/// Reconstruct an evaluator-checked closed-universal counterexample as a genuine
/// Lean `forall` elimination followed by integer-ring normalization.
///
/// The supported proof body is an integer equality or disequality over `Int`
/// arithmetic and Bool-controlled integer `ite`. The original universal becomes
/// nested dependent products over the integer prelude's `Z` and the logic
/// prelude's computational `Bool`; the carried values are applied as witnesses.
/// No certificate-specific refuter axiom is introduced. The only non-prelude
/// axiom is the input universal itself.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] if the certificate is invalid or
/// the checked theorem is outside this reconstruction slice, and
/// [`ReconstructError::KernelRejected`] if any generated term fails to infer to
/// `False`.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_closed_universal_counterexample_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &ClosedUniversalCounterexampleCertificate,
) -> Result<String, ReconstructError> {
    if !check_closed_universal_counterexample(arena, assertions, certificate) {
        return Err(ReconstructError::UnsupportedTerm {
            term: "invalid closed-universal counterexample certificate".to_owned(),
        });
    }
    let Some((binders, body)) = peel_closed_foralls(arena, certificate.assertion) else {
        return Err(closed_cex_decline(
            "assertion is not a universal binder chain",
        ));
    };
    if binders
        .iter()
        .any(|&binder| !matches!(arena.symbol(binder).1, Sort::Int | Sort::Bool))
    {
        return Err(closed_cex_decline(
            "Lean reconstruction currently supports only Int/Bool binders",
        ));
    }
    let Some((negated, lhs, rhs)) = match_closed_int_equality_body(arena, body) else {
        return Err(closed_cex_decline(
            "body is not an integer equality or disequality",
        ));
    };
    let binding_values = certificate
        .bindings
        .iter()
        .filter_map(|(_, value)| match value {
            Value::Int(value) => Some(*value),
            _ => None,
        });
    if !source_int_literals_fit_proof_unit_budget(arena, [body])
        || !int_values_fit_proof_unit_budget(binding_values)
    {
        return Err(closed_cex_decline(
            "integer literals or witnesses exceed proof-size cap",
        ));
    }

    let mut assignment = Assignment::new();
    for &(binder, ref value) in &certificate.bindings {
        assignment.set(binder, value.clone());
    }
    let Ok(Value::Int(lhs_value)) = eval(arena, lhs, &assignment) else {
        return Err(closed_cex_decline(
            "left equality operand did not evaluate to Int",
        ));
    };
    let Ok(Value::Int(rhs_value)) = eval(arena, rhs, &assignment) else {
        return Err(closed_cex_decline(
            "right equality operand did not evaluate to Int",
        ));
    };
    if !int_values_fit_proof_unit_budget([lhs_value, rhs_value]) {
        return Err(closed_cex_decline(
            "evaluated integer operands exceed proof-size cap",
        ));
    }
    if !ground_int_term_fits_proof_unit_budget(arena, lhs, &assignment)
        || !ground_int_term_fits_proof_unit_budget(arena, rhs, &assignment)
    {
        return Err(closed_cex_decline(
            "ground integer normalization exceeds proof-size cap",
        ));
    }

    let mut ctx = IntReconstructCtx::new();
    let lhs_bound = ctx.emit_closed_cex_int_term(arena, lhs, &binders)?;
    let rhs_bound = ctx.emit_closed_cex_int_term(arena, rhs, &binders)?;
    let eq_bound = ctx.mk_eq(lhs_bound, rhs_bound);
    let body_prop = if negated {
        ctx.mk_not(eq_bound)
    } else {
        eq_bound
    };

    // Build `h : Π binder_0, ... Π binder_n, body`. `body_prop` uses de Bruijn
    // indices for the complete outer-to-inner binder list, so wrap innermost first.
    let mut universal_ty = body_prop;
    for &binder in binders.iter().rev() {
        let binder_ty = ctx.closed_cex_sort_expr(arena.symbol(binder).1)?;
        let anon = ctx.kernel.anon();
        universal_ty = ctx
            .kernel
            .pi(anon, binder_ty, universal_ty, BinderInfo::Default);
    }
    let mut instance_proof = ctx.hyp_axiom(universal_ty)?;
    for &(binder, ref value) in &certificate.bindings {
        let witness = ctx.closed_cex_value_expr(arena.symbol(binder).1, value)?;
        instance_proof = ctx.kernel.app(instance_proof, witness);
    }

    let lhs_ground = closed_cex_ground_zexpr(arena, lhs, &assignment)?;
    let rhs_ground = closed_cex_ground_zexpr(arena, rhs, &assignment)?;
    if !zexpr_fits_proof_unit_budget(&lhs_ground) || !zexpr_fits_proof_unit_budget(&rhs_ground) {
        return Err(closed_cex_decline(
            "ground integer normalization exceeds proof-size cap",
        ));
    }
    let lhs_expr = ctx.emit_zexpr(&lhs_ground);
    let rhs_expr = ctx.emit_zexpr(&rhs_ground);

    let proof = if negated {
        if lhs_value != rhs_value {
            return Err(closed_cex_decline(
                "disequality counterexample does not make its equality true",
            ));
        }
        let eq = ctx.prove_ground_zexpr_equality(&lhs_ground, &rhs_ground)?;
        ctx.kernel.app(instance_proof, eq)
    } else {
        if lhs_value == rhs_value {
            return Err(closed_cex_decline(
                "equality counterexample does not make its operands distinct",
            ));
        }
        let lhs_to_lit = ctx.prove_ground_zexpr_value(&lhs_ground, lhs_value)?;
        let rhs_to_lit = ctx.prove_ground_zexpr_value(&rhs_ground, rhs_value)?;
        let lhs_lit = ctx.mk_intlit(lhs_value);
        let rhs_lit = ctx.mk_intlit(rhs_value);
        let lit_lhs_to_lhs = ctx.eq_symm(lhs_expr, lhs_lit, lhs_to_lit);
        let lit_lhs_to_rhs =
            ctx.eq_trans(lhs_lit, lhs_expr, rhs_expr, lit_lhs_to_lhs, instance_proof);
        let lit_eq = ctx.eq_trans(lhs_lit, rhs_expr, rhs_lit, lit_lhs_to_rhs, rhs_to_lit);
        let not_lit_eq = ctx.prove_intlit_disequality(lhs_value, rhs_value)?;
        ctx.kernel.app(not_lit_eq, lit_eq)
    };

    let inferred =
        ctx.kernel_mut()
            .infer(proof)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "closed_universal_counterexample".to_owned(),
                detail: format!("infer failed: {error:?}"),
            })?;
    let false_name = ctx.int().logic.false_;
    let false_ = ctx.kernel_mut().const_(false_name, Vec::new());
    if !ctx.kernel_mut().def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "closed_universal_counterexample".to_owned(),
            detail: "counterexample reconstruction did not infer to False".to_owned(),
        });
    }
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

/// Reconstruct an ADR-0099 nested-XOR certificate to a kernel-checked Lean
/// `False` proof using three universal applications and propositional case
/// analysis.
///
/// The independently checked certificate guarantees that the equality between
/// the two same-branch integer selectors is equivalent to equality of their
/// guards. The translator therefore represents that atom as `Iff` of the guards.
/// The proof instantiates both outer binders at their pivots, derives the nested
/// universal from the outer XOR (one classical excluded-middle split), then
/// instantiates the nested binder at an adjacent off-pivot integer and closes by
/// integer-order disequality. No theorem-specific refuter or arithmetic axiom is
/// introduced.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] when the certificate is invalid
/// or its checked theorem exceeds this proof term's bounded integer-literal
/// representation, and [`ReconstructError::KernelRejected`] on any failed kernel
/// gate.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_int_nested_xor_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntNestedXorRefutationCertificate,
) -> Result<String, ReconstructError> {
    if int_nested_xor_refutation(arena, assertions) != Some(*certificate) {
        return Err(ReconstructError::UnsupportedTerm {
            term: "invalid nested-XOR refutation certificate".to_owned(),
        });
    }
    if !int_values_fit_proof_unit_budget([
        certificate.active_pivot,
        certificate.passive_pivot,
        certificate.nested_pivot,
    ]) {
        return Err(nested_xor_decline("integer literals exceed proof-size cap"));
    }
    let Some((outer_binders, outer_body)) = peel_closed_foralls(arena, certificate.assertion)
    else {
        return Err(nested_xor_decline(
            "assertion is not an outer universal chain",
        ));
    };
    if outer_binders.len() != 2 {
        return Err(nested_xor_decline("expected exactly two outer binders"));
    }
    let (selector, nested_forall, selector_is_left) =
        split_nested_xor_lean_children(arena, outer_body)?;
    let (_, nested_body) = as_single_forall(arena, nested_forall)
        .ok_or_else(|| nested_xor_decline("nested child is not a direct universal"))?;
    let (nested_guard_is_left, active_guard, nested_guard) =
        nested_selector_guard_order(arena, nested_body, certificate.nested)?;

    let mut ctx = IntReconstructCtx::new();
    let outer_prop = ctx.emit_nested_xor_prop(arena, outer_body, &outer_binders)?;

    // Independently materialize the proposition after the two outer witness
    // applications. These closed expressions must be definitionally equal to the
    // kernel type inferred for `outer_instance`; using them avoids leaking the
    // original outer de Bruijn variables into the subsequent classical case split.
    let mut instantiated_arena = arena.clone();
    let mut replacements = HashMap::new();
    for &binder in &outer_binders {
        let value = if binder == certificate.active {
            certificate.active_pivot
        } else if binder == certificate.passive {
            certificate.passive_pivot
        } else {
            return Err(nested_xor_decline(
                "certificate binder is not in outer prefix",
            ));
        };
        let variable = instantiated_arena.var(binder);
        let literal = instantiated_arena.int_const(value);
        replacements.insert(variable, literal);
    }
    let mut memo = HashMap::new();
    let instantiated_outer_body = replace_subterms(
        &mut instantiated_arena,
        outer_body,
        &replacements,
        &mut memo,
    )
    .map_err(|error| nested_xor_decline(&format!("outer substitution failed: {error}")))?;
    let (instantiated_selector, instantiated_nested, instantiated_selector_is_left) =
        split_nested_xor_lean_children(&instantiated_arena, instantiated_outer_body)?;
    if instantiated_selector_is_left != selector_is_left {
        return Err(nested_xor_decline(
            "outer substitution changed XOR child orientation",
        ));
    }
    let selector_prop =
        ctx.emit_nested_xor_prop(&instantiated_arena, instantiated_selector, &[])?;
    let nested_prop = ctx.emit_nested_xor_prop(&instantiated_arena, instantiated_nested, &[])?;

    let mut universal_ty = outer_prop;
    for _ in outer_binders.iter().rev() {
        let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
        let anon = ctx.kernel.anon();
        universal_ty = ctx.kernel.pi(anon, z_ty, universal_ty, BinderInfo::Default);
    }
    let mut outer_instance = ctx.hyp_axiom(universal_ty)?;
    for &binder in &outer_binders {
        let value = if binder == certificate.active {
            certificate.active_pivot
        } else if binder == certificate.passive {
            certificate.passive_pivot
        } else {
            return Err(nested_xor_decline(
                "certificate binder is not in outer prefix",
            ));
        };
        let witness = ctx.mk_intlit(value);
        outer_instance = ctx.kernel.app(outer_instance, witness);
    }

    // At both pivots the two selector equalities are true, hence their XOR is
    // false. Preserve the assertion's child order when constructing the Iff.
    let (selector_left, selector_right) = binary_app_children(arena, selector, Op::BoolXor)?;
    let (instantiated_selector_left, instantiated_selector_right) =
        binary_app_children(&instantiated_arena, instantiated_selector, Op::BoolXor)?;
    let left_prop =
        ctx.emit_nested_xor_prop(&instantiated_arena, instantiated_selector_left, &[])?;
    let right_prop =
        ctx.emit_nested_xor_prop(&instantiated_arena, instantiated_selector_right, &[])?;
    let left_proof = ctx.prove_pivot_guard(arena, selector_left, certificate)?;
    let right_proof = ctx.prove_pivot_guard(arena, selector_right, certificate)?;
    let left_to_right = ctx.const_implication(left_prop, right_prop, right_proof);
    let right_to_left = ctx.const_implication(right_prop, left_prop, left_proof);
    let selector_iff = ctx.iff_intro(left_prop, right_prop, left_to_right, right_to_left);
    let selector_children_iff = ctx.mk_iff(left_prop, right_prop);
    ctx.require_nested_xor_type(selector_iff, selector_children_iff, "selector equality Iff")?;
    let not_selector = ctx.negate_negation(selector_prop, selector_iff);
    let expected_not_selector = ctx.mk_not(selector_prop);
    ctx.require_nested_xor_type(not_selector, expected_not_selector, "selector XOR falsity")?;

    let normalized_outer_instance = if selector_is_left {
        outer_instance
    } else {
        ctx.swap_negated_iff(nested_prop, selector_prop, outer_instance)
    };
    let selector_nested_iff = ctx.mk_iff(selector_prop, nested_prop);
    let expected_normalized_outer = ctx.mk_not(selector_nested_iff);
    ctx.require_nested_xor_type(
        normalized_outer_instance,
        expected_normalized_outer,
        "normalized outer XOR",
    )?;
    let nested_universal = ctx.derive_xor_other_from_false(
        selector_prop,
        nested_prop,
        normalized_outer_instance,
        not_selector,
        true,
    )?;
    ctx.require_nested_xor_type(nested_universal, nested_prop, "derived nested universal")?;

    let nested_witness = certificate
        .nested_pivot
        .checked_add(1)
        .or_else(|| certificate.nested_pivot.checked_sub(1))
        .ok_or_else(|| nested_xor_decline("could not choose an adjacent nested witness"))?;
    if !int_values_fit_proof_unit_budget([
        certificate.active_pivot,
        certificate.passive_pivot,
        certificate.nested_pivot,
        nested_witness,
    ]) {
        return Err(nested_xor_decline("pivot literal exceeds proof-size cap"));
    }
    let witness_expr = ctx.mk_intlit(nested_witness);
    let nested_instance = ctx.kernel.app(nested_universal, witness_expr);

    let active_guard_prop = ctx.emit_instantiated_guard(
        arena,
        active_guard,
        certificate.active,
        certificate.active_pivot,
    )?;
    let nested_guard_prop =
        ctx.emit_instantiated_guard(arena, nested_guard, certificate.nested, nested_witness)?;
    let expected_nested_instance = if nested_guard_is_left {
        ctx.mk_iff(nested_guard_prop, active_guard_prop)
    } else {
        ctx.mk_iff(active_guard_prop, nested_guard_prop)
    };
    ctx.require_nested_xor_type(
        nested_instance,
        expected_nested_instance,
        "nested off-pivot instance",
    )?;
    let active_guard_proof = ctx.prove_instantiated_true_guard(
        arena,
        active_guard,
        certificate.active,
        certificate.active_pivot,
    )?;
    ctx.require_nested_xor_type(
        active_guard_proof,
        active_guard_prop,
        "active pivot equality",
    )?;
    let not_nested_guard = ctx.prove_instantiated_false_guard(
        arena,
        nested_guard,
        certificate.nested,
        nested_witness,
    )?;
    let expected_not_nested = ctx.mk_not(nested_guard_prop);
    ctx.require_nested_xor_type(
        not_nested_guard,
        expected_not_nested,
        "nested off-pivot disequality",
    )?;
    let active_to_nested = ctx.iff_project(
        if nested_guard_is_left {
            nested_guard_prop
        } else {
            active_guard_prop
        },
        if nested_guard_is_left {
            active_guard_prop
        } else {
            nested_guard_prop
        },
        nested_instance,
        !nested_guard_is_left,
    );
    let nested_guard_proof = ctx.kernel.app(active_to_nested, active_guard_proof);
    let proof = ctx.kernel.app(not_nested_guard, nested_guard_proof);

    let inferred =
        ctx.kernel_mut()
            .infer(proof)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "int_nested_xor".to_owned(),
                detail: format!("infer failed: {error:?}"),
            })?;
    let false_name = ctx.int().logic.false_;
    let false_ = ctx.kernel_mut().const_(false_name, Vec::new());
    if !ctx.kernel_mut().def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "int_nested_xor".to_owned(),
            detail: "nested-XOR reconstruction did not infer to False".to_owned(),
        });
    }
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

fn nested_xor_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("nested-XOR reconstruction: {detail}"),
    }
}

fn binary_app_children(
    arena: &TermArena,
    term: TermId,
    expected: Op,
) -> Result<(TermId, TermId), ReconstructError> {
    let TermNode::App { op, args } = arena.node(term) else {
        return Err(nested_xor_decline("expected binary application"));
    };
    let [left, right] = &**args else {
        return Err(nested_xor_decline(
            "expected exactly two application children",
        ));
    };
    if *op != expected {
        return Err(nested_xor_decline("unexpected binary operator"));
    }
    Ok((*left, *right))
}

fn as_single_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [body] = &**args else {
        return None;
    };
    Some((*binder, *body))
}

fn split_nested_xor_lean_children(
    arena: &TermArena,
    body: TermId,
) -> Result<(TermId, TermId, bool), ReconstructError> {
    let (left, right) = binary_app_children(arena, body, Op::BoolXor)?;
    match (
        as_single_forall(arena, left),
        as_single_forall(arena, right),
    ) {
        (None, Some(_)) => Ok((left, right, true)),
        (Some(_), None) => Ok((right, left, false)),
        _ => Err(nested_xor_decline(
            "outer XOR does not have exactly one direct universal child",
        )),
    }
}

fn nested_selector_guard_order(
    arena: &TermArena,
    nested_body: TermId,
    nested: SymbolId,
) -> Result<(bool, TermId, TermId), ReconstructError> {
    let (left, right) = binary_app_children(arena, nested_body, Op::Eq)?;
    let left_guard = ite_guard(arena, left)?;
    let right_guard = ite_guard(arena, right)?;
    let left_nested = guard_symbol(arena, left_guard) == Some(nested);
    let right_nested = guard_symbol(arena, right_guard) == Some(nested);
    match (left_nested, right_nested) {
        (true, false) => Ok((true, right_guard, left_guard)),
        (false, true) => Ok((false, left_guard, right_guard)),
        _ => Err(nested_xor_decline(
            "selector equality does not have one active and one nested guard",
        )),
    }
}

fn ite_guard(arena: &TermArena, term: TermId) -> Result<TermId, ReconstructError> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return Err(nested_xor_decline("selector operand is not an ite"));
    };
    let [guard, _, _] = &**args else {
        return Err(nested_xor_decline("selector ite is not ternary"));
    };
    Ok(*guard)
}

fn guard_symbol(arena: &TermArena, guard: TermId) -> Option<SymbolId> {
    let TermNode::App { op: Op::Eq, args } = arena.node(guard) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(symbol), _) | (_, TermNode::Symbol(symbol)) => Some(*symbol),
        _ => None,
    }
}

fn closed_cex_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("closed-universal counterexample: {detail}"),
    }
}

fn peel_closed_foralls(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        let [body] = &**args else {
            return None;
        };
        binders.push(*binder);
        term = *body;
    }
    (!binders.is_empty()).then_some((binders, term))
}

/// Returns `(negated, lhs, rhs)` for `lhs = rhs` or `not (lhs = rhs)`.
fn match_closed_int_equality_body(
    arena: &TermArena,
    body: TermId,
) -> Option<(bool, TermId, TermId)> {
    let (negated, equality) = match arena.node(body) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => (true, *args.first()?),
        _ => (false, body),
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(equality) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    (arena.sort_of(*lhs) == Sort::Int && arena.sort_of(*rhs) == Sort::Int)
        .then_some((negated, *lhs, *rhs))
}

fn closed_cex_ground_zexpr(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
) -> Result<ZExpr, ReconstructError> {
    match arena.node(term) {
        TermNode::IntConst(value) => {
            if !int_values_fit_proof_unit_budget([*value]) {
                return Err(closed_cex_decline("integer literal exceeds proof-size cap"));
            }
            Ok(intlit_zexpr(*value))
        }
        TermNode::Symbol(symbol) => match assignment.get(*symbol) {
            Some(Value::Int(value)) if int_values_fit_proof_unit_budget([value]) => {
                Ok(intlit_zexpr(value))
            }
            Some(Value::Int(_)) => {
                Err(closed_cex_decline("integer witness exceeds proof-size cap"))
            }
            _ => Err(closed_cex_decline(
                "unassigned non-Int symbol in integer term",
            )),
        },
        TermNode::App { op, args } => match (op, &**args) {
            (Op::IntNeg, [arg]) => Ok(ZExpr::Neg(Box::new(closed_cex_ground_zexpr(
                arena, *arg, assignment,
            )?))),
            (Op::IntAdd, [lhs, rhs]) => Ok(ZExpr::Add(
                Box::new(closed_cex_ground_zexpr(arena, *lhs, assignment)?),
                Box::new(closed_cex_ground_zexpr(arena, *rhs, assignment)?),
            )),
            (Op::IntSub, [lhs, rhs]) => Ok(ZExpr::Add(
                Box::new(closed_cex_ground_zexpr(arena, *lhs, assignment)?),
                Box::new(ZExpr::Neg(Box::new(closed_cex_ground_zexpr(
                    arena, *rhs, assignment,
                )?))),
            )),
            (Op::IntMul, [lhs, rhs]) => Ok(ZExpr::Mul(
                Box::new(closed_cex_ground_zexpr(arena, *lhs, assignment)?),
                Box::new(closed_cex_ground_zexpr(arena, *rhs, assignment)?),
            )),
            (Op::Ite, [condition, then_term, else_term]) => {
                match eval(arena, *condition, assignment) {
                    Ok(Value::Bool(true)) => closed_cex_ground_zexpr(arena, *then_term, assignment),
                    Ok(Value::Bool(false)) => {
                        closed_cex_ground_zexpr(arena, *else_term, assignment)
                    }
                    _ => Err(closed_cex_decline("integer ite condition did not evaluate")),
                }
            }
            _ => Err(closed_cex_decline(
                "integer term uses an operator outside add/sub/mul/neg/ite",
            )),
        },
        _ => Err(closed_cex_decline("integer term uses a non-integer leaf")),
    }
}

impl IntReconstructCtx {
    fn mk_not(&mut self, prop: ExprId) -> ExprId {
        let not = self.kernel.const_(self.int.logic.not, Vec::new());
        self.kernel.app(not, prop)
    }

    fn closed_cex_sort_expr(&mut self, sort: Sort) -> Result<ExprId, ReconstructError> {
        match sort {
            Sort::Int => Ok(self.kernel.const_(self.int.z, Vec::new())),
            Sort::Bool => Ok(self.kernel.const_(self.int.logic.bool_, Vec::new())),
            _ => Err(closed_cex_decline("unsupported binder sort")),
        }
    }

    fn closed_cex_value_expr(
        &mut self,
        sort: Sort,
        value: &Value,
    ) -> Result<ExprId, ReconstructError> {
        match (sort, value) {
            (Sort::Int, Value::Int(value)) => {
                if !int_values_fit_proof_unit_budget([*value]) {
                    return Err(closed_cex_decline("integer witness exceeds proof-size cap"));
                }
                Ok(self.mk_intlit(*value))
            }
            (Sort::Bool, Value::Bool(true)) => {
                Ok(self.kernel.const_(self.int.logic.bool_true, Vec::new()))
            }
            (Sort::Bool, Value::Bool(false)) => {
                Ok(self.kernel.const_(self.int.logic.bool_false, Vec::new()))
            }
            _ => Err(closed_cex_decline(
                "witness value does not match binder sort",
            )),
        }
    }

    fn emit_closed_cex_bool_term(
        &mut self,
        arena: &TermArena,
        term: TermId,
        binders: &[SymbolId],
    ) -> Result<ExprId, ReconstructError> {
        match arena.node(term) {
            TermNode::BoolConst(value) => Ok(self.kernel.const_(
                if *value {
                    self.int.logic.bool_true
                } else {
                    self.int.logic.bool_false
                },
                Vec::new(),
            )),
            TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
                let position = binders
                    .iter()
                    .position(|candidate| candidate == symbol)
                    .ok_or_else(|| closed_cex_decline("free Bool symbol in body"))?;
                let index = u32::try_from(binders.len() - 1 - position)
                    .map_err(|_| closed_cex_decline("too many binders"))?;
                Ok(self.kernel.bvar(index))
            }
            _ => Err(closed_cex_decline(
                "Bool term currently supports only bound variables and constants",
            )),
        }
    }

    fn emit_closed_cex_int_term(
        &mut self,
        arena: &TermArena,
        term: TermId,
        binders: &[SymbolId],
    ) -> Result<ExprId, ReconstructError> {
        match arena.node(term) {
            TermNode::IntConst(value) => {
                if !int_values_fit_proof_unit_budget([*value]) {
                    return Err(closed_cex_decline("integer literal exceeds proof-size cap"));
                }
                Ok(self.mk_intlit(*value))
            }
            TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Int => {
                let position = binders
                    .iter()
                    .position(|candidate| candidate == symbol)
                    .ok_or_else(|| closed_cex_decline("free Int symbol in body"))?;
                let index = u32::try_from(binders.len() - 1 - position)
                    .map_err(|_| closed_cex_decline("too many binders"))?;
                Ok(self.kernel.bvar(index))
            }
            TermNode::App { op, args } => match (op, &**args) {
                (Op::IntNeg, [arg]) => {
                    let arg = self.emit_closed_cex_int_term(arena, *arg, binders)?;
                    Ok(self.mk_neg(arg))
                }
                (Op::IntAdd, [lhs, rhs]) => {
                    let lhs = self.emit_closed_cex_int_term(arena, *lhs, binders)?;
                    let rhs = self.emit_closed_cex_int_term(arena, *rhs, binders)?;
                    Ok(self.mk_add(lhs, rhs))
                }
                (Op::IntSub, [lhs, rhs]) => {
                    let lhs = self.emit_closed_cex_int_term(arena, *lhs, binders)?;
                    let rhs = self.emit_closed_cex_int_term(arena, *rhs, binders)?;
                    let neg_rhs = self.mk_neg(rhs);
                    Ok(self.mk_add(lhs, neg_rhs))
                }
                (Op::IntMul, [lhs, rhs]) => {
                    let lhs = self.emit_closed_cex_int_term(arena, *lhs, binders)?;
                    let rhs = self.emit_closed_cex_int_term(arena, *rhs, binders)?;
                    Ok(self.mk_mul(lhs, rhs))
                }
                (Op::Ite, [condition, then_term, else_term]) => {
                    let condition = self.emit_closed_cex_bool_term(arena, *condition, binders)?;
                    let then_term = self.emit_closed_cex_int_term(arena, *then_term, binders)?;
                    let else_term = self.emit_closed_cex_int_term(arena, *else_term, binders)?;
                    let bool_ty = self.kernel.const_(self.int.logic.bool_, Vec::new());
                    let z_ty = self.kernel.const_(self.int.z, Vec::new());
                    let anon = self.kernel.anon();
                    let motive = self.kernel.lam(anon, bool_ty, z_ty, BinderInfo::Default);
                    let zero = self.kernel.level_zero();
                    let one = self.kernel.level_succ(zero);
                    let rec = self.kernel.const_(self.int.logic.bool_rec, vec![one]);
                    let rec = self.kernel.app(rec, motive);
                    let rec = self.kernel.app(rec, then_term);
                    let rec = self.kernel.app(rec, else_term);
                    Ok(self.kernel.app(rec, condition))
                }
                _ => Err(closed_cex_decline(
                    "integer term uses an operator outside add/sub/mul/neg/ite",
                )),
            },
            _ => Err(closed_cex_decline("integer term uses a non-integer leaf")),
        }
    }

    fn prove_ground_zexpr_equality(
        &mut self,
        lhs: &ZExpr,
        rhs: &ZExpr,
    ) -> Result<ExprId, ReconstructError> {
        if !zexpr_fits_proof_unit_budget(lhs) || !zexpr_fits_proof_unit_budget(rhs) {
            return Err(closed_cex_decline(
                "integer equality proof exceeds proof-size cap",
            ));
        }
        let (lhs_gens, lhs_expr, lhs_proof) = self
            .normalize(lhs)
            .ok_or_else(|| closed_cex_decline("left integer normalization declined"))?;
        let (rhs_gens, rhs_expr, rhs_proof) = self
            .normalize(rhs)
            .ok_or_else(|| closed_cex_decline("right integer normalization declined"))?;
        if lhs_gens != rhs_gens {
            return Err(closed_cex_decline(
                "equal operands normalized to different integer forms",
            ));
        }
        let canonical = self.gens_to_expr(&lhs_gens);
        let rhs_sym = self.eq_symm(rhs_expr, canonical, rhs_proof);
        Ok(self.eq_trans(lhs_expr, canonical, rhs_expr, lhs_proof, rhs_sym))
    }

    fn prove_ground_zexpr_value(
        &mut self,
        expr: &ZExpr,
        value: i128,
    ) -> Result<ExprId, ReconstructError> {
        if !int_values_fit_proof_unit_budget([value]) || !zexpr_fits_proof_unit_budget(expr) {
            return Err(closed_cex_decline(
                "integer value proof exceeds proof-size cap",
            ));
        }
        let (gens, kernel_expr, proof) = self
            .normalize(expr)
            .ok_or_else(|| closed_cex_decline("integer normalization declined"))?;
        let expected = lin_to_canon_gens(&[], value);
        if gens != expected {
            return Err(closed_cex_decline(
                "integer normalization disagrees with evaluator value",
            ));
        }
        let canonical = self.gens_to_expr(&gens);
        let literal = self.mk_intlit(value);
        let literal_to_canonical = self.intlit_eq_canon(value);
        let canonical_to_literal = self.eq_symm(literal, canonical, literal_to_canonical);
        Ok(self.eq_trans(kernel_expr, canonical, literal, proof, canonical_to_literal))
    }

    fn prove_intlit_disequality(
        &mut self,
        lhs: i128,
        rhs: i128,
    ) -> Result<ExprId, ReconstructError> {
        if lhs == rhs {
            return Err(closed_cex_decline(
                "literal disequality requires distinct values",
            ));
        }
        if !int_values_fit_proof_unit_budget([lhs, rhs]) {
            return Err(closed_cex_decline(
                "literal disequality exceeds proof-size cap",
            ));
        }
        let lhs_expr = self.mk_intlit(lhs);
        let rhs_expr = self.mk_intlit(rhs);
        let eq_prop = self.mk_eq(lhs_expr, rhs_expr);
        let fvar = self.fresh_fvar();
        let equality = self.kernel.fvar(fvar);
        let false_proof = if lhs < rhs {
            let lt = self.lt_lit_lit(lhs, rhs)?;
            let equality_sym = self.eq_symm(lhs_expr, rhs_expr, equality);
            let self_lt = self.lt_cast_right(lhs_expr, rhs_expr, lhs_expr, lt, equality_sym);
            let irrefl = self.lt_irrefl_app(lhs_expr);
            self.kernel.app(irrefl, self_lt)
        } else {
            let lt = self.lt_lit_lit(rhs, lhs)?;
            let self_lt = self.lt_cast_right(rhs_expr, lhs_expr, rhs_expr, lt, equality);
            let irrefl = self.lt_irrefl_app(rhs_expr);
            self.kernel.app(irrefl, self_lt)
        };
        let body = self.kernel.abstract_fvars(false_proof, &[fvar]);
        let anon = self.kernel.anon();
        Ok(self.kernel.lam(anon, eq_prop, body, BinderInfo::Default))
    }

    fn mk_iff(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let iff = self.kernel.const_(self.int.logic.iff, Vec::new());
        let iff = self.kernel.app(iff, left);
        self.kernel.app(iff, right)
    }

    fn mk_or(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let or = self.kernel.const_(self.int.logic.or, Vec::new());
        let or = self.kernel.app(or, left);
        self.kernel.app(or, right)
    }

    fn mk_and(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let and = self.kernel.const_(self.int.logic.and, Vec::new());
        let and = self.kernel.app(and, left);
        self.kernel.app(and, right)
    }

    fn and_project(
        &mut self,
        left: ExprId,
        right: ExprId,
        proof: ExprId,
        select_left: bool,
    ) -> ExprId {
        let target = if select_left { left } else { right };
        let conjunction = self.mk_and(left, right);
        let anon = self.kernel.anon();
        let motive = self
            .kernel
            .lam(anon, conjunction, target, BinderInfo::Default);
        let chosen = if select_left {
            self.kernel.bvar(1)
        } else {
            self.kernel.bvar(0)
        };
        let minor = self.kernel.lam(anon, right, chosen, BinderInfo::Default);
        let minor = self.kernel.lam(anon, left, minor, BinderInfo::Default);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.int.logic.and_rec, vec![zero]);
        let rec = self.kernel.app(rec, left);
        let rec = self.kernel.app(rec, right);
        let rec = self.kernel.app(rec, motive);
        let rec = self.kernel.app(rec, minor);
        self.kernel.app(rec, proof)
    }

    fn mk_exists(&mut self, predicate: ExprId) -> ExprId {
        let z_ty = self.kernel.const_(self.int.z, Vec::new());
        self.mk_exists_for_carrier(z_ty, predicate)
    }

    fn mk_exists_for_carrier(&mut self, carrier: ExprId, predicate: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let exists = self.kernel.const_(self.int.logic.exists_, vec![one]);
        let exists = self.kernel.app(exists, carrier);
        self.kernel.app(exists, predicate)
    }

    fn exists_elim_false(
        &mut self,
        predicate: ExprId,
        proposition: ExprId,
        minor: ExprId,
        major: ExprId,
    ) -> ExprId {
        let z_ty = self.kernel.const_(self.int.z, Vec::new());
        self.exists_elim_false_for_carrier(z_ty, predicate, proposition, minor, major)
    }

    fn exists_elim_false_for_carrier(
        &mut self,
        carrier: ExprId,
        predicate: ExprId,
        proposition: ExprId,
        minor: ExprId,
        major: ExprId,
    ) -> ExprId {
        let false_ = self.kernel.const_(self.int.logic.false_, Vec::new());
        let anon = self.kernel.anon();
        let motive = self
            .kernel
            .lam(anon, proposition, false_, BinderInfo::Default);
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let rec = self.kernel.const_(self.int.logic.exists_rec, vec![one]);
        let rec = self.kernel.app(rec, carrier);
        let rec = self.kernel.app(rec, predicate);
        let rec = self.kernel.app(rec, motive);
        let rec = self.kernel.app(rec, minor);
        self.kernel.app(rec, major)
    }

    fn require_affine_growth_type(
        &mut self,
        proof: ExprId,
        expected: ExprId,
        stage: &str,
    ) -> Result<(), ReconstructError> {
        let inferred =
            self.kernel
                .infer(proof)
                .map_err(|error| ReconstructError::KernelRejected {
                    rule: "int_affine_growth".to_owned(),
                    detail: format!("{stage} infer failed: {error:?}"),
                })?;
        if self.kernel.def_eq(inferred, expected) {
            Ok(())
        } else {
            Err(ReconstructError::KernelRejected {
                rule: "int_affine_growth".to_owned(),
                detail: format!("{stage} inferred the wrong proposition"),
            })
        }
    }

    fn require_partition_type(
        &mut self,
        proof: ExprId,
        expected: ExprId,
        stage: &str,
    ) -> Result<(), ReconstructError> {
        let inferred =
            self.kernel
                .infer(proof)
                .map_err(|error| ReconstructError::KernelRejected {
                    rule: "single_pivot_equality_partition".to_owned(),
                    detail: format!("{stage} infer failed: {error:?}"),
                })?;
        if self.kernel.def_eq(inferred, expected) {
            Ok(())
        } else {
            Err(ReconstructError::KernelRejected {
                rule: "single_pivot_equality_partition".to_owned(),
                detail: format!("{stage} inferred the wrong proposition"),
            })
        }
    }

    fn mk_true(&mut self) -> ExprId {
        self.kernel.const_(self.int.logic.true_, Vec::new())
    }

    fn true_intro(&mut self) -> ExprId {
        self.kernel.const_(self.int.logic.true_intro, Vec::new())
    }

    fn mk_bool_eq(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let equality = self.kernel.const_(self.int.logic.eq, vec![one]);
        let bool_ty = self.kernel.const_(self.int.logic.bool_, Vec::new());
        let equality = self.kernel.app(equality, bool_ty);
        let equality = self.kernel.app(equality, left);
        self.kernel.app(equality, right)
    }

    fn bool_eq_refl(&mut self, value: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let refl = self.kernel.const_(self.int.logic.eq_refl, vec![one]);
        let bool_ty = self.kernel.const_(self.int.logic.bool_, Vec::new());
        let refl = self.kernel.app(refl, bool_ty);
        self.kernel.app(refl, value)
    }

    /// `lhs != Bool.true` when `lhs` definitionally reduces to `Bool.false`.
    fn bool_false_ne_true(&mut self, lhs: ExprId) -> ExprId {
        let bool_true = self.kernel.const_(self.int.logic.bool_true, Vec::new());
        let equality = self.mk_bool_eq(lhs, bool_true);
        let equality_id = self.fresh_fvar();
        let equality_proof = self.kernel.fvar(equality_id);

        let anon = self.kernel.anon();
        let bool_ty = self.kernel.const_(self.int.logic.bool_, Vec::new());
        let prop = self.kernel.sort_zero();
        let true_prop = self.mk_true();
        let false_prop = self.kernel.const_(self.int.logic.false_, Vec::new());
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let rec = self.kernel.const_(self.int.logic.bool_rec, vec![one]);
        let motive = self.kernel.lam(anon, bool_ty, prop, BinderInfo::Default);
        let discriminator = {
            let rec = self.kernel.app(rec, motive);
            let rec = self.kernel.app(rec, false_prop);
            let rec = self.kernel.app(rec, true_prop);
            let value = self.kernel.bvar(0);
            let body = self.kernel.app(rec, value);
            self.kernel.lam(anon, bool_ty, body, BinderInfo::Default)
        };
        let transport_motive = {
            let value = self.kernel.bvar(1);
            let discriminator_value = self.kernel.app(discriminator, value);
            let value0 = self.kernel.bvar(0);
            let equality = self.mk_bool_eq(lhs, value0);
            let inner = self
                .kernel
                .lam(anon, equality, discriminator_value, BinderInfo::Default);
            self.kernel.lam(anon, bool_ty, inner, BinderInfo::Default)
        };
        let refl_case = self.true_intro();
        let eq_rec = self.kernel.const_(self.int.logic.eq_rec, vec![zero, one]);
        let proof = self.kernel.app(eq_rec, bool_ty);
        let proof = self.kernel.app(proof, lhs);
        let proof = self.kernel.app(proof, transport_motive);
        let proof = self.kernel.app(proof, refl_case);
        let proof = self.kernel.app(proof, bool_true);
        let false_proof = self.kernel.app(proof, equality_proof);
        let body = self.kernel.abstract_fvars(false_proof, &[equality_id]);
        self.kernel.lam(anon, equality, body, BinderInfo::Default)
    }

    fn or_intro_left(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let intro = self.kernel.const_(self.int.logic.or_inl, Vec::new());
        let intro = self.kernel.app(intro, left);
        let intro = self.kernel.app(intro, right);
        self.kernel.app(intro, proof)
    }

    fn or_intro_right(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let intro = self.kernel.const_(self.int.logic.or_inr, Vec::new());
        let intro = self.kernel.app(intro, left);
        let intro = self.kernel.app(intro, right);
        self.kernel.app(intro, proof)
    }

    fn exists_intro(
        &mut self,
        carrier: ExprId,
        predicate: ExprId,
        witness: ExprId,
        proof: ExprId,
    ) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let intro = self.kernel.const_(self.int.logic.exists_intro, vec![one]);
        let intro = self.kernel.app(intro, carrier);
        let intro = self.kernel.app(intro, predicate);
        let intro = self.kernel.app(intro, witness);
        self.kernel.app(intro, proof)
    }

    fn int_eq_em_app(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let theorem = self.kernel.const_(self.int.eq_em, Vec::new());
        let theorem = self.kernel.app(theorem, left);
        self.kernel.app(theorem, right)
    }

    /// `lt x (add x one)` from ordered-ring addition and `zero_lt_one`.
    fn prove_successor_lt(&mut self, value: ExprId) -> ExprId {
        let zero = self.mk_zero();
        let one = self.mk_one();
        let refl = self.le_refl_app(value);
        let zero_lt_one = self.kernel.const_(self.int.zero_lt_one, Vec::new());
        let lifted = self.add_lt_add_of_le_of_lt_app(value, value, zero, one, refl, zero_lt_one);
        let value_plus_zero = self.mk_add(value, zero);
        let successor = self.mk_add(value, one);
        let add_zero = self.add_zero_eq(value);
        self.lt_cast_left(value_plus_zero, value, successor, lifted, add_zero)
    }

    /// `Eq Z (add (neg b) (add b t)) t` from additive ring axioms.
    fn prove_neg_add_sum_eq(&mut self, b: ExprId, t: ExprId) -> ExprId {
        let neg_b = self.mk_neg(b);
        let neg_b_b = self.mk_add(neg_b, b);
        let b_neg_b = self.mk_add(b, neg_b);
        let comm = self.add_comm_eq(neg_b, b);
        let cancel = self.add_neg_eq(b);
        let zero = self.mk_zero();
        let neg_b_b_zero = self.eq_trans(neg_b_b, b_neg_b, zero, comm, cancel);

        let inner_plus_t = self.mk_add(neg_b_b, t);
        let b_plus_t = self.mk_add(b, t);
        let neg_b_plus_sum = self.mk_add(neg_b, b_plus_t);
        let assoc = self.add_assoc_eq(neg_b, b, t);
        let assoc_sym = self.eq_symm(inner_plus_t, neg_b_plus_sum, assoc);
        let zero_plus_t = self.mk_add(zero, t);
        let collapse_inner = self.congr_add_left(neg_b_b, zero, t, neg_b_b_zero);
        let zero_t_comm = self.add_comm_eq(zero, t);
        let t_zero = self.mk_add(t, zero);
        let t_zero_t = self.add_zero_eq(t);
        let zero_plus_t_t = self.eq_trans(zero_plus_t, t_zero, t, zero_t_comm, t_zero_t);
        let inner_plus_t_t =
            self.eq_trans(inner_plus_t, zero_plus_t, t, collapse_inner, zero_plus_t_t);
        self.eq_trans(neg_b_plus_sum, inner_plus_t, t, assoc_sym, inner_plus_t_t)
    }

    fn require_nested_xor_type(
        &mut self,
        proof: ExprId,
        expected: ExprId,
        stage: &str,
    ) -> Result<(), ReconstructError> {
        let inferred =
            self.kernel
                .infer(proof)
                .map_err(|error| ReconstructError::KernelRejected {
                    rule: "int_nested_xor".to_owned(),
                    detail: format!("{stage} infer failed: {error:?}"),
                })?;
        if self.kernel.def_eq(inferred, expected) {
            Ok(())
        } else {
            Err(ReconstructError::KernelRejected {
                rule: "int_nested_xor".to_owned(),
                detail: format!("{stage} inferred the wrong proposition"),
            })
        }
    }

    fn iff_intro(
        &mut self,
        left: ExprId,
        right: ExprId,
        forward: ExprId,
        backward: ExprId,
    ) -> ExprId {
        let intro = self.kernel.const_(self.int.logic.iff_intro, Vec::new());
        let intro = self.kernel.app(intro, left);
        let intro = self.kernel.app(intro, right);
        let intro = self.kernel.app(intro, forward);
        self.kernel.app(intro, backward)
    }

    fn iff_project(
        &mut self,
        left: ExprId,
        right: ExprId,
        proof: ExprId,
        select_forward: bool,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let (domain, codomain) = if select_forward {
            (left, right)
        } else {
            (right, left)
        };
        let arrow = self.kernel.pi(anon, domain, codomain, BinderInfo::Default);
        let iff = self.mk_iff(left, right);
        let motive = self.kernel.lam(anon, iff, arrow, BinderInfo::Default);
        let chosen = if select_forward {
            self.kernel.bvar(1)
        } else {
            self.kernel.bvar(0)
        };
        let backward_ty = self.kernel.pi(anon, right, left, BinderInfo::Default);
        let minor = self
            .kernel
            .lam(anon, backward_ty, chosen, BinderInfo::Default);
        let forward_ty = self.kernel.pi(anon, left, right, BinderInfo::Default);
        let minor = self
            .kernel
            .lam(anon, forward_ty, minor, BinderInfo::Default);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.int.logic.iff_rec, vec![zero]);
        let rec = self.kernel.app(rec, left);
        let rec = self.kernel.app(rec, right);
        let rec = self.kernel.app(rec, motive);
        let rec = self.kernel.app(rec, minor);
        self.kernel.app(rec, proof)
    }

    fn const_implication(&mut self, domain: ExprId, _codomain: ExprId, proof: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        self.kernel.lam(anon, domain, proof, BinderInfo::Default)
    }

    fn negate_negation(&mut self, negated_prop: ExprId, positive: ExprId) -> ExprId {
        let fvar = self.fresh_fvar();
        let negation = self.kernel.fvar(fvar);
        let false_proof = self.kernel.app(negation, positive);
        let body = self.kernel.abstract_fvars(false_proof, &[fvar]);
        let anon = self.kernel.anon();
        self.kernel
            .lam(anon, negated_prop, body, BinderInfo::Default)
    }

    /// Turn `Not (Iff left right)` into `Not (Iff right left)` by projecting
    /// both directions from the supplied swapped `Iff` and rebuilding the
    /// original orientation before applying the negation.
    fn swap_negated_iff(&mut self, left: ExprId, right: ExprId, not_iff: ExprId) -> ExprId {
        let swapped_prop = self.mk_iff(right, left);
        let fvar = self.fresh_fvar();
        let swapped = self.kernel.fvar(fvar);
        let left_to_right = self.iff_project(right, left, swapped, false);
        let right_to_left = self.iff_project(right, left, swapped, true);
        let original = self.iff_intro(left, right, left_to_right, right_to_left);
        let false_proof = self.kernel.app(not_iff, original);
        let body = self.kernel.abstract_fvars(false_proof, &[fvar]);
        let anon = self.kernel.anon();
        self.kernel
            .lam(anon, swapped_prop, body, BinderInfo::Default)
    }

    fn classical_em(&mut self, prop: ExprId) -> Result<ExprId, ReconstructError> {
        let not_prop = self.mk_not(prop);
        let em_prop = self.mk_or(prop, not_prop);
        let name = self.fresh_name("em");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: Vec::new(),
                ty: em_prop,
            })
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "int_nested_xor".to_owned(),
                detail: format!("excluded-middle axiom did not admit: {error:?}"),
            })?;
        Ok(self.kernel.const_(name, Vec::new()))
    }

    fn or_rec_prop(
        &mut self,
        left: ExprId,
        right: ExprId,
        target: ExprId,
        left_case: ExprId,
        right_case: ExprId,
        proof: ExprId,
    ) -> ExprId {
        let anon = self.kernel.anon();
        let disjunction = self.mk_or(left, right);
        let motive = self
            .kernel
            .lam(anon, disjunction, target, BinderInfo::Default);
        let rec = self.kernel.const_(self.int.logic.or_rec, vec![]);
        let rec = self.kernel.app(rec, left);
        let rec = self.kernel.app(rec, right);
        let rec = self.kernel.app(rec, motive);
        let rec = self.kernel.app(rec, left_case);
        let rec = self.kernel.app(rec, right_case);
        self.kernel.app(rec, proof)
    }

    fn impossible_implication(
        &mut self,
        domain: ExprId,
        target: ExprId,
        not_domain: ExprId,
    ) -> ExprId {
        let fvar = self.fresh_fvar();
        let hypothesis = self.kernel.fvar(fvar);
        let false_proof = self.kernel.app(not_domain, hypothesis);
        let target_proof = self.ex_falso(target, false_proof);
        let body = self.kernel.abstract_fvars(target_proof, &[fvar]);
        let anon = self.kernel.anon();
        self.kernel.lam(anon, domain, body, BinderInfo::Default)
    }

    fn derive_xor_other_from_false(
        &mut self,
        left: ExprId,
        right: ExprId,
        xor_proof: ExprId,
        not_false_side: ExprId,
        false_is_left: bool,
    ) -> Result<ExprId, ReconstructError> {
        let target = if false_is_left { right } else { left };
        let not_target = self.mk_not(target);
        let em = self.classical_em(target)?;
        let target_bvar = self.kernel.bvar(0);
        let left_case = self.const_implication(target, target, target_bvar);

        let not_target_fvar = self.fresh_fvar();
        let not_target_proof = self.kernel.fvar(not_target_fvar);
        let (forward, backward) = if false_is_left {
            (
                self.impossible_implication(left, right, not_false_side),
                self.impossible_implication(right, left, not_target_proof),
            )
        } else {
            (
                self.impossible_implication(left, right, not_target_proof),
                self.impossible_implication(right, left, not_false_side),
            )
        };
        let equal_when_false = self.iff_intro(left, right, forward, backward);
        let contradiction = self.kernel.app(xor_proof, equal_when_false);
        let target_from_false = self.ex_falso(target, contradiction);
        let right_case_body = self
            .kernel
            .abstract_fvars(target_from_false, &[not_target_fvar]);
        let anon = self.kernel.anon();
        let right_case = self
            .kernel
            .lam(anon, not_target, right_case_body, BinderInfo::Default);
        Ok(self.or_rec_prop(target, not_target, target, left_case, right_case, em))
    }

    fn emit_nested_xor_prop(
        &mut self,
        arena: &TermArena,
        term: TermId,
        binders: &[SymbolId],
    ) -> Result<ExprId, ReconstructError> {
        match arena.node(term) {
            TermNode::App {
                op: Op::BoolXor,
                args,
            } => {
                let [left, right] = &**args else {
                    return Err(nested_xor_decline("XOR is not binary"));
                };
                let left = self.emit_nested_xor_prop(arena, *left, binders)?;
                let right = self.emit_nested_xor_prop(arena, *right, binders)?;
                let iff = self.mk_iff(left, right);
                Ok(self.mk_not(iff))
            }
            TermNode::App {
                op: Op::Forall(binder),
                args,
            } => {
                let [body] = &**args else {
                    return Err(nested_xor_decline("universal is not unary"));
                };
                let mut nested_binders = binders.to_vec();
                nested_binders.push(*binder);
                let body = self.emit_nested_xor_prop(arena, *body, &nested_binders)?;
                let z_ty = self.kernel.const_(self.int.z, Vec::new());
                let anon = self.kernel.anon();
                Ok(self.kernel.pi(anon, z_ty, body, BinderInfo::Default))
            }
            TermNode::App { op: Op::Eq, args } => {
                let [left, right] = &**args else {
                    return Err(nested_xor_decline("equality is not binary"));
                };
                if matches!(arena.node(*left), TermNode::App { op: Op::Ite, .. })
                    && matches!(arena.node(*right), TermNode::App { op: Op::Ite, .. })
                {
                    let left_guard = ite_guard(arena, *left)?;
                    let right_guard = ite_guard(arena, *right)?;
                    let left = self.emit_nested_xor_prop(arena, left_guard, binders)?;
                    let right = self.emit_nested_xor_prop(arena, right_guard, binders)?;
                    Ok(self.mk_iff(left, right))
                } else {
                    let left = self.emit_closed_cex_int_term(arena, *left, binders)?;
                    let right = self.emit_closed_cex_int_term(arena, *right, binders)?;
                    Ok(self.mk_eq(left, right))
                }
            }
            _ => Err(nested_xor_decline(
                "Boolean body uses an operator outside XOR/equality/forall",
            )),
        }
    }

    fn prove_pivot_guard(
        &mut self,
        arena: &TermArena,
        guard: TermId,
        certificate: &IntNestedXorRefutationCertificate,
    ) -> Result<ExprId, ReconstructError> {
        let symbol = guard_symbol(arena, guard)
            .ok_or_else(|| nested_xor_decline("selector child is not a symbol equality"))?;
        let value = if symbol == certificate.active {
            certificate.active_pivot
        } else if symbol == certificate.passive {
            certificate.passive_pivot
        } else {
            return Err(nested_xor_decline("selector child uses an unknown binder"));
        };
        self.prove_instantiated_true_guard(arena, guard, symbol, value)
    }

    fn emit_instantiated_guard(
        &mut self,
        arena: &TermArena,
        guard: TermId,
        symbol: SymbolId,
        value: i128,
    ) -> Result<ExprId, ReconstructError> {
        let (left, right, _, _) = instantiated_guard_zexprs(arena, guard, symbol, value)?;
        let left = self.emit_zexpr(&left);
        let right = self.emit_zexpr(&right);
        Ok(self.mk_eq(left, right))
    }

    fn prove_instantiated_true_guard(
        &mut self,
        arena: &TermArena,
        guard: TermId,
        symbol: SymbolId,
        value: i128,
    ) -> Result<ExprId, ReconstructError> {
        let (left, right, left_value, right_value) =
            instantiated_guard_zexprs(arena, guard, symbol, value)?;
        if left_value != right_value {
            return Err(nested_xor_decline("pivot guard is not true"));
        }
        self.prove_ground_zexpr_equality(&left, &right)
    }

    fn prove_instantiated_false_guard(
        &mut self,
        arena: &TermArena,
        guard: TermId,
        symbol: SymbolId,
        value: i128,
    ) -> Result<ExprId, ReconstructError> {
        let (left, right, left_value, right_value) =
            instantiated_guard_zexprs(arena, guard, symbol, value)?;
        let left_expr = self.emit_zexpr(&left);
        let right_expr = self.emit_zexpr(&right);
        let left_to_literal = self.prove_ground_zexpr_value(&left, left_value)?;
        let right_to_literal = self.prove_ground_zexpr_value(&right, right_value)?;
        let left_literal = self.mk_intlit(left_value);
        let right_literal = self.mk_intlit(right_value);
        let not_literal_eq = self.prove_adjacent_intlit_disequality(left_value, right_value)?;

        let fvar = self.fresh_fvar();
        let equality = self.kernel.fvar(fvar);
        let literal_to_left = self.eq_symm(left_expr, left_literal, left_to_literal);
        let literal_to_right = self.eq_trans(
            left_literal,
            left_expr,
            right_expr,
            literal_to_left,
            equality,
        );
        let literal_eq = self.eq_trans(
            left_literal,
            right_expr,
            right_literal,
            literal_to_right,
            right_to_literal,
        );
        let false_proof = self.kernel.app(not_literal_eq, literal_eq);
        let body = self.kernel.abstract_fvars(false_proof, &[fvar]);
        let eq_prop = self.mk_eq(left_expr, right_expr);
        let anon = self.kernel.anon();
        Ok(self.kernel.lam(anon, eq_prop, body, BinderInfo::Default))
    }

    fn prove_adjacent_intlit_disequality(
        &mut self,
        left: i128,
        right: i128,
    ) -> Result<ExprId, ReconstructError> {
        let (low, high, equality_low_high) = if left.checked_add(1) == Some(right) {
            (left, right, true)
        } else if right.checked_add(1) == Some(left) {
            (right, left, false)
        } else {
            return Err(nested_xor_decline("off-pivot values are not adjacent"));
        };
        let low_expr = self.mk_intlit(low);
        let high_expr = self.mk_intlit(high);
        let zero = self.mk_zero();
        let one = self.mk_one();
        let low_refl = self.le_refl_app(low_expr);
        let zero_lt_one = self.kernel.const_(self.int.zero_lt_one, Vec::new());
        let combined =
            self.add_lt_add_of_le_of_lt_app(low_expr, low_expr, zero, one, low_refl, zero_lt_one);
        let low_plus_zero = self.mk_add(low_expr, zero);
        let low_plus_one = self.mk_add(low_expr, one);
        let add_zero = self.add_zero_eq(low_expr);
        let low_lt_sum =
            self.lt_cast_left(low_plus_zero, low_expr, low_plus_one, combined, add_zero);
        let sum_zexpr = ZExpr::Add(Box::new(intlit_zexpr(low)), Box::new(intlit_zexpr(1)));
        let sum_to_high = self.prove_ground_zexpr_value(&sum_zexpr, high)?;
        let low_lt_high =
            self.lt_cast_right(low_expr, low_plus_one, high_expr, low_lt_sum, sum_to_high);

        let left_expr = self.mk_intlit(left);
        let right_expr = self.mk_intlit(right);
        let eq_prop = self.mk_eq(left_expr, right_expr);
        let fvar = self.fresh_fvar();
        let equality = self.kernel.fvar(fvar);
        let low_high_equality = if equality_low_high {
            equality
        } else {
            self.eq_symm(high_expr, low_expr, equality)
        };
        let high_low_equality = self.eq_symm(low_expr, high_expr, low_high_equality);
        let self_lt = self.lt_cast_right(
            low_expr,
            high_expr,
            low_expr,
            low_lt_high,
            high_low_equality,
        );
        let irrefl = self.lt_irrefl_app(low_expr);
        let false_proof = self.kernel.app(irrefl, self_lt);
        let body = self.kernel.abstract_fvars(false_proof, &[fvar]);
        let anon = self.kernel.anon();
        Ok(self.kernel.lam(anon, eq_prop, body, BinderInfo::Default))
    }
}

fn instantiated_guard_zexprs(
    arena: &TermArena,
    guard: TermId,
    symbol: SymbolId,
    value: i128,
) -> Result<(ZExpr, ZExpr, i128, i128), ReconstructError> {
    let (left, right) = binary_app_children(arena, guard, Op::Eq)?;
    if guard_symbol(arena, guard) != Some(symbol) {
        return Err(nested_xor_decline(
            "guard does not compare the expected binder to a literal",
        ));
    }
    let mut assignment = Assignment::new();
    assignment.set(symbol, Value::Int(value));
    let Ok(Value::Int(left_value)) = eval(arena, left, &assignment) else {
        return Err(nested_xor_decline("guard lhs did not evaluate to Int"));
    };
    let Ok(Value::Int(right_value)) = eval(arena, right, &assignment) else {
        return Err(nested_xor_decline("guard rhs did not evaluate to Int"));
    };
    let left_expr = closed_cex_ground_zexpr(arena, left, &assignment)?;
    let right_expr = closed_cex_ground_zexpr(arena, right, &assignment)?;
    Ok((left_expr, right_expr, left_value, right_value))
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

    /// `lt (intlit a)(intlit b)` for `a < b`. Derived: `b − a ≥ 1`, so
    /// `lt zero (intlit (b−a))`; add `intlit a` on the left of both sides
    /// (`add_lt_add_of_le_of_lt` with `le (intlit a)(intlit a)`), then renormalize
    /// `a + 0 → a` and `a + (b−a) → b`. To keep the proof small we instead use the
    /// ring fact directly: `lt a b ⇐ lt zero (b−a)` via casting.
    fn lt_intlit_intlit(&mut self, a: i128, b: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(b > a);
        let diff = b
            .checked_sub(a)
            .ok_or_else(|| ReconstructError::UnsupportedTerm {
                term: "integer literal difference overflow".to_owned(),
            })?;
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
}

mod affine_growth;
pub(crate) use affine_growth::int_affine_growth_lean_shape;
pub use affine_growth::reconstruct_int_affine_growth_to_lean_module;

mod counterexample_cover;
pub(crate) use counterexample_cover::quantified_counterexample_cover_lean_shape;
pub use counterexample_cover::reconstruct_quantified_counterexample_cover_to_lean_module;

mod diophantine;
pub use diophantine::{reconstruct_diophantine_proof, reconstruct_diophantine_to_lean_module};

mod equality_partition;
pub use equality_partition::reconstruct_single_pivot_equality_partition_to_lean_module;
pub(crate) use equality_partition::single_pivot_equality_partition_lean_shape;

mod euclidean_residue;
pub(crate) use euclidean_residue::int_euclidean_residue_lean_shape;
pub use euclidean_residue::reconstruct_int_euclidean_residue_to_lean_module;

mod inequality;
pub use inequality::{
    is_int_inequality_refutation, reconstruct_int_inequality_proof,
    reconstruct_int_inequality_to_lean_module,
};
