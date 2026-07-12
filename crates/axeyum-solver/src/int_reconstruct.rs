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

use crate::lia_gcd::{DiophantineCertificate, Equality, prove_lia_unsat_by_diophantine_certified};
use crate::quant_affine_growth_cert::{
    IntAffineGrowthRefutationCertificate, int_affine_growth_refutation,
};
use crate::quant_bool_model_sat::admitted_free_booleans;
use crate::quant_closed_counterexample_cert::{
    ClosedUniversalCounterexampleCertificate, check_closed_universal_counterexample,
};
use crate::quant_counterexample_cover::{
    QuantifiedCounterexampleCoverCase, QuantifiedCounterexampleCoverCertificate,
    check_quantified_counterexample_cover,
};
use crate::quant_eq_partition_cert::{
    EqualityPartitionRefutationCertificate, check_equality_partition_refutation,
};
use crate::quant_nested_xor_cert::{IntNestedXorRefutationCertificate, int_nested_xor_refutation};
use crate::quant_residue_cert::{
    IntEuclideanResidueRefutationCertificate, int_euclidean_residue_refutation,
};
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

/// Returns whether `assertions` has the canonical ADR-0104 clock spelling.
/// This router predicate is intentionally narrower than ADR-0095's independent
/// evidence matcher: the Lean proof currently preserves one exact binder,
/// arithmetic, and parser-preserved disjunction orientation.
pub(crate) fn int_euclidean_residue_lean_shape(arena: &TermArena, assertions: &[TermId]) -> bool {
    canonical_int_euclidean_residue(arena, assertions).is_some()
}

/// Reconstruct the canonical ADR-0095 Euclidean-residue refutation using the
/// general ADR-0104 integer-prelude decomposition theorem.
///
/// The only query axiom is the original universal. The decomposition theorem
/// supplies existential quotient/remainder witnesses; `Exists.rec` exposes
/// their recomposition and bounds, and three `Or.rec` branches contradict those
/// facts. No query-specific witness or refuter axiom is introduced.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] if the certificate is invalid,
/// the assertion is outside the canonical Lean slice, or the modulus exceeds
/// the bounded literal representation. Returns
/// [`ReconstructError::KernelRejected`] if the assembled proof does not infer to
/// `False`.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_int_euclidean_residue_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntEuclideanResidueRefutationCertificate,
) -> Result<String, ReconstructError> {
    if int_euclidean_residue_refutation(arena, assertions) != Some(*certificate) {
        return Err(residue_decline("invalid refutation certificate"));
    }
    let Some(canonical) = canonical_int_euclidean_residue(arena, assertions) else {
        return Err(residue_decline(
            "assertion is outside the canonical clock proof shape",
        ));
    };
    if canonical != *certificate {
        return Err(residue_decline(
            "certificate does not match the canonical assertion",
        ));
    }
    if certificate.modulus.unsigned_abs() > DIO_UNIT_MAX as u128 {
        return Err(residue_decline("modulus exceeds proof-size cap"));
    }

    let mut ctx = IntReconstructCtx::new();
    let dividend_name = ctx.var_const(0);
    let dividend = ctx.kernel.const_(dividend_name, Vec::new());
    let modulus = ctx.mk_intlit(certificate.modulus);
    let zero = ctx.mk_zero();

    // Faithfully encode the canonical input theorem with open fvars, then
    // abstract quotient followed by remainder to recover binder order `s, m`.
    let remainder_id = ctx.fresh_fvar();
    let quotient_id = ctx.fresh_fvar();
    let remainder = ctx.kernel.fvar(remainder_id);
    let quotient = ctx.kernel.fvar(quotient_id);
    let scaled = ctx.mk_mul(modulus, quotient);
    let sum = ctx.mk_add(scaled, remainder);
    let sum_eq_dividend = ctx.mk_eq(sum, dividend);
    let recomposition_disjunct = ctx.mk_not(sum_eq_dividend);
    let lower_disjunct = ctx.mk_lt(remainder, zero);
    let upper_disjunct = ctx.mk_le(modulus, remainder);
    let disequality_or_lower = ctx.mk_or(recomposition_disjunct, lower_disjunct);
    let universal_body = ctx.mk_or(disequality_or_lower, upper_disjunct);
    let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
    let anon = ctx.kernel.anon();
    let quotient_body = ctx.kernel.abstract_fvars(universal_body, &[quotient_id]);
    let after_quotient = ctx
        .kernel
        .pi(anon, z_ty, quotient_body, BinderInfo::Default);
    let remainder_body = ctx.kernel.abstract_fvars(after_quotient, &[remainder_id]);
    let universal_ty = ctx
        .kernel
        .pi(anon, z_ty, remainder_body, BinderInfo::Default);
    let universal = ctx.hyp_axiom(universal_ty)?;

    // Build exactly the existential proposition exposed by the prelude theorem.
    let theorem_recomposition = ctx.mk_eq(dividend, sum);
    let nonnegative = ctx.mk_le(zero, remainder);
    let below_modulus = ctx.mk_lt(remainder, modulus);
    let bounds = ctx.mk_and(nonnegative, below_modulus);
    let facts = ctx.mk_and(theorem_recomposition, bounds);
    let r_body = ctx.kernel.abstract_fvars(facts, &[remainder_id]);
    let r_predicate = ctx.kernel.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists_r = ctx.mk_exists(r_predicate);
    let q_body = ctx.kernel.abstract_fvars(exists_r, &[quotient_id]);
    let q_predicate = ctx.kernel.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists_q = ctx.mk_exists(q_predicate);

    let positive = ctx.lt_zero_intlit(certificate.modulus)?;
    let decomposition = ctx
        .kernel
        .const_(ctx.int.euclidean_decomposition, Vec::new());
    let decomposition = ctx.kernel.app(decomposition, dividend);
    let decomposition = ctx.kernel.app(decomposition, modulus);
    let decomposition = ctx.kernel.app(decomposition, positive);

    // Open the quotient witness, then the remainder witness and its conjunction.
    let q_major_id = ctx.fresh_fvar();
    let q_major = ctx.kernel.fvar(q_major_id);
    let facts_id = ctx.fresh_fvar();
    let facts_proof = ctx.kernel.fvar(facts_id);
    let recomposition = ctx.and_project(theorem_recomposition, bounds, facts_proof, true);
    let bounds_proof = ctx.and_project(theorem_recomposition, bounds, facts_proof, false);
    let nonnegative_proof = ctx.and_project(nonnegative, below_modulus, bounds_proof, true);
    let below_modulus_proof = ctx.and_project(nonnegative, below_modulus, bounds_proof, false);
    let universal_instance = ctx.kernel.app(universal, remainder);
    let universal_instance = ctx.kernel.app(universal_instance, quotient);

    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());

    // Branch 1: `k*q+r != t`, contradicted by `t = k*q+r` symmetry.
    let disequality_id = ctx.fresh_fvar();
    let disequality = ctx.kernel.fvar(disequality_id);
    let sum_equals_dividend = ctx.eq_symm(dividend, sum, recomposition);
    let first_false = ctx.kernel.app(disequality, sum_equals_dividend);
    let first_body = ctx.kernel.abstract_fvars(first_false, &[disequality_id]);
    let first_case = ctx.kernel.lam(
        anon,
        recomposition_disjunct,
        first_body,
        BinderInfo::Default,
    );

    // Branch 2: `r < 0`, contradicted by `0 <= r`.
    let lower_id = ctx.fresh_fvar();
    let lower_proof = ctx.kernel.fvar(lower_id);
    let lower_self =
        ctx.lt_of_lt_of_le_app(remainder, zero, remainder, lower_proof, nonnegative_proof);
    let lower_irrefl = ctx.lt_irrefl_app(remainder);
    let lower_false = ctx.kernel.app(lower_irrefl, lower_self);
    let lower_body = ctx.kernel.abstract_fvars(lower_false, &[lower_id]);
    let lower_case = ctx
        .kernel
        .lam(anon, lower_disjunct, lower_body, BinderInfo::Default);

    // Branch 3: `k <= r`, contradicted by `r < k`.
    let upper_id = ctx.fresh_fvar();
    let upper_proof = ctx.kernel.fvar(upper_id);
    let upper_self = ctx.lt_of_lt_of_le_app(
        remainder,
        modulus,
        remainder,
        below_modulus_proof,
        upper_proof,
    );
    let upper_irrefl = ctx.lt_irrefl_app(remainder);
    let upper_false = ctx.kernel.app(upper_irrefl, upper_self);
    let upper_body = ctx.kernel.abstract_fvars(upper_false, &[upper_id]);
    let upper_case = ctx
        .kernel
        .lam(anon, upper_disjunct, upper_body, BinderInfo::Default);

    let left_id = ctx.fresh_fvar();
    let left_proof = ctx.kernel.fvar(left_id);
    let left_false = ctx.or_rec_prop(
        recomposition_disjunct,
        lower_disjunct,
        false_,
        first_case,
        lower_case,
        left_proof,
    );
    let left_body = ctx.kernel.abstract_fvars(left_false, &[left_id]);
    let left_case = ctx
        .kernel
        .lam(anon, disequality_or_lower, left_body, BinderInfo::Default);
    let contradiction = ctx.or_rec_prop(
        disequality_or_lower,
        upper_disjunct,
        false_,
        left_case,
        upper_case,
        universal_instance,
    );

    let facts_body = ctx.kernel.abstract_fvars(contradiction, &[facts_id]);
    let facts_minor = ctx.kernel.lam(anon, facts, facts_body, BinderInfo::Default);
    let r_minor_body = ctx.kernel.abstract_fvars(facts_minor, &[remainder_id]);
    let r_minor = ctx
        .kernel
        .lam(anon, z_ty, r_minor_body, BinderInfo::Default);
    let q_false = ctx.exists_elim_false(r_predicate, exists_r, r_minor, q_major);
    let q_major_body = ctx.kernel.abstract_fvars(q_false, &[q_major_id]);
    let q_major_minor = ctx
        .kernel
        .lam(anon, exists_r, q_major_body, BinderInfo::Default);
    let q_minor_body = ctx.kernel.abstract_fvars(q_major_minor, &[quotient_id]);
    let q_minor = ctx
        .kernel
        .lam(anon, z_ty, q_minor_body, BinderInfo::Default);
    let proof = ctx.exists_elim_false(q_predicate, exists_q, q_minor, decomposition);

    let inferred =
        ctx.kernel_mut()
            .infer(proof)
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "int_euclidean_residue".to_owned(),
                detail: format!("infer failed: {error:?}"),
            })?;
    if !ctx.kernel_mut().def_eq(inferred, false_) {
        return Err(ReconstructError::KernelRejected {
            rule: "int_euclidean_residue".to_owned(),
            detail: "residue reconstruction did not infer to False".to_owned(),
        });
    }
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

fn residue_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("integer Euclidean residue: {detail}"),
    }
}

#[allow(clippy::too_many_lines)]
fn canonical_int_euclidean_residue(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntEuclideanResidueRefutationCertificate> {
    let [assertion] = assertions else {
        return None;
    };
    let certificate = int_euclidean_residue_refutation(arena, assertions)?;
    if certificate.assertion != *assertion {
        return None;
    }
    let (binders, body) = peel_closed_foralls(arena, *assertion)?;
    if binders != [certificate.remainder, certificate.quotient] {
        return None;
    }
    let TermNode::Symbol(dividend) = arena.node(certificate.dividend) else {
        return None;
    };
    if *dividend == certificate.remainder
        || *dividend == certificate.quotient
        || arena.symbol(*dividend).1 != Sort::Int
    {
        return None;
    }
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [disequality_or_lower, upper] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(*disequality_or_lower)
    else {
        return None;
    };
    let [disequality, lower] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(*disequality)
    else {
        return None;
    };
    let [equality] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*equality) else {
        return None;
    };
    let [sum, found_dividend] = &**args else {
        return None;
    };
    if *found_dividend != certificate.dividend {
        return None;
    }
    let TermNode::App {
        op: Op::IntAdd,
        args,
    } = arena.node(*sum)
    else {
        return None;
    };
    let [scaled, found_remainder] = &**args else {
        return None;
    };
    if !matches!(arena.node(*found_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(*scaled)
    else {
        return None;
    };
    let [found_modulus, found_quotient] = &**args else {
        return None;
    };
    if !matches!(arena.node(*found_modulus), TermNode::IntConst(found) if *found == certificate.modulus)
        || !matches!(arena.node(*found_quotient), TermNode::Symbol(found) if *found == certificate.quotient)
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntLt,
        args,
    } = arena.node(*lower)
    else {
        return None;
    };
    let [lower_remainder, lower_zero] = &**args else {
        return None;
    };
    if !matches!(arena.node(*lower_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
        || !matches!(arena.node(*lower_zero), TermNode::IntConst(0))
    {
        return None;
    }
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(*upper)
    else {
        return None;
    };
    let [upper_remainder, upper_modulus] = &**args else {
        return None;
    };
    if !matches!(arena.node(*upper_remainder), TermNode::Symbol(found) if *found == certificate.remainder)
        || !matches!(arena.node(*upper_modulus), TermNode::IntConst(found) if *found == certificate.modulus)
    {
        return None;
    }
    Some(certificate)
}

/// Returns whether ADR-0097's independent checker recognizes a proof shape.
/// Certificate regeneration and kernel inference remain the authoritative
/// acceptance gates.
pub(crate) fn int_affine_growth_lean_shape(arena: &TermArena, assertions: &[TermId]) -> bool {
    int_affine_growth_refutation(arena, assertions).is_some()
}

#[derive(Debug, Clone, Copy)]
struct AffineGrowthProps {
    body: ExprId,
    equality: ExprId,
    then_implication: ExprId,
    else_guard: ExprId,
    else_implication: ExprId,
}

/// Reconstruct an ADR-0097 positive-slope affine-growth certificate through
/// ADR-0104's Euclidean decomposition theorem, guarded exact `ite` semantics,
/// and two consecutive universal instances.
///
/// Bound-variable-free parameter terms are represented by consistently shared
/// opaque integer constants. This is a denotational abstraction of their fixed
/// values, while every original quantified binder remains a genuine dependent
/// product. No query-specific witness/refuter axiom or additional arithmetic
/// theorem is introduced.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for an invalid certificate,
/// malformed universal prefix, or coefficient beyond the proof-size cap, and
/// [`ReconstructError::KernelRejected`] if any generated proof fails its kernel
/// gate.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_int_affine_growth_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntAffineGrowthRefutationCertificate,
) -> Result<String, ReconstructError> {
    if int_affine_growth_refutation(arena, assertions) != Some(*certificate) {
        return Err(affine_growth_decline("invalid refutation certificate"));
    }
    if certificate.coefficient <= 0 || certificate.coefficient.unsigned_abs() > DIO_UNIT_MAX as u128
    {
        return Err(affine_growth_decline(
            "coefficient is non-positive or exceeds proof-size cap",
        ));
    }
    let Some((binders, _)) = peel_closed_foralls(arena, certificate.assertion) else {
        return Err(affine_growth_decline(
            "certificate assertion is not a universal prefix",
        ));
    };
    if binders.is_empty()
        || binders
            .iter()
            .any(|&binder| arena.symbol(binder).1 != Sort::Int)
        || !binders.contains(&certificate.variable)
    {
        return Err(affine_growth_decline(
            "universal prefix is not the checked all-Int class",
        ));
    }

    let mut ctx = IntReconstructCtx::new();
    let mut parameter_indices = BTreeMap::new();
    for term in [
        certificate.pivot,
        certificate.then_value,
        certificate.else_value,
        certificate.threshold,
    ] {
        let next = parameter_indices.len();
        parameter_indices.entry(term).or_insert(next);
    }
    let pivot = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.pivot);
    let then_value = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.then_value);
    let else_value = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.else_value);
    let threshold = affine_parameter_expr(&mut ctx, &parameter_indices, certificate.threshold);
    let coefficient = ctx.mk_intlit(certificate.coefficient);

    // Encode the complete universal. The integer `ite` is represented exactly
    // by its two guarded branch implications.
    let mut binder_fvars = BTreeMap::new();
    for &binder in &binders {
        let id = ctx.fresh_fvar();
        binder_fvars.insert(binder, id);
    }
    let active_id = binder_fvars[&certificate.variable];
    let active = ctx.kernel.fvar(active_id);
    let open_props = affine_growth_props(
        &mut ctx,
        active,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
    let anon = ctx.kernel.anon();
    let mut universal_ty = open_props.body;
    for &binder in binders.iter().rev() {
        universal_ty = ctx
            .kernel
            .abstract_fvars(universal_ty, &[binder_fvars[&binder]]);
        universal_ty = ctx.kernel.pi(anon, z_ty, universal_ty, BinderInfo::Default);
    }
    let universal = ctx.hyp_axiom(universal_ty)?;

    // Apply Euclidean decomposition to the fixed value `b+t`.
    let dividend = ctx.mk_add(else_value, threshold);
    let quotient_id = ctx.fresh_fvar();
    let remainder_id = ctx.fresh_fvar();
    let quotient = ctx.kernel.fvar(quotient_id);
    let remainder = ctx.kernel.fvar(remainder_id);
    let scaled_quotient = ctx.mk_mul(coefficient, quotient);
    let decomposition_sum = ctx.mk_add(scaled_quotient, remainder);
    let recomposition = ctx.mk_eq(dividend, decomposition_sum);
    let zero = ctx.mk_zero();
    let nonnegative = ctx.mk_le(zero, remainder);
    let below_coefficient = ctx.mk_lt(remainder, coefficient);
    let bounds = ctx.mk_and(nonnegative, below_coefficient);
    let facts = ctx.mk_and(recomposition, bounds);
    let r_body = ctx.kernel.abstract_fvars(facts, &[remainder_id]);
    let r_predicate = ctx.kernel.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists_r = ctx.mk_exists(r_predicate);
    let q_body = ctx.kernel.abstract_fvars(exists_r, &[quotient_id]);
    let q_predicate = ctx.kernel.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists_q = ctx.mk_exists(q_predicate);
    let positive = ctx.lt_zero_intlit(certificate.coefficient)?;
    let decomposition = ctx
        .kernel
        .const_(ctx.int.euclidean_decomposition, Vec::new());
    let decomposition = ctx.kernel.app(decomposition, dividend);
    let decomposition = ctx.kernel.app(decomposition, coefficient);
    let decomposition = ctx.kernel.app(decomposition, positive);
    ctx.require_affine_growth_type(decomposition, exists_q, "Euclidean decomposition")?;

    let q_major_id = ctx.fresh_fvar();
    let q_major = ctx.kernel.fvar(q_major_id);
    let facts_id = ctx.fresh_fvar();
    let facts_proof = ctx.kernel.fvar(facts_id);
    let recomposition_proof = ctx.and_project(recomposition, bounds, facts_proof, true);
    let bounds_proof = ctx.and_project(recomposition, bounds, facts_proof, false);
    let below_proof = ctx.and_project(nonnegative, below_coefficient, bounds_proof, false);

    let one = ctx.mk_one();
    let first = ctx.mk_add(quotient, one);
    let second = ctx.mk_add(first, one);
    let first_scaled = ctx.mk_mul(coefficient, first);
    let second_scaled = ctx.mk_mul(coefficient, second);
    let neg_else = ctx.mk_neg(else_value);
    let first_difference = ctx.mk_add(first_scaled, neg_else);
    let second_difference = ctx.mk_add(second_scaled, neg_else);

    // b+t = c*q+r and r<c imply b+t <= c*q+c = c*(q+1).
    let remainder_le_coefficient = ctx.le_of_lt_app(remainder, coefficient, below_proof);
    let scaled_refl = ctx.le_refl_app(scaled_quotient);
    let sum_le_sum = ctx.add_le_add_app(
        scaled_quotient,
        scaled_quotient,
        remainder,
        coefficient,
        scaled_refl,
        remainder_le_coefficient,
    );
    let scaled_plus_coefficient = ctx.mk_add(scaled_quotient, coefficient);
    let distributed = ctx.left_distrib_eq(coefficient, quotient, one);
    let coefficient_times_one = ctx.mk_mul(coefficient, one);
    let mul_one = ctx.mul_one_eq(coefficient);
    let collapse_one =
        ctx.congr_add_right(scaled_quotient, coefficient_times_one, coefficient, mul_one);
    let scaled_plus_times_one = ctx.mk_add(scaled_quotient, coefficient_times_one);
    let first_scaled_to_sum = ctx.eq_trans(
        first_scaled,
        scaled_plus_times_one,
        scaled_plus_coefficient,
        distributed,
        collapse_one,
    );
    let sum_to_first_scaled =
        ctx.eq_symm(first_scaled, scaled_plus_coefficient, first_scaled_to_sum);
    let sum_eq_dividend = ctx.eq_symm(dividend, decomposition_sum, recomposition_proof);
    let dividend_le_sum = ctx.le_cast_left(
        decomposition_sum,
        dividend,
        scaled_plus_coefficient,
        sum_le_sum,
        sum_eq_dividend,
    );
    let dividend_le_first_scaled = ctx.le_cast_right(
        dividend,
        scaled_plus_coefficient,
        first_scaled,
        dividend_le_sum,
        sum_to_first_scaled,
    );

    // Add `-b` to both sides and normalize `-b+(b+t)` to `t`.
    let neg_else_refl = ctx.le_refl_app(neg_else);
    let shifted = ctx.add_le_add_app(
        neg_else,
        neg_else,
        dividend,
        first_scaled,
        neg_else_refl,
        dividend_le_first_scaled,
    );
    let shifted_left = ctx.mk_add(neg_else, dividend);
    let shifted_right = ctx.mk_add(neg_else, first_scaled);
    let left_to_threshold = ctx.prove_neg_add_sum_eq(else_value, threshold);
    let threshold_le_shifted = ctx.le_cast_left(
        shifted_left,
        threshold,
        shifted_right,
        shifted,
        left_to_threshold,
    );
    let right_to_first_difference = ctx.add_comm_eq(neg_else, first_scaled);
    let first_inequality = ctx.le_cast_right(
        threshold,
        shifted_right,
        first_difference,
        threshold_le_shifted,
        right_to_first_difference,
    );

    // Positive slope makes the second consecutive candidate at least as large.
    let zero_le_coefficient = ctx.le_of_lt_app(zero, coefficient, positive);
    let first_lt_second = ctx.prove_successor_lt(first);
    let first_le_second = ctx.le_of_lt_app(first, second, first_lt_second);
    let scaled_monotone = ctx.mul_le_mul_left_app(
        coefficient,
        first,
        second,
        zero_le_coefficient,
        first_le_second,
    );
    let neg_else_refl = ctx.le_refl_app(neg_else);
    let difference_monotone = ctx.add_le_add_app(
        first_scaled,
        second_scaled,
        neg_else,
        neg_else,
        scaled_monotone,
        neg_else_refl,
    );
    let second_inequality = ctx.le_trans_app(
        threshold,
        first_difference,
        second_difference,
        first_inequality,
        difference_monotone,
    );

    let first_props = affine_growth_props(
        &mut ctx,
        first,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let second_props = affine_growth_props(
        &mut ctx,
        second,
        coefficient,
        pivot,
        then_value,
        else_value,
        threshold,
    );
    let first_instance = instantiate_affine_growth_universal(
        &mut ctx,
        universal,
        &binders,
        certificate.variable,
        first,
    );
    let second_instance = instantiate_affine_growth_universal(
        &mut ctx,
        universal,
        &binders,
        certificate.variable,
        second,
    );

    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());

    // Each guarded else branch plus its positive affine comparison proves
    // `Not (Not (candidate = pivot))` constructively.
    let second_else = ctx.and_project(
        second_props.then_implication,
        second_props.else_implication,
        second_instance,
        false,
    );
    let second_guard_id = ctx.fresh_fvar();
    let second_guard = ctx.kernel.fvar(second_guard_id);
    let second_negated = ctx.kernel.app(second_else, second_guard);
    let second_guard_false = ctx.kernel.app(second_negated, second_inequality);
    let second_guard_body = ctx
        .kernel
        .abstract_fvars(second_guard_false, &[second_guard_id]);
    let double_neg_second = ctx.kernel.lam(
        anon,
        second_props.else_guard,
        second_guard_body,
        BinderInfo::Default,
    );

    let first_else = ctx.and_project(
        first_props.then_implication,
        first_props.else_implication,
        first_instance,
        false,
    );
    let first_guard_id = ctx.fresh_fvar();
    let first_guard = ctx.kernel.fvar(first_guard_id);
    let first_negated = ctx.kernel.app(first_else, first_guard);
    let first_guard_false = ctx.kernel.app(first_negated, first_inequality);
    let first_guard_body = ctx
        .kernel
        .abstract_fvars(first_guard_false, &[first_guard_id]);
    let double_neg_first = ctx.kernel.lam(
        anon,
        first_props.else_guard,
        first_guard_body,
        BinderInfo::Default,
    );

    // If the first candidate equals the pivot, strict consecutiveness makes
    // the second candidate unequal to it; that contradicts the second double
    // negation. Hence the first candidate is unequal, contradicting its own
    // double negation. No excluded middle is required.
    let first_eq_id = ctx.fresh_fvar();
    let first_eq_pivot = ctx.kernel.fvar(first_eq_id);
    let second_eq_id = ctx.fresh_fvar();
    let second_eq_pivot = ctx.kernel.fvar(second_eq_id);
    let pivot_eq_second = ctx.eq_symm(second, pivot, second_eq_pivot);
    let first_eq_second = ctx.eq_trans(first, pivot, second, first_eq_pivot, pivot_eq_second);
    let second_eq_first = ctx.eq_symm(first, second, first_eq_second);
    let first_self_lt = ctx.lt_cast_right(first, second, first, first_lt_second, second_eq_first);
    let first_irrefl = ctx.lt_irrefl_app(first);
    let distinct_false = ctx.kernel.app(first_irrefl, first_self_lt);
    let second_eq_body = ctx.kernel.abstract_fvars(distinct_false, &[second_eq_id]);
    let second_not_pivot = ctx.kernel.lam(
        anon,
        second_props.equality,
        second_eq_body,
        BinderInfo::Default,
    );
    let first_eq_false = ctx.kernel.app(double_neg_second, second_not_pivot);
    let first_eq_body = ctx.kernel.abstract_fvars(first_eq_false, &[first_eq_id]);
    let first_not_pivot = ctx.kernel.lam(
        anon,
        first_props.equality,
        first_eq_body,
        BinderInfo::Default,
    );
    let contradiction = ctx.kernel.app(double_neg_first, first_not_pivot);

    let facts_body = ctx.kernel.abstract_fvars(contradiction, &[facts_id]);
    let facts_minor = ctx.kernel.lam(anon, facts, facts_body, BinderInfo::Default);
    let r_minor_body = ctx.kernel.abstract_fvars(facts_minor, &[remainder_id]);
    let r_minor = ctx
        .kernel
        .lam(anon, z_ty, r_minor_body, BinderInfo::Default);
    let q_false = ctx.exists_elim_false(r_predicate, exists_r, r_minor, q_major);
    let q_major_body = ctx.kernel.abstract_fvars(q_false, &[q_major_id]);
    let q_major_minor = ctx
        .kernel
        .lam(anon, exists_r, q_major_body, BinderInfo::Default);
    let q_minor_body = ctx.kernel.abstract_fvars(q_major_minor, &[quotient_id]);
    let q_minor = ctx
        .kernel
        .lam(anon, z_ty, q_minor_body, BinderInfo::Default);
    let proof = ctx.exists_elim_false(q_predicate, exists_q, q_minor, decomposition);
    ctx.require_affine_growth_type(proof, false_, "final contradiction")?;
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

fn affine_growth_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("integer affine growth: {detail}"),
    }
}

fn affine_parameter_expr(
    ctx: &mut IntReconstructCtx,
    indices: &BTreeMap<TermId, usize>,
    term: TermId,
) -> ExprId {
    let name = ctx.var_const(indices[&term]);
    ctx.kernel.const_(name, Vec::new())
}

fn affine_growth_props(
    ctx: &mut IntReconstructCtx,
    variable: ExprId,
    coefficient: ExprId,
    pivot: ExprId,
    then_value: ExprId,
    else_value: ExprId,
    threshold: ExprId,
) -> AffineGrowthProps {
    let equality = ctx.mk_eq(variable, pivot);
    let not_equality = ctx.mk_not(equality);
    let scaled = ctx.mk_mul(coefficient, variable);
    let neg_then = ctx.mk_neg(then_value);
    let then_difference = ctx.mk_add(scaled, neg_then);
    let then_comparison = ctx.mk_le(threshold, then_difference);
    let then_negated = ctx.mk_not(then_comparison);
    let neg_else = ctx.mk_neg(else_value);
    let else_difference = ctx.mk_add(scaled, neg_else);
    let else_comparison = ctx.mk_le(threshold, else_difference);
    let else_negated = ctx.mk_not(else_comparison);
    let anon = ctx.kernel.anon();
    let then_implication = ctx
        .kernel
        .pi(anon, equality, then_negated, BinderInfo::Default);
    let else_implication = ctx
        .kernel
        .pi(anon, not_equality, else_negated, BinderInfo::Default);
    let body = ctx.mk_and(then_implication, else_implication);
    AffineGrowthProps {
        body,
        equality,
        then_implication,
        else_guard: not_equality,
        else_implication,
    }
}

fn instantiate_affine_growth_universal(
    ctx: &mut IntReconstructCtx,
    universal: ExprId,
    binders: &[SymbolId],
    active: SymbolId,
    candidate: ExprId,
) -> ExprId {
    let mut proof = universal;
    for &binder in binders {
        let witness = if binder == active {
            candidate
        } else {
            ctx.mk_zero()
        };
        proof = ctx.kernel.app(proof, witness);
    }
    proof
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PartitionFormula {
    True,
    False,
    BoolAtom(SymbolId),
    IntAtom(SymbolId, i128),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Implies(Box<Self>, Box<Self>),
    Iff(Box<Self>, Box<Self>),
    Forall(SymbolId, Sort, Box<Self>),
    Exists(SymbolId, Sort, Box<Self>),
}

#[derive(Debug, Clone)]
enum PartitionInt {
    Literal(i128),
    Ite(Box<PartitionFormula>, Box<Self>, Box<Self>),
}

fn partition_ite(
    condition: PartitionFormula,
    then_formula: PartitionFormula,
    else_formula: PartitionFormula,
) -> PartitionFormula {
    PartitionFormula::Or(
        Box::new(PartitionFormula::And(
            Box::new(condition.clone()),
            Box::new(then_formula),
        )),
        Box::new(PartitionFormula::And(
            Box::new(PartitionFormula::Not(Box::new(condition))),
            Box::new(else_formula),
        )),
    )
}

fn lower_single_pivot_partition(
    arena: &TermArena,
    assertion: TermId,
) -> Result<PartitionFormula, ReconstructError> {
    let mut bound = BTreeMap::new();
    let formula = lower_partition_bool(arena, assertion, &mut bound)?;
    let mut symbols = BTreeSet::new();
    collect_partition_binders(&formula, &mut symbols);
    for symbol in symbols {
        let mut constants = BTreeSet::new();
        collect_partition_constants(&formula, symbol, &mut constants);
        if constants.len() > 1 {
            return Err(eq_partition_decline(
                "an Int binder is compared with multiple distinct literals",
            ));
        }
    }
    Ok(formula)
}

fn lower_partition_bool(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionFormula, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(true) => Ok(PartitionFormula::True),
        TermNode::BoolConst(false) => Ok(PartitionFormula::False),
        TermNode::Symbol(symbol)
            if bound.get(symbol) == Some(&Sort::Bool) && arena.sort_of(term) == Sort::Bool =>
        {
            Ok(PartitionFormula::BoolAtom(*symbol))
        }
        TermNode::App {
            op: Op::Forall(symbol) | Op::Exists(symbol),
            args,
        } => {
            let [body] = &**args else {
                return Err(eq_partition_decline("quantifier is not unary"));
            };
            let sort = arena.symbol(*symbol).1;
            if !matches!(sort, Sort::Bool | Sort::Int) || bound.insert(*symbol, sort).is_some() {
                return Err(eq_partition_decline(
                    "quantifier binder is unsupported or duplicated",
                ));
            }
            let body = lower_partition_bool(arena, *body, bound)?;
            bound.remove(symbol);
            if matches!(
                arena.node(term),
                TermNode::App {
                    op: Op::Forall(_),
                    ..
                }
            ) {
                Ok(PartitionFormula::Forall(*symbol, sort, Box::new(body)))
            } else {
                Ok(PartitionFormula::Exists(*symbol, sort, Box::new(body)))
            }
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [arg]) => Ok(PartitionFormula::Not(Box::new(lower_partition_bool(
                arena, *arg, bound,
            )?))),
            (Op::BoolAnd, [left, right]) => Ok(PartitionFormula::And(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolOr, [left, right]) => Ok(PartitionFormula::Or(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolImplies, [left, right]) => Ok(PartitionFormula::Implies(
                Box::new(lower_partition_bool(arena, *left, bound)?),
                Box::new(lower_partition_bool(arena, *right, bound)?),
            )),
            (Op::BoolXor, [left, right]) => {
                Ok(PartitionFormula::Not(Box::new(PartitionFormula::Iff(
                    Box::new(lower_partition_bool(arena, *left, bound)?),
                    Box::new(lower_partition_bool(arena, *right, bound)?),
                ))))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => {
                Ok(PartitionFormula::Iff(
                    Box::new(lower_partition_bool(arena, *left, bound)?),
                    Box::new(lower_partition_bool(arena, *right, bound)?),
                ))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                lower_partition_int_equality(arena, *left, *right, bound)
            }
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                Ok(partition_ite(
                    lower_partition_bool(arena, *condition, bound)?,
                    lower_partition_bool(arena, *then_term, bound)?,
                    lower_partition_bool(arena, *else_term, bound)?,
                ))
            }
            _ => match eval(arena, term, &Assignment::new()) {
                Ok(Value::Bool(value)) => Ok(if value {
                    PartitionFormula::True
                } else {
                    PartitionFormula::False
                }),
                _ => Err(eq_partition_decline(
                    "Boolean term exceeds the proof-producing partition slice",
                )),
            },
        },
        _ => Err(eq_partition_decline("expected a Boolean partition term")),
    }
}

fn lower_partition_int_equality(
    arena: &TermArena,
    left: TermId,
    right: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionFormula, ReconstructError> {
    if let TermNode::Symbol(symbol) = arena.node(left)
        && bound.get(symbol) == Some(&Sort::Int)
        && let Some(value) = partition_int_literal(arena, right)
    {
        return Ok(PartitionFormula::IntAtom(*symbol, value));
    }
    if let TermNode::Symbol(symbol) = arena.node(right)
        && bound.get(symbol) == Some(&Sort::Int)
        && let Some(value) = partition_int_literal(arena, left)
    {
        return Ok(PartitionFormula::IntAtom(*symbol, value));
    }
    let left = lower_partition_int(arena, left, bound)?;
    let right = lower_partition_int(arena, right, bound)?;
    Ok(partition_int_equality_formula(left, right))
}

fn lower_partition_int(
    arena: &TermArena,
    term: TermId,
    bound: &mut BTreeMap<SymbolId, Sort>,
) -> Result<PartitionInt, ReconstructError> {
    if let Some(value) = partition_int_literal(arena, term) {
        return Ok(PartitionInt::Literal(value));
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return Err(eq_partition_decline(
            "integer leaf is not a literal or guarded expression",
        ));
    };
    match (op, &**args) {
        (Op::Ite, [condition, then_term, else_term]) => Ok(PartitionInt::Ite(
            Box::new(lower_partition_bool(arena, *condition, bound)?),
            Box::new(lower_partition_int(arena, *then_term, bound)?),
            Box::new(lower_partition_int(arena, *else_term, bound)?),
        )),
        (Op::IntNeg, [arg]) => partition_int_map1(lower_partition_int(arena, *arg, bound)?, |x| {
            x.checked_neg()
        }),
        (Op::IntAdd, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_add,
        ),
        (Op::IntSub, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_sub,
        ),
        (Op::IntMul, [left, right]) => partition_int_map2(
            lower_partition_int(arena, *left, bound)?,
            lower_partition_int(arena, *right, bound)?,
            i128::checked_mul,
        ),
        _ => Err(eq_partition_decline(
            "integer expression uses an unsupported partition operator",
        )),
    }
}

fn partition_int_map1(
    value: PartitionInt,
    operation: impl Copy + Fn(i128) -> Option<i128>,
) -> Result<PartitionInt, ReconstructError> {
    match value {
        PartitionInt::Literal(value) => operation(value)
            .map(PartitionInt::Literal)
            .ok_or_else(|| eq_partition_decline("integer leaf operation overflowed")),
        PartitionInt::Ite(condition, then_value, else_value) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map1(*then_value, operation)?),
            Box::new(partition_int_map1(*else_value, operation)?),
        )),
    }
}

fn partition_int_map2(
    left: PartitionInt,
    right: PartitionInt,
    operation: impl Copy + Fn(i128, i128) -> Option<i128>,
) -> Result<PartitionInt, ReconstructError> {
    match (left, right) {
        (PartitionInt::Literal(left), PartitionInt::Literal(right)) => operation(left, right)
            .map(PartitionInt::Literal)
            .ok_or_else(|| eq_partition_decline("integer leaf operation overflowed")),
        (PartitionInt::Ite(condition, then_value, else_value), right) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map2(*then_value, right.clone(), operation)?),
            Box::new(partition_int_map2(*else_value, right, operation)?),
        )),
        (left, PartitionInt::Ite(condition, then_value, else_value)) => Ok(PartitionInt::Ite(
            condition,
            Box::new(partition_int_map2(left.clone(), *then_value, operation)?),
            Box::new(partition_int_map2(left, *else_value, operation)?),
        )),
    }
}

fn partition_int_equality_formula(left: PartitionInt, right: PartitionInt) -> PartitionFormula {
    match (left, right) {
        (PartitionInt::Literal(left), PartitionInt::Literal(right)) => {
            if left == right {
                PartitionFormula::True
            } else {
                PartitionFormula::False
            }
        }
        (PartitionInt::Ite(condition, then_value, else_value), right) => partition_ite(
            *condition,
            partition_int_equality_formula(*then_value, right.clone()),
            partition_int_equality_formula(*else_value, right),
        ),
        (left, PartitionInt::Ite(condition, then_value, else_value)) => partition_ite(
            *condition,
            partition_int_equality_formula(left.clone(), *then_value),
            partition_int_equality_formula(left, *else_value),
        ),
    }
}

fn partition_int_literal(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } if args.len() == 1 => {
            let TermNode::IntConst(value) = arena.node(args[0]) else {
                return None;
            };
            value.checked_neg()
        }
        _ => None,
    }
}

fn collect_partition_binders(formula: &PartitionFormula, out: &mut BTreeSet<SymbolId>) {
    match formula {
        PartitionFormula::Forall(symbol, Sort::Int, body)
        | PartitionFormula::Exists(symbol, Sort::Int, body) => {
            out.insert(*symbol);
            collect_partition_binders(body, out);
        }
        PartitionFormula::Forall(_, _, body)
        | PartitionFormula::Exists(_, _, body)
        | PartitionFormula::Not(body) => collect_partition_binders(body, out),
        PartitionFormula::And(left, right)
        | PartitionFormula::Or(left, right)
        | PartitionFormula::Implies(left, right)
        | PartitionFormula::Iff(left, right) => {
            collect_partition_binders(left, out);
            collect_partition_binders(right, out);
        }
        _ => {}
    }
}

fn collect_partition_constants(
    formula: &PartitionFormula,
    symbol: SymbolId,
    out: &mut BTreeSet<i128>,
) {
    match formula {
        PartitionFormula::IntAtom(found, value) if *found == symbol => {
            out.insert(*value);
        }
        PartitionFormula::Forall(_, _, body)
        | PartitionFormula::Exists(_, _, body)
        | PartitionFormula::Not(body) => collect_partition_constants(body, symbol, out),
        PartitionFormula::And(left, right)
        | PartitionFormula::Or(left, right)
        | PartitionFormula::Implies(left, right)
        | PartitionFormula::Iff(left, right) => {
            collect_partition_constants(left, symbol, out);
            collect_partition_constants(right, symbol, out);
        }
        _ => {}
    }
}

fn partition_representatives(
    formula: &PartitionFormula,
    symbol: SymbolId,
    sort: Sort,
) -> Vec<Value> {
    match sort {
        Sort::Bool => vec![Value::Bool(false), Value::Bool(true)],
        Sort::Int => {
            let mut constants = BTreeSet::new();
            collect_partition_constants(formula, symbol, &mut constants);
            match constants.into_iter().next() {
                Some(value) => {
                    let other = value
                        .checked_add(1)
                        .or_else(|| value.checked_sub(1))
                        .unwrap();
                    vec![Value::Int(value), Value::Int(other)]
                }
                None => vec![Value::Int(0)],
            }
        }
        _ => Vec::new(),
    }
}

fn partition_formula_truth(formula: &PartitionFormula, assignment: &Assignment) -> Option<bool> {
    match formula {
        PartitionFormula::True => Some(true),
        PartitionFormula::False => Some(false),
        PartitionFormula::BoolAtom(symbol) => assignment.get(*symbol)?.as_bool(),
        PartitionFormula::IntAtom(symbol, value) => {
            Some(assignment.get(*symbol)?.as_int()? == *value)
        }
        PartitionFormula::Not(body) => Some(!partition_formula_truth(body, assignment)?),
        PartitionFormula::And(left, right) => Some(
            partition_formula_truth(left, assignment)?
                && partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Or(left, right) => Some(
            partition_formula_truth(left, assignment)?
                || partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Implies(left, right) => Some(
            !partition_formula_truth(left, assignment)?
                || partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Iff(left, right) => Some(
            partition_formula_truth(left, assignment)?
                == partition_formula_truth(right, assignment)?,
        ),
        PartitionFormula::Forall(symbol, sort, body) => {
            for value in partition_representatives(body, *symbol, *sort) {
                let mut branch = assignment.clone();
                branch.set(*symbol, value);
                if !partition_formula_truth(body, &branch)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        PartitionFormula::Exists(symbol, sort, body) => {
            for value in partition_representatives(body, *symbol, *sort) {
                let mut branch = assignment.clone();
                branch.set(*symbol, value);
                if partition_formula_truth(body, &branch)? {
                    return Some(true);
                }
            }
            Some(false)
        }
    }
}

fn partition_literals_fit_proof_unit_budget(formula: &PartitionFormula) -> bool {
    fn collect(formula: &PartitionFormula, values: &mut Vec<i128>) {
        match formula {
            PartitionFormula::IntAtom(_, value) => {
                values.push(*value);
                values.push(
                    value
                        .checked_add(1)
                        .or_else(|| value.checked_sub(1))
                        .expect("every i128 has an adjacent representable value"),
                );
            }
            PartitionFormula::Forall(_, _, body)
            | PartitionFormula::Exists(_, _, body)
            | PartitionFormula::Not(body) => collect(body, values),
            PartitionFormula::And(left, right)
            | PartitionFormula::Or(left, right)
            | PartitionFormula::Implies(left, right)
            | PartitionFormula::Iff(left, right) => {
                collect(left, values);
                collect(right, values);
            }
            PartitionFormula::True | PartitionFormula::False | PartitionFormula::BoolAtom(_) => {}
        }
    }

    let mut values = Vec::new();
    collect(formula, &mut values);
    int_values_fit_proof_unit_budget(values)
}

#[derive(Debug, Clone, Copy)]
struct PartitionSignedProof {
    truth: bool,
    proof: ExprId,
}

type PartitionKernelEnv = BTreeMap<SymbolId, ExprId>;
type PartitionFactEnv = BTreeMap<(SymbolId, i128), PartitionSignedProof>;

fn partition_carrier(ctx: &mut IntReconstructCtx, sort: Sort) -> ExprId {
    match sort {
        Sort::Bool => ctx.kernel.const_(ctx.int.logic.bool_, Vec::new()),
        Sort::Int => ctx.kernel.const_(ctx.int.z, Vec::new()),
        _ => unreachable!("partition lowering admits only Bool/Int binders"),
    }
}

fn partition_value_expr(ctx: &mut IntReconstructCtx, value: &Value) -> ExprId {
    match value {
        Value::Bool(value) => {
            let name = if *value {
                ctx.int.logic.bool_true
            } else {
                ctx.int.logic.bool_false
            };
            ctx.kernel.const_(name, Vec::new())
        }
        Value::Int(value) => ctx.mk_intlit(*value),
        _ => unreachable!("partition representatives are Bool/Int"),
    }
}

fn partition_formula_prop(
    ctx: &mut IntReconstructCtx,
    formula: &PartitionFormula,
    environment: &mut PartitionKernelEnv,
) -> Result<ExprId, ReconstructError> {
    match formula {
        PartitionFormula::True => Ok(ctx.mk_true()),
        PartitionFormula::False => Ok(ctx.kernel.const_(ctx.int.logic.false_, Vec::new())),
        PartitionFormula::BoolAtom(symbol) => {
            let value = *environment
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("unbound Bool atom"))?;
            let true_value = ctx.kernel.const_(ctx.int.logic.bool_true, Vec::new());
            Ok(ctx.mk_bool_eq(value, true_value))
        }
        PartitionFormula::IntAtom(symbol, value) => {
            let variable = *environment
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("unbound Int atom"))?;
            let literal = ctx.mk_intlit(*value);
            Ok(ctx.mk_eq(variable, literal))
        }
        PartitionFormula::Not(body) => {
            let body = partition_formula_prop(ctx, body, environment)?;
            Ok(ctx.mk_not(body))
        }
        PartitionFormula::And(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_and(left, right))
        }
        PartitionFormula::Or(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_or(left, right))
        }
        PartitionFormula::Implies(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            let anon = ctx.kernel.anon();
            Ok(ctx.kernel.pi(anon, left, right, BinderInfo::Default))
        }
        PartitionFormula::Iff(left, right) => {
            let left = partition_formula_prop(ctx, left, environment)?;
            let right = partition_formula_prop(ctx, right, environment)?;
            Ok(ctx.mk_iff(left, right))
        }
        PartitionFormula::Forall(symbol, sort, body) => {
            let id = ctx.fresh_fvar();
            let value = ctx.kernel.fvar(id);
            environment.insert(*symbol, value);
            let body = partition_formula_prop(ctx, body, environment)?;
            environment.remove(symbol);
            let body = ctx.kernel.abstract_fvars(body, &[id]);
            let carrier = partition_carrier(ctx, *sort);
            let anon = ctx.kernel.anon();
            Ok(ctx.kernel.pi(anon, carrier, body, BinderInfo::Default))
        }
        PartitionFormula::Exists(symbol, sort, body) => {
            let id = ctx.fresh_fvar();
            let value = ctx.kernel.fvar(id);
            environment.insert(*symbol, value);
            let body = partition_formula_prop(ctx, body, environment)?;
            environment.remove(symbol);
            let body = ctx.kernel.abstract_fvars(body, &[id]);
            let carrier = partition_carrier(ctx, *sort);
            let anon = ctx.kernel.anon();
            let predicate = ctx.kernel.lam(anon, carrier, body, BinderInfo::Default);
            Ok(ctx.mk_exists_for_carrier(carrier, predicate))
        }
    }
}

fn partition_not_lambda(
    ctx: &mut IntReconstructCtx,
    proposition: ExprId,
    hypothesis_id: u64,
    false_proof: ExprId,
) -> ExprId {
    let body = ctx.kernel.abstract_fvars(false_proof, &[hypothesis_id]);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, proposition, body, BinderInfo::Default)
}

#[allow(clippy::too_many_lines)]
fn prove_partition_formula(
    ctx: &mut IntReconstructCtx,
    formula: &PartitionFormula,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let truth = partition_formula_truth(formula, assignment)
        .ok_or_else(|| eq_partition_decline("proof search could not evaluate formula"))?;
    match formula {
        PartitionFormula::True => Ok(PartitionSignedProof {
            truth,
            proof: ctx.true_intro(),
        }),
        PartitionFormula::False => {
            let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
            let anon = ctx.kernel.anon();
            let hypothesis = ctx.kernel.bvar(0);
            let proof = ctx
                .kernel
                .lam(anon, false_prop, hypothesis, BinderInfo::Default);
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::BoolAtom(symbol) => {
            let value = assignment
                .get(*symbol)
                .and_then(|value| value.as_bool())
                .ok_or_else(|| eq_partition_decline("Bool atom lacks an assignment"))?;
            let expression = *kernel_env
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("Bool atom lacks a kernel binding"))?;
            let proof = if value {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::IntAtom(symbol, constant) => {
            if let Some(proof) = facts.get(&(*symbol, *constant)) {
                if proof.truth != truth {
                    return Err(eq_partition_decline(
                        "atom fact disagrees with representative",
                    ));
                }
                return Ok(*proof);
            }
            let value = assignment
                .get(*symbol)
                .and_then(|value| value.as_int())
                .ok_or_else(|| eq_partition_decline("Int atom lacks an assignment"))?;
            let expression = *kernel_env
                .get(symbol)
                .ok_or_else(|| eq_partition_decline("Int atom lacks a kernel binding"))?;
            let proof = if truth {
                ctx.eq_refl(expression)
            } else {
                ctx.prove_adjacent_intlit_disequality(value, *constant)?
            };
            Ok(PartitionSignedProof { truth, proof })
        }
        PartitionFormula::Not(body) => {
            let body_proof = prove_partition_formula(ctx, body, assignment, kernel_env, facts)?;
            if truth {
                Ok(PartitionSignedProof {
                    truth,
                    proof: body_proof.proof,
                })
            } else {
                let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
                let not_body = ctx.mk_not(body_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let false_proof = ctx.kernel.app(hypothesis, body_proof.proof);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, not_body, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::And(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.and_intro(
                        left_prop,
                        right_prop,
                        left_proof.proof,
                        right_proof.proof,
                    ),
                })
            } else {
                let conjunction = ctx.mk_and(left_prop, right_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let (false_child, child_not) = if left_proof.truth {
                    (
                        ctx.and_project(left_prop, right_prop, hypothesis, false),
                        right_proof.proof,
                    )
                } else {
                    (
                        ctx.and_project(left_prop, right_prop, hypothesis, true),
                        left_proof.proof,
                    )
                };
                let false_proof = ctx.kernel.app(child_not, false_child);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, conjunction, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Or(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
                let proof = if left_proof.truth {
                    ctx.or_intro_left(left_prop, right_prop, left_proof.proof)
                } else {
                    ctx.or_intro_right(left_prop, right_prop, right_proof.proof)
                };
                Ok(PartitionSignedProof { truth, proof })
            } else {
                let disjunction = ctx.mk_or(left_prop, right_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let left_id = ctx.fresh_fvar();
                let left_hypothesis = ctx.kernel.fvar(left_id);
                let left_false = ctx.kernel.app(left_proof.proof, left_hypothesis);
                let left_case = partition_not_lambda(ctx, left_prop, left_id, left_false);
                let right_id = ctx.fresh_fvar();
                let right_hypothesis = ctx.kernel.fvar(right_id);
                let right_false = ctx.kernel.app(right_proof.proof, right_hypothesis);
                let right_case = partition_not_lambda(ctx, right_prop, right_id, right_false);
                let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
                let false_proof = ctx.or_rec_prop(
                    left_prop, right_prop, false_prop, left_case, right_case, hypothesis,
                );
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, disjunction, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Implies(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            let anon = ctx.kernel.anon();
            let implication = ctx
                .kernel
                .pi(anon, left_prop, right_prop, BinderInfo::Default);
            if truth {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let result = if left_proof.truth {
                    right_proof.proof
                } else {
                    let false_proof = ctx.kernel.app(left_proof.proof, hypothesis);
                    ctx.ex_falso(right_prop, false_proof)
                };
                let body = ctx.kernel.abstract_fvars(result, &[hypothesis_id]);
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default),
                })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let right = ctx.kernel.app(hypothesis, left_proof.proof);
                let false_proof = ctx.kernel.app(right_proof.proof, right);
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, implication, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Iff(left, right) => {
            let left_proof = prove_partition_formula(ctx, left, assignment, kernel_env, facts)?;
            let right_proof = prove_partition_formula(ctx, right, assignment, kernel_env, facts)?;
            let left_prop = partition_formula_prop(ctx, left, kernel_env)?;
            let right_prop = partition_formula_prop(ctx, right, kernel_env)?;
            if truth {
                let anon = ctx.kernel.anon();
                let forward = if left_proof.truth {
                    ctx.const_implication(left_prop, right_prop, right_proof.proof)
                } else {
                    let id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(id);
                    let false_proof = ctx.kernel.app(left_proof.proof, hypothesis);
                    let result = ctx.ex_falso(right_prop, false_proof);
                    let body = ctx.kernel.abstract_fvars(result, &[id]);
                    ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default)
                };
                let backward = if right_proof.truth {
                    ctx.const_implication(right_prop, left_prop, left_proof.proof)
                } else {
                    let id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(id);
                    let false_proof = ctx.kernel.app(right_proof.proof, hypothesis);
                    let result = ctx.ex_falso(left_prop, false_proof);
                    let body = ctx.kernel.abstract_fvars(result, &[id]);
                    ctx.kernel.lam(anon, right_prop, body, BinderInfo::Default)
                };
                Ok(PartitionSignedProof {
                    truth,
                    proof: ctx.iff_intro(left_prop, right_prop, forward, backward),
                })
            } else {
                let iff_prop = ctx.mk_iff(left_prop, right_prop);
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let false_proof = if left_proof.truth {
                    let forward = ctx.iff_project(left_prop, right_prop, hypothesis, true);
                    let right = ctx.kernel.app(forward, left_proof.proof);
                    ctx.kernel.app(right_proof.proof, right)
                } else {
                    let backward = ctx.iff_project(left_prop, right_prop, hypothesis, false);
                    let left = ctx.kernel.app(backward, right_proof.proof);
                    ctx.kernel.app(left_proof.proof, left)
                };
                Ok(PartitionSignedProof {
                    truth,
                    proof: partition_not_lambda(ctx, iff_prop, hypothesis_id, false_proof),
                })
            }
        }
        PartitionFormula::Forall(symbol, sort, body) => prove_partition_forall(
            ctx, *symbol, *sort, body, truth, assignment, kernel_env, facts,
        ),
        PartitionFormula::Exists(symbol, sort, body) => prove_partition_exists(
            ctx, *symbol, *sort, body, truth, assignment, kernel_env, facts,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_partition_forall(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    truth: bool,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let carrier = partition_carrier(ctx, sort);
    let anon = ctx.kernel.anon();
    if truth {
        let witness_id = ctx.fresh_fvar();
        let witness = ctx.kernel.fvar(witness_id);
        kernel_env.insert(symbol, witness);
        let body_proof = prove_partition_for_arbitrary(
            ctx, symbol, sort, body, true, witness_id, witness, assignment, kernel_env, facts,
        )?;
        kernel_env.remove(&symbol);
        let proof_body = ctx.kernel.abstract_fvars(body_proof.proof, &[witness_id]);
        let proof = ctx
            .kernel
            .lam(anon, carrier, proof_body, BinderInfo::Default);
        Ok(PartitionSignedProof { truth, proof })
    } else {
        let representatives = partition_representatives(body, symbol, sort);
        let witness = representatives
            .into_iter()
            .find(|value| {
                let mut branch = assignment.clone();
                branch.set(symbol, value.clone());
                partition_formula_truth(body, &branch) == Some(false)
            })
            .ok_or_else(|| eq_partition_decline("false forall lacks a false representative"))?;
        let mut branch_assignment = assignment.clone();
        branch_assignment.set(symbol, witness.clone());
        let witness_expr = partition_value_expr(ctx, &witness);
        kernel_env.insert(symbol, witness_expr);
        let body_proof = prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
        kernel_env.remove(&symbol);
        if body_proof.truth {
            return Err(eq_partition_decline(
                "selected false-forall representative proved true",
            ));
        }
        let formula = PartitionFormula::Forall(symbol, sort, Box::new(body.clone()));
        let forall_prop = partition_formula_prop(ctx, &formula, kernel_env)?;
        let hypothesis_id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(hypothesis_id);
        let instance = ctx.kernel.app(hypothesis, witness_expr);
        let false_proof = ctx.kernel.app(body_proof.proof, instance);
        let proof = partition_not_lambda(ctx, forall_prop, hypothesis_id, false_proof);
        Ok(PartitionSignedProof { truth, proof })
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_partition_exists(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    truth: bool,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    let carrier = partition_carrier(ctx, sort);
    let anon = ctx.kernel.anon();
    if truth {
        let representatives = partition_representatives(body, symbol, sort);
        let witness = representatives
            .into_iter()
            .find(|value| {
                let mut branch = assignment.clone();
                branch.set(symbol, value.clone());
                partition_formula_truth(body, &branch) == Some(true)
            })
            .ok_or_else(|| eq_partition_decline("true exists lacks a true representative"))?;
        let mut branch_assignment = assignment.clone();
        branch_assignment.set(symbol, witness.clone());
        let witness_expr = partition_value_expr(ctx, &witness);
        kernel_env.insert(symbol, witness_expr);
        let body_proof = prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
        kernel_env.remove(&symbol);
        if !body_proof.truth {
            return Err(eq_partition_decline(
                "selected true-exists representative proved false",
            ));
        }
        let predicate_id = ctx.fresh_fvar();
        let predicate_value = ctx.kernel.fvar(predicate_id);
        kernel_env.insert(symbol, predicate_value);
        let predicate_body = partition_formula_prop(ctx, body, kernel_env)?;
        kernel_env.remove(&symbol);
        let predicate_body = ctx.kernel.abstract_fvars(predicate_body, &[predicate_id]);
        let predicate = ctx
            .kernel
            .lam(anon, carrier, predicate_body, BinderInfo::Default);
        let proof = ctx.exists_intro(carrier, predicate, witness_expr, body_proof.proof);
        Ok(PartitionSignedProof { truth, proof })
    } else {
        let witness_id = ctx.fresh_fvar();
        let witness = ctx.kernel.fvar(witness_id);
        kernel_env.insert(symbol, witness);
        let body_proof = prove_partition_for_arbitrary(
            ctx, symbol, sort, body, false, witness_id, witness, assignment, kernel_env, facts,
        )?;
        let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
        let predicate_body = ctx.kernel.abstract_fvars(body_prop, &[witness_id]);
        let predicate = ctx
            .kernel
            .lam(anon, carrier, predicate_body, BinderInfo::Default);
        let exists_prop = ctx.mk_exists_for_carrier(carrier, predicate);
        let body_hypothesis_id = ctx.fresh_fvar();
        let body_hypothesis = ctx.kernel.fvar(body_hypothesis_id);
        let false_proof = ctx.kernel.app(body_proof.proof, body_hypothesis);
        let body_hypothesis_body = ctx
            .kernel
            .abstract_fvars(false_proof, &[body_hypothesis_id]);
        let body_minor = ctx
            .kernel
            .lam(anon, body_prop, body_hypothesis_body, BinderInfo::Default);
        let witness_minor_body = ctx.kernel.abstract_fvars(body_minor, &[witness_id]);
        let minor = ctx
            .kernel
            .lam(anon, carrier, witness_minor_body, BinderInfo::Default);
        kernel_env.remove(&symbol);
        let exists_hypothesis_id = ctx.fresh_fvar();
        let exists_hypothesis = ctx.kernel.fvar(exists_hypothesis_id);
        let eliminated = ctx.exists_elim_false_for_carrier(
            carrier,
            predicate,
            exists_prop,
            minor,
            exists_hypothesis,
        );
        let proof = partition_not_lambda(ctx, exists_prop, exists_hypothesis_id, eliminated);
        Ok(PartitionSignedProof { truth, proof })
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_partition_for_arbitrary(
    ctx: &mut IntReconstructCtx,
    symbol: SymbolId,
    sort: Sort,
    body: &PartitionFormula,
    desired: bool,
    witness_id: u64,
    witness: ExprId,
    assignment: &Assignment,
    kernel_env: &mut PartitionKernelEnv,
    facts: &PartitionFactEnv,
) -> Result<PartitionSignedProof, ReconstructError> {
    match sort {
        Sort::Bool => {
            let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
            let target = if desired {
                body_prop
            } else {
                ctx.mk_not(body_prop)
            };
            let target_body = ctx.kernel.abstract_fvars(target, &[witness_id]);
            let bool_ty = partition_carrier(ctx, Sort::Bool);
            let anon = ctx.kernel.anon();
            let motive = ctx
                .kernel
                .lam(anon, bool_ty, target_body, BinderInfo::Default);

            let true_value = Value::Bool(true);
            let true_expr = partition_value_expr(ctx, &true_value);
            let mut true_assignment = assignment.clone();
            true_assignment.set(symbol, true_value);
            kernel_env.insert(symbol, true_expr);
            let true_proof =
                prove_partition_formula(ctx, body, &true_assignment, kernel_env, facts)?;
            if true_proof.truth != desired {
                return Err(eq_partition_decline(
                    "Bool true cell disagrees with quantified result",
                ));
            }

            let false_value = Value::Bool(false);
            let false_expr = partition_value_expr(ctx, &false_value);
            let mut false_assignment = assignment.clone();
            false_assignment.set(symbol, false_value);
            kernel_env.insert(symbol, false_expr);
            let false_proof =
                prove_partition_formula(ctx, body, &false_assignment, kernel_env, facts)?;
            if false_proof.truth != desired {
                return Err(eq_partition_decline(
                    "Bool false cell disagrees with quantified result",
                ));
            }
            kernel_env.insert(symbol, witness);
            let zero = ctx.kernel.level_zero();
            let rec = ctx.kernel.const_(ctx.int.logic.bool_rec, vec![zero]);
            let rec = ctx.kernel.app(rec, motive);
            let rec = ctx.kernel.app(rec, true_proof.proof);
            let rec = ctx.kernel.app(rec, false_proof.proof);
            let proof = ctx.kernel.app(rec, witness);
            Ok(PartitionSignedProof {
                truth: desired,
                proof,
            })
        }
        Sort::Int => {
            let mut constants = BTreeSet::new();
            collect_partition_constants(body, symbol, &mut constants);
            let Some(constant) = constants.into_iter().next() else {
                let mut branch_assignment = assignment.clone();
                branch_assignment.set(symbol, Value::Int(0));
                let proof =
                    prove_partition_formula(ctx, body, &branch_assignment, kernel_env, facts)?;
                if proof.truth != desired {
                    return Err(eq_partition_decline(
                        "unused Int binder disagrees with quantified result",
                    ));
                }
                return Ok(proof);
            };
            let other = constant
                .checked_add(1)
                .or_else(|| constant.checked_sub(1))
                .ok_or_else(|| eq_partition_decline("could not choose adjacent other cell"))?;
            let literal = ctx.mk_intlit(constant);
            let equality = ctx.mk_eq(witness, literal);
            let not_equality = ctx.mk_not(equality);
            let em = ctx.int_eq_em_app(witness, literal);
            let target_prop = {
                let body_prop = partition_formula_prop(ctx, body, kernel_env)?;
                if desired {
                    body_prop
                } else {
                    ctx.mk_not(body_prop)
                }
            };

            let equal_id = ctx.fresh_fvar();
            let equal_hypothesis = ctx.kernel.fvar(equal_id);
            let mut equal_assignment = assignment.clone();
            equal_assignment.set(symbol, Value::Int(constant));
            let mut equal_facts = facts.clone();
            equal_facts.insert(
                (symbol, constant),
                PartitionSignedProof {
                    truth: true,
                    proof: equal_hypothesis,
                },
            );
            let equal_proof =
                prove_partition_formula(ctx, body, &equal_assignment, kernel_env, &equal_facts)?;
            if equal_proof.truth != desired {
                return Err(eq_partition_decline(
                    "equal Int cell disagrees with quantified result",
                ));
            }
            let equal_body = ctx.kernel.abstract_fvars(equal_proof.proof, &[equal_id]);
            let anon = ctx.kernel.anon();
            let equal_case = ctx
                .kernel
                .lam(anon, equality, equal_body, BinderInfo::Default);

            let other_id = ctx.fresh_fvar();
            let other_hypothesis = ctx.kernel.fvar(other_id);
            let mut other_assignment = assignment.clone();
            other_assignment.set(symbol, Value::Int(other));
            let mut other_facts = facts.clone();
            other_facts.insert(
                (symbol, constant),
                PartitionSignedProof {
                    truth: false,
                    proof: other_hypothesis,
                },
            );
            let other_proof =
                prove_partition_formula(ctx, body, &other_assignment, kernel_env, &other_facts)?;
            if other_proof.truth != desired {
                return Err(eq_partition_decline(
                    "other Int cell disagrees with quantified result",
                ));
            }
            let other_body = ctx.kernel.abstract_fvars(other_proof.proof, &[other_id]);
            let anon = ctx.kernel.anon();
            let other_case = ctx
                .kernel
                .lam(anon, not_equality, other_body, BinderInfo::Default);
            let proof = ctx.or_rec_prop(
                equality,
                not_equality,
                target_prop,
                equal_case,
                other_case,
                em,
            );
            Ok(PartitionSignedProof {
                truth: desired,
                proof,
            })
        }
        _ => Err(eq_partition_decline(
            "arbitrary binder has unsupported sort",
        )),
    }
}

fn eq_partition_decline(detail: &str) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("single-pivot equality partition: {detail}"),
    }
}

/// Cheap router predicate for ADR-0106's one-pivot-per-Int-binder proof slice.
pub(crate) fn single_pivot_equality_partition_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    let Some(certificate) =
        crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions)
    else {
        return false;
    };
    lower_single_pivot_partition(arena, certificate.assertion).is_ok()
}

/// Reconstruct an ADR-0101 certificate in the ADR-0106 single-pivot sub-class
/// as a kernel-checked proof over genuine Bool/Int quantifiers.
///
/// The executable equality-partition checker is rerun only to validate the
/// certificate and guide proof search. The generated proof recursively
/// introduces/eliminates every quantifier and connective; arbitrary Int
/// witnesses are split with [`IntPrelude::eq_em`](axeyum_lean_kernel::IntPrelude::eq_em),
/// while arbitrary Bool witnesses use the computational `Bool.rec` eliminator.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for an invalid certificate or
/// formula outside the one-pivot proof slice, and
/// [`ReconstructError::KernelRejected`] if the independently assembled closed
/// proof does not infer to `False`.
#[allow(clippy::too_many_lines)]
pub fn reconstruct_single_pivot_equality_partition_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &EqualityPartitionRefutationCertificate,
) -> Result<String, ReconstructError> {
    if !check_equality_partition_refutation(arena, assertions, certificate) {
        return Err(eq_partition_decline("invalid ADR-0101 certificate"));
    }
    let formula = lower_single_pivot_partition(arena, certificate.assertion)?;
    if !partition_literals_fit_proof_unit_budget(&formula) {
        return Err(eq_partition_decline(
            "integer literals exceed proof-size cap",
        ));
    }
    if partition_formula_truth(&formula, &Assignment::new()) != Some(false) {
        return Err(eq_partition_decline(
            "lowered formula is not false under its exact partitions",
        ));
    }
    let mut ctx = IntReconstructCtx::new();
    let mut kernel_env = PartitionKernelEnv::new();
    let signed = prove_partition_formula(
        &mut ctx,
        &formula,
        &Assignment::new(),
        &mut kernel_env,
        &PartitionFactEnv::new(),
    )?;
    if signed.truth {
        return Err(eq_partition_decline(
            "proof search returned a positive top-level theorem",
        ));
    }
    let proposition = partition_formula_prop(&mut ctx, &formula, &mut kernel_env)?;
    let assertion = ctx.hyp_axiom(proposition)?;
    let proof = ctx.kernel.app(signed.proof, assertion);
    let false_ = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
    ctx.require_partition_type(proof, false_, "final contradiction")?;
    Ok(ctx
        .kernel()
        .render_lean_module("axeyum_refutation", false_, proof))
}

// ---------------------------------------------------------------------------
// ADR-0108: source-instantiated quantified counterexample covers.

type CoverKernelEnv = BTreeMap<SymbolId, ExprId>;
type CoverFreeProps = BTreeMap<SymbolId, ExprId>;

#[derive(Debug, Clone, Copy)]
struct CoverSignedProof {
    truth: bool,
    proof: ExprId,
}

fn cover_decline(detail: impl Into<String>) -> ReconstructError {
    ReconstructError::UnsupportedTerm {
        term: format!("quantified counterexample cover: {}", detail.into()),
    }
}

fn cover_bool_carrier(ctx: &mut IntReconstructCtx) -> ExprId {
    ctx.kernel.const_(ctx.int.logic.bool_, Vec::new())
}

fn cover_bool_literal(ctx: &mut IntReconstructCtx, value: bool) -> ExprId {
    ctx.kernel.const_(
        if value {
            ctx.int.logic.bool_true
        } else {
            ctx.int.logic.bool_false
        },
        Vec::new(),
    )
}

fn cover_bool_value_prop(ctx: &mut IntReconstructCtx, value: ExprId) -> ExprId {
    let true_value = cover_bool_literal(ctx, true);
    ctx.mk_bool_eq(value, true_value)
}

fn cover_bool_value(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    bool_env: &CoverKernelEnv,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Ok(cover_bool_literal(ctx, *value)),
        TermNode::Symbol(symbol) => bool_env
            .get(symbol)
            .copied()
            .ok_or_else(|| cover_decline("free Bool occurs in an integer ite condition")),
        _ => Err(cover_decline(
            "integer ite condition is not a bound Bool symbol or literal",
        )),
    }
}

fn cover_int_term(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: Option<&Assignment>,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::IntConst(value) => {
            if !int_values_fit_proof_unit_budget([*value]) {
                return Err(cover_decline("integer literal exceeds proof-size cap"));
            }
            Ok(ctx.mk_intlit(*value))
        }
        TermNode::Symbol(symbol) => int_env
            .get(symbol)
            .copied()
            .ok_or_else(|| cover_decline("free Int symbol in admitted cover")),
        TermNode::App { op, args } => match (op, &**args) {
            (Op::IntNeg, [argument]) => {
                let argument = cover_int_term(ctx, arena, *argument, int_env, bool_env, values)?;
                Ok(ctx.mk_neg(argument))
            }
            (Op::IntAdd, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_add(left, right))
            }
            (Op::IntSub, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                let right = ctx.mk_neg(right);
                Ok(ctx.mk_add(left, right))
            }
            (Op::IntMul, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_mul(left, right))
            }
            (Op::Ite, [condition, then_term, else_term]) => {
                if let Some(values) = values {
                    match eval(arena, *condition, values) {
                        Ok(Value::Bool(true)) => {
                            return cover_int_term(
                                ctx,
                                arena,
                                *then_term,
                                int_env,
                                bool_env,
                                Some(values),
                            );
                        }
                        Ok(Value::Bool(false)) => {
                            return cover_int_term(
                                ctx,
                                arena,
                                *else_term,
                                int_env,
                                bool_env,
                                Some(values),
                            );
                        }
                        _ => {}
                    }
                }
                let condition = cover_bool_value(ctx, arena, *condition, bool_env)?;
                let then_term = cover_int_term(ctx, arena, *then_term, int_env, bool_env, values)?;
                let else_term = cover_int_term(ctx, arena, *else_term, int_env, bool_env, values)?;
                let bool_ty = cover_bool_carrier(ctx);
                let z_ty = ctx.kernel.const_(ctx.int.z, Vec::new());
                let anon = ctx.kernel.anon();
                let motive = ctx.kernel.lam(anon, bool_ty, z_ty, BinderInfo::Default);
                let zero = ctx.kernel.level_zero();
                let one = ctx.kernel.level_succ(zero);
                let rec = ctx.kernel.const_(ctx.int.logic.bool_rec, vec![one]);
                let rec = ctx.kernel.app(rec, motive);
                let rec = ctx.kernel.app(rec, then_term);
                let rec = ctx.kernel.app(rec, else_term);
                Ok(ctx.kernel.app(rec, condition))
            }
            _ => Err(cover_decline("unsupported integer operator")),
        },
        _ => Err(cover_decline("unsupported integer term")),
    }
}

#[allow(clippy::too_many_lines)]
fn cover_formula_prop(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: Option<&Assignment>,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        TermNode::BoolConst(value) => {
            let value = cover_bool_literal(ctx, *value);
            Ok(cover_bool_value_prop(ctx, value))
        }
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            if let Some(value) = bool_env.get(symbol).copied() {
                Ok(cover_bool_value_prop(ctx, value))
            } else {
                free_props
                    .get(symbol)
                    .copied()
                    .ok_or_else(|| cover_decline("unregistered free Bool symbol"))
            }
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => {
                let argument = cover_formula_prop(
                    ctx, arena, *argument, int_env, bool_env, free_props, values,
                )?;
                Ok(ctx.mk_not(argument))
            }
            (Op::BoolAnd, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_and(left, right))
            }
            (Op::BoolOr, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_or(left, right))
            }
            (Op::BoolImplies, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                let anon = ctx.kernel.anon();
                Ok(ctx.kernel.pi(anon, left, right, BinderInfo::Default))
            }
            (Op::BoolXor, [left, right]) => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                let iff = ctx.mk_iff(left, right);
                Ok(ctx.mk_not(iff))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => {
                let left =
                    cover_formula_prop(ctx, arena, *left, int_env, bool_env, free_props, values)?;
                let right =
                    cover_formula_prop(ctx, arena, *right, int_env, bool_env, free_props, values)?;
                Ok(ctx.mk_iff(left, right))
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_eq(left, right))
            }
            (Op::IntLt, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_lt(left, right))
            }
            (Op::IntLe, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_le(left, right))
            }
            (Op::IntGt, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_lt(right, left))
            }
            (Op::IntGe, [left, right]) => {
                let left = cover_int_term(ctx, arena, *left, int_env, bool_env, values)?;
                let right = cover_int_term(ctx, arena, *right, int_env, bool_env, values)?;
                Ok(ctx.mk_le(right, left))
            }
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                let condition = cover_formula_prop(
                    ctx, arena, *condition, int_env, bool_env, free_props, values,
                )?;
                let then_term = cover_formula_prop(
                    ctx, arena, *then_term, int_env, bool_env, free_props, values,
                )?;
                let else_term = cover_formula_prop(
                    ctx, arena, *else_term, int_env, bool_env, free_props, values,
                )?;
                let positive = ctx.mk_and(condition, then_term);
                let negative_condition = ctx.mk_not(condition);
                let negative = ctx.mk_and(negative_condition, else_term);
                Ok(ctx.mk_or(positive, negative))
            }
            (Op::Forall(symbol), [body]) => {
                let sort = arena.symbol(*symbol).1;
                let id = ctx.fresh_fvar();
                let variable = ctx.kernel.fvar(id);
                match sort {
                    Sort::Int => {
                        int_env.insert(*symbol, variable);
                    }
                    Sort::Bool => {
                        bool_env.insert(*symbol, variable);
                    }
                    _ => return Err(cover_decline("non-Bool/Int universal binder")),
                }
                let body =
                    cover_formula_prop(ctx, arena, *body, int_env, bool_env, free_props, values)?;
                int_env.remove(symbol);
                bool_env.remove(symbol);
                let body = ctx.kernel.abstract_fvars(body, &[id]);
                let carrier = match sort {
                    Sort::Int => ctx.kernel.const_(ctx.int.z, Vec::new()),
                    Sort::Bool => cover_bool_carrier(ctx),
                    _ => unreachable!(),
                };
                let anon = ctx.kernel.anon();
                Ok(ctx.kernel.pi(anon, carrier, body, BinderInfo::Default))
            }
            (Op::Exists(_), _) => Err(cover_decline("existential in cover proof")),
            _ => Err(cover_decline(format!(
                "unsupported Boolean operator {op:?}"
            ))),
        },
        _ => Err(cover_decline("expected a Boolean formula")),
    }
}

fn cover_formula_truth(arena: &TermArena, term: TermId, values: &Assignment) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            values.get(*symbol)?.as_bool()
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => Some(!cover_formula_truth(arena, *argument, values)?),
            (Op::BoolAnd, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                }
            }
            (Op::BoolOr, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                }
            }
            (Op::BoolImplies, [left, right]) => {
                let left = cover_formula_truth(arena, *left, values);
                let right = cover_formula_truth(arena, *right, values);
                match (left, right) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }
            (Op::BoolXor, [left, right]) => Some(
                cover_formula_truth(arena, *left, values)?
                    != cover_formula_truth(arena, *right, values)?,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => Some(
                cover_formula_truth(arena, *left, values)?
                    == cover_formula_truth(arena, *right, values)?,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    == eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntLt, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    < eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntLe, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    <= eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntGt, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    > eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::IntGe, [left, right]) => Some(
                eval(arena, *left, values).ok()?.as_int()?
                    >= eval(arena, *right, values).ok()?.as_int()?,
            ),
            (Op::Ite, [condition, then_term, else_term]) if arena.sort_of(term) == Sort::Bool => {
                if cover_formula_truth(arena, *condition, values)? {
                    cover_formula_truth(arena, *then_term, values)
                } else {
                    cover_formula_truth(arena, *else_term, values)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn cover_not_lambda(
    ctx: &mut IntReconstructCtx,
    proposition: ExprId,
    hypothesis_id: u64,
    false_proof: ExprId,
) -> ExprId {
    let body = ctx.kernel.abstract_fvars(false_proof, &[hypothesis_id]);
    let anon = ctx.kernel.anon();
    ctx.kernel.lam(anon, proposition, body, BinderInfo::Default)
}

fn cover_int_value_proof(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: &Assignment,
) -> Result<(ExprId, i128, ExprId), ReconstructError> {
    if !ground_int_term_fits_proof_unit_budget(arena, term, values) {
        return Err(cover_decline(
            "ground integer normalization exceeds proof-size cap",
        ));
    }
    let expression = cover_int_term(ctx, arena, term, int_env, bool_env, Some(values))?;
    let value = eval(arena, term, values)
        .ok()
        .and_then(|value| value.as_int())
        .ok_or_else(|| cover_decline("ground integer term did not evaluate"))?;
    let (gens, _, normalized) = ctx
        .normalize_kernel(expression)
        .ok_or_else(|| cover_decline("ground integer normalization declined"))?;
    if gens != lin_to_canon_gens(&[], value) {
        return Err(cover_decline("integer normalizer disagrees with evaluator"));
    }
    let canonical = ctx.gens_to_expr(&gens);
    let literal = ctx.mk_intlit(value);
    let literal_to_canonical = ctx.intlit_eq_canon(value);
    let canonical_to_literal = ctx.eq_symm(literal, canonical, literal_to_canonical);
    let proof = ctx.eq_trans(
        expression,
        canonical,
        literal,
        normalized,
        canonical_to_literal,
    );
    Ok((expression, value, proof))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn cover_signed_int_atom(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    op: Op,
    left: TermId,
    right: TermId,
    int_env: &CoverKernelEnv,
    bool_env: &CoverKernelEnv,
    values: &Assignment,
) -> Result<CoverSignedProof, ReconstructError> {
    let (left_expr, left_value, left_to_literal) =
        cover_int_value_proof(ctx, arena, left, int_env, bool_env, values)?;
    let (right_expr, right_value, right_to_literal) =
        cover_int_value_proof(ctx, arena, right, int_env, bool_env, values)?;
    let (left_expr, left_value, left_to_literal, right_expr, right_value, right_to_literal, op) =
        match op {
            Op::IntGt => (
                right_expr,
                right_value,
                right_to_literal,
                left_expr,
                left_value,
                left_to_literal,
                Op::IntLt,
            ),
            Op::IntGe => (
                right_expr,
                right_value,
                right_to_literal,
                left_expr,
                left_value,
                left_to_literal,
                Op::IntLe,
            ),
            op => (
                left_expr,
                left_value,
                left_to_literal,
                right_expr,
                right_value,
                right_to_literal,
                op,
            ),
        };
    let left_literal = ctx.mk_intlit(left_value);
    let right_literal = ctx.mk_intlit(right_value);
    let literal_to_left = ctx.eq_symm(left_expr, left_literal, left_to_literal);
    let literal_to_right = ctx.eq_symm(right_expr, right_literal, right_to_literal);

    match op {
        Op::Eq => {
            let proposition = ctx.mk_eq(left_expr, right_expr);
            if left_value == right_value {
                let literal_refl = ctx.eq_refl(left_literal);
                let literal_to_right_expr = ctx.eq_trans(
                    left_literal,
                    right_literal,
                    right_expr,
                    literal_refl,
                    literal_to_right,
                );
                let proof = ctx.eq_trans(
                    left_expr,
                    left_literal,
                    right_expr,
                    left_to_literal,
                    literal_to_right_expr,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let not_literal = ctx.prove_intlit_disequality(left_value, right_value)?;
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let literal_to_right_expr = ctx.eq_trans(
                    left_literal,
                    left_expr,
                    right_expr,
                    literal_to_left,
                    hypothesis,
                );
                let literal_equality = ctx.eq_trans(
                    left_literal,
                    right_expr,
                    right_literal,
                    literal_to_right_expr,
                    right_to_literal,
                );
                let false_proof = ctx.kernel.app(not_literal, literal_equality);
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        Op::IntLt => {
            let proposition = ctx.mk_lt(left_expr, right_expr);
            if left_value < right_value {
                let literal_lt = ctx.lt_lit_lit(left_value, right_value)?;
                let cast_left = ctx.lt_cast_left(
                    left_literal,
                    left_expr,
                    right_literal,
                    literal_lt,
                    literal_to_left,
                );
                let proof = ctx.lt_cast_right(
                    left_expr,
                    right_literal,
                    right_expr,
                    cast_left,
                    literal_to_right,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let cast_left = ctx.lt_cast_left(
                    left_expr,
                    left_literal,
                    right_expr,
                    hypothesis,
                    left_to_literal,
                );
                let literal_left_right = ctx.lt_cast_right(
                    left_literal,
                    right_expr,
                    right_literal,
                    cast_left,
                    right_to_literal,
                );
                let false_proof = if left_value == right_value {
                    let irrefl = ctx.lt_irrefl_app(left_literal);
                    ctx.kernel.app(irrefl, literal_left_right)
                } else {
                    let reverse = ctx.lt_lit_lit(right_value, left_value)?;
                    let cycle = ctx.lt_trans_app(
                        right_literal,
                        left_literal,
                        right_literal,
                        reverse,
                        literal_left_right,
                    );
                    let irrefl = ctx.lt_irrefl_app(right_literal);
                    ctx.kernel.app(irrefl, cycle)
                };
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        Op::IntLe => {
            let proposition = ctx.mk_le(left_expr, right_expr);
            if left_value <= right_value {
                let literal_le = if left_value == right_value {
                    ctx.le_refl_app(left_literal)
                } else {
                    let literal_lt = ctx.lt_lit_lit(left_value, right_value)?;
                    ctx.le_of_lt_app(left_literal, right_literal, literal_lt)
                };
                let cast_left = ctx.le_cast_left(
                    left_literal,
                    left_expr,
                    right_literal,
                    literal_le,
                    literal_to_left,
                );
                let proof = ctx.le_cast_right(
                    left_expr,
                    right_literal,
                    right_expr,
                    cast_left,
                    literal_to_right,
                );
                Ok(CoverSignedProof { truth: true, proof })
            } else {
                let hypothesis_id = ctx.fresh_fvar();
                let hypothesis = ctx.kernel.fvar(hypothesis_id);
                let cast_left = ctx.le_cast_left(
                    left_expr,
                    left_literal,
                    right_expr,
                    hypothesis,
                    left_to_literal,
                );
                let literal_le = ctx.le_cast_right(
                    left_literal,
                    right_expr,
                    right_literal,
                    cast_left,
                    right_to_literal,
                );
                let reverse = ctx.lt_lit_lit(right_value, left_value)?;
                let cycle = ctx.lt_of_lt_of_le_app(
                    right_literal,
                    left_literal,
                    right_literal,
                    reverse,
                    literal_le,
                );
                let irrefl = ctx.lt_irrefl_app(right_literal);
                let false_proof = ctx.kernel.app(irrefl, cycle);
                Ok(CoverSignedProof {
                    truth: false,
                    proof: cover_not_lambda(ctx, proposition, hypothesis_id, false_proof),
                })
            }
        }
        _ => Err(cover_decline("unsupported integer atom")),
    }
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn cover_signed_formula(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    term: TermId,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<CoverSignedProof, ReconstructError> {
    let truth = cover_formula_truth(arena, term, values)
        .ok_or_else(|| cover_decline("formula is not decided by the current cover branch"))?;
    match arena.node(term) {
        TermNode::BoolConst(value) => {
            let expression = cover_bool_literal(ctx, *value);
            let proof = if *value {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(CoverSignedProof { truth, proof })
        }
        TermNode::Symbol(symbol) if arena.symbol(*symbol).1 == Sort::Bool => {
            if let Some(proof) = facts.get(symbol) {
                if proof.truth != truth {
                    return Err(cover_decline("free Bool fact disagrees with assignment"));
                }
                return Ok(*proof);
            }
            let expression = bool_env
                .get(symbol)
                .copied()
                .ok_or_else(|| cover_decline("decided Bool atom has no proof fact"))?;
            let proof = if truth {
                ctx.bool_eq_refl(expression)
            } else {
                ctx.bool_false_ne_true(expression)
            };
            Ok(CoverSignedProof { truth, proof })
        }
        TermNode::App { op, args } => match (op, &**args) {
            (Op::BoolNot, [argument]) => {
                let child = cover_signed_formula(
                    ctx, arena, *argument, int_env, bool_env, free_props, values, facts,
                )?;
                if truth {
                    Ok(CoverSignedProof {
                        truth,
                        proof: child.proof,
                    })
                } else {
                    let child_prop = cover_formula_prop(
                        ctx,
                        arena,
                        *argument,
                        int_env,
                        bool_env,
                        free_props,
                        Some(values),
                    )?;
                    let not_child = ctx.mk_not(child_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let false_proof = ctx.kernel.app(hypothesis, child.proof);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, not_child, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolAnd, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                if truth {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    Ok(CoverSignedProof {
                        truth,
                        proof: ctx.and_intro(left_prop, right_prop, left.proof, right.proof),
                    })
                } else {
                    let (selected, select_left) = if left_truth == Some(false) {
                        (*left, true)
                    } else if right_truth == Some(false) {
                        (*right, false)
                    } else {
                        return Err(cover_decline("false conjunction lacks a false child"));
                    };
                    let child = cover_signed_formula(
                        ctx, arena, selected, int_env, bool_env, free_props, values, facts,
                    )?;
                    let conjunction = ctx.mk_and(left_prop, right_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let projected = ctx.and_project(left_prop, right_prop, hypothesis, select_left);
                    let false_proof = ctx.kernel.app(child.proof, projected);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, conjunction, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolOr, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                if truth {
                    if left_truth == Some(true) {
                        let left = cover_signed_formula(
                            ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                        )?;
                        Ok(CoverSignedProof {
                            truth,
                            proof: ctx.or_intro_left(left_prop, right_prop, left.proof),
                        })
                    } else if right_truth == Some(true) {
                        let right = cover_signed_formula(
                            ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                        )?;
                        Ok(CoverSignedProof {
                            truth,
                            proof: ctx.or_intro_right(left_prop, right_prop, right.proof),
                        })
                    } else {
                        Err(cover_decline("true disjunction lacks a true child"))
                    }
                } else {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    let disjunction = ctx.mk_or(left_prop, right_prop);
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let left_id = ctx.fresh_fvar();
                    let left_hypothesis = ctx.kernel.fvar(left_id);
                    let left_false = ctx.kernel.app(left.proof, left_hypothesis);
                    let left_case = cover_not_lambda(ctx, left_prop, left_id, left_false);
                    let right_id = ctx.fresh_fvar();
                    let right_hypothesis = ctx.kernel.fvar(right_id);
                    let right_false = ctx.kernel.app(right.proof, right_hypothesis);
                    let right_case = cover_not_lambda(ctx, right_prop, right_id, right_false);
                    let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
                    let false_proof = ctx.or_rec_prop(
                        left_prop, right_prop, false_prop, left_case, right_case, hypothesis,
                    );
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, disjunction, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::BoolImplies, [left, right]) => {
                let left_truth = cover_formula_truth(arena, *left, values);
                let right_truth = cover_formula_truth(arena, *right, values);
                let left_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *left,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let right_prop = cover_formula_prop(
                    ctx,
                    arena,
                    *right,
                    int_env,
                    bool_env,
                    free_props,
                    Some(values),
                )?;
                let anon = ctx.kernel.anon();
                let implication = ctx
                    .kernel
                    .pi(anon, left_prop, right_prop, BinderInfo::Default);
                if truth {
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let result = if right_truth == Some(true) {
                        cover_signed_formula(
                            ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                        )?
                        .proof
                    } else if left_truth == Some(false) {
                        let left = cover_signed_formula(
                            ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                        )?;
                        let false_proof = ctx.kernel.app(left.proof, hypothesis);
                        ctx.ex_falso(right_prop, false_proof)
                    } else {
                        return Err(cover_decline("true implication is not decided"));
                    };
                    let body = ctx.kernel.abstract_fvars(result, &[hypothesis_id]);
                    Ok(CoverSignedProof {
                        truth,
                        proof: ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default),
                    })
                } else {
                    let left = cover_signed_formula(
                        ctx, arena, *left, int_env, bool_env, free_props, values, facts,
                    )?;
                    let right = cover_signed_formula(
                        ctx, arena, *right, int_env, bool_env, free_props, values, facts,
                    )?;
                    let hypothesis_id = ctx.fresh_fvar();
                    let hypothesis = ctx.kernel.fvar(hypothesis_id);
                    let result = ctx.kernel.app(hypothesis, left.proof);
                    let false_proof = ctx.kernel.app(right.proof, result);
                    Ok(CoverSignedProof {
                        truth,
                        proof: cover_not_lambda(ctx, implication, hypothesis_id, false_proof),
                    })
                }
            }
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Bool => cover_signed_iff(
                ctx, arena, *left, *right, false, int_env, bool_env, free_props, values, facts,
            ),
            (Op::BoolXor, [left, right]) => cover_signed_iff(
                ctx, arena, *left, *right, true, int_env, bool_env, free_props, values, facts,
            ),
            (Op::Eq, [left, right]) if arena.sort_of(*left) == Sort::Int => {
                cover_signed_int_atom(ctx, arena, Op::Eq, *left, *right, int_env, bool_env, values)
            }
            (Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe, [left, right]) => {
                cover_signed_int_atom(ctx, arena, *op, *left, *right, int_env, bool_env, values)
            }
            (Op::Ite, _) if arena.sort_of(term) == Sort::Bool => Err(cover_decline(
                "Boolean ite proof is outside the first cover slice",
            )),
            _ => Err(cover_decline(format!(
                "unsupported signed Boolean operator {op:?}"
            ))),
        },
        _ => Err(cover_decline("expected a decided Boolean formula")),
    }
}

#[allow(clippy::too_many_arguments)]
fn cover_signed_iff(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    left: TermId,
    right: TermId,
    negate: bool,
    int_env: &mut CoverKernelEnv,
    bool_env: &mut CoverKernelEnv,
    free_props: &CoverFreeProps,
    values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<CoverSignedProof, ReconstructError> {
    let left_proof = cover_signed_formula(
        ctx, arena, left, int_env, bool_env, free_props, values, facts,
    )?;
    let right_proof = cover_signed_formula(
        ctx, arena, right, int_env, bool_env, free_props, values, facts,
    )?;
    let left_prop = cover_formula_prop(
        ctx,
        arena,
        left,
        int_env,
        bool_env,
        free_props,
        Some(values),
    )?;
    let right_prop = cover_formula_prop(
        ctx,
        arena,
        right,
        int_env,
        bool_env,
        free_props,
        Some(values),
    )?;
    let iff_truth = left_proof.truth == right_proof.truth;
    let iff_prop = ctx.mk_iff(left_prop, right_prop);
    let iff_proof = if iff_truth {
        let anon = ctx.kernel.anon();
        let forward = if left_proof.truth {
            ctx.const_implication(left_prop, right_prop, right_proof.proof)
        } else {
            let id = ctx.fresh_fvar();
            let hypothesis = ctx.kernel.fvar(id);
            let false_proof = ctx.kernel.app(left_proof.proof, hypothesis);
            let result = ctx.ex_falso(right_prop, false_proof);
            let body = ctx.kernel.abstract_fvars(result, &[id]);
            ctx.kernel.lam(anon, left_prop, body, BinderInfo::Default)
        };
        let backward = if right_proof.truth {
            ctx.const_implication(right_prop, left_prop, left_proof.proof)
        } else {
            let id = ctx.fresh_fvar();
            let hypothesis = ctx.kernel.fvar(id);
            let false_proof = ctx.kernel.app(right_proof.proof, hypothesis);
            let result = ctx.ex_falso(left_prop, false_proof);
            let body = ctx.kernel.abstract_fvars(result, &[id]);
            ctx.kernel.lam(anon, right_prop, body, BinderInfo::Default)
        };
        ctx.iff_intro(left_prop, right_prop, forward, backward)
    } else {
        let hypothesis_id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(hypothesis_id);
        let false_proof = if left_proof.truth {
            let forward = ctx.iff_project(left_prop, right_prop, hypothesis, true);
            let right = ctx.kernel.app(forward, left_proof.proof);
            ctx.kernel.app(right_proof.proof, right)
        } else {
            let backward = ctx.iff_project(left_prop, right_prop, hypothesis, false);
            let left = ctx.kernel.app(backward, right_proof.proof);
            ctx.kernel.app(left_proof.proof, left)
        };
        cover_not_lambda(ctx, iff_prop, hypothesis_id, false_proof)
    };
    if !negate {
        Ok(CoverSignedProof {
            truth: iff_truth,
            proof: iff_proof,
        })
    } else if !iff_truth {
        Ok(CoverSignedProof {
            truth: true,
            proof: iff_proof,
        })
    } else {
        let not_iff = ctx.mk_not(iff_prop);
        let id = ctx.fresh_fvar();
        let hypothesis = ctx.kernel.fvar(id);
        let false_proof = ctx.kernel.app(hypothesis, iff_proof);
        Ok(CoverSignedProof {
            truth: false,
            proof: cover_not_lambda(ctx, not_iff, id, false_proof),
        })
    }
}

const COVER_LEAN_NODE_CAP: usize = 100_000;

fn cover_contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn cover_flatten_conjunction(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
        && let [left, right] = &**args
    {
        cover_flatten_conjunction(arena, *left, out);
        cover_flatten_conjunction(arena, *right, out);
    } else {
        out.push(term);
    }
}

fn cover_forall_chain(arena: &TermArena, mut term: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(symbol),
        args,
    } = arena.node(term)
    {
        let [body] = &**args else {
            return None;
        };
        if !matches!(arena.symbol(*symbol).1, Sort::Bool | Sort::Int) {
            return None;
        }
        binders.push(*symbol);
        term = *body;
    }
    (!binders.is_empty() && !cover_contains_quantifier(arena, term)).then_some((binders, term))
}

fn cover_lean_parts(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Vec<TermId>, usize, Vec<SymbolId>, TermId)> {
    let mut leaves = Vec::new();
    for &assertion in assertions {
        cover_flatten_conjunction(arena, assertion, &mut leaves);
    }
    let quantified = leaves
        .iter()
        .enumerate()
        .filter_map(|(index, term)| cover_contains_quantifier(arena, *term).then_some(index))
        .collect::<Vec<_>>();
    let [index] = &*quantified else {
        return None;
    };
    let index = *index;
    let (binders, body) = cover_forall_chain(arena, leaves[index])?;
    Some((leaves, index, binders, body))
}

/// Cheap router predicate for ADR-0108's first kernel reconstruction slice.
pub(crate) fn quantified_counterexample_cover_lean_shape(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    cover_lean_parts(arena, assertions).is_some()
        && admitted_free_booleans(arena, assertions).is_some_and(|free| !free.is_empty())
}

fn cover_declare_free_props(
    ctx: &mut IntReconstructCtx,
    symbols: &[SymbolId],
) -> Result<CoverFreeProps, ReconstructError> {
    let mut props = CoverFreeProps::new();
    for &symbol in symbols {
        let name = ctx.fresh_name("bool_atom");
        let prop = ctx.kernel.sort_zero();
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: Vec::new(),
                ty: prop,
            })
            .map_err(|error| ReconstructError::KernelRejected {
                rule: "quantified_counterexample_cover".to_owned(),
                detail: format!("free proposition declaration failed: {error:?}"),
            })?;
        props.insert(symbol, ctx.kernel.const_(name, Vec::new()));
    }
    Ok(props)
}

fn cover_case_matches(case: &QuantifiedCounterexampleCoverCase, values: &Assignment) -> bool {
    case.cube.iter().all(|&(symbol, value)| {
        values.get(symbol).and_then(|assigned| assigned.as_bool()) == Some(value)
    })
}

fn cover_case_compatible(case: &QuantifiedCounterexampleCoverCase, values: &Assignment) -> bool {
    case.cube.iter().all(|&(symbol, value)| {
        values
            .get(symbol)
            .and_then(|assigned| assigned.as_bool())
            .is_none_or(|assigned| assigned == value)
    })
}

fn cover_score_unassigned(
    arena: &TermArena,
    term: TermId,
    values: &Assignment,
    scores: &mut BTreeMap<SymbolId, usize>,
) {
    if cover_formula_truth(arena, term, values).is_some() {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(symbol)
            if arena.symbol(*symbol).1 == Sort::Bool && values.get(*symbol).is_none() =>
        {
            *scores.entry(*symbol).or_default() += 4;
        }
        TermNode::App { args, .. } => {
            for &argument in args {
                cover_score_unassigned(arena, argument, values, scores);
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn cover_case_contradiction(
    ctx: &mut IntReconstructCtx,
    arena: &TermArena,
    case: &QuantifiedCounterexampleCoverCase,
    binders: &[SymbolId],
    body: TermId,
    universal_hypothesis: ExprId,
    free_props: &CoverFreeProps,
    branch_values: &Assignment,
    facts: &BTreeMap<SymbolId, CoverSignedProof>,
) -> Result<ExprId, ReconstructError> {
    if case.bindings.len() != binders.len()
        || case
            .bindings
            .iter()
            .zip(binders)
            .any(|((symbol, _), expected)| symbol != expected)
    {
        return Err(cover_decline("case bindings do not match universal chain"));
    }
    let mut values = branch_values.clone();
    let mut int_env = CoverKernelEnv::new();
    let mut bool_env = CoverKernelEnv::new();
    let mut instance = universal_hypothesis;
    for &(symbol, ref value) in &case.bindings {
        values.set(symbol, value.clone());
        let witness = match value {
            Value::Int(value) => {
                if !int_values_fit_proof_unit_budget([*value]) {
                    return Err(cover_decline("integer witness exceeds proof-size cap"));
                }
                let witness = ctx.mk_intlit(*value);
                int_env.insert(symbol, witness);
                witness
            }
            Value::Bool(value) => {
                let witness = cover_bool_literal(ctx, *value);
                bool_env.insert(symbol, witness);
                witness
            }
            _ => return Err(cover_decline("non-Bool/Int case binding")),
        };
        instance = ctx.kernel.app(instance, witness);
    }
    let signed = cover_signed_formula(
        ctx,
        arena,
        body,
        &mut int_env,
        &mut bool_env,
        free_props,
        &values,
        facts,
    )?;
    if signed.truth {
        return Err(cover_decline(
            "matched case does not falsify universal body",
        ));
    }
    Ok(ctx.kernel.app(signed.proof, instance))
}

struct CoverTree<'a> {
    arena: &'a TermArena,
    ground_leaves: &'a [(TermId, ExprId)],
    universal_hypothesis: ExprId,
    binders: &'a [SymbolId],
    body: TermId,
    cases: &'a [QuantifiedCounterexampleCoverCase],
    free_symbols: &'a [SymbolId],
    free_props: &'a CoverFreeProps,
    nodes: usize,
}

impl CoverTree<'_> {
    #[allow(clippy::too_many_lines)]
    fn contradiction(
        &mut self,
        ctx: &mut IntReconstructCtx,
        values: &Assignment,
        facts: &BTreeMap<SymbolId, CoverSignedProof>,
    ) -> Result<ExprId, ReconstructError> {
        self.nodes += 1;
        if self.nodes > COVER_LEAN_NODE_CAP {
            return Err(cover_decline(
                "excluded-middle proof tree exceeded node cap",
            ));
        }

        for &(term, hypothesis) in self.ground_leaves {
            if cover_formula_truth(self.arena, term, values) == Some(false) {
                let signed = cover_signed_formula(
                    ctx,
                    self.arena,
                    term,
                    &mut CoverKernelEnv::new(),
                    &mut CoverKernelEnv::new(),
                    self.free_props,
                    values,
                    facts,
                )?;
                return Ok(ctx.kernel.app(signed.proof, hypothesis));
            }
        }

        if let Some(case) = self
            .cases
            .iter()
            .find(|case| cover_case_matches(case, values))
        {
            return cover_case_contradiction(
                ctx,
                self.arena,
                case,
                self.binders,
                self.body,
                self.universal_hypothesis,
                self.free_props,
                values,
                facts,
            );
        }

        let mut scores = BTreeMap::<SymbolId, usize>::new();
        for &(term, _) in self.ground_leaves {
            cover_score_unassigned(self.arena, term, values, &mut scores);
        }
        for case in self
            .cases
            .iter()
            .filter(|case| cover_case_compatible(case, values))
        {
            for &(symbol, _) in &case.cube {
                if values.get(symbol).is_none() {
                    *scores.entry(symbol).or_default() += 1;
                }
            }
        }
        let symbol = scores
            .into_iter()
            .max_by_key(|(symbol, score)| (*score, std::cmp::Reverse(*symbol)))
            .map(|(symbol, _)| symbol)
            .or_else(|| {
                self.free_symbols
                    .iter()
                    .copied()
                    .find(|symbol| values.get(*symbol).is_none())
            })
            .ok_or_else(|| cover_decline("complete Boolean branch is not covered"))?;
        let proposition = *self
            .free_props
            .get(&symbol)
            .ok_or_else(|| cover_decline("branch symbol has no proposition"))?;

        let true_id = ctx.fresh_fvar();
        let true_hypothesis = ctx.kernel.fvar(true_id);
        let mut true_values = values.clone();
        true_values.set(symbol, Value::Bool(true));
        let mut true_facts = facts.clone();
        true_facts.insert(
            symbol,
            CoverSignedProof {
                truth: true,
                proof: true_hypothesis,
            },
        );
        let true_false = self.contradiction(ctx, &true_values, &true_facts)?;
        let true_body = ctx.kernel.abstract_fvars(true_false, &[true_id]);
        let anon = ctx.kernel.anon();
        let true_case = ctx
            .kernel
            .lam(anon, proposition, true_body, BinderInfo::Default);

        let not_proposition = ctx.mk_not(proposition);
        let false_id = ctx.fresh_fvar();
        let false_hypothesis = ctx.kernel.fvar(false_id);
        let mut false_values = values.clone();
        false_values.set(symbol, Value::Bool(false));
        let mut false_facts = facts.clone();
        false_facts.insert(
            symbol,
            CoverSignedProof {
                truth: false,
                proof: false_hypothesis,
            },
        );
        let false_false = self.contradiction(ctx, &false_values, &false_facts)?;
        let false_body = ctx.kernel.abstract_fvars(false_false, &[false_id]);
        let false_case = ctx
            .kernel
            .lam(anon, not_proposition, false_body, BinderInfo::Default);

        let excluded_middle = ctx.classical_em(proposition)?;
        let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
        Ok(ctx.or_rec_prop(
            proposition,
            not_proposition,
            false_prop,
            true_case,
            false_case,
            excluded_middle,
        ))
    }
}

/// Reconstruct an ADR-0108 checked counterexample cover as a kernel-checked
/// contradiction over the original ground conjuncts and genuine universal.
///
/// The first slice admits exactly one positive top-level universal conjunct.
/// Each retained cube is used only to choose a concrete source instantiation;
/// a bounded excluded-middle tree proves that every free-Boolean branch either
/// violates an original ground conjunct or one instantiated universal body.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] when the certificate or formula
/// is outside the bounded slice, and [`ReconstructError::KernelRejected`] when
/// the assembled closed proof does not infer to `False`.
pub fn reconstruct_quantified_counterexample_cover_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &QuantifiedCounterexampleCoverCertificate,
) -> Result<String, ReconstructError> {
    if !check_quantified_counterexample_cover(arena, assertions, certificate) {
        return Err(cover_decline("invalid ADR-0108 certificate"));
    }
    let (leaves, universal_index, binders, body) = cover_lean_parts(arena, assertions)
        .ok_or_else(|| cover_decline("unsupported source shape"))?;
    let universal = leaves[universal_index];
    if certificate.cases.iter().any(|case| {
        let mut source_leaves = Vec::new();
        cover_flatten_conjunction(arena, case.assertion, &mut source_leaves);
        !source_leaves.contains(&universal)
    }) {
        return Err(cover_decline(
            "case source does not contain admitted universal",
        ));
    }
    let binding_values = certificate.cases.iter().flat_map(|case| {
        case.bindings.iter().filter_map(|(_, value)| match value {
            Value::Int(value) => Some(*value),
            _ => None,
        })
    });
    if !source_int_literals_fit_proof_unit_budget(arena, assertions.iter().copied())
        || !int_values_fit_proof_unit_budget(binding_values)
    {
        return Err(cover_decline(
            "integer literals or witnesses exceed proof-size cap",
        ));
    }
    let free_symbols = admitted_free_booleans(arena, assertions)
        .ok_or_else(|| cover_decline("source has inadmissible free symbols"))?;
    let mut ctx = IntReconstructCtx::new();
    let free_props = cover_declare_free_props(&mut ctx, &free_symbols)?;

    let mut hypotheses = Vec::with_capacity(leaves.len());
    for &leaf in &leaves {
        let proposition = cover_formula_prop(
            &mut ctx,
            arena,
            leaf,
            &mut CoverKernelEnv::new(),
            &mut CoverKernelEnv::new(),
            &free_props,
            None,
        )?;
        hypotheses.push(ctx.hyp_axiom(proposition)?);
    }
    let universal_hypothesis = hypotheses[universal_index];
    let ground_leaves = leaves
        .iter()
        .copied()
        .zip(hypotheses.iter().copied())
        .enumerate()
        .filter_map(|(index, pair)| (index != universal_index).then_some(pair))
        .collect::<Vec<_>>();
    let mut tree = CoverTree {
        arena,
        ground_leaves: &ground_leaves,
        universal_hypothesis,
        binders: &binders,
        body,
        cases: &certificate.cases,
        free_symbols: &free_symbols,
        free_props: &free_props,
        nodes: 0,
    };
    let proof = tree.contradiction(&mut ctx, &Assignment::new(), &BTreeMap::new())?;
    let false_prop = ctx.kernel.const_(ctx.int.logic.false_, Vec::new());
    ctx.require_partition_type(proof, false_prop, "counterexample-cover contradiction")?;
    let bool_inductive = ctx.int.logic.bool_;
    Ok(ctx.kernel().render_lean_module_compact_with_inductives(
        "axeyum_refutation",
        false_prop,
        proof,
        &[bool_inductive],
    ))
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
        let rec = self
            .kernel
            .const_(self.int.logic.exists_rec, vec![zero, one]);
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
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.int.logic.or_rec, vec![zero]);
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

/// **Reconstruct an integer Diophantine refutation to a kernel-checked Lean
/// `False`.** Runs the in-tree [`DiophantineCertificate`] decision on `assertions`;
/// on a refutation, reconstructs the integer-infeasibility argument over
/// [`IntPrelude`] and returns the assembled `False` proof term (already `infer` +
/// `def_eq False`-gated through the kernel).
///
/// Handles the main case `g = gcd(|combined_j|) > 0` (the certificate guarantees `g
/// ∤ constant`) via discreteness, and the degenerate empty-`combined` row (`g = 0`,
/// `0 = constant ≠ 0`) via the sign-based `Not (Eq Z zero (intlit constant))` close.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when there is no Diophantine refutation, a
/// coefficient/bound overflow, or a normalizer mismatch (the certificate's claimed
/// combined row does not canonicalize as expected — never fabricated);
/// [`ReconstructError::KernelRejected`] when the assembled term does not
/// kernel-check to `False`.
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
        // Faithful combined form and its own normalization to `lhs_canon`. When the
        // combined row is empty (the degenerate `g = 0` case: all variables cancel),
        // the faithful form is `zero`, which `normalize_kernel` reads as `ZExpr::Zero`
        // and canonicalizes to the empty gen list (= `expected_lhs`). This yields
        // `h_comb : Eq Z zero (intlit constant)` for the `0 = constant` contradiction.
        let combined_faithful = match lin_to_zexpr(combined_dense, 0) {
            Some(z) => self.emit_zexpr(&z),
            None => self.mk_zero(),
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

    /// `lt (intlit c) zero` for `c < 0`. Derived from `lt zero (intlit |c|)` by
    /// adding `intlit c` to both sides (`add_lt_add_of_le_of_lt` with `le_refl`),
    /// then renormalizing `intlit c + 0 → intlit c` and `intlit c + intlit |c| → 0`.
    fn lt_neg_intlit_zero(&mut self, c: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(c < 0);
        let abs = c.unsigned_abs();
        let abs_i = i128::try_from(abs).map_err(|_| ReconstructError::UnsupportedTerm {
            term: "|constant| overflow".to_owned(),
        })?;
        // h0 : lt zero (intlit |c|).
        let h0 = self.lt_zero_intlit(abs_i)?;
        let zero = self.mk_zero();
        let c_lit = self.mk_intlit(c);
        let abs_lit = self.mk_intlit(abs_i);
        // h_le : le (intlit c)(intlit c)  (le_refl).
        let h_le = self.le_refl_app(c_lit);
        // add_lt_add_of_le_of_lt c c zero |c| h_le h0 : lt (add c zero)(add c |c|).
        let combined = self.add_lt_add_of_le_of_lt_app(c_lit, c_lit, zero, abs_lit, h_le, h0);
        // cast lhs (add c zero) → c via add_zero.
        let c_zero = self.mk_add(c_lit, zero);
        let c_abs = self.mk_add(c_lit, abs_lit);
        let addz = self.add_zero_eq(c_lit); // add c zero = c
        let lt_c_cabs = self.lt_cast_left(c_zero, c_lit, c_abs, combined, addz);
        // cast rhs (add c |c|) → zero : Eq Z (add (intlit c)(intlit |c|)) (intlit 0).
        let sum_eq_zero = self.intlit_add_eq(c, abs_i, 0)?; // Eq Z (add c |c|) (intlit 0) = zero
        Ok(self.lt_cast_right(c_lit, c_abs, zero, lt_c_cabs, sum_eq_zero))
    }

    /// Build `ne_c : Not (Eq Z zero (intlit constant))` for `constant ≠ 0`. The
    /// returned term is the lambda `fun (h : Eq Z zero c) => …` whose body transports
    /// the sign fact (`lt zero c` for `c > 0`, or `lt c zero` for `c < 0`) along `h`
    /// to `lt zero zero` and closes with `lt_irrefl zero`. `Not (Eq Z zero c)`
    /// def-unfolds to `Eq Z zero c → False`, so the lambda's type is the `Not`.
    fn ne_zero_intlit(&mut self, constant: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(constant != 0);
        let zero = self.mk_zero();
        let c_lit = self.mk_intlit(constant);
        // The sign fact, oriented so a cast along `h : Eq Z zero c` lands on `lt zero zero`.
        // c > 0: lt zero c ; cast RIGHT (c → zero) along (symm h).
        // c < 0: lt c zero ; cast LEFT  (c → zero) along (symm h).
        let fid = self.fresh_fvar();
        let h = self.kernel.fvar(fid); // Eq Z zero c
        let h_sym = self.eq_symm(zero, c_lit, h); // Eq Z c zero
        let lt_zero_zero = if constant > 0 {
            let lt_zero_c = self.lt_zero_intlit(constant)?; // lt zero c
            self.lt_cast_right(zero, c_lit, zero, lt_zero_c, h_sym)
        } else {
            let lt_c_zero = self.lt_neg_intlit_zero(constant)?; // lt c zero
            self.lt_cast_left(c_lit, zero, zero, lt_c_zero, h_sym)
        };
        let irr = self.lt_irrefl_app(zero); // Not (lt zero zero)
        let false_proof = self.kernel.app(irr, lt_zero_zero); // False
        let body = self.kernel.abstract_fvars(false_proof, &[fid]);
        let anon = self.kernel.anon();
        let eq_zero_c = self.mk_eq(zero, c_lit);
        Ok(self.kernel.lam(anon, eq_zero_c, body, BinderInfo::Default))
    }

    /// Declare each input equality `E_i` as a hypothesis axiom `h_i : Eq Z L_i
    /// (intlit b_i)`, returning the `(l_expr, l_gens, r_expr, b_i, h_i)` tuples the
    /// combiner consumes. Declines on any coefficient/rhs magnitude over the bound.
    #[allow(clippy::type_complexity)]
    fn build_hyps(
        &mut self,
        equalities: &[Equality],
        index_of: &BTreeMap<SymbolId, usize>,
    ) -> Result<Vec<(ExprId, Vec<IGen>, ExprId, i128, ExprId)>, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };
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
        Ok(hyps)
    }

    /// Close the degenerate `g = 0` row: the combined row is `Eq Z zero (intlit
    /// constant)` with `constant ≠ 0`, a contradiction in any ordered ring (no
    /// discreteness needed). `False := ne_c h_comb`, where `ne_c : Not (Eq Z zero
    /// (intlit constant))` is built from the SIGN of `constant`. Declines if
    /// `|constant|` exceeds the unit-expansion bound (keeps the repeated-`one` build
    /// small).
    fn build_diophantine_false_g0(
        &mut self,
        equalities: &[Equality],
        cert: &DiophantineCertificate,
        index_of: &BTreeMap<SymbolId, usize>,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };
        debug_assert!(cert.combined.is_empty());
        if cert.constant == 0 {
            // gcd(∅) = 0 ∤ d requires d ≠ 0; a `0 = 0` row is not a refutation.
            return Err(decline("g = 0 with constant = 0 (no contradiction)"));
        }
        if cert.constant.unsigned_abs() > DIO_UNIT_MAX as u128 {
            return Err(decline("|constant| exceeds the unit-expansion bound"));
        }
        let combined_dense: Vec<(usize, i128)> = Vec::new();
        let hyps = self.build_hyps(equalities, index_of)?;
        // h_comb : Eq Z zero (intlit constant)  (combined LHS normalizes to `zero`).
        let h_comb =
            self.combine_equalities(&hyps, &cert.multipliers, &combined_dense, cert.constant)?;
        // ne_c : Not (Eq Z zero (intlit constant)) ; False := ne_c h_comb.
        let ne_c = self.ne_zero_intlit(cert.constant)?;
        Ok(self.kernel.app(ne_c, h_comb))
    }

    /// Assemble the `False` proof term for the Diophantine certificate. Handles both
    /// the main `g > 0` discreteness path and the degenerate `g = 0` row
    /// (`0 = constant ≠ 0`, all variables cancelled): the latter is a contradiction
    /// in any ordered ring (no discreteness needed), closed by `ne_c h_comb` where
    /// `ne_c : Not (Eq Z zero (intlit constant))`. Returns a [`ReconstructError`]
    /// (decline) on a bound overflow or a normalizer/identity mismatch; the caller
    /// gates the result through `infer`/`def_eq False`.
    #[allow(clippy::too_many_lines)]
    fn build_diophantine_false(
        &mut self,
        equalities: &[Equality],
        cert: &DiophantineCertificate,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |detail: &str| ReconstructError::UnsupportedTerm {
            term: format!("Diophantine reconstruction declined: {detail}"),
        };

        // --- dense variable indices (stable, shared by both paths) -------------
        let index_of = dense_index_map(equalities, cert);

        // --- gcd g and Euclidean (q, r): constant = g·q + r, 0 < r < g ---------
        let mut g: i128 = 0;
        for &(_, c) in &cert.combined {
            g = gcd_i128(g, c);
        }
        if g == 0 {
            // Degenerate `0 = constant ≠ 0` row (all variables cancelled). No
            // discreteness is needed — `0 = c` with `c ≠ 0` is false in any ordered
            // ring; route to the dedicated sign-based close.
            return self.build_diophantine_false_g0(equalities, cert, &index_of);
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
        let hyps = self.build_hyps(equalities, &index_of)?;

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

// =============================================================================
// Integer-INEQUALITY infeasibility reconstruction (ADR-0042, the integer-cut
// payoff for the single-variable `c ≤ k·x ≤ d` shape).
// =============================================================================

/// The identity of the single integer "variable" an interval/equality atom is over.
///
/// Either a genuine integer [`SymbolId`] (`Σ … x …`) or an **opaque integer
/// application** `(f args)` keyed by its structurally-hashed [`TermId`] — the latter
/// lets the integer reconstructor treat a maximal non-arithmetic `Int`-sorted subterm
/// `(f c)` (an uninterpreted-function application) as a fresh opaque integer, exactly
/// as the conjunctive `QF_UFLIA` interpolant's congruence-free refutations require.
///
/// **Soundness of the opaque case.** An `(f args)` application is `Int`-sorted, so it
/// denotes *some* integer. Treating it as a fresh integer variable `y` GENERALIZES the
/// atom: the original (with `y := f(args)`) is a special case of the free-`y` system.
/// If the free-`y` system is integer-infeasible (which the discreteness reconstruction
/// proves over an opaque `Z` axiom — [`IntReconstructCtx::var_const_for`] already maps
/// every variable to one opaque `Z` constant), then a fortiori the original is. So an
/// opaque atom can only make UNSAT *harder* to witness, never spuriously UNSAT — and
/// the kernel gate (`infer` + `def_eq False`) remains the sole authority. The two
/// equal `TermId`s of a shared `(f c)` (structural hashing) compare equal here, so the
/// "same variable" detector checks hold for a shared opaque application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomVar {
    /// A genuine integer symbol.
    Sym(SymbolId),
    /// An opaque integer application `(f args)`, keyed by its `TermId`.
    Opaque(TermId),
}

/// The detected single-variable integer-interval shape `c ≤ k·x ≤ d` with `k > 0`,
/// over one integer variable `x`, where **no multiple of `k` lies in `[c, d]`** (so
/// the system is integer-infeasible while its LP relaxation is feasible).
///
/// The discreteness reduction picks the integer `m` with `k·m < c` and `d < k·(m+1)`
/// (forced and unique when one exists): then `m < x < m+1`, i.e. `0 < x − m < 1`,
/// refuted by `no_int_between (x − m)`.
#[derive(Debug, Clone, Copy)]
struct IntInterval {
    /// The single integer variable (a symbol or an opaque application).
    var: AtomVar,
    /// The positive multiplier `k`.
    k: i128,
    /// The lower bound `c` (so `c ≤ k·x`).
    c: i128,
    /// The upper bound `d` (so `k·x ≤ d`).
    d: i128,
    /// The reduction offset `m` with `k·m < c` and `d < k·(m+1)`.
    m: i128,
}

/// A single-variable integer interval with **distinct** lower/upper multipliers:
/// `c ≤ k_lo·x` and `k_hi·x ≤ d` (`k_lo, k_hi > 0`, `k_lo ≠ k_hi`). Integer-infeasible
/// because the implied integer window `(m_lo, m_lo+1)` on `x` contains no integer,
/// while it is LP-feasible (genuinely needs an integer cut, not a Farkas/LRA close).
#[derive(Debug, Clone, Copy)]
struct IntIntervalDiff {
    var: AtomVar,
    /// Lower multiplier `k_lo > 0` (so `c ≤ k_lo·x`).
    k_lo: i128,
    c: i128,
    /// Upper multiplier `k_hi > 0` (so `k_hi·x ≤ d`).
    k_hi: i128,
    d: i128,
    /// Lower reduction offset: `m_lo = ⌊(c−1)/k_lo⌋`, the forced `lt m_lo x`.
    m_lo: i128,
    /// Upper reduction offset: `m_hi = ⌊d/k_hi⌋`, the forced `lt x (m_hi+1)`.
    m_hi: i128,
}

/// A single-variable integer **equality combined with a unit-multiplier bound** that is
/// **real-infeasible**: an equality `k·x = b` (`k > 0`) together with a bound `c ≤ x`
/// (lower) or `x ≤ c` (upper). The equality pins `x = b/k` (a rational); the bound
/// excludes it, so the conjunction is unsatisfiable already over ℝ — yet neither
/// dedicated integer reconstructor covers it: the Diophantine path ignores the inequality
/// and the equality alone (`k | b` permitted) is feasible, and the interval detectors
/// require **two** inequalities (no equality atom). The refutation scales the bound by
/// `k` and chains through the equality to a literal `b ⋈ k·c` contradiction.
///
/// Lower-bound infeasibility: `c ≤ x ⟹ k·c ≤ k·x = b`, contradicting `b < k·c`.
/// Upper-bound infeasibility: `x ≤ c ⟹ b = k·x ≤ k·c`, contradicting `k·c < b`.
#[derive(Debug, Clone, Copy)]
struct IntEqBound {
    var: AtomVar,
    /// The positive equality multiplier `k > 0` (oriented), so `k·x = b`.
    k: i128,
    /// The equality right-hand value `b`.
    b: i128,
    /// The bound constant `c`: `c ≤ x` when `lower`, else `x ≤ c`.
    c: i128,
    /// Whether the bound is a lower bound (`c ≤ x`) or an upper bound (`x ≤ c`).
    lower: bool,
}

/// A bound atom recovered from one assertion: `lower` ⇒ `k·x ≥ c` (i.e. `c ≤ k·x`),
/// `!lower` ⇒ `k·x ≤ d`. Both sides are normalized so the variable side is exactly
/// `k·x` (`k > 0`) and the bound is the integer constant on the other side.
#[derive(Debug, Clone, Copy)]
struct BoundAtom {
    var: AtomVar,
    k: i128,
    bound: i128,
    lower: bool,
}

/// Parse a linear integer term into `(coeff·var, constant)` for a **single** variable
/// (or a pure constant). The "variable" is either a genuine integer symbol or an
/// **opaque integer application** `(f args)` treated as a fresh opaque integer (see
/// [`AtomVar`] for the soundness of the opaque case). Returns `None` for
/// multi-variable / nonlinear / multi-term forms — this slice handles only the
/// single-variable interval shape.
fn single_var_linear(arena: &TermArena, t: TermId) -> Option<(Option<(AtomVar, i128)>, i128)> {
    match arena.node(t) {
        TermNode::IntConst(n) => Some((None, *n)),
        TermNode::Symbol(s) => Some((Some((AtomVar::Sym(*s), 1)), 0)),
        // A maximal non-arithmetic `Int`-sorted subterm `(f args)` is an opaque integer
        // variable, keyed by its (structurally-hashed) `TermId`.
        TermNode::App {
            op: Op::Apply(_), ..
        } => Some((Some((AtomVar::Opaque(t), 1)), 0)),
        TermNode::App { op, args } => match (op, &args[..]) {
            (Op::IntNeg, [x]) => {
                let (v, k) = single_var_linear(arena, *x)?;
                let v = match v {
                    Some((s, c)) => Some((s, c.checked_neg()?)),
                    None => None,
                };
                Some((v, k.checked_neg()?))
            }
            (Op::IntAdd | Op::IntSub, [x, y]) => {
                let sub = matches!(op, Op::IntSub);
                let (vx, kx) = single_var_linear(arena, *x)?;
                let (vy, ky) = single_var_linear(arena, *y)?;
                let ky = if sub { ky.checked_neg()? } else { ky };
                let var = match (vx, vy) {
                    (None, None) => None,
                    (Some(p), None) => Some(p),
                    (None, Some((s, c))) => Some((s, if sub { c.checked_neg()? } else { c })),
                    (Some((sx, cx)), Some((sy, cy))) => {
                        if sx != sy {
                            return None; // two distinct variables — out of scope
                        }
                        let cy = if sub { cy.checked_neg()? } else { cy };
                        Some((sx, cx.checked_add(cy)?))
                    }
                };
                Some((var, kx.checked_add(ky)?))
            }
            (Op::IntMul, [x, y]) => {
                let (vx, kx) = single_var_linear(arena, *x)?;
                let (vy, ky) = single_var_linear(arena, *y)?;
                match (vx, vy) {
                    (None, Some((s, c))) => {
                        Some((Some((s, c.checked_mul(kx)?)), ky.checked_mul(kx)?))
                    }
                    (Some((s, c)), None) => {
                        Some((Some((s, c.checked_mul(ky)?)), kx.checked_mul(ky)?))
                    }
                    (None, None) => Some((None, kx.checked_mul(ky)?)),
                    (Some(_), Some(_)) => None, // nonlinear (var·var)
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse one assertion into a [`BoundAtom`] of the form `c ≤ k·x` or `k·x ≤ d`
/// (`k > 0`, single variable `x`). Recognizes `IntLe`/`IntGe`/`IntLt`/`IntGt` and
/// rewrites strict integer bounds to non-strict ones (`k·x > c ⟺ k·x ≥ c+1`,
/// `k·x < d ⟺ k·x ≤ d−1`). Returns `None` on any other shape.
fn parse_bound_atom(arena: &TermArena, t: TermId) -> Option<BoundAtom> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    let [a, b] = &args[..] else {
        return None;
    };
    let (a, b) = (*a, *b);
    // Normalize each comparison `lhs ⋈ rhs` to `var_side ⋈' bound`, with `var_side`
    // the side carrying the variable. We collect `lhs − rhs = k·x + const ⋈ 0` and
    // read off the bound on `x` directly.
    let (la, ka) = single_var_linear(arena, a)?;
    let (lb, kb) = single_var_linear(arena, b)?;
    // Move everything to the left: `(lhs − rhs) ⋈ 0`, i.e. `kx·x + (ka − kb) ⋈ 0`.
    let (var, coeff) = match (la, lb) {
        (Some((s, c)), None) => (s, c),
        (None, Some((s, c))) => (s, c.checked_neg()?),
        (Some((sx, cx)), Some((sy, cy))) if sx == sy => (sx, cx.checked_sub(cy)?),
        _ => return None,
    };
    if coeff == 0 {
        return None;
    }
    let konst = ka.checked_sub(kb)?; // `coeff·x + konst ⋈ 0`

    // Direction of the relation as `coeff·x + konst R 0` with R ∈ {≤,<,≥,>}.
    // We rewrite to an oriented `k·x ⋈ bound` with `k > 0`.
    // op compares `a R b`, i.e. `(a − b) R 0`.
    let (mut k, mut konst, mut rel) = (coeff, konst, *op);
    // If coeff < 0, multiply the inequality by −1, flipping the relation.
    if k < 0 {
        k = k.checked_neg()?;
        konst = konst.checked_neg()?;
        rel = flip_rel(rel)?;
    }
    // Now `k·x + konst R 0`, k > 0. Rearrange to `k·x R (−konst)`.
    let rhs = konst.checked_neg()?;
    // Map to a lower/upper non-strict bound on `k·x`.
    // k·x ≤ rhs (Le), k·x < rhs (Lt ⇒ ≤ rhs−1), k·x ≥ rhs (Ge), k·x > rhs (Gt ⇒ ≥ rhs+1).
    let (bound, lower) = match rel {
        Op::IntLe => (rhs, false),
        Op::IntLt => (rhs.checked_sub(1)?, false),
        Op::IntGe => (rhs, true),
        Op::IntGt => (rhs.checked_add(1)?, true),
        _ => return None,
    };
    Some(BoundAtom {
        var,
        k,
        bound,
        lower,
    })
}

/// Flip a comparison `Op` under negation of both sides (`a R b` ⟺ `−a R' −b`).
fn flip_rel(op: Op) -> Option<Op> {
    Some(match op {
        Op::IntLe => Op::IntGe,
        Op::IntLt => Op::IntGt,
        Op::IntGe => Op::IntLe,
        Op::IntGt => Op::IntLt,
        _ => return None,
    })
}

/// Detect the canonical single-variable integer-interval shape `c ≤ k·x ≤ d` (k > 0,
/// one variable, LP-feasible `c ≤ d`, integer-infeasible: no multiple of `k` in
/// `[c, d]`). On a match returns the [`IntInterval`] with the forced reduction offset
/// `m` (`k·m < c` and `d < k·(m+1)`). `None` otherwise (declines — never fabricates).
fn detect_int_interval(arena: &TermArena, assertions: &[TermId]) -> Option<IntInterval> {
    let [a1, a2] = assertions else {
        return None;
    };
    let b1 = parse_bound_atom(arena, *a1)?;
    let b2 = parse_bound_atom(arena, *a2)?;
    if b1.var != b2.var || b1.lower == b2.lower {
        return None; // need exactly one lower and one upper bound on the same var
    }
    let (lo, hi) = if b1.lower { (b1, b2) } else { (b2, b1) };
    // Require the SAME positive multiplier on both sides for the clean `c ≤ k·x ≤ d`
    // reduction (a later slice may rescale to a common multiple).
    if lo.k != hi.k || lo.k <= 0 {
        return None;
    }
    let k = lo.k;
    let c = lo.bound; // c ≤ k·x
    let d = hi.bound; // k·x ≤ d
    if c > d {
        return None; // LP-infeasible — an LRA (not integer-cut) refutation; decline
    }
    // The infeasible-interval reduction: find integer m with k·m < c and d < k·(m+1).
    // m is forced: m = ⌊(c−1)/k⌋ (Euclidean, k > 0). Verify both strict bounds; if
    // they hold there is no multiple of k in [c, d] and we have a discreteness proof.
    let m = (c.checked_sub(1)?).div_euclid(k);
    let km = k.checked_mul(m)?;
    let km1 = k.checked_mul(m.checked_add(1)?)?;
    if !(km < c && d < km1) {
        return None; // some multiple of k lies in [c, d] — integer-feasible; decline
    }
    Some(IntInterval {
        var: b1.var,
        k,
        c,
        d,
        m,
    })
}

/// Detect the **different-multiplier** single-variable integer interval `c ≤ k_lo·x`
/// and `k_hi·x ≤ d` (`k_lo, k_hi > 0`, `k_lo ≠ k_hi`) that is LP-feasible yet
/// integer-infeasible: the lower bound forces `x ≥ m_lo+1` and the upper `x ≤ m_hi`
/// with `m_hi ≤ m_lo`, leaving the empty open window `(m_lo, m_lo+1)`. Returns the
/// [`IntIntervalDiff`] on a match, `None` otherwise (declines — never fabricates).
/// (The equal-multiplier case is owned by [`detect_int_interval`].)
fn detect_int_interval_diff_mult(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntIntervalDiff> {
    let [a1, a2] = assertions else {
        return None;
    };
    let b1 = parse_bound_atom(arena, *a1)?;
    let b2 = parse_bound_atom(arena, *a2)?;
    if b1.var != b2.var || b1.lower == b2.lower {
        return None; // need exactly one lower and one upper bound on the same var
    }
    let (lo, hi) = if b1.lower { (b1, b2) } else { (b2, b1) };
    if lo.k <= 0 || hi.k <= 0 || lo.k == hi.k {
        return None; // equal multiplier → detect_int_interval; non-positive → reject
    }
    let (k_lo, c) = (lo.k, lo.bound); // c ≤ k_lo·x
    let (k_hi, d) = (hi.k, hi.bound); // k_hi·x ≤ d
    // Lower forces x > m_lo with m_lo = ⌊(c−1)/k_lo⌋ (k_lo·m_lo < c ≤ k_lo·(m_lo+1)).
    let m_lo = (c.checked_sub(1)?).div_euclid(k_lo);
    if k_lo.checked_mul(m_lo)? >= c {
        return None;
    }
    // Upper forces x < m_hi+1 with m_hi = ⌊d/k_hi⌋ (k_hi·m_hi ≤ d < k_hi·(m_hi+1)).
    let m_hi = d.div_euclid(k_hi);
    if d >= k_hi.checked_mul(m_hi.checked_add(1)?)? {
        return None;
    }
    // Integer-infeasible iff the forced lower `x ≥ m_lo+1` exceeds the upper `x ≤ m_hi`,
    // i.e. m_hi ≤ m_lo (the open window `(m_lo, m_lo+1)` then holds no integer).
    if m_hi > m_lo {
        return None; // some integer lies in [m_lo+1, m_hi] — integer-feasible; decline
    }
    Some(IntIntervalDiff {
        var: lo.var,
        k_lo,
        c,
        k_hi,
        d,
        m_lo,
        m_hi,
    })
}

/// Parse one assertion into a single-variable integer equality `k·x = b` (`k > 0`).
/// Recognizes the generic [`Op::Eq`] over a single-variable linear term on one side and
/// a value on the other (in either orientation), normalizes so the variable coefficient
/// is positive, and returns `(var, k, b)`. Returns `None` on any other shape (multiple
/// variables, a zero coefficient, a non-equality, or an overflow) — never fabricates.
fn parse_int_equality(arena: &TermArena, t: TermId) -> Option<(AtomVar, i128, i128)> {
    let TermNode::App { op, args } = arena.node(t) else {
        return None;
    };
    if *op != Op::Eq {
        return None;
    }
    let [a, b] = &args[..] else {
        return None;
    };
    let (la, ka) = single_var_linear(arena, *a)?;
    let (lb, kb) = single_var_linear(arena, *b)?;
    // Move to `coeff·x + konst = 0`, i.e. `coeff·x = −konst`.
    let (var, coeff) = match (la, lb) {
        (Some((s, c)), None) => (s, c),
        (None, Some((s, c))) => (s, c.checked_neg()?),
        (Some((sx, cx)), Some((sy, cy))) if sx == sy => (sx, cx.checked_sub(cy)?),
        _ => return None, // two distinct variables or a pure-constant equality
    };
    if coeff == 0 {
        return None;
    }
    let konst = ka.checked_sub(kb)?; // `coeff·x + konst = 0`
    // Orient so the multiplier is positive (negate both coeff and the moved constant).
    let (k, rhs) = if coeff < 0 {
        (coeff.checked_neg()?, konst) // (−coeff)·x = konst
    } else {
        (coeff, konst.checked_neg()?) // coeff·x = −konst
    };
    Some((var, k, rhs))
}

/// Detect the single-variable integer **equality-and-unit-bound** refutation shape: an
/// equality `k·x = b` (`k > 0`) and a **unit-multiplier** bound (`c ≤ x` or `x ≤ c`) on
/// the same variable, whose conjunction is **real-infeasible** (the rational point
/// `x = b/k` violates the bound). Returns the [`IntEqBound`] on a match, `None` otherwise.
///
/// Real-infeasibility (`k > 0`, so multiplying the bound by `k` preserves direction):
/// a lower bound `c ≤ x` forces `k·c ≤ b`, so it is refuted iff `b < k·c`; an upper
/// bound `x ≤ c` forces `b ≤ k·c`, refuted iff `k·c < b`. Declines (never fabricates)
/// on any other shape, a non-unit bound multiplier, or a feasible conjunction.
fn detect_int_eq_bound(arena: &TermArena, assertions: &[TermId]) -> Option<IntEqBound> {
    let [a1, a2] = assertions else {
        return None; // exactly one equality + one bound
    };
    // Identify which assertion is the equality and which is the inequality (either order).
    let (eq_term, bound_term) = match (
        parse_int_equality(arena, *a1),
        parse_int_equality(arena, *a2),
    ) {
        (Some(_), None) => (*a1, *a2),
        (None, Some(_)) => (*a2, *a1),
        _ => return None, // zero or two equalities — out of this shape's scope
    };
    let (var, k, b) = parse_int_equality(arena, eq_term)?;
    if k <= 0 {
        return None;
    }
    let bound = parse_bound_atom(arena, bound_term)?;
    if bound.var != var || bound.k != 1 {
        return None; // different variable, or a non-unit-multiplier bound (later slice)
    }
    let c = bound.bound;
    let kc = k.checked_mul(c)?;
    // Real-infeasible test (see the type docs); feasible ⇒ decline.
    let infeasible = if bound.lower { b < kc } else { kc < b };
    if !infeasible {
        return None;
    }
    Some(IntEqBound {
        var,
        k,
        b,
        c,
        lower: bound.lower,
    })
}

impl IntReconstructCtx {
    /// Build the kernel `False` proof for a single-variable integer
    /// equality-and-unit-bound [`IntEqBound`] (`k·x = b` with `c ≤ x` or `x ≤ c`,
    /// real-infeasible).
    ///
    /// Mirrors the equality as `h_eq : Eq Z (k·x) b` and the bound as a hypothesis over
    /// `Z`, scales the bound by the positive `k` (`mul_le_mul_of_nonneg_left`), rewrites
    /// the scaled literal `k·c` through the ring normalizer, and chains through the
    /// equality (recast `k·x → b`) to a literal `b ⋈ k·c` contradiction closed by
    /// `lt_irrefl`.
    fn build_int_eq_bound_false(&mut self, iv: &IntEqBound) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("integer equality-bound reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX.unsigned_abs();
        let kc =
            iv.k.checked_mul(iv.c)
                .ok_or_else(|| decline("k·c overflow"))?;
        if iv.k > DIO_UNIT_MAX
            || iv.b.unsigned_abs() > bound
            || iv.c.unsigned_abs() > bound
            || kc.unsigned_abs() > bound
        {
            return Err(decline("k / b / c / k·c exceed the unit-expansion bound"));
        }
        // The literal `lt` facts need non-negative operands for `lt_lit_lit`.
        if iv.b < 0 || kc < 0 {
            return Err(decline("a literal bound is negative (later slice)"));
        }

        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let k_lit = self.mk_intlit(iv.k);
        let gx = self.mk_mul(k_lit, xe); // k·x
        let b_lit = self.mk_intlit(iv.b);
        let c_lit = self.mk_intlit(iv.c);

        // h_eq : Eq Z (k·x) b (the asserted equality, mirrored verbatim).
        let eq_prop = self.mk_eq(gx, b_lit);
        let h_eq = self.hyp_axiom(eq_prop)?;

        // 0 ≤ k (k > 0), for the positive scaling of the bound.
        let zero = self.mk_zero();
        let lt_zero_k = self.lt_zero_intlit(iv.k)?;
        let le_zero_k = self.le_of_lt_app(zero, k_lit, lt_zero_k);

        if iv.lower {
            self.close_eq_bound_lower(iv, xe, gx, k_lit, b_lit, c_lit, h_eq, le_zero_k)
        } else {
            self.close_eq_bound_upper(iv, xe, gx, k_lit, b_lit, c_lit, h_eq, le_zero_k)
        }
    }

    /// Lower-bound close: from `h_eq : Eq Z (k·x) b`, `c ≤ x`, and `b < k·c`, derive
    /// `False`. Scales `c ≤ x` to `k·c ≤ k·x`, recasts the RHS to `b` through `h_eq`,
    /// rewrites the literal `k·c`, and closes `b < k·c ≤ b ⇒ b < b`.
    #[allow(clippy::too_many_arguments)]
    fn close_eq_bound_lower(
        &mut self,
        iv: &IntEqBound,
        xe: ExprId,
        gx: ExprId,
        k_lit: ExprId,
        b_lit: ExprId,
        c_lit: ExprId,
        h_eq: ExprId,      // Eq Z (k·x) b
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let kc = iv.k * iv.c;
        let kc_lit = self.mk_intlit(kc);
        // h_bound : le c x.
        let bound_prop = self.mk_le(c_lit, xe);
        let h_bound = self.hyp_axiom(bound_prop)?;
        // le (k·c)(k·x) by scaling; recast (mul k c) → literal k·c on the left.
        let le_kc_kx = self.mul_le_mul_left_app(k_lit, c_lit, xe, le_zero_k, h_bound);
        let mul_kc = self.mk_mul(k_lit, c_lit);
        let eq_mul_kc = self.eq_mul_lit_lit(iv.k, iv.c); // Eq Z (mul k c)(intlit k·c)
        let le_kclit_kx = self.le_cast_left(mul_kc, kc_lit, gx, le_kc_kx, eq_mul_kc);
        // recast (k·x) → b on the right via h_eq : le (intlit k·c) b.
        let le_kclit_b = self.le_cast_right(kc_lit, gx, b_lit, le_kclit_kx, h_eq);
        // lt b (k·c) literal (b < k·c by infeasibility) ∘ le (k·c) b ⇒ lt b b.
        let lt_b_kc = self.lt_lit_lit(iv.b, kc)?;
        let lt_b_b = self.lt_of_lt_of_le_app(b_lit, kc_lit, b_lit, lt_b_kc, le_kclit_b);
        let irr = self.lt_irrefl_app(b_lit);
        Ok(self.kernel.app(irr, lt_b_b))
    }

    /// Upper-bound close: from `h_eq : Eq Z (k·x) b`, `x ≤ c`, and `k·c < b`, derive
    /// `False`. Scales `x ≤ c` to `k·x ≤ k·c`, recasts the LHS to `b` through `h_eq`,
    /// rewrites the literal `k·c`, and closes `b ≤ k·c < b ⇒ b < b`.
    #[allow(clippy::too_many_arguments)]
    fn close_eq_bound_upper(
        &mut self,
        iv: &IntEqBound,
        xe: ExprId,
        gx: ExprId,
        k_lit: ExprId,
        b_lit: ExprId,
        c_lit: ExprId,
        h_eq: ExprId,      // Eq Z (k·x) b
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let kc = iv.k * iv.c;
        let kc_lit = self.mk_intlit(kc);
        // h_bound : le x c.
        let bound_prop = self.mk_le(xe, c_lit);
        let h_bound = self.hyp_axiom(bound_prop)?;
        // le (k·x)(k·c) by scaling; recast (mul k c) → literal k·c on the right.
        let le_kx_kc = self.mul_le_mul_left_app(k_lit, xe, c_lit, le_zero_k, h_bound);
        let mul_kc = self.mk_mul(k_lit, c_lit);
        let eq_mul_kc = self.eq_mul_lit_lit(iv.k, iv.c); // Eq Z (mul k c)(intlit k·c)
        let le_kx_kclit = self.le_cast_right(gx, mul_kc, kc_lit, le_kx_kc, eq_mul_kc);
        // recast (k·x) → b on the left via h_eq : le b (intlit k·c).
        let le_b_kclit = self.le_cast_left(gx, b_lit, kc_lit, le_kx_kclit, h_eq);
        // le b (k·c) ∘ lt (k·c) b literal (k·c < b) ⇒ lt b b.
        let lt_kc_b = self.lt_lit_lit(kc, iv.b)?;
        let lt_b_b = self.lt_of_le_of_lt_app(b_lit, kc_lit, b_lit, le_b_kclit, lt_kc_b);
        let irr = self.lt_irrefl_app(b_lit);
        Ok(self.kernel.app(irr, lt_b_b))
    }

    /// Build the kernel `False` proof for a detected [`IntInterval`] `c ≤ k·x ≤ d`.
    ///
    /// Mirrors the asserted atoms as hypothesis axioms `h_lo : le c (k·x)` and
    /// `h_hi : le (k·x) d`, derives the strict literal facts `lt (k·m) (k·x)` and
    /// `lt (k·x) (k·(m+1))`, cancels the positive `k` (via `le_total` + the forward
    /// scaling axiom, exactly as the Diophantine discreteness closers) to obtain
    /// `lt m x` and `lt x (m+1)`, shifts by `−m` to `lt 0 (x−m)` / `lt (x−m) 1`, and
    /// closes with `no_int_between (x−m)`. For `m = 0` the shift is the identity and
    /// the close is `no_int_between x` directly.
    fn build_int_interval_false(&mut self, iv: &IntInterval) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("integer-interval reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX.unsigned_abs();
        if iv.k > DIO_UNIT_MAX
            || iv.c.unsigned_abs() > bound
            || iv.d.unsigned_abs() > bound
            || iv.m.unsigned_abs() > bound
        {
            return Err(decline("k / c / d / m exceed the unit-expansion bound"));
        }
        // Dense index 0 for the single variable; `x` as a kernel constant.
        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let k_lit = self.mk_intlit(iv.k);
        let gx = self.mk_mul(k_lit, xe); // k·x
        let c_lit = self.mk_intlit(iv.c);
        let d_lit = self.mk_intlit(iv.d);

        // --- mirror the asserted atoms as hypotheses over Z -------------------
        // h_lo : le c (k·x) ; h_hi : le (k·x) d.
        let lo_prop = self.mk_le(c_lit, gx);
        let h_lo = self.hyp_axiom(lo_prop)?;
        let hi_prop = self.mk_le(gx, d_lit);
        let h_hi = self.hyp_axiom(hi_prop)?;

        // --- 0 ≤ k (k > 0) ----------------------------------------------------
        let zero = self.mk_zero();
        let lt_zero_k = self.lt_zero_intlit(iv.k)?; // lt zero k
        let le_zero_k = self.le_of_lt_app(zero, k_lit, lt_zero_k); // le zero k

        // --- strict literal facts about k·x ----------------------------------
        let km = iv.k * iv.m;
        let km1 = iv.k * (iv.m + 1);
        // Require non-negative bounds for the `lt_intlit_intlit` literal facts (true
        // whenever m ≥ 0, i.e. c ≥ 1); decline otherwise.
        if km < 0 || iv.d < 0 || km1 < 0 {
            return Err(decline(
                "reduction offset yields a negative bound (later slice)",
            ));
        }
        // --- cancel the positive k : lt m x and lt x (m+1) -------------------
        let lt_m_x = self.derive_lt_m_x(iv.k, iv.c, iv.m, c_lit, gx, xe, k_lit, h_lo, le_zero_k)?;
        let lt_x_m1 =
            self.derive_lt_x_m1(iv.k, iv.d, iv.m, d_lit, gx, xe, k_lit, h_hi, le_zero_k)?;

        // --- shift by −m, then close with no_int_between ----------------------
        self.close_no_int_between(xe, zero, iv.m, lt_m_x, lt_x_m1)
    }

    /// From `h_lo : le c (k·x)` and `le_zero_k : le 0 k` (with `k·m < c`, `0 ≤ k·m`),
    /// derive `lt (intlit m) x` by chaining `lt (k·m) c ∘ le c (k·x)`, recasting the
    /// literal `k·m` to `mul k m`, and cancelling the positive `k`. The lower half of
    /// the interval reduction, parametric in the multiplier `k` so the
    /// different-multiplier path can reuse it with its own lower multiplier.
    #[allow(clippy::too_many_arguments)]
    fn derive_lt_m_x(
        &mut self,
        k: i128,
        c: i128,
        m: i128,
        c_lit: ExprId,
        gx: ExprId, // mul k x
        xe: ExprId,
        k_lit: ExprId,
        h_lo: ExprId,      // le c (k·x)
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let km = k * m;
        let km_lit = self.mk_intlit(km);
        let m_lit = self.mk_intlit(m);
        // lt (k·m) c (literal) ∘ le c (k·x) : lt (intlit (k·m)) (k·x); recast left.
        let lt_km_c = self.lt_lit_lit(km, c)?;
        let lt_kmlit_gx = self.lt_of_lt_of_le_app(km_lit, c_lit, gx, lt_km_c, h_lo);
        let mul_km = self.mk_mul(k_lit, m_lit); // mul k m
        let eq_mul_km = self.eq_mul_lit_lit(k, m); // Eq Z (mul k m)(intlit (k·m))
        let eq_kmlit_mul = self.eq_symm(mul_km, km_lit, eq_mul_km);
        let lt_km_gx = self.lt_cast_left(km_lit, mul_km, gx, lt_kmlit_gx, eq_kmlit_mul);
        Ok(self.cancel_pos_mul_lt_lower(k_lit, m_lit, xe, le_zero_k, lt_km_gx))
    }

    /// From `h_hi : le (k·x) d` and `le_zero_k : le 0 k` (with `d < k·(m+1)`,
    /// `0 ≤ k·(m+1)`), derive `lt x (intlit (m+1))` symmetrically to
    /// [`Self::derive_lt_m_x`]: the upper half of the interval reduction.
    #[allow(clippy::too_many_arguments)]
    fn derive_lt_x_m1(
        &mut self,
        k: i128,
        d: i128,
        m: i128,
        d_lit: ExprId,
        gx: ExprId, // mul k x
        xe: ExprId,
        k_lit: ExprId,
        h_hi: ExprId,      // le (k·x) d
        le_zero_k: ExprId, // le 0 k
    ) -> Result<ExprId, ReconstructError> {
        let km1 = k * (m + 1);
        let km1_lit = self.mk_intlit(km1);
        let m1_lit = self.mk_intlit(m + 1);
        // le (k·x) d ∘ lt d (intlit (k·(m+1))) : lt (k·x)(intlit …); recast right.
        let lt_d_km1 = self.lt_lit_lit(d, km1)?;
        let lt_gx_km1lit = self.lt_of_le_of_lt_app(gx, d_lit, km1_lit, h_hi, lt_d_km1);
        let mul_km1 = self.mk_mul(k_lit, m1_lit); // mul k (m+1)
        let eq_mul_km1 = self.eq_mul_lit_lit(k, m + 1);
        let eq_km1lit_mul = self.eq_symm(mul_km1, km1_lit, eq_mul_km1);
        let lt_gx_km1 = self.lt_cast_right(gx, km1_lit, mul_km1, lt_gx_km1lit, eq_km1lit_mul);
        Ok(self.cancel_pos_mul_lt_upper(k_lit, xe, m1_lit, le_zero_k, lt_gx_km1))
    }

    /// Close a single-variable discreteness contradiction: from `lt_m_x : lt m x`
    /// and `lt_x_m1 : lt x (m+1)` (both literals `m`, `m+1` ≥ 0), derive `False` by
    /// `no_int_between`. For `m = 0` the bounds are already `lt 0 x`/`lt x 1`; for
    /// `m ≠ 0` it shifts both by `−m` to the unit window `0 < x−m < 1`. Shared by the
    /// common-multiplier and different-multiplier interval reconstructors.
    fn close_no_int_between(
        &mut self,
        xe: ExprId,
        zero: ExprId,
        m: i128,
        lt_m_x: ExprId,  // lt (intlit m) x
        lt_x_m1: ExprId, // lt x (intlit (m+1))
    ) -> Result<ExprId, ReconstructError> {
        if m == 0 {
            // lt_m_x : lt zero x and lt_x_m1 : lt x one already (mk_intlit 0/1 fold to
            // zero/one) — close with `no_int_between x (And.intro (lt 0 x)(lt x 1))`.
            let one = self.mk_one();
            let p_prop = self.mk_lt(zero, xe);
            let q_prop = self.mk_lt(xe, one);
            let and_proof = self.and_intro(p_prop, q_prop, lt_m_x, lt_x_m1);
            return Ok(self.no_int_between_app(xe, and_proof));
        }
        // General m ≠ 0: w = x + (−m) = x − m. Prove lt 0 w from lt m x, and lt w 1
        // from lt x (m+1), by adding (−m) to both sides (additive shift), then close.
        let m_lit = self.mk_intlit(m);
        let m1_lit = self.mk_intlit(m + 1);
        let neg_m_lit = self.mk_intlit(-m);
        let w = self.mk_add(xe, neg_m_lit); // x + (−m)

        // lt 0 w :  from lt m x add (−m): lt (m + (−m)) (x + (−m)); normalize lhs → 0.
        let lt_zero_w = self.shift_lt_lower(m_lit, xe, neg_m_lit, m, lt_m_x)?;
        // lt w 1 :  from lt x (m+1) add (−m): lt (x + (−m)) ((m+1) + (−m)); rhs → 1.
        let lt_w_one = self.shift_lt_upper(xe, m1_lit, neg_m_lit, m, lt_x_m1)?;

        let one = self.mk_one();
        let p_prop = self.mk_lt(zero, w);
        let q_prop = self.mk_lt(w, one);
        let and_proof = self.and_intro(p_prop, q_prop, lt_zero_w, lt_w_one);
        Ok(self.no_int_between_app(w, and_proof))
    }

    /// Build the kernel `False` proof for a [`IntIntervalDiff`] `c ≤ k_lo·x`,
    /// `k_hi·x ≤ d` (distinct positive multipliers).
    ///
    /// Mirrors the asserted atoms verbatim as hypotheses `h_lo : le c (k_lo·x)` and
    /// `h_hi : le (k_hi·x) d`, derives `lt m_lo x` from the lower (cancelling `k_lo`)
    /// and `lt x (m_hi+1)` from the upper (cancelling `k_hi`) — each via the SAME
    /// half-reduction the equal-multiplier path uses, but with its own multiplier.
    /// When `m_hi < m_lo` it weakens the upper to `lt x (m_lo+1)` by transitivity
    /// through the literal fact `lt (m_hi+1) (m_lo+1)`, so both bounds share the
    /// offset `m_lo`, then closes with [`Self::close_no_int_between`].
    fn build_int_interval_diff_mult_false(
        &mut self,
        iv: &IntIntervalDiff,
    ) -> Result<ExprId, ReconstructError> {
        let decline = |d: &str| ReconstructError::UnsupportedTerm {
            term: format!("different-multiplier interval reconstruction declined: {d}"),
        };
        let bound = DIO_UNIT_MAX;
        if iv.k_lo > bound
            || iv.k_hi > bound
            || iv.c.unsigned_abs() > bound.unsigned_abs()
            || iv.d.unsigned_abs() > bound.unsigned_abs()
            || iv.m_lo.unsigned_abs() > bound.unsigned_abs()
            || iv.m_hi.unsigned_abs() > bound.unsigned_abs()
        {
            return Err(decline(
                "k_lo / k_hi / c / d / m exceed the unit-expansion bound",
            ));
        }
        // Require non-negative bounds for the literal `lt` facts (true when c ≥ 1, d ≥ 0).
        if iv.k_lo * iv.m_lo < 0 || iv.d < 0 || iv.k_hi * (iv.m_hi + 1) < 0 {
            return Err(decline("a reduction bound is negative (later slice)"));
        }

        let x_name = self.var_const_for(iv.var);
        let xe = self.kernel.const_(x_name, vec![]);
        let zero = self.mk_zero();

        // --- lower half: h_lo : le c (k_lo·x) ⟹ lt m_lo x -------------------
        let klo_lit = self.mk_intlit(iv.k_lo);
        let glo = self.mk_mul(klo_lit, xe); // k_lo·x
        let c_lit = self.mk_intlit(iv.c);
        let lo_prop = self.mk_le(c_lit, glo);
        let h_lo = self.hyp_axiom(lo_prop)?;
        let lt_zero_klo = self.lt_zero_intlit(iv.k_lo)?;
        let le_zero_klo = self.le_of_lt_app(zero, klo_lit, lt_zero_klo);
        let lt_m_x = self.derive_lt_m_x(
            iv.k_lo,
            iv.c,
            iv.m_lo,
            c_lit,
            glo,
            xe,
            klo_lit,
            h_lo,
            le_zero_klo,
        )?;

        // --- upper half: h_hi : le (k_hi·x) d ⟹ lt x (m_hi+1) ---------------
        let khi_lit = self.mk_intlit(iv.k_hi);
        let ghi = self.mk_mul(khi_lit, xe); // k_hi·x
        let d_lit = self.mk_intlit(iv.d);
        let hi_prop = self.mk_le(ghi, d_lit);
        let h_hi = self.hyp_axiom(hi_prop)?;
        let lt_zero_khi = self.lt_zero_intlit(iv.k_hi)?;
        let le_zero_khi = self.le_of_lt_app(zero, khi_lit, lt_zero_khi);
        let lt_x_mhi1 = self.derive_lt_x_m1(
            iv.k_hi,
            iv.d,
            iv.m_hi,
            d_lit,
            ghi,
            xe,
            khi_lit,
            h_hi,
            le_zero_khi,
        )?;

        // --- align the offsets at m_lo, then close --------------------------
        // m_hi ≤ m_lo (detector invariant). If equal, the upper is already
        // `lt x (m_lo+1)`. Otherwise weaken via `lt (m_hi+1)(m_lo+1)` (literals).
        let lt_x_mlo1 = if iv.m_hi == iv.m_lo {
            lt_x_mhi1
        } else {
            let mhi1_lit = self.mk_intlit(iv.m_hi + 1);
            let mlo1_lit = self.mk_intlit(iv.m_lo + 1);
            // 0 ≤ m_hi+1 < m_lo+1, so the literal `lt` and its `le` weakening hold.
            let lt_mhi1_mlo1 = self.lt_lit_lit(iv.m_hi + 1, iv.m_lo + 1)?;
            let le_mhi1_mlo1 = self.le_of_lt_app(mhi1_lit, mlo1_lit, lt_mhi1_mlo1);
            self.lt_of_lt_of_le_app(xe, mhi1_lit, mlo1_lit, lt_x_mhi1, le_mhi1_mlo1)
        };
        self.close_no_int_between(xe, zero, iv.m_lo, lt_m_x, lt_x_mlo1)
    }

    /// Get (declaring lazily) the opaque `Z`-typed constant for the single interval
    /// variable, using a fixed dense index `0`. The variable identity ([`AtomVar`] —
    /// a symbol or an opaque application) is irrelevant to the proof: the
    /// single-variable shape always maps to the one opaque `Z` constant, which is
    /// exactly why an opaque application reconstructs identically to a symbol.
    fn var_const_for(&mut self, _var: AtomVar) -> NameId {
        self.var_const(0)
    }

    /// `Eq Z (mul (intlit a)(intlit b)) (intlit (a·b))` via the ring normalizer (the
    /// kernel term `mul (mk_intlit a)(mk_intlit b)` hash-conses with the normalizer's
    /// `kexpr`). Handles `a = 0` or `b = 0` (product `zero`) through the normalizer's
    /// `Zero`/`mul_zero` path; both nonzero go through the literal-product distribution.
    fn eq_mul_lit_lit(&mut self, a: i128, b: i128) -> ExprId {
        let za = intlit_zexpr(a);
        let zb = intlit_zexpr(b);
        let prod = ZExpr::Mul(Box::new(za), Box::new(zb));
        let (gens, kexpr, proof) = self
            .normalize(&prod)
            .expect("literal·literal normalizer never declines (degree ≤ 1)");
        let prod_val = a.checked_mul(b).expect("k·m within i128");
        debug_assert_eq!(gens, lin_to_canon_gens(&[], prod_val));
        let canon = self.gens_to_expr(&gens);
        let lit = self.mk_intlit(prod_val);
        let bridge = self.intlit_eq_canon(prod_val); // Eq Z lit canon
        let bridge_sym = self.eq_symm(lit, canon, bridge); // canon = lit
        // proof : Eq Z kexpr canon ; kexpr == mul (mk_intlit a)(mk_intlit b).
        self.eq_trans(kexpr, canon, lit, proof, bridge_sym)
    }

    /// `lt (intlit a)(intlit b)` for arbitrary `a < b`, dispatching the `a = 0`
    /// case to [`Self::lt_zero_intlit`].
    fn lt_lit_lit(&mut self, a: i128, b: i128) -> Result<ExprId, ReconstructError> {
        debug_assert!(b > a);
        if a == 0 {
            self.lt_zero_intlit(b)
        } else {
            self.lt_intlit_intlit(a, b)
        }
    }

    /// From `h_lt : lt (k·m) (k·x)` and `h_k : le 0 k` derive `lt m x` — cancel the
    /// positive multiplier `k`. Pure forward scaling + total order + irreflexivity (no
    /// strict-cancel axiom), mirroring `prove_m_prime_lt_one`.
    fn cancel_pos_mul_lt_lower(
        &mut self,
        k_lit: ExprId,
        m_lit: ExprId,
        xe: ExprId,
        h_k: ExprId,
        h_lt: ExprId, // lt (mul k m) (mul k x)
    ) -> ExprId {
        // le_total m x : Or (le m x)(le x m).
        let a_prop = self.mk_le(m_lit, xe);
        let b_prop = self.mk_le(xe, m_lit);
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, m_lit);
            self.kernel.app(e, xe)
        };
        let target = self.mk_le(m_lit, xe);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_x_m = self.kernel.fvar(fid); // le x m
            // mul_le_mul_of_nonneg_left k x m h_k h_le_x_m : le (k·x)(k·m).
            let le_kx_km = self.mul_le_mul_left_app(k_lit, xe, m_lit, h_k, h_le_x_m);
            // lt (k·m)(k·x) ∘ le (k·x)(k·m) : lt (k·m)(k·m).
            let km = self.mk_mul(k_lit, m_lit);
            let kx = self.mk_mul(k_lit, xe);
            let lt_km_km = self.lt_of_lt_of_le_app(km, kx, km, h_lt, le_kx_km);
            let irr = self.lt_irrefl_app(km);
            let false_proof = self.kernel.app(irr, lt_km_km);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_m_x = self.or_rec_le(a_prop, b_prop, target, minor_inl, minor_inr, or_proof);
        // m ≠ x : else k·m = k·x contradicts lt (k·m)(k·x).
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z m x
            let cong = self.congr_mul_right(k_lit, m_lit, xe, h_eq); // mul k m = mul k x
            let km = self.mk_mul(k_lit, m_lit);
            let kx = self.mk_mul(k_lit, xe);
            // cast lt (k·m)(k·x) on the LEFT km → kx ⇒ lt (k·x)(k·x).
            let lt_kx_kx = self.lt_cast_left(km, kx, kx, h_lt, cong);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_m_x = self.mk_eq(m_lit, xe);
            self.kernel.lam(anon, eq_m_x, body, BinderInfo::Default)
        };
        self.lt_of_le_of_ne_app(m_lit, xe, le_m_x, not_eq)
    }

    /// From `h_lt : lt (k·x) (k·(m+1))` and `h_k : le 0 k` derive `lt x (m+1)` — cancel
    /// the positive multiplier on the upper bound. Symmetric to
    /// [`Self::cancel_pos_mul_lt_lower`].
    fn cancel_pos_mul_lt_upper(
        &mut self,
        k_lit: ExprId,
        xe: ExprId,
        m1_lit: ExprId,
        h_k: ExprId,
        h_lt: ExprId, // lt (mul k x) (mul k (m+1))
    ) -> ExprId {
        let a_prop = self.mk_le(xe, m1_lit); // le x (m+1)
        let b_prop = self.mk_le(m1_lit, xe); // le (m+1) x
        let or_proof = {
            let ax = self.kernel.const_(self.int.le_total, vec![]);
            let e = self.kernel.app(ax, xe);
            self.kernel.app(e, m1_lit)
        };
        let target = self.mk_le(xe, m1_lit);
        let minor_inl = {
            let fid = self.fresh_fvar();
            let h = self.kernel.fvar(fid);
            let body = self.kernel.abstract_fvars(h, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, a_prop, body, BinderInfo::Default)
        };
        let minor_inr = {
            let fid = self.fresh_fvar();
            let h_le_m1_x = self.kernel.fvar(fid); // le (m+1) x
            // mul_le_mul_of_nonneg_left k (m+1) x h_k h_le_m1_x : le (k·(m+1))(k·x).
            let le_km1_kx = self.mul_le_mul_left_app(k_lit, m1_lit, xe, h_k, h_le_m1_x);
            let kx = self.mk_mul(k_lit, xe);
            let km1 = self.mk_mul(k_lit, m1_lit);
            // lt (k·x)(k·(m+1)) ∘ le (k·(m+1))(k·x) : lt (k·x)(k·x).
            let lt_kx_kx = self.lt_of_lt_of_le_app(kx, km1, kx, h_lt, le_km1_kx);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let exf = self.ex_falso(target, false_proof);
            let body = self.kernel.abstract_fvars(exf, &[fid]);
            let anon = self.kernel.anon();
            self.kernel.lam(anon, b_prop, body, BinderInfo::Default)
        };
        let le_x_m1 = self.or_rec_le(a_prop, b_prop, target, minor_inl, minor_inr, or_proof);
        // x ≠ (m+1) : else k·x = k·(m+1) contradicts lt (k·x)(k·(m+1)).
        let not_eq = {
            let fid = self.fresh_fvar();
            let h_eq = self.kernel.fvar(fid); // Eq Z x (m+1)
            let cong = self.congr_mul_right(k_lit, xe, m1_lit, h_eq); // mul k x = mul k (m+1)
            let kx = self.mk_mul(k_lit, xe);
            let km1 = self.mk_mul(k_lit, m1_lit);
            // cast lt (k·x)(k·(m+1)) on the RIGHT km1 → kx ⇒ lt (k·x)(k·x).
            let cong_sym = self.eq_symm(kx, km1, cong); // mul k (m+1) = mul k x
            let lt_kx_kx = self.lt_cast_right(kx, km1, kx, h_lt, cong_sym);
            let irr = self.lt_irrefl_app(kx);
            let false_proof = self.kernel.app(irr, lt_kx_kx);
            let body = self.kernel.abstract_fvars(false_proof, &[fid]);
            let anon = self.kernel.anon();
            let eq_x_m1 = self.mk_eq(xe, m1_lit);
            self.kernel.lam(anon, eq_x_m1, body, BinderInfo::Default)
        };
        self.lt_of_le_of_ne_app(xe, m1_lit, le_x_m1, not_eq)
    }

    /// `Or.rec.{0}` over `le`-valued props: from `minor_inl : a → target`,
    /// `minor_inr : b → target`, and `or_proof : Or a b`, build `target`.
    fn or_rec_le(
        &mut self,
        a_prop: ExprId,
        b_prop: ExprId,
        target: ExprId,
        minor_inl: ExprId,
        minor_inr: ExprId,
        or_proof: ExprId,
    ) -> ExprId {
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
    }

    /// From `h : lt (intlit m) x` derive `lt zero (add x (neg (intlit m)))` by adding
    /// `neg (intlit m)` to both sides and normalizing the lhs `m + (−m) → 0`.
    fn shift_lt_lower(
        &mut self,
        m_lit: ExprId,
        xe: ExprId,
        neg_m_lit: ExprId,
        m: i128,
        h: ExprId, // lt m x
    ) -> Result<ExprId, ReconstructError> {
        // h_le : le (neg m)(neg m)  (le_refl).
        let h_le = self.le_refl_app(neg_m_lit);
        // add_lt_add_of_le_of_lt (neg m)(neg m) m x h_le h : lt (add (neg m) m)(add (neg m) x).
        let combined = self.add_lt_add_of_le_of_lt_app(neg_m_lit, neg_m_lit, m_lit, xe, h_le, h);
        // lhs (add (neg m) m) → zero ; rhs (add (neg m) x) → (add x (neg m)) (= w).
        let lhs = self.mk_add(neg_m_lit, m_lit); // (−m) + m
        let rhs = self.mk_add(neg_m_lit, xe); // (−m) + x
        let zero = self.mk_zero();
        // Eq Z ((−m) + m) zero via the ring normalizer (neg_m_lit is the *literal*
        // `intlit (−m)`, not `neg (intlit m)`, so we normalize the literal sum).
        let lhs_eq_zero = self.intlit_pair_sum_eq_zero(neg_m_lit, m_lit, -m, m)?;
        let lt_zero_rhs = self.lt_cast_left(lhs, zero, rhs, combined, lhs_eq_zero); // lt zero ((−m)+x)
        // rhs ((−m)+x) → w = (x + (−m)) by commutativity.
        let w = self.mk_add(xe, neg_m_lit);
        let comm2 = self.add_comm_eq(neg_m_lit, xe); // (−m)+x = x+(−m)
        Ok(self.lt_cast_right(zero, rhs, w, lt_zero_rhs, comm2))
    }

    /// From `h : lt x (intlit (m+1))` derive `lt (add x (neg (intlit m))) one` by adding
    /// `neg (intlit m)` to both sides and normalizing the rhs `(m+1) + (−m) → 1`.
    fn shift_lt_upper(
        &mut self,
        xe: ExprId,
        m1_lit: ExprId,
        neg_m_lit: ExprId,
        m: i128,
        h: ExprId, // lt x (m+1)
    ) -> Result<ExprId, ReconstructError> {
        let h_le = self.le_refl_app(neg_m_lit);
        // add_lt_add_of_le_of_lt (neg m)(neg m) x (m+1) h_le h :
        //   lt (add (neg m) x)(add (neg m)(m+1)).
        let combined = self.add_lt_add_of_le_of_lt_app(neg_m_lit, neg_m_lit, xe, m1_lit, h_le, h);
        let lhs = self.mk_add(neg_m_lit, xe); // (−m)+x
        let rhs = self.mk_add(neg_m_lit, m1_lit); // (−m)+(m+1)
        let one = self.mk_one();
        // rhs ((−m)+(m+1)) → one (sum is 1).
        let rhs_eq_one = self.intlit_pair_sum_eq_one(neg_m_lit, m1_lit, -m, m + 1)?;
        let lt_lhs_one = self.lt_cast_right(lhs, rhs, one, combined, rhs_eq_one); // lt ((−m)+x) one
        // lhs ((−m)+x) → w = (x+(−m)) by commutativity.
        let w = self.mk_add(xe, neg_m_lit);
        let comm = self.add_comm_eq(neg_m_lit, xe); // (−m)+x = x+(−m)
        Ok(self.lt_cast_left(lhs, w, one, lt_lhs_one, comm))
    }

    /// `Eq Z (add (intlit a)(intlit b)) zero` when `a + b = 0` (both nonzero), via the
    /// ring normalizer (canonical form is the empty gen list = `zero`).
    fn intlit_pair_sum_eq_zero(
        &mut self,
        _a_lit: ExprId,
        _b_lit: ExprId,
        a: i128,
        b: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, 0);
        self.intlit_pair_sum_eq(a, b, 0)
    }

    /// `Eq Z (add (intlit a)(intlit b)) one` when `a + b = 1` (both nonzero), via the
    /// ring normalizer.
    fn intlit_pair_sum_eq_one(
        &mut self,
        _a_lit: ExprId,
        _b_lit: ExprId,
        a: i128,
        b: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, 1);
        self.intlit_pair_sum_eq(a, b, 1)
    }

    /// `Eq Z (add (intlit a)(intlit b)) (intlit s)` when `a + b = s` (`a`, `b` nonzero),
    /// via the ring normalizer (a generalization of [`Self::intlit_add_eq`] permitting
    /// `s = 0` or any `s`). Builds the faithful sum, normalizes, checks the canonical
    /// form matches `s`, and bridges to the `mk_intlit s` term.
    fn intlit_pair_sum_eq(
        &mut self,
        a: i128,
        b: i128,
        s: i128,
    ) -> Result<ExprId, ReconstructError> {
        debug_assert_eq!(a + b, s);
        let (Some(za), Some(zb)) = (lin_to_zexpr(&[], a), lin_to_zexpr(&[], b)) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_pair_sum requires both operands nonzero".to_owned(),
            });
        };
        let sum_zexpr = ZExpr::Add(Box::new(za), Box::new(zb));
        let (gens, kexpr, proof) =
            self.normalize(&sum_zexpr)
                .ok_or_else(|| ReconstructError::UnsupportedTerm {
                    term: "intlit_pair_sum normalizer declined".to_owned(),
                })?;
        let expected = lin_to_canon_gens(&[], s);
        if gens != expected {
            return Err(ReconstructError::UnsupportedTerm {
                term: "intlit_pair_sum did not canonicalize to the expected sum".to_owned(),
            });
        }
        let canon = self.gens_to_expr(&gens);
        let s_lit = self.mk_intlit(s);
        let bridge = self.intlit_eq_canon(s); // Eq Z (intlit s) canon
        let bridge_sym = self.eq_symm(s_lit, canon, bridge); // canon = intlit s
        Ok(self.eq_trans(kexpr, canon, s_lit, proof, bridge_sym))
    }
}

/// **Reconstruct an integer-inequality (interval) infeasibility to a kernel-checked
/// Lean `False`** (ADR-0042, the integer-cut payoff). Detects the single-variable
/// shape `c ≤ k·x ≤ d` (k > 0) with no multiple of `k` in `[c, d]`, reconstructs the
/// discreteness argument over [`IntPrelude`], and returns the assembled `False` proof
/// term (already `infer` + `def_eq False`-gated through the kernel).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when the assertions do not match the detected
/// shape (multiple variables, non-unit multipliers, an integer-feasible interval, or a
/// coefficient/bound overflow) — never fabricated; [`ReconstructError::KernelRejected`]
/// when the assembled term does not kernel-check to `False`.
pub fn reconstruct_int_inequality_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let (_, proof) = build_and_gate_int_interval(arena, assertions)?;
    Ok(proof)
}

/// The theorem name used for the exported integer-interval refutation Lean module.
const INT_INEQ_LEAN_THEOREM: &str = "axeyum_refutation";

/// **Like [`reconstruct_int_inequality_proof`], but also renders a self-contained Lean
/// module** re-proving the refutation. A successful return means the proof was emitted,
/// kernel-checked to `False`, and rendered to externally-checkable Lean source.
///
/// # Errors
///
/// Same as [`reconstruct_int_inequality_proof`].
pub fn reconstruct_int_inequality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let (mut ctx, proof) = build_and_gate_int_interval(arena, assertions)?;
    let false_ = {
        let f = ctx.int().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    Ok(ctx
        .kernel()
        .render_lean_module(INT_INEQ_LEAN_THEOREM, false_, proof))
}

/// Shared core: detect the interval shape, build the `False` proof over a fresh
/// [`IntReconstructCtx`], and gate it through the kernel (`infer` + `def_eq False`).
fn build_and_gate_int_interval(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<(IntReconstructCtx, ExprId), ReconstructError> {
    // Build the (ungated) `False` proof: the equal-multiplier interval first, then
    // the different-multiplier interval. Either way the kernel gate below is the sole
    // soundness authority — a builder bug surfaces as `KernelRejected`, never accept.
    let mut ctx = IntReconstructCtx::new();
    let proof = if let Some(iv) = detect_int_interval(arena, assertions) {
        ctx.build_int_interval_false(&iv)?
    } else if let Some(iv) = detect_int_interval_diff_mult(arena, assertions) {
        ctx.build_int_interval_diff_mult_false(&iv)?
    } else if let Some(iv) = detect_int_eq_bound(arena, assertions) {
        ctx.build_int_eq_bound_false(&iv)?
    } else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no single-variable integer-interval (c ≤ k·x ≤ d) refutation".to_owned(),
        });
    };
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "int_inequality".to_owned(),
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
            rule: "int_inequality".to_owned(),
            detail: "integer-interval refutation did not infer to False".to_owned(),
        })
    }
}

/// Detect the single-variable integer-interval refutation shape (used by the fragment
/// classifier to route to the integer-inequality reconstructor). Returns `true` iff the
/// equal-multiplier, the different-multiplier, or the equality-and-unit-bound
/// (`k·x = b` ∧ `c ≤ x`/`x ≤ c`, real-infeasible) integer matcher matches.
#[must_use]
pub fn is_int_inequality_refutation(arena: &TermArena, assertions: &[TermId]) -> bool {
    detect_int_interval(arena, assertions).is_some()
        || detect_int_interval_diff_mult(arena, assertions).is_some()
        || detect_int_eq_bound(arena, assertions).is_some()
}
