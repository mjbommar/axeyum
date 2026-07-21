//! Kernel-checked linear-real and sum-of-squares proof reconstruction.

use super::{
    BTreeMap, BTreeSet, BinderInfo, Declaration, ExprId, IrOp, IrSort, IrTermNode, Kernel, NameId,
    Rational, ReconstructError, TermArena, TermId, is_am_gm_two_var,
    is_single_square_lt_zero,
};
// ===========================================================================
// LRA `la_generic` (Farkas) reconstruction (P3.7 arithmetic fragment, slice 1).
//
// A small real `QF_LRA` `unsat` instance's Farkas certificate is reconstructed
// into a Lean term of type `False` that the trusted kernel type-checks, over the
// axiomatized linear ordered field of `build_arith_prelude` (carrier `R`, ops
// `add`/`mul`/`neg`/`zero`/`one`, relations `le`/`lt`, the order/ring axioms).
//
// ## The model
//
// - Each real variable `xⱼ` ⇒ an opaque `R`-typed `Axiom` (declared lazily,
//   deterministically, by dense variable index).
// - A linear term `Σ aⱼ xⱼ + c` ⇒ an `R` expression built from `add`/`neg`/
//   `one`/`zero`. **Coefficient restriction (slice 1):** only small integer
//   coefficients in `{-1, 0, +1}` and a constant in `{0, 1}` are modelled (no
//   general rationals); a `±1` coefficient is `xⱼ` / `neg xⱼ`, and the constant
//   `1` is the prelude's `one`. Anything outside this is rejected, not guessed.
// - A constraint atom `t ⋈ c` (`≤`/`<`) ⇒ `le`/`lt` over the `R` expressions; an
//   input assumption is a hypothesis axiom of that exact `Prop`.
//
// ## What is reconstructed (slice 1): the transitivity-reducible refutation
//
// The bar is the baby-Farkas / order-chaining shape: a two-constraint instance
// `e ≤ 0 ∧ 1 ≤ e` (`e` a shared `R` expression). The refutation is **pure order
// chaining**, with NO ring sum:
//
//   step1 := le_trans one e zero h_lo h_hi : le one zero
//   step2 := lt_of_le_of_lt one zero one step1 zero_lt_one : lt one one
//   refute := lt_irrefl one step2 : False
//
// where `h_hi : le e zero` and `h_lo : le one e` are the input-constraint
// hypotheses. The general multi-variable / arbitrary-rational Farkas normalizer
// (scaling by `λ` and a ring cancellation `Σ λᵢ tᵢ = const`) is a LATER slice;
// out-of-scope cert shapes are rejected with a clear [`ReconstructError`].
//
// ## Soundness
//
// The kernel `infer`s the final term and requires it `def_eq` `False`. A wrong
// combination ⇒ the kernel rejects ⇒ [`ReconstructError::KernelRejected`], never
// a wrong `False`. The arith-prelude axioms are the (kernel-type-checked) trusted
// base; the only added axioms are the input-constraint hypotheses.
// ===========================================================================

use axeyum_lean_kernel::{ArithPrelude, build_arith_prelude};

// The LRA reconstruction items below are the public API surface a `lib.rs`
// re-export will expose (mirroring the EUF `reconstruct_qf_uf_proof` re-export);
// until that re-export lands they are reachable only from this module's tests, so
// the crate-level dead-code lint flags them. The `allow(dead_code)` markers are
// scoped to these items (not the module) and become inert once re-exported.

/// A linear real expression `Σ aⱼ xⱼ + c` over dense variable indices, the
/// reconstruction-side mirror of the LRA collector's linear form. Coefficients and
/// the constant are exact [`Rational`]s; slice 1 only *reconstructs* the small
/// `{-1,0,+1}` coefficient / `{0,1}` constant subset into `R` (see [`LinR`]).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[allow(dead_code)]
pub(super) struct LinR {
    /// `(variable index, coefficient)` pairs, ascending, all coefficients nonzero.
    pub(super) coeffs: Vec<(usize, Rational)>,
    /// The constant term.
    pub(super) constant: Rational,
}

#[allow(dead_code)]
impl LinR {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: Vec::new(),
            constant: value,
        }
    }

    fn var(index: usize) -> Self {
        Self {
            coeffs: vec![(index, Rational::integer(1))],
            constant: Rational::zero(),
        }
    }

    /// Negate, declining (`None`) on any `i128` overflow during normalization.
    fn neg(&self) -> Option<Self> {
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for &(i, c) in &self.coeffs {
            coeffs.push((i, c.checked_neg()?));
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_neg()?,
        })
    }

    /// Add, declining (`None`) on any `i128` overflow.
    fn add(&self, other: &Self) -> Option<Self> {
        let mut map: BTreeMap<usize, Rational> = BTreeMap::new();
        for &(i, c) in self.coeffs.iter().chain(&other.coeffs) {
            let e = map.entry(i).or_insert_with(Rational::zero);
            *e = e.checked_add(c)?;
        }
        let coeffs = map.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    /// Whether this is the linear expression of a single bare variable `xⱼ`
    /// (coefficient `+1`, no constant), returning its index.
    fn as_bare_var(&self) -> Option<usize> {
        match self.coeffs.as_slice() {
            [(i, c)] if *c == Rational::integer(1) && self.constant.is_zero() => Some(*i),
            _ => None,
        }
    }

    /// Whether this is the constant `value` (no variables).
    fn is_constant_eq(&self, value: Rational) -> bool {
        self.coeffs.is_empty() && self.constant == value
    }
}

/// The reconstruction context for LRA Farkas proofs: a [`Kernel`] seeded with the
/// arithmetic prelude (linear ordered field `R`), plus a deterministic map from a
/// dense real-variable index to its opaque `R`-typed [`NameId`].
///
/// Distinct from [`super::ReconstructCtx`] (the EUF carrier `α`): the carrier here is the
/// ordered field `R` and the trusted base is [`build_arith_prelude`]'s axioms.
#[allow(dead_code)]
pub struct LraReconstructCtx {
    kernel: Kernel,
    arith: ArithPrelude,
    /// Dense variable index → its opaque `R`-typed constant `NameId`.
    vars: BTreeMap<usize, NameId>,
    /// Monotone counter for fresh, collision-free declaration names.
    next_id: u64,
}

impl core::fmt::Debug for LraReconstructCtx {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LraReconstructCtx")
            .field("vars", &self.vars.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl Default for LraReconstructCtx {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
impl LraReconstructCtx {
    /// Build a fresh LRA reconstruction context: a kernel with the arithmetic
    /// prelude declared and an empty variable map.
    #[must_use]
    pub fn new() -> Self {
        let mut kernel = Kernel::new();
        let arith = build_arith_prelude(&mut kernel);
        Self {
            kernel,
            arith,
            vars: BTreeMap::new(),
            next_id: 0,
        }
    }

    /// A shared reference to the underlying kernel (e.g. to `infer`/`def_eq` an
    /// externally-built term, or to inspect the environment).
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// A mutable reference to the underlying kernel.
    pub fn kernel_mut(&mut self) -> &mut Kernel {
        &mut self.kernel
    }

    /// The arithmetic prelude names (`R`, `le`, `lt`, `le_trans`, …).
    #[must_use]
    pub fn arith(&self) -> &ArithPrelude {
        &self.arith
    }

    /// Mint a fresh private name component under the anonymous root.
    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.lra");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Mint a fresh free-variable id for building open `Or.rec` minor-premise
    /// bodies (the disjunctive-LRA case split). Reuses the deterministic `next_id`
    /// counter; fvar ids live in a separate namespace from `NameId` declarations,
    /// so sharing the counter cannot collide.
    fn fresh_fvar_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Get (declaring lazily) the opaque `R`-typed constant for variable `index`.
    /// Idempotent: the same index always maps to the same constant.
    fn var_const(&mut self, index: usize) -> NameId {
        if let Some(&id) = self.vars.get(&index) {
            return id;
        }
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let decl_name = self.fresh_name("x");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: r_ty,
            })
            .expect("real variable axiom (_ : R) should admit");
        self.vars.insert(index, decl_name);
        decl_name
    }

    /// `add x y : R`.
    fn mk_add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let add = self.kernel.const_(self.arith.add, vec![]);
        let e = self.kernel.app(add, x);
        self.kernel.app(e, y)
    }

    /// `mul x y : R`.
    fn mk_mul(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let mul = self.kernel.const_(self.arith.mul, vec![]);
        let e = self.kernel.app(mul, x);
        self.kernel.app(e, y)
    }

    /// `neg x : R`.
    fn mk_neg(&mut self, x: ExprId) -> ExprId {
        let neg = self.kernel.const_(self.arith.neg, vec![]);
        self.kernel.app(neg, x)
    }

    /// `zero : R`.
    fn mk_zero(&mut self) -> ExprId {
        self.kernel.const_(self.arith.zero, vec![])
    }

    /// `one : R`.
    fn mk_one(&mut self) -> ExprId {
        self.kernel.const_(self.arith.one, vec![])
    }

    /// `le x y : Prop`.
    fn mk_le(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let le = self.kernel.const_(self.arith.le, vec![]);
        let e = self.kernel.app(le, x);
        self.kernel.app(e, y)
    }

    fn mk_lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let lt = self.kernel.const_(self.arith.lt, vec![]);
        let e = self.kernel.app(lt, x);
        self.kernel.app(e, y)
    }

    /// Build the `R` expression for a [`LinR`], restricted to the slice-1 small
    /// subset: integer coefficients in `{-1, 0, +1}` and a constant in `{0, 1}`.
    ///
    /// `Σ ±xⱼ (+ 1)` is a left-nested `add` over `xⱼ` / `neg xⱼ` terms (and a
    /// trailing `one` when the constant is `1`); a bare constant `0` is `zero`.
    ///
    /// # Errors
    ///
    /// Returns [`ReconstructError::UnsupportedTerm`] for any coefficient outside
    /// `{-1,0,+1}` or a constant outside `{0,1}` — the boundary of this slice.
    fn lin_to_r(&mut self, lin: &LinR) -> Result<ExprId, ReconstructError> {
        let one = Rational::integer(1);
        let neg_one = Rational::integer(-1);
        let mut terms: Vec<ExprId> = Vec::new();
        for &(index, coeff) in &lin.coeffs {
            let var_name = self.var_const(index);
            let var = self.kernel.const_(var_name, vec![]);
            if coeff == one {
                terms.push(var);
            } else if coeff == neg_one {
                let neg = self.mk_neg(var);
                terms.push(neg);
            } else {
                return Err(ReconstructError::UnsupportedTerm {
                    term: format!(
                        "LRA reconstruction (slice 1) only models ±1 coefficients; \
                         got {}/{} on variable {index}",
                        coeff.numerator(),
                        coeff.denominator()
                    ),
                });
            }
        }
        if lin.constant == one {
            let one_r = self.mk_one();
            terms.push(one_r);
        } else if !lin.constant.is_zero() {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "LRA reconstruction (slice 1) only models a constant of 0 or 1; got {}/{}",
                    lin.constant.numerator(),
                    lin.constant.denominator()
                ),
            });
        }
        // Fold the terms with `add`; an empty term list is `zero`.
        let mut iter = terms.into_iter();
        let Some(first) = iter.next() else {
            return Ok(self.mk_zero());
        };
        let mut acc = first;
        for t in iter {
            acc = self.mk_add(acc, t);
        }
        Ok(acc)
    }

    /// Declare a fresh hypothesis axiom `h : prop` and return its `Const` proof.
    fn hyp_axiom(&mut self, prop: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name("hyp");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: prop,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "la_generic".to_owned(),
                detail: format!("hypothesis axiom did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    // -----------------------------------------------------------------------
    // General-Farkas ring engine.
    //
    // The general la_generic reconstruction (any nonneg integer multipliers over
    // integer-coefficient `≤`-constraints) needs to manipulate linear `R`
    // expressions up to the ordered-field axioms. Since `R` is axiomatic the kernel
    // never *computes* `λ·L = c`; every cancellation is an explicit `Eq`-rewrite
    // built from `add_comm`/`add_assoc`/`add_neg`/`add_zero`. The helpers below are
    // that explicit ring layer: `Eq R`-combinators (`refl`/`symm`/`trans`/`congr_add`),
    // a canonical additive normal form, and a normalizer that *proves* every linear
    // expression equal to the canonical form of its [`LinR`]. Two ring-equal
    // expressions then normalize to the **same** interned canonical term, so their
    // equality is `trans normA (symm normB)` — kernel-checked end to end.
    // -----------------------------------------------------------------------

    /// `Eq R x y` (the carrier-level equality proposition).
    fn mk_eq_r(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let eq = self.kernel.const_(self.arith.logic.eq, vec![one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(eq, r_ty);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    /// `Eq.refl R a : Eq R a a`.
    fn eq_refl_r(&mut self, a: ExprId) -> ExprId {
        let one_lvl = {
            let z = self.kernel.level_zero();
            self.kernel.level_succ(z)
        };
        let refl = self.kernel.const_(self.arith.logic.eq_refl, vec![one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(refl, r_ty);
        self.kernel.app(e, a)
    }

    /// `Eq.rec`-based transport over the `R` carrier: given `h : Eq R p q` and a
    /// `refl_case : motive p (Eq.refl R p)`, builds `motive q h`. Mirrors the EUF
    /// [`ReconstructCtx::mk_eq_rec_transport`] but at the `R` (`Sort 1`) carrier.
    fn eq_rec_transport_r(
        &mut self,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let z = self.kernel.level_zero();
        let one_lvl = self.kernel.level_succ(z);
        let rec = self
            .kernel
            .const_(self.arith.logic.eq_rec, vec![z, one_lvl]);
        let r_ty = self.kernel.const_(self.arith.r, vec![]);
        let e = self.kernel.app(rec, r_ty);
        let e = self.kernel.app(e, p);
        let e = self.kernel.app(e, motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, q);
        self.kernel.app(e, h)
    }

    /// `Eq.symm`: given `h : Eq R a b`, build a proof of `Eq R b a`.
    ///
    /// `Eq.rec R a (fun x _ => Eq R x a) (Eq.refl R a) b h`.
    fn eq_symm_r(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_x_a = self.mk_eq_r(x1, a);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = self.eq_refl_r(a);
        self.eq_rec_transport_r(a, motive, refl_case, b, h)
    }

    /// `Eq.trans`: given `h1 : Eq R a b` and `h2 : Eq R b c`, build `Eq R a c`.
    ///
    /// `Eq.rec R b (fun x _ => Eq R a x) h1 c h2`.
    fn eq_trans_r(&mut self, a: ExprId, b: ExprId, c: ExprId, h1: ExprId, h2: ExprId) -> ExprId {
        let motive = {
            let x1 = self.kernel.bvar(1);
            let eq_a_x = self.mk_eq_r(a, x1);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(b, motive, h1, c, h2)
    }

    /// Congruence on the *left* argument of `add`: given `h : Eq R a a'`, build
    /// `Eq R (add a b) (add a' b)`.
    fn congr_add_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (add a b) (add x b).
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_add(x1, b);
            let eq_body = self.mk_eq_r(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// Congruence on the *right* argument of `add`: given `h : Eq R b b'`, build
    /// `Eq R (add a b) (add a b')`.
    fn congr_add_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R b x) => Eq R (add a b) (add a x).
        let motive = {
            let a_b = self.mk_add(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_add(a, x1);
            let eq_body = self.mk_eq_r(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_add(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(b, motive, refl_case, bp, h)
    }

    /// `add_assoc a b c : Eq R (add (add a b) c) (add a (add b c))`.
    fn add_assoc_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_assoc, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    /// `add_comm a b : Eq R (add a b) (add b a)`.
    fn add_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    /// `add_zero a : Eq R (add a zero) a`.
    fn add_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_zero, vec![]);
        self.kernel.app(ax, a)
    }

    /// `add_neg a : Eq R (add a (neg a)) zero`.
    fn add_neg_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_neg, vec![]);
        self.kernel.app(ax, a)
    }

    // -----------------------------------------------------------------------
    // Multiplicative ring layer (degree-2 SOS ring normalizer, ADR-0040).
    //
    // The single-square SOS path needs no ring normalizer (the asserted lhs is
    // literally `ℓ·ℓ`). A *sum-of-monomials* SOS — e.g. AM-GM's
    // `x² + y² − 2xy < 0`, whose lhs is `(x−y)·(x−y)` only after a ring identity —
    // does: we must PROVE `Eq R p ((x−y)·(x−y))` in the kernel and rewrite the
    // square-nonnegativity across it. The helpers below extend the additive
    // `Eq R` engine with the multiplicative axiom wrappers, `mul` congruence, and
    // the three derived `neg`/`mul` bridge lemmas (each grounded in
    // inverse-uniqueness, which is itself derived from the additive axioms — no
    // new kernel axiom is introduced).
    // -----------------------------------------------------------------------

    /// `mul_comm a b : Eq R (mul a b) (mul b a)`.
    fn mul_comm_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_comm, vec![]);
        let e = self.kernel.app(ax, a);
        self.kernel.app(e, b)
    }

    /// `mul_zero a : Eq R (mul a zero) zero`.
    fn mul_zero_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_zero, vec![]);
        self.kernel.app(ax, a)
    }

    /// `left_distrib a b c : Eq R (mul a (add b c)) (add (mul a b) (mul a c))`.
    fn left_distrib_eq(&mut self, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.left_distrib, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, c)
    }

    /// Congruence on the *left* argument of `mul`: given `h : Eq R a a'`, build
    /// `Eq R (mul a b) (mul a' b)`.
    fn congr_mul_left(&mut self, a: ExprId, ap: ExprId, b: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (mul a b) (mul x b).
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let x_b = self.mk_mul(x1, b);
            let eq_body = self.mk_eq_r(a_b, x_b);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// Congruence on the *right* argument of `mul`: given `h : Eq R b b'`, build
    /// `Eq R (mul a b) (mul a b')`.
    fn congr_mul_right(&mut self, a: ExprId, b: ExprId, bp: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R b x) => Eq R (mul a b) (mul a x).
        let motive = {
            let a_b = self.mk_mul(a, b);
            let x1 = self.kernel.bvar(1);
            let a_x = self.mk_mul(a, x1);
            let eq_body = self.mk_eq_r(a_b, a_x);
            let x0 = self.kernel.bvar(0);
            let eq_b_x = self.mk_eq_r(b, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_b_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let a_b = self.mk_mul(a, b);
            self.eq_refl_r(a_b)
        };
        self.eq_rec_transport_r(b, motive, refl_case, bp, h)
    }

    /// Inverse-uniqueness over the additive group: from `h1 : Eq R (add c u) zero`
    /// and `h2 : Eq R (add c v) zero`, derive `Eq R u v`. Pure additive-axiom chain
    /// (`add_zero`, `add_assoc`, `add_comm` + congruence), so it needs **no** new
    /// kernel axiom — it is the bridge every `neg`/`mul` lemma below rests on.
    ///
    /// `u = u+0 = u+(c+v) = (u+c)+v = (c+u)+v = 0+v = v+0 = v`.
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
        // s0 : u = add u zero  (symm add_zero).
        let u_zero = self.mk_add(u, zero);
        let s0 = {
            let az = self.add_zero_eq(u); // add u zero = u
            self.eq_symm_r(u_zero, u, az) // u = add u zero
        };
        // s1 : add u zero = add u (add c v)  (congr_right with symm h2).
        let h2_sym = self.eq_symm_r(cv, zero, h2); // zero = add c v
        let s1 = self.congr_add_right(u, zero, cv, h2_sym);
        // s2 : add u (add c v) = add (add u c) v  (symm add_assoc).
        let u_cv = self.mk_add(u, cv);
        let uc = self.mk_add(u, c);
        let uc_v = self.mk_add(uc, v);
        let s2 = {
            let assoc = self.add_assoc_eq(u, c, v); // (u+c)+v = u+(c+v)
            self.eq_symm_r(uc_v, u_cv, assoc) // u+(c+v) = (u+c)+v
        };
        // s3 : add (add u c) v = add (add c u) v  (congr_left add_comm u c).
        let comm_uc = self.add_comm_eq(u, c); // add u c = add c u
        let s3 = self.congr_add_left(uc, cu, v, comm_uc);
        // s4 : add (add c u) v = add zero v  (congr_left h1).
        let cu_v = self.mk_add(cu, v);
        let s4 = self.congr_add_left(cu, zero, v, h1);
        // s5 : add zero v = add v zero  (add_comm zero v).
        let zero_v = self.mk_add(zero, v);
        let v_zero = self.mk_add(v, zero);
        let s5 = self.add_comm_eq(zero, v);
        // s6 : add v zero = v  (add_zero v).
        let s6 = self.add_zero_eq(v);
        // Chain u = … = v.
        let t01 = self.eq_trans_r(u, u_zero, u_cv, s0, s1);
        let t02 = self.eq_trans_r(u, u_cv, uc_v, t01, s2);
        let t03 = self.eq_trans_r(u, uc_v, cu_v, t02, s3);
        let t04 = self.eq_trans_r(u, cu_v, zero_v, t03, s4);
        let t05 = self.eq_trans_r(u, zero_v, v_zero, t04, s5);
        self.eq_trans_r(u, v_zero, v, t05, s6)
    }

    /// `neg_neg z : Eq R (neg (neg z)) z`. Derived: `z` and `neg (neg z)` are both
    /// additive inverses of `neg z`, so inverse-uniqueness identifies them.
    fn neg_neg_eq(&mut self, z: ExprId) -> ExprId {
        let nz = self.mk_neg(z);
        let nnz = self.mk_neg(nz);
        let zero = self.mk_zero();
        // h1 : add (neg z) z = zero  — from add_neg (neg z)? No: add_neg gives
        // `add a (neg a) = zero`. With `a = z`: add z (neg z) = zero; commute.
        let add_z_nz = self.mk_add(z, nz);
        let add_nz_z = self.mk_add(nz, z);
        let h1 = {
            let comm = self.add_comm_eq(nz, z); // add (neg z) z = add z (neg z)
            let an = self.add_neg_eq(z); // add z (neg z) = zero
            self.eq_trans_r(add_nz_z, add_z_nz, zero, comm, an)
        };
        // h2 : add (neg z) (neg (neg z)) = zero  — add_neg (neg z).
        let h2 = self.add_neg_eq(nz);
        // inverse-uniqueness with c = neg z, u = z, v = neg (neg z) ⇒ z = neg(neg z).
        let z_eq_nnz = self.add_left_cancel_eq(nz, z, nnz, h1, h2);
        self.eq_symm_r(z, nnz, z_eq_nnz) // neg (neg z) = z
    }

    /// `mul_neg_right a b : Eq R (mul a (neg b)) (neg (mul a b))`. Derived:
    /// `mul a (neg b)` is an additive inverse of `mul a b` (via `left_distrib` +
    /// `add_neg` + `mul_zero`), and `neg (mul a b)` is too; inverse-uniqueness
    /// identifies them.
    fn mul_neg_right_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let nb = self.mk_neg(b);
        let ab = self.mk_mul(a, b);
        let a_nb = self.mk_mul(a, nb);
        let zero = self.mk_zero();
        // inv1 : add (mul a b) (mul a (neg b)) = zero.
        //   left_distrib a b (neg b) : mul a (add b (neg b)) = add (mul a b)(mul a (neg b))
        //   add_neg b               : add b (neg b) = zero
        //   ⇒ mul a (add b (neg b)) = mul a zero = zero.
        let b_nb = self.mk_add(b, nb);
        let a_bnb = self.mk_mul(a, b_nb);
        let sum = self.mk_add(ab, a_nb);
        let inv1 = {
            let ld = self.left_distrib_eq(a, b, nb); // a*(b+(-b)) = a*b + a*(-b)
            let an = self.add_neg_eq(b); // b+(-b) = zero
            let cong = self.congr_mul_right(a, b_nb, zero, an); // a*(b+(-b)) = a*0
            let mz = self.mul_zero_eq(a); // a*0 = zero
            let a_zero = self.mk_mul(a, zero);
            // a*(b+(-b)) = zero
            let lhs_zero = self.eq_trans_r(a_bnb, a_zero, zero, cong, mz);
            // sum = a*(b+(-b)) (symm ld), then = zero.
            let sum_to_lhs = self.eq_symm_r(a_bnb, sum, ld); // a*b+a*(-b) = a*(b+(-b))
            self.eq_trans_r(sum, a_bnb, zero, sum_to_lhs, lhs_zero)
        };
        // inv2 : add (mul a b) (neg (mul a b)) = zero  — add_neg (mul a b).
        let inv2 = self.add_neg_eq(ab);
        // inverse-uniqueness: c = mul a b, u = mul a (neg b), v = neg (mul a b).
        let neg_ab = self.mk_neg(ab);
        self.add_left_cancel_eq(ab, a_nb, neg_ab, inv1, inv2)
    }

    /// `mul_neg_left a b : Eq R (mul (neg a) b) (neg (mul a b))`. Derived from
    /// `mul_neg_right` by commuting the product on both sides of the `neg`.
    fn mul_neg_left_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let na_b = self.mk_mul(na, b);
        let b_na = self.mk_mul(b, na);
        let ba = self.mk_mul(b, a);
        let ab = self.mk_mul(a, b);
        // mul (neg a) b =[mul_comm] mul b (neg a) =[mul_neg_right] neg (mul b a)
        //   =[congr neg mul_comm] neg (mul a b).
        let comm1 = self.mul_comm_eq(na, b); // (neg a)*b = b*(neg a)
        let mnr = self.mul_neg_right_eq(b, a); // b*(neg a) = neg (b*a)
        let neg_ba = self.mk_neg(ba);
        let comm2 = self.mul_comm_eq(b, a); // b*a = a*b
        let neg_ab = self.mk_neg(ab);
        let neg_cong = self.congr_neg(ba, ab, comm2); // neg (b*a) = neg (a*b)
        let t01 = self.eq_trans_r(na_b, b_na, neg_ba, comm1, mnr);
        self.eq_trans_r(na_b, neg_ba, neg_ab, t01, neg_cong)
    }

    /// Congruence under `neg`: given `h : Eq R a a'`, build `Eq R (neg a) (neg a')`.
    fn congr_neg(&mut self, a: ExprId, ap: ExprId, h: ExprId) -> ExprId {
        // motive := fun (x : R) (_ : Eq R a x) => Eq R (neg a) (neg x).
        let motive = {
            let neg_a = self.mk_neg(a);
            let x1 = self.kernel.bvar(1);
            let neg_x = self.mk_neg(x1);
            let eq_body = self.mk_eq_r(neg_a, neg_x);
            let x0 = self.kernel.bvar(0);
            let eq_a_x = self.mk_eq_r(a, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_a_x, eq_body, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        let refl_case = {
            let neg_a = self.mk_neg(a);
            self.eq_refl_r(neg_a)
        };
        self.eq_rec_transport_r(a, motive, refl_case, ap, h)
    }

    /// `neg_add a b : Eq R (neg (add a b)) (add (neg a) (neg b))`. Derived:
    /// `add (neg a)(neg b)` is an additive inverse of `add a b` (shown by
    /// reassociating `(a+b)+((-a)+(-b))` to `zero`), and `neg (add a b)` is too;
    /// inverse-uniqueness identifies them.
    fn neg_add_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let nb = self.mk_neg(b);
        let ab = self.mk_add(a, b);
        let na_nb = self.mk_add(na, nb); // (-a)+(-b)
        let zero = self.mk_zero();
        // inv1 : add (add a b) (add (neg a)(neg b)) = zero.
        let inv1 = {
            // (a+b)+T =[add_assoc a b T] a+(b+T),  T = (-a)+(-b).
            let assoc0 = self.add_assoc_eq(a, b, na_nb);
            let ab_t = self.mk_add(ab, na_nb); // (a+b)+T
            let b_t = self.mk_add(b, na_nb); // b+T
            let a_bt = self.mk_add(a, b_t); // a+(b+T)
            // inner: b+T = b+((-a)+(-b)) ⟶ -a.
            // b+((-a)+(-b)) =[symm add_assoc b (-a)(-b)] (b+(-a))+(-b)
            let assoc1 = self.add_assoc_eq(b, na, nb); // (b+(-a))+(-b) = b+((-a)+(-b))
            let b_na = self.mk_add(b, na); // b+(-a)
            let bna_nb = self.mk_add(b_na, nb); // (b+(-a))+(-b)
            let s1 = self.eq_symm_r(bna_nb, b_t, assoc1); // b+T = (b+(-a))+(-b)
            // (b+(-a)) =[add_comm] ((-a)+b) ⟶ congr_left.
            let na_b = self.mk_add(na, b); // (-a)+b
            let comm1 = self.add_comm_eq(b, na); // b+(-a) = (-a)+b
            let s2 = self.congr_add_left(b_na, na_b, nb, comm1); // (b+(-a))+(-b) = ((-a)+b)+(-b)
            let nab_nb = self.mk_add(na_b, nb); // ((-a)+b)+(-b)
            // ((-a)+b)+(-b) =[add_assoc (-a) b (-b)] (-a)+(b+(-b)).
            let assoc2 = self.add_assoc_eq(na, b, nb);
            let b_nb = self.mk_add(b, nb); // b+(-b)
            let na_bnb = self.mk_add(na, b_nb); // (-a)+(b+(-b))
            // (b+(-b)) =[add_neg b] zero ⟶ congr_right.
            let an_b = self.add_neg_eq(b); // b+(-b) = zero
            let na_zero = self.mk_add(na, zero); // (-a)+zero
            let s3 = self.congr_add_right(na, b_nb, zero, an_b); // (-a)+(b+(-b)) = (-a)+zero
            // (-a)+zero =[add_zero] -a.
            let s4 = self.add_zero_eq(na); // (-a)+zero = -a
            // chain inner: b+T = (b+(-a))+(-b) = ((-a)+b)+(-b) = (-a)+(b+(-b)) = (-a)+zero = -a.
            let i01 = self.eq_trans_r(b_t, bna_nb, nab_nb, s1, s2);
            let i02 = self.eq_trans_r(b_t, nab_nb, na_bnb, i01, assoc2);
            let i03 = self.eq_trans_r(b_t, na_bnb, na_zero, i02, s3);
            let inner = self.eq_trans_r(b_t, na_zero, na, i03, s4); // b+T = -a
            // a+(b+T) =[congr_right inner] a+(-a) =[add_neg a] zero.
            let a_na = self.mk_add(a, na); // a+(-a)
            let lift = self.congr_add_right(a, b_t, na, inner); // a+(b+T) = a+(-a)
            let an_a = self.add_neg_eq(a); // a+(-a) = zero
            // (a+b)+T = a+(b+T) = a+(-a) = zero.
            let c01 = self.eq_trans_r(ab_t, a_bt, a_na, assoc0, lift);
            self.eq_trans_r(ab_t, a_na, zero, c01, an_a)
        };
        // inv2 : add (add a b) (neg (add a b)) = zero  — add_neg (add a b).
        let inv2 = self.add_neg_eq(ab);
        // inverse-uniqueness: c = add a b, u = add(neg a)(neg b), v = neg(add a b).
        let neg_ab = self.mk_neg(ab);
        let u_eq_v = self.add_left_cancel_eq(ab, na_nb, neg_ab, inv1, inv2); // (-a)+(-b) = neg(a+b)
        self.eq_symm_r(na_nb, neg_ab, u_eq_v) // neg(a+b) = (-a)+(-b)
    }

    /// `neg_mul_neg a b : Eq R (mul (neg a) (neg b)) (mul a b)`. Derived:
    /// `(neg a)·(neg b) = neg ((neg a)·b) = neg (neg (a·b)) = a·b`.
    fn neg_mul_neg_eq(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let na = self.mk_neg(a);
        let nb = self.mk_neg(b);
        let na_nb = self.mk_mul(na, nb);
        let na_b = self.mk_mul(na, b);
        let ab = self.mk_mul(a, b);
        // (neg a)*(neg b) =[mul_neg_right (neg a) b] neg ((neg a)*b)
        let mnr = self.mul_neg_right_eq(na, b); // (neg a)*(neg b) = neg ((neg a)*b)
        let neg_na_b = self.mk_neg(na_b);
        // neg ((neg a)*b) =[congr_neg mul_neg_left a b] neg (neg (a*b))
        let mnl = self.mul_neg_left_eq(a, b); // (neg a)*b = neg (a*b)
        let neg_ab = self.mk_neg(ab);
        let neg_neg_ab = self.mk_neg(neg_ab);
        let cong = self.congr_neg(na_b, neg_ab, mnl); // neg ((neg a)*b) = neg (neg (a*b))
        // neg (neg (a*b)) =[neg_neg] a*b
        let nn = self.neg_neg_eq(ab); // neg (neg (a*b)) = a*b
        let t01 = self.eq_trans_r(na_nb, neg_na_b, neg_neg_ab, mnr, cong);
        self.eq_trans_r(na_nb, neg_neg_ab, ab, t01, nn)
    }
}

/// A signed unit **generator** in the canonical additive normal form: either a
/// bare variable `±xⱼ` or the unit `±1`. The canonical form of a linear expression
/// is a right-nested `add` over a flat list of generators (terminated by `zero`),
/// with variables ascending by index and the constant last. Repeated generators
/// model integer coefficients (`coeff = 3` ⇒ three `+xⱼ` generators).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gen {
    /// `+xⱼ` (variable at dense index).
    Var(usize),
    /// `-xⱼ`.
    NegVar(usize),
    /// `+one`.
    One,
    /// `-one` (= `neg one`).
    NegOne,
}

impl Gen {
    /// The negation of this generator (so `Var` ↔ `NegVar`, `One` ↔ `NegOne`).
    fn negate(self) -> Self {
        match self {
            Gen::Var(i) => Gen::NegVar(i),
            Gen::NegVar(i) => Gen::Var(i),
            Gen::One => Gen::NegOne,
            Gen::NegOne => Gen::One,
        }
    }

    /// A total sort key putting variables (ascending by index, `+` before `−`)
    /// ahead of the constant generators. The exact order only needs to be total
    /// and to keep a generator adjacent to its negation after bubbling, so the
    /// merge can cancel; this key does both.
    fn sort_key(self) -> (usize, u8) {
        match self {
            Gen::Var(i) => (i, 0),
            Gen::NegVar(i) => (i, 1),
            Gen::One => (usize::MAX, 0),
            Gen::NegOne => (usize::MAX, 1),
        }
    }
}

/// A **monomial** of total degree ≤ 2 over canonical variable indices, the atom of
/// the degree-2 ring normalizer's canonical form (ADR-0040 generalization). Its
/// kernel encoding is a fixed, deterministic `R`-expression:
/// - [`Mono::Const`] → `one`,
/// - [`Mono::Lin`] → `xᵢ`,
/// - [`Mono::Quad`] (`i ≤ j`) → `mul xᵢ xⱼ`.
///
/// `Quad` is normalized so `i ≤ j`, giving each unordered variable pair a single
/// canonical kernel representative (`x·y` and `y·x` map to the same `Quad`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mono {
    /// The constant monomial `1`.
    Const,
    /// The linear monomial `xᵢ`.
    Lin(usize),
    /// The quadratic monomial `xᵢ·xⱼ` with `i ≤ j` (the kernel term is `mul xᵢ xⱼ`).
    Quad(usize, usize),
}

impl Mono {
    /// Build the canonical quadratic monomial for an unordered variable pair,
    /// ordering the two indices so the kernel representative is unique.
    fn quad(i: usize, j: usize) -> Self {
        if i <= j {
            Mono::Quad(i, j)
        } else {
            Mono::Quad(j, i)
        }
    }

    /// A total sort key: linear monomials (ascending index) first, then quadratic
    /// monomials (lexicographic on the ordered pair), then the constant last —
    /// mirroring [`Gen::sort_key`]'s "variables before constant" convention. Only
    /// totality and determinism matter (it fixes the canonical order).
    fn sort_key(self) -> (u8, usize, usize) {
        match self {
            Mono::Lin(i) => (0, i, 0),
            Mono::Quad(i, j) => (1, i, j),
            Mono::Const => (2, usize::MAX, usize::MAX),
        }
    }
}

/// A signed monomial **generator** in the degree-2 canonical additive normal form:
/// a [`Mono`] with a sign. The canonical form of a degree-≤2 expression is a
/// right-nested `add` over a flat list of these (terminated by `zero`), monomials
/// in [`Mono::sort_key`] order, repeated to model integer coefficients. This is the
/// degree-2 analogue of [`Gen`]; the normalizer reuses the same bubble-sort +
/// cancellation algorithm, extended with a multiplicative distribution step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MonoGen {
    mono: Mono,
    /// `true` ⇒ the generator is `neg (mono_expr)`, `false` ⇒ `mono_expr`.
    neg: bool,
}

impl MonoGen {
    fn pos(mono: Mono) -> Self {
        MonoGen { mono, neg: false }
    }

    /// The negation of this generator (flips the sign bit).
    fn negate(self) -> Self {
        MonoGen {
            mono: self.mono,
            neg: !self.neg,
        }
    }

    /// A total sort key keeping a generator adjacent to its negation after bubbling
    /// (same monomial ⇒ same primary key; sign breaks the tie) so the merge can
    /// cancel — exactly as [`Gen::sort_key`] does for the linear engine.
    fn sort_key(self) -> (u8, usize, usize, u8) {
        let (a, b, c) = self.mono.sort_key();
        (a, b, c, u8::from(self.neg))
    }
}

/// A small owned degree-≤2 expression AST over canonical variable indices, the
/// **input** to the degree-2 ring normalizer ([`LraReconstructCtx::normalize_deg2`]).
/// Built from `var`/`neg`/`add`/`mul`; the normalizer both emits its faithful kernel
/// `R`-encoding and proves it equals the canonical signed-monomial sum.
#[derive(Debug, Clone)]
enum RExpr {
    /// The variable `xᵢ`.
    Var(usize),
    /// `neg e`.
    Neg(Box<RExpr>),
    /// `add a b`.
    Add(Box<RExpr>, Box<RExpr>),
    /// `mul a b`.
    Mul(Box<RExpr>, Box<RExpr>),
    /// The constant `one`.
    One,
}

/// The carrier of the general-Farkas additive ring engine, on top of
/// [`LraReconstructCtx`]. Builds generator expressions, the canonical right-nested
/// normal form, and the per-rewrite `Eq R` proofs that drive normalization.
#[allow(dead_code)]
impl LraReconstructCtx {
    /// The `R` expression for a single generator.
    fn gen_expr(&mut self, g: Gen) -> ExprId {
        match g {
            Gen::Var(i) => {
                let name = self.var_const(i);
                self.kernel.const_(name, vec![])
            }
            Gen::NegVar(i) => {
                let name = self.var_const(i);
                let v = self.kernel.const_(name, vec![]);
                self.mk_neg(v)
            }
            Gen::One => self.mk_one(),
            Gen::NegOne => {
                let one = self.mk_one();
                self.mk_neg(one)
            }
        }
    }

    /// The canonical right-nested additive expression `g0 + (g1 + … + (g_{k-1} + zero))`
    /// over `gens`; an empty list is `zero`.
    fn gens_to_expr(&mut self, gens: &[Gen]) -> ExprId {
        let mut acc = self.mk_zero();
        for &g in gens.iter().rev() {
            let ge = self.gen_expr(g);
            acc = self.mk_add(ge, acc);
        }
        acc
    }

    /// Lift a tail rewrite `tail_proof : Eq R tail tail'` up through the `prefix`
    /// leading generators, yielding `Eq R (prefix ++ tail) (prefix ++ tail')` where
    /// both sides are the right-nested canonical forms. Each leading generator is
    /// re-attached with [`Self::congr_add_right`].
    fn lift_tail_rewrite(
        &mut self,
        prefix: &[Gen],
        tail: &[Gen],
        tail2: &[Gen],
        mut proof: ExprId,
    ) -> ExprId {
        // Build proof bottom-up: at each step we have `proof : Eq R T T2` for the
        // current tail `T = (prefix[i+1..] ++ tail)`; prepend prefix[i].
        for k in (0..prefix.len()).rev() {
            let g = self.gen_expr(prefix[k]);
            let mut sub_tail: Vec<Gen> = prefix[k + 1..].to_vec();
            sub_tail.extend_from_slice(tail);
            let mut sub_tail2: Vec<Gen> = prefix[k + 1..].to_vec();
            sub_tail2.extend_from_slice(tail2);
            let t = self.gens_to_expr(&sub_tail);
            let t2 = self.gens_to_expr(&sub_tail2);
            proof = self.congr_add_right(g, t, t2, proof);
        }
        proof
    }

    /// Prove `Eq R (g0 + (g1 + tail)) (g1 + (g0 + tail))` — an adjacent swap at the
    /// head of a right-nested sum. `t` is the canonical expr of `tail`.
    fn swap_head_eq(&mut self, g0: Gen, g1: Gen, tail: &[Gen]) -> ExprId {
        let e0 = self.gen_expr(g0);
        let e1 = self.gen_expr(g1);
        let t = self.gens_to_expr(tail);
        // add e0 (add e1 t) =[symm assoc] add (add e0 e1) t
        let assoc1 = self.add_assoc_eq(e0, e1, t); // (e0+e1)+t = e0+(e1+t)
        let lhs = {
            let inner = self.mk_add(e1, t);
            self.mk_add(e0, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e0, e1);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc1); // add e0 (add e1 t) = add (add e0 e1) t
        // congr_left (add_comm e0 e1) : add (add e0 e1) t = add (add e1 e0) t
        let comm = self.add_comm_eq(e0, e1); // add e0 e1 = add e1 e0
        let e0e1 = self.mk_add(e0, e1);
        let e1e0 = self.mk_add(e1, e0);
        let step2 = self.congr_add_left(e0e1, e1e0, t, comm);
        // assoc : add (add e1 e0) t = add e1 (add e0 t)
        let step3 = self.add_assoc_eq(e1, e0, t);
        // chain: lhs = mid1 = mid2 = rhs
        let mid2 = self.mk_add(e1e0, t);
        let rhs = {
            let inner = self.mk_add(e0, t);
            self.mk_add(e1, inner)
        };
        let t01 = self.eq_trans_r(lhs, mid1, mid2, step1, step2);
        self.eq_trans_r(lhs, mid2, rhs, t01, step3)
    }

    /// Prove `Eq R (g + (g.negate() + tail)) tail` — cancel an adjacent
    /// generator/anti-generator pair at the head. `t` is the canonical expr of `tail`.
    fn cancel_head_eq(&mut self, g: Gen, tail: &[Gen]) -> ExprId {
        let gn = g.negate();
        let e = self.gen_expr(g);
        let en = self.gen_expr(gn);
        let t = self.gens_to_expr(tail);
        // add e (add en t) =[symm assoc] add (add e en) t
        let assoc = self.add_assoc_eq(e, en, t);
        let lhs = {
            let inner = self.mk_add(en, t);
            self.mk_add(e, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e, en);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc);
        // Prove `add e en = zero`. add_neg gives `add p (neg p) = zero`. For a
        // `+`-generator g (e = p, en = neg p) this is direct; for a `−`-generator
        // (e = neg p, en = p) commute first.
        let (e_e_en_zero, e_en) = match g {
            Gen::Var(_) | Gen::One => {
                // e = p, en = neg p  ⇒ add_neg p.
                let p = e;
                let an = self.add_neg_eq(p); // add p (neg p) = zero
                let e_en = self.mk_add(e, en);
                (an, e_en)
            }
            Gen::NegVar(_) | Gen::NegOne => {
                // e = neg p, en = p ⇒ add (neg p) p = zero via comm + add_neg.
                let p = en; // the positive form
                let np = e; // neg p
                // add (neg p) p =[comm] add p (neg p) =[add_neg] zero.
                let comm = self.add_comm_eq(np, p); // add np p = add p np
                let an = self.add_neg_eq(p); // add p np = zero
                let lhs_c = self.mk_add(np, p);
                let mid_c = self.mk_add(p, np);
                let zero = self.mk_zero();
                let chained = self.eq_trans_r(lhs_c, mid_c, zero, comm, an);
                let e_en = self.mk_add(e, en);
                (chained, e_en)
            }
        };
        // congr_left (add e en = zero) : add (add e en) t = add zero t
        let zero = self.mk_zero();
        let step2 = self.congr_add_left(e_en, zero, t, e_e_en_zero);
        // add zero t =[comm] add t zero =[add_zero] t
        let comm0 = self.add_comm_eq(zero, t); // add zero t = add t zero
        let addz = self.add_zero_eq(t); // add t zero = t
        let zt = self.mk_add(zero, t);
        let tz = self.mk_add(t, zero);
        let step3 = self.eq_trans_r(zt, tz, t, comm0, addz);
        // chain lhs = mid1 = (add zero t) = t
        let t01 = self.eq_trans_r(lhs, mid1, zt, step1, step2);
        self.eq_trans_r(lhs, zt, t, t01, step3)
    }

    /// Normalize a generator list to the canonical sorted-and-cancelled list,
    /// returning the canonical generators and a proof
    /// `Eq R (gens_to_expr gens) (gens_to_expr canonical)`.
    ///
    /// Implemented as a bubble pass with cancellation: repeatedly find the first
    /// adjacent pair that is either out of sort order (swap) or a cancelling
    /// generator/anti-generator pair (cancel), apply the corresponding head rewrite
    /// lifted to that position, and post-compose into the running proof. Terminates
    /// because every swap strictly decreases the inversion count and every cancel
    /// strictly decreases the length.
    fn normalize_gens(&mut self, gens: &[Gen]) -> (Vec<Gen>, ExprId) {
        let mut cur: Vec<Gen> = gens.to_vec();
        let start = self.gens_to_expr(&cur);
        // proof : Eq R start (gens_to_expr cur), initially refl.
        let mut proof = self.eq_refl_r(start);
        loop {
            // Find first actionable adjacent pair.
            let mut action: Option<(usize, bool)> = None; // (index, is_cancel)
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
                // tail of the lifted rewrite: [g, g.negate()] ++ tail → tail.
                let mut from_tail = vec![g, g.negate()];
                from_tail.extend_from_slice(&tail);
                let lifted = self.lift_tail_rewrite(&prefix, &from_tail, &tail, head_proof);
                let mut next = prefix.clone();
                next.extend_from_slice(&tail);
                let after = self.gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
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
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            }
        }
        (cur, proof)
    }

    /// Prove `Eq R (add canonA canonB) (gens_to_expr(gensA ++ gensB))` where
    /// `canonA`/`canonB` are the canonical exprs of `gensA`/`gensB`. This "absorbs"
    /// the trailing `zero` of `canonA`, splicing `canonB` in its place, by induction
    /// over `gensA` with `add_assoc` (and `add_comm`+`add_zero` at the base).
    fn append_eq(&mut self, gens_a: &[Gen], gens_b: &[Gen]) -> ExprId {
        let canon_b = self.gens_to_expr(gens_b);
        if gens_a.is_empty() {
            // add zero canon_b =[comm] add canon_b zero =[add_zero] canon_b.
            let zero = self.mk_zero();
            let comm = self.add_comm_eq(zero, canon_b);
            let addz = self.add_zero_eq(canon_b);
            let zt = self.mk_add(zero, canon_b);
            let tz = self.mk_add(canon_b, zero);
            return self.eq_trans_r(zt, tz, canon_b, comm, addz);
        }
        // gens_a = g :: rest. canonA = add g canonRest.
        // add (add g canonRest) canon_b =[assoc] add g (add canonRest canon_b)
        //   =[congr_right (append_eq rest gens_b)] add g (gens_to_expr(rest++gens_b)).
        let g = self.gen_expr(gens_a[0]);
        let rest = &gens_a[1..].to_vec();
        let canon_rest = self.gens_to_expr(rest);
        let assoc = self.add_assoc_eq(g, canon_rest, canon_b);
        let lhs = {
            let ca = self.mk_add(g, canon_rest);
            self.mk_add(ca, canon_b)
        };
        let mid = {
            let inner = self.mk_add(canon_rest, canon_b);
            self.mk_add(g, inner)
        };
        // recursive: add canonRest canon_b = gens_to_expr(rest ++ gens_b)
        let rec = self.append_eq(rest, gens_b);
        let mut rest_b: Vec<Gen> = rest.clone();
        rest_b.extend_from_slice(gens_b);
        let rest_b_expr = self.gens_to_expr(&rest_b);
        let inner_from = self.mk_add(canon_rest, canon_b);
        let step2 = self.congr_add_right(g, inner_from, rest_b_expr, rec);
        let rhs = self.mk_add(g, rest_b_expr);
        self.eq_trans_r(lhs, mid, rhs, assoc, step2)
    }

    // -----------------------------------------------------------------------
    // Degree-2 ring normalizer (ADR-0040 generalization): canonicalize any
    // degree-≤2 `R`-expression built from `var`/`neg`/`add`/`mul`/`one` into a
    // fixed-order sum of signed monomials, carrying an `Eq R` proof. Reuses the
    // additive bubble-sort+cancel engine above, lifted from linear [`Gen`]s to
    // degree-2 [`MonoGen`]s, plus a multiplicative distribution step. No new kernel
    // axiom: every rewrite is one of `left_distrib`/`mul_comm`/`mul_zero`/`mul_one`
    // /the derived neg-bridge lemmas/`add_*` + congruence.
    // -----------------------------------------------------------------------

    /// The kernel `R`-expression for a single bare [`Mono`] (no sign).
    fn mono_expr(&mut self, m: Mono) -> ExprId {
        match m {
            Mono::Const => self.mk_one(),
            Mono::Lin(i) => {
                let name = self.var_const(i);
                self.kernel.const_(name, vec![])
            }
            Mono::Quad(i, j) => {
                let ni = self.var_const(i);
                let xi = self.kernel.const_(ni, vec![]);
                let nj = self.var_const(j);
                let xj = self.kernel.const_(nj, vec![]);
                self.mk_mul(xi, xj)
            }
        }
    }

    /// The kernel `R`-expression for a single signed [`MonoGen`].
    fn mono_gen_expr(&mut self, g: MonoGen) -> ExprId {
        let m = self.mono_expr(g.mono);
        if g.neg { self.mk_neg(m) } else { m }
    }

    /// The canonical right-nested additive expression
    /// `g0 + (g1 + … + (g_{k-1} + zero))` over `gens`; empty ⇒ `zero`.
    fn mono_gens_to_expr(&mut self, gens: &[MonoGen]) -> ExprId {
        let mut acc = self.mk_zero();
        for &g in gens.iter().rev() {
            let ge = self.mono_gen_expr(g);
            acc = self.mk_add(ge, acc);
        }
        acc
    }

    /// Lift a tail rewrite `proof : Eq R tail tail'` up through the `prefix` leading
    /// generators (re-attaching each with [`Self::congr_add_right`]). Degree-2
    /// analogue of [`Self::lift_tail_rewrite`].
    fn mono_lift_tail_rewrite(
        &mut self,
        prefix: &[MonoGen],
        tail: &[MonoGen],
        tail2: &[MonoGen],
        mut proof: ExprId,
    ) -> ExprId {
        for k in (0..prefix.len()).rev() {
            let g = self.mono_gen_expr(prefix[k]);
            let mut sub_tail: Vec<MonoGen> = prefix[k + 1..].to_vec();
            sub_tail.extend_from_slice(tail);
            let mut sub_tail2: Vec<MonoGen> = prefix[k + 1..].to_vec();
            sub_tail2.extend_from_slice(tail2);
            let t = self.mono_gens_to_expr(&sub_tail);
            let t2 = self.mono_gens_to_expr(&sub_tail2);
            proof = self.congr_add_right(g, t, t2, proof);
        }
        proof
    }

    /// Prove `Eq R (g0 + (g1 + tail)) (g1 + (g0 + tail))` — an adjacent head swap.
    /// Degree-2 analogue of [`Self::swap_head_eq`] (identical additive proof shape).
    fn mono_swap_head_eq(&mut self, g0: MonoGen, g1: MonoGen, tail: &[MonoGen]) -> ExprId {
        let e0 = self.mono_gen_expr(g0);
        let e1 = self.mono_gen_expr(g1);
        let t = self.mono_gens_to_expr(tail);
        let assoc1 = self.add_assoc_eq(e0, e1, t);
        let lhs = {
            let inner = self.mk_add(e1, t);
            self.mk_add(e0, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e0, e1);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc1);
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
        let t01 = self.eq_trans_r(lhs, mid1, mid2, step1, step2);
        self.eq_trans_r(lhs, mid2, rhs, t01, step3)
    }

    /// Prove `Eq R (g + (g.negate() + tail)) tail` — cancel an adjacent
    /// generator/anti-generator pair at the head. Degree-2 analogue of
    /// [`Self::cancel_head_eq`].
    fn mono_cancel_head_eq(&mut self, g: MonoGen, tail: &[MonoGen]) -> ExprId {
        let gn = g.negate();
        let e = self.mono_gen_expr(g);
        let en = self.mono_gen_expr(gn);
        let t = self.mono_gens_to_expr(tail);
        let assoc = self.add_assoc_eq(e, en, t);
        let lhs = {
            let inner = self.mk_add(en, t);
            self.mk_add(e, inner)
        };
        let mid1 = {
            let inner = self.mk_add(e, en);
            self.mk_add(inner, t)
        };
        let step1 = self.eq_symm_r(mid1, lhs, assoc);
        // Prove `add e en = zero`. For a positive generator (e = p, en = neg p) this
        // is `add_neg p` directly; for a negative one (e = neg p, en = p) commute.
        let e_en = self.mk_add(e, en);
        let e_e_en_zero = if g.neg {
            // e = neg p, en = p ⇒ add (neg p) p = zero via comm + add_neg.
            let p = en;
            let np = e;
            let comm = self.add_comm_eq(np, p);
            let an = self.add_neg_eq(p);
            let lhs_c = self.mk_add(np, p);
            let mid_c = self.mk_add(p, np);
            let zero = self.mk_zero();
            self.eq_trans_r(lhs_c, mid_c, zero, comm, an)
        } else {
            // e = p, en = neg p ⇒ add_neg p.
            self.add_neg_eq(e)
        };
        let zero = self.mk_zero();
        let step2 = self.congr_add_left(e_en, zero, t, e_e_en_zero);
        let comm0 = self.add_comm_eq(zero, t);
        let addz = self.add_zero_eq(t);
        let zt = self.mk_add(zero, t);
        let tz = self.mk_add(t, zero);
        let step3 = self.eq_trans_r(zt, tz, t, comm0, addz);
        let t01 = self.eq_trans_r(lhs, mid1, zt, step1, step2);
        self.eq_trans_r(lhs, zt, t, t01, step3)
    }

    /// Normalize a [`MonoGen`] list to the canonical sorted-and-cancelled list,
    /// returning the canonical generators and a proof
    /// `Eq R (mono_gens_to_expr gens) (mono_gens_to_expr canonical)`. Degree-2
    /// analogue of [`Self::normalize_gens`] (same terminating bubble pass: each
    /// swap strictly decreases the inversion count, each cancel the length).
    fn mono_normalize_gens(&mut self, gens: &[MonoGen]) -> (Vec<MonoGen>, ExprId) {
        let mut cur: Vec<MonoGen> = gens.to_vec();
        let start = self.mono_gens_to_expr(&cur);
        let mut proof = self.eq_refl_r(start);
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
            let before = self.mono_gens_to_expr(&cur);
            if is_cancel {
                let g = cur[i];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.mono_cancel_head_eq(g, &tail);
                let mut from_tail = vec![g, g.negate()];
                from_tail.extend_from_slice(&tail);
                let lifted = self.mono_lift_tail_rewrite(&prefix, &from_tail, &tail, head_proof);
                let mut next = prefix.clone();
                next.extend_from_slice(&tail);
                let after = self.mono_gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            } else {
                let g0 = cur[i];
                let g1 = cur[i + 1];
                let tail = cur[i + 2..].to_vec();
                let head_proof = self.mono_swap_head_eq(g0, g1, &tail);
                let mut from_tail = vec![g0, g1];
                from_tail.extend_from_slice(&tail);
                let mut to_tail = vec![g1, g0];
                to_tail.extend_from_slice(&tail);
                let lifted = self.mono_lift_tail_rewrite(&prefix, &from_tail, &to_tail, head_proof);
                let mut next = prefix.clone();
                next.push(g1);
                next.push(g0);
                next.extend_from_slice(&tail);
                let after = self.mono_gens_to_expr(&next);
                proof = self.eq_trans_r(start, before, after, proof, lifted);
                cur = next;
            }
        }
        (cur, proof)
    }

    /// Prove `Eq R (add canonA canonB) (mono_gens_to_expr(gensA ++ gensB))` — splice
    /// `canonB` into `canonA`'s trailing `zero`. Degree-2 analogue of
    /// [`Self::append_eq`].
    fn mono_append_eq(&mut self, gens_a: &[MonoGen], gens_b: &[MonoGen]) -> ExprId {
        let canon_b = self.mono_gens_to_expr(gens_b);
        if gens_a.is_empty() {
            let zero = self.mk_zero();
            let comm = self.add_comm_eq(zero, canon_b);
            let addz = self.add_zero_eq(canon_b);
            let zt = self.mk_add(zero, canon_b);
            let tz = self.mk_add(canon_b, zero);
            return self.eq_trans_r(zt, tz, canon_b, comm, addz);
        }
        let g = self.mono_gen_expr(gens_a[0]);
        let rest = gens_a[1..].to_vec();
        let canon_rest = self.mono_gens_to_expr(&rest);
        let assoc = self.add_assoc_eq(g, canon_rest, canon_b);
        let lhs = {
            let ca = self.mk_add(g, canon_rest);
            self.mk_add(ca, canon_b)
        };
        let mid = {
            let inner = self.mk_add(canon_rest, canon_b);
            self.mk_add(g, inner)
        };
        let rec = self.mono_append_eq(&rest, gens_b);
        let mut rest_b: Vec<MonoGen> = rest.clone();
        rest_b.extend_from_slice(gens_b);
        let rest_b_expr = self.mono_gens_to_expr(&rest_b);
        let inner_from = self.mk_add(canon_rest, canon_b);
        let step2 = self.congr_add_right(g, inner_from, rest_b_expr, rec);
        let rhs = self.mk_add(g, rest_b_expr);
        self.eq_trans_r(lhs, mid, rhs, assoc, step2)
    }

    /// Prove `Eq R (neg (mono_gens_to_expr gens)) (mono_gens_to_expr neg_gens)` where
    /// `neg_gens` is `gens` with every generator's sign flipped — `neg` distributes
    /// over the right-nested sum (via `neg_add` + `neg_neg`). Used by the `Neg` case
    /// of [`Self::normalize_deg2`].
    fn mono_neg_gens_eq(&mut self, gens: &[MonoGen]) -> ExprId {
        let inner = self.mono_gens_to_expr(gens);
        let neg_inner = self.mk_neg(inner);
        let Some((&head, tail)) = gens.split_first() else {
            // neg zero = zero (= mono_gens_to_expr []). Derive: zero is its own
            // additive inverse, so neg zero = zero by inverse-uniqueness; but more
            // directly, neg zero = neg (add zero zero)? Use add_zero on neg side:
            // neg zero =[symm add_zero (neg zero)] add (neg zero) zero ... simpler:
            // add zero (neg zero) = zero (add_neg zero) and add zero (neg zero)
            // =[add_comm] add (neg zero) zero =[add_zero] neg zero ⇒ neg zero = zero.
            let zero = self.mk_zero();
            let nz = self.mk_neg(zero);
            let an = self.add_neg_eq(zero); // add zero (neg zero) = zero
            let z_nz = self.mk_add(zero, nz);
            let comm = self.add_comm_eq(zero, nz); // add zero (neg zero) = add (neg zero) zero
            let nz_z = self.mk_add(nz, zero);
            let addz = self.add_zero_eq(nz); // add (neg zero) zero = neg zero
            // neg zero = add (neg zero) zero = add zero (neg zero) = zero.
            let s0 = self.eq_symm_r(nz_z, nz, addz); // neg zero = add (neg zero) zero
            let comm_sym = self.eq_symm_r(z_nz, nz_z, comm); // add (neg zero) zero = add zero (neg zero)
            let t01 = self.eq_trans_r(nz, nz_z, z_nz, s0, comm_sym);
            return self.eq_trans_r(nz, z_nz, zero, t01, an);
        };
        // gens = head :: tail. inner = add (mono_gen_expr head) canon_tail.
        let head_e = self.mono_gen_expr(head);
        let canon_tail = self.mono_gens_to_expr(tail);
        // neg (add head canon_tail) =[neg_add] add (neg head)(neg canon_tail).
        let na = self.neg_add_eq(head_e, canon_tail);
        let neg_head = self.mk_neg(head_e);
        let neg_tail = self.mk_neg(canon_tail);
        let na_nt = self.mk_add(neg_head, neg_tail);
        // (neg head) ⟶ mono_gen_expr(head.negate()):
        //   • head positive (e = p): neg p IS mono_gen_expr(neg) — refl.
        //   • head negative (e = neg p): neg (neg p) =[neg_neg] p = mono_gen_expr(neg).
        let head_neg_gen = head.negate();
        let head_neg_e = self.mono_gen_expr(head_neg_gen);
        let neg_head_eq = if head.neg {
            // head_e = neg p, head_neg_e = p ; neg head_e = neg (neg p) = p.
            self.neg_neg_eq(head_neg_e) // neg (neg p) = p
        } else {
            // neg head_e is literally mono_gen_expr(head.negate()).
            self.eq_refl_r(neg_head)
        };
        // (neg canon_tail) ⟶ mono_gens_to_expr(neg tail) by recursion.
        let rec = self.mono_neg_gens_eq(tail);
        let neg_tail_gens: Vec<MonoGen> = tail.iter().map(|g| g.negate()).collect();
        let neg_tail_canon = self.mono_gens_to_expr(&neg_tail_gens);
        // congr both sides of `add (neg head)(neg canon_tail)`.
        let cong_l = self.congr_add_left(neg_head, head_neg_e, neg_tail, neg_head_eq);
        let mid = self.mk_add(head_neg_e, neg_tail);
        let cong_r = self.congr_add_right(head_neg_e, neg_tail, neg_tail_canon, rec);
        let target = self.mk_add(head_neg_e, neg_tail_canon);
        let cong = self.eq_trans_r(na_nt, mid, target, cong_l, cong_r);
        // neg inner = add(neg head)(neg canon_tail) = target = mono_gens_to_expr(neg gens).
        self.eq_trans_r(neg_inner, na_nt, target, na, cong)
    }

    /// Multiply a single signed generator `g` (LHS, degree-≤1) into a generator list
    /// `bs` (degree-≤1): prove
    /// `Eq R (mul (mono_gen_expr g) (mono_gens_to_expr bs)) (mono_gens_to_expr out)`
    /// where `out[k] = product_gen(g, bs[k])`. Distributes with `left_distrib`,
    /// reducing each `mul (mono_gen_expr g)(mono_gen_expr bs[k])` to a single signed
    /// monomial via [`Self::mul_mono_gen_eq`]. Returns `None` if any product exceeds
    /// degree 2 (out of scope — decline).
    fn mul_gen_into_list_eq(
        &mut self,
        g: MonoGen,
        bs: &[MonoGen],
    ) -> Option<(Vec<MonoGen>, ExprId)> {
        let ge = self.mono_gen_expr(g);
        let bs_canon = self.mono_gens_to_expr(bs);
        let lhs = self.mk_mul(ge, bs_canon);
        let Some((&b0, rest)) = bs.split_first() else {
            // mul ge zero = zero (= mono_gens_to_expr []).
            let mz = self.mul_zero_eq(ge); // mul ge zero = zero
            return Some((Vec::new(), mz));
        };
        // mul ge (add b0e rest_canon) =[left_distrib] add (mul ge b0e)(mul ge rest_canon).
        let b0e = self.mono_gen_expr(b0);
        let rest_canon = self.mono_gens_to_expr(rest);
        let ld = self.left_distrib_eq(ge, b0e, rest_canon);
        let ge_b0 = self.mk_mul(ge, b0e);
        let ge_rest = self.mk_mul(ge, rest_canon);
        let sum = self.mk_add(ge_b0, ge_rest);
        // head: mul ge b0e ⟶ single signed monomial `prod0`.
        let (prod0, head_eq) = self.mul_mono_gen_eq(g, b0)?;
        let prod0_e = self.mono_gen_expr(prod0);
        // tail: recurse on `rest`.
        let (out_rest, rest_eq) = self.mul_gen_into_list_eq(g, rest)?;
        let out_rest_canon = self.mono_gens_to_expr(&out_rest);
        // congr both sides of `add (mul ge b0e)(mul ge rest_canon)`.
        let cong_l = self.congr_add_left(ge_b0, prod0_e, ge_rest, head_eq);
        let mid = self.mk_add(prod0_e, ge_rest);
        let cong_r = self.congr_add_right(prod0_e, ge_rest, out_rest_canon, rest_eq);
        let target = self.mk_add(prod0_e, out_rest_canon);
        let cong = self.eq_trans_r(sum, mid, target, cong_l, cong_r);
        let full = self.eq_trans_r(lhs, sum, target, ld, cong);
        // out = prod0 :: out_rest, and target IS mono_gens_to_expr(out).
        let mut out = vec![prod0];
        out.extend_from_slice(&out_rest);
        Some((out, full))
    }

    /// Distribute a full product `(mono_gens_to_expr as) * (mono_gens_to_expr bs)`
    /// of two degree-≤1 generator lists into a sum of signed monomials: prove
    /// `Eq R (mul as_canon bs_canon) (mono_gens_to_expr out)` where `out` is the
    /// Cartesian product of single-generator products. `None` if any product exceeds
    /// degree 2. Recurses on `as` with `right`-distribution (via `mul_comm` +
    /// [`Self::mul_gen_into_list_eq`]).
    fn mul_lists_eq(
        &mut self,
        a_gens: &[MonoGen],
        b_gens: &[MonoGen],
    ) -> Option<(Vec<MonoGen>, ExprId)> {
        let a_canon = self.mono_gens_to_expr(a_gens);
        let b_canon = self.mono_gens_to_expr(b_gens);
        let lhs = self.mk_mul(a_canon, b_canon);
        let Some((&a0, rest)) = a_gens.split_first() else {
            // mul zero b_canon: zero_mul not in prelude ⇒ commute then mul_zero.
            // mul zero b =[mul_comm] mul b zero =[mul_zero] zero.
            let comm = self.mul_comm_eq(a_canon, b_canon); // mul zero b = mul b zero
            let b_zero = self.mk_mul(b_canon, a_canon); // mul b zero
            let mz = self.mul_zero_eq(b_canon); // mul b zero = zero
            let zero = self.mk_zero();
            let eq = self.eq_trans_r(lhs, b_zero, zero, comm, mz);
            return Some((Vec::new(), eq));
        };
        // mul (add a0e rest_canon) b_canon — distribute on the LEFT operand.
        // No right_distrib axiom: commute to `mul b_canon (add a0e rest_canon)`,
        // left_distrib, then commute each product back.
        let a0e = self.mono_gen_expr(a0);
        let rest_canon = self.mono_gens_to_expr(rest);
        let add_a = self.mk_add(a0e, rest_canon); // = a_canon
        // mul add_a b_canon =[mul_comm] mul b_canon add_a.
        let comm0 = self.mul_comm_eq(add_a, b_canon);
        let b_adda = self.mk_mul(b_canon, add_a);
        // mul b_canon (add a0e rest_canon) =[left_distrib] add (mul b_canon a0e)(mul b_canon rest_canon).
        let ld = self.left_distrib_eq(b_canon, a0e, rest_canon);
        let b_a0 = self.mk_mul(b_canon, a0e);
        let b_rest = self.mk_mul(b_canon, rest_canon);
        let sum_b = self.mk_add(b_a0, b_rest);
        // head: mul b_canon a0e =[mul_comm] mul a0e b_canon, then distribute a0 into bs.
        let comm_h = self.mul_comm_eq(b_canon, a0e); // mul b_canon a0e = mul a0e b_canon
        let a0_b = self.mk_mul(a0e, b_canon);
        let (head_out, head_dist) = self.mul_gen_into_list_eq(a0, b_gens)?;
        let head_out_canon = self.mono_gens_to_expr(&head_out);
        let head_eq = self.eq_trans_r(b_a0, a0_b, head_out_canon, comm_h, head_dist);
        // tail: recurse on `rest`. The recursion proves about `mul rest_canon b_canon`
        // (the canonical operand order), but `left_distrib` produced `b_rest =
        // mul b_canon rest_canon`; commute first, then apply the recursive proof.
        let (tail_out, tail_inner_eq) = self.mul_lists_eq(rest, b_gens)?;
        let tail_out_canon = self.mono_gens_to_expr(&tail_out);
        let comm_t = self.mul_comm_eq(b_canon, rest_canon); // b_rest = mul rest_canon b_canon
        let rest_b = self.mk_mul(rest_canon, b_canon);
        let tail_eq = self.eq_trans_r(b_rest, rest_b, tail_out_canon, comm_t, tail_inner_eq);
        // congr both sides of `add (mul b_canon a0e)(mul b_canon rest_canon)`.
        let cong_l = self.congr_add_left(b_a0, head_out_canon, b_rest, head_eq);
        let mid = self.mk_add(head_out_canon, b_rest);
        let cong_r = self.congr_add_right(head_out_canon, b_rest, tail_out_canon, tail_eq);
        // append head_out ++ tail_out to a single right-nested canonical sum.
        let appended = self.mono_append_eq(&head_out, &tail_out);
        let mut out: Vec<MonoGen> = head_out.clone();
        out.extend_from_slice(&tail_out);
        let out_canon = self.mono_gens_to_expr(&out);
        let pre_target = self.mk_add(head_out_canon, tail_out_canon);
        let cong = self.eq_trans_r(sum_b, mid, pre_target, cong_l, cong_r);
        // Chain: lhs =[comm0] b_adda =[ld] sum_b =[cong] pre_target =[appended] out_canon.
        let t01 = self.eq_trans_r(lhs, b_adda, sum_b, comm0, ld);
        let t02 = self.eq_trans_r(lhs, sum_b, pre_target, t01, cong);
        let full = self.eq_trans_r(lhs, pre_target, out_canon, t02, appended);
        Some((out, full))
    }

    /// Reduce a product of two single signed generators (each degree ≤ 1) to a
    /// single signed monomial: prove
    /// `Eq R (mul (mono_gen_expr a)(mono_gen_expr b)) (mono_gen_expr out)`.
    /// Handles the four sign combinations via the derived neg-bridge lemmas
    /// (`mul_neg_right`/`mul_neg_left`/`neg_mul_neg`) and `mul_one`/`mul_comm` for
    /// the constant factor. Returns `None` if either factor is quadratic (the product
    /// would exceed degree 2 — out of scope).
    fn mul_mono_gen_eq(&mut self, a: MonoGen, b: MonoGen) -> Option<(MonoGen, ExprId)> {
        // The unsigned monomial product (both must be degree ≤ 1).
        let (out_mono, base_eq) = self.mul_base_mono_eq(a.mono, b.mono)?;
        let ae = self.mono_expr(a.mono);
        let be = self.mono_expr(b.mono);
        let out_e = self.mono_expr(out_mono);
        // Resulting sign is the XOR of the input signs.
        let out_neg = a.neg ^ b.neg;
        let out_gen = MonoGen {
            mono: out_mono,
            neg: out_neg,
        };
        // The LHS as built by `mono_gen_expr`: `mul (sign ae)(sign be)`.
        let lhs_a = if a.neg { self.mk_neg(ae) } else { ae };
        let lhs_b = if b.neg { self.mk_neg(be) } else { be };
        let lhs = self.mk_mul(lhs_a, lhs_b);
        // Strip the signs down to `mul ae be`, tracking the accumulated outer neg.
        // Case on the sign pattern; `base_eq : Eq R (mul ae be) out_e`.
        let ab = self.mk_mul(ae, be);
        let proof = match (a.neg, b.neg) {
            (false, false) => {
                // lhs = mul ae be IS `ab` (no signs); base_eq : Eq R ab out_e.
                base_eq
            }
            (true, false) => {
                // lhs = mul (neg ae) be =[mul_neg_left] neg (mul ae be) =[congr_neg base] neg out_e.
                let mnl = self.mul_neg_left_eq(ae, be); // mul (neg ae) be = neg (ab)
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq); // neg ab = neg out_e
                self.eq_trans_r(lhs, neg_ab, neg_out, mnl, cong)
            }
            (false, true) => {
                // lhs = mul ae (neg be) =[mul_neg_right] neg (mul ae be) =[congr_neg base] neg out_e.
                let mnr = self.mul_neg_right_eq(ae, be); // mul ae (neg be) = neg ab
                let neg_ab = self.mk_neg(ab);
                let neg_out = self.mk_neg(out_e);
                let cong = self.congr_neg(ab, out_e, base_eq);
                self.eq_trans_r(lhs, neg_ab, neg_out, mnr, cong)
            }
            (true, true) => {
                // lhs = mul (neg ae)(neg be) =[neg_mul_neg] mul ae be =[base] out_e.
                let nmn = self.neg_mul_neg_eq(ae, be); // mul (neg ae)(neg be) = ab
                self.eq_trans_r(lhs, ab, out_e, nmn, base_eq)
            }
        };
        Some((out_gen, proof))
    }

    /// Reduce an UNSIGNED product `mul (mono_expr a)(mono_expr b)` of two degree-≤1
    /// base monomials to a single base monomial, proving
    /// `Eq R (mul (mono_expr a)(mono_expr b)) (mono_expr out)`. `None` if either is
    /// [`Mono::Quad`] (product degree ≥ 3 — out of scope).
    fn mul_base_mono_eq(&mut self, a: Mono, b: Mono) -> Option<(Mono, ExprId)> {
        match (a, b) {
            (Mono::Quad(..), _) | (_, Mono::Quad(..)) => None,
            (Mono::Const, Mono::Const) => {
                // mul one one =[mul_one one] one.
                let one = self.mk_one();
                let mo = self.mul_one_eq(one); // mul one one = one
                Some((Mono::Const, mo))
            }
            (Mono::Const, other) | (other, Mono::Const) => {
                // mul one v =[mul_comm] mul v one =[mul_one] v  (or mul v one directly).
                let one = self.mk_one();
                let ve = self.mono_expr(other);
                // Determine actual operand order in `mul (mono_expr a)(mono_expr b)`.
                let (le, re, is_one_left) = if matches!(a, Mono::Const) {
                    (one, ve, true)
                } else {
                    (ve, one, false)
                };
                let lhs = self.mk_mul(le, re);
                let eq = if is_one_left {
                    // mul one v =[mul_comm] mul v one =[mul_one] v.
                    let comm = self.mul_comm_eq(one, ve);
                    let v_one = self.mk_mul(ve, one);
                    let mo = self.mul_one_eq(ve);
                    self.eq_trans_r(lhs, v_one, ve, comm, mo)
                } else {
                    // mul v one =[mul_one] v.
                    self.mul_one_eq(ve)
                };
                Some((other, eq))
            }
            (Mono::Lin(i), Mono::Lin(j)) => {
                // mul xi xj is already a base monomial `Quad(min,max)`.
                let xi = self.mono_expr(Mono::Lin(i));
                let xj = self.mono_expr(Mono::Lin(j));
                let lhs = self.mk_mul(xi, xj);
                let out = Mono::quad(i, j);
                if i <= j {
                    // out = Quad(i,j) ⇒ mono_expr(out) = mul xi xj = lhs ⇒ refl.
                    Some((out, self.eq_refl_r(lhs)))
                } else {
                    // out = Quad(j,i) ⇒ mono_expr(out) = mul xj xi; lhs = mul xi xj.
                    // mul xi xj =[mul_comm] mul xj xi.
                    let comm = self.mul_comm_eq(xi, xj);
                    Some((out, comm))
                }
            }
        }
    }

    /// `mul_one a : Eq R (mul a one) a`.
    fn mul_one_eq(&mut self, a: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.mul_one, vec![]);
        self.kernel.app(ax, a)
    }

    /// Emit just the faithful kernel `R`-encoding of an [`RExpr`] (no proof). The
    /// kernel hash-conses structurally, so this yields the SAME [`ExprId`] the
    /// normalizer's `kernel_expr` carries for the same `RExpr`.
    fn emit_rexpr(&mut self, expr: &RExpr) -> ExprId {
        match expr {
            RExpr::Var(i) => {
                let name = self.var_const(*i);
                self.kernel.const_(name, vec![])
            }
            RExpr::One => self.mk_one(),
            RExpr::Neg(a) => {
                let ae = self.emit_rexpr(a);
                self.mk_neg(ae)
            }
            RExpr::Add(a, b) => {
                let ae = self.emit_rexpr(a);
                let be = self.emit_rexpr(b);
                self.mk_add(ae, be)
            }
            RExpr::Mul(a, b) => {
                let ae = self.emit_rexpr(a);
                let be = self.emit_rexpr(b);
                self.mk_mul(ae, be)
            }
        }
    }

    /// **Degree-2 ring normalizer** (ADR-0040 generalization). Recursively rewrite an
    /// [`RExpr`] of total degree ≤ 2 into a canonical signed-monomial sum, returning
    /// `(gens, kernel_expr, proof)` with `proof : Eq R kernel_expr (mono_gens_to_expr
    /// gens)` and `gens` the SORTED-AND-CANCELLED canonical generators. `kernel_expr`
    /// is the faithful encoding of the input. Returns `None` (decline) if any
    /// subproduct would exceed degree 2.
    ///
    /// Two `RExpr`s with the SAME canonical `gens` are provably equal over `R`:
    /// `Eq R e1 e2 = trans (proof1) (symm proof2)`. The asserted-polynomial identity
    /// `Eq R pK sqK` is assembled exactly this way (after confirming the two `gens`
    /// agree — which the SOS certificate guarantees, but the reconstructor checks).
    fn normalize_deg2(&mut self, expr: &RExpr) -> Option<(Vec<MonoGen>, ExprId, ExprId)> {
        // First produce the raw (unsorted) gens + a proof `Eq R expr raw_canon`,
        // then run the additive normalizer to sort & cancel.
        let (raw_gens, kernel_expr, raw_proof) = self.normalize_deg2_raw(expr)?;
        let (canon_gens, sort_proof) = self.mono_normalize_gens(&raw_gens);
        let raw_canon = self.mono_gens_to_expr(&raw_gens);
        let canon = self.mono_gens_to_expr(&canon_gens);
        // proof : Eq R expr canon = trans raw_proof sort_proof.
        let proof = self.eq_trans_r(kernel_expr, raw_canon, canon, raw_proof, sort_proof);
        Some((canon_gens, kernel_expr, proof))
    }

    /// The recursive core of [`Self::normalize_deg2`]: returns `(raw_gens,
    /// kernel_expr, proof)` with `proof : Eq R kernel_expr (mono_gens_to_expr
    /// raw_gens)`, where `raw_gens` is NOT yet sorted/cancelled. `None` on a
    /// degree-≥3 subproduct.
    fn normalize_deg2_raw(&mut self, expr: &RExpr) -> Option<(Vec<MonoGen>, ExprId, ExprId)> {
        match expr {
            RExpr::Var(i) => {
                let name = self.var_const(*i);
                let xe = self.kernel.const_(name, vec![]);
                // xi = add xi zero  (symm add_zero).
                let zero = self.mk_zero();
                let xz = self.mk_add(xe, zero);
                let az = self.add_zero_eq(xe); // add xi zero = xi
                let proof = self.eq_symm_r(xz, xe, az); // xi = add xi zero
                Some((vec![MonoGen::pos(Mono::Lin(*i))], xe, proof))
            }
            RExpr::One => {
                let one_e = self.mk_one();
                let zero = self.mk_zero();
                let oz = self.mk_add(one_e, zero);
                let az = self.add_zero_eq(one_e);
                let proof = self.eq_symm_r(oz, one_e, az);
                Some((vec![MonoGen::pos(Mono::Const)], one_e, proof))
            }
            RExpr::Neg(a) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let neg_e = self.mk_neg(a_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                // neg a_e =[congr_neg a_proof] neg a_canon =[neg_gens] canon(neg gens).
                let cong = self.congr_neg(a_e, a_canon, a_proof); // neg a_e = neg a_canon
                let neg_a_canon = self.mk_neg(a_canon);
                let neg_gens: Vec<MonoGen> = a_gens.iter().map(|g| g.negate()).collect();
                let neg_gens_eq = self.mono_neg_gens_eq(&a_gens); // neg a_canon = canon(neg gens)
                let out_canon = self.mono_gens_to_expr(&neg_gens);
                let proof = self.eq_trans_r(neg_e, neg_a_canon, out_canon, cong, neg_gens_eq);
                Some((neg_gens, neg_e, proof))
            }
            RExpr::Add(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_deg2_raw(b)?;
                let add_e = self.mk_add(a_e, b_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                let b_canon = self.mono_gens_to_expr(&b_gens);
                // add a_e b_e =[congr both] add a_canon b_canon =[append] canon(a++b).
                let cong_l = self.congr_add_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_add(a_canon, b_e);
                let cong_r = self.congr_add_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_add(a_canon, b_canon);
                let cong = self.eq_trans_r(add_e, mid, ab_canon, cong_l, cong_r);
                let appended = self.mono_append_eq(&a_gens, &b_gens);
                let mut out: Vec<MonoGen> = a_gens.clone();
                out.extend_from_slice(&b_gens);
                let out_canon = self.mono_gens_to_expr(&out);
                let proof = self.eq_trans_r(add_e, ab_canon, out_canon, cong, appended);
                Some((out, add_e, proof))
            }
            RExpr::Mul(a, b) => {
                let (a_gens, a_e, a_proof) = self.normalize_deg2_raw(a)?;
                let (b_gens, b_e, b_proof) = self.normalize_deg2_raw(b)?;
                let mul_e = self.mk_mul(a_e, b_e);
                let a_canon = self.mono_gens_to_expr(&a_gens);
                let b_canon = self.mono_gens_to_expr(&b_gens);
                // mul a_e b_e =[congr both] mul a_canon b_canon =[distribute] canon(out).
                let cong_l = self.congr_mul_left(a_e, a_canon, b_e, a_proof);
                let mid = self.mk_mul(a_canon, b_e);
                let cong_r = self.congr_mul_right(a_canon, b_e, b_canon, b_proof);
                let ab_canon = self.mk_mul(a_canon, b_canon);
                let cong = self.eq_trans_r(mul_e, mid, ab_canon, cong_l, cong_r);
                let (out, dist) = self.mul_lists_eq(&a_gens, &b_gens)?;
                let out_canon = self.mono_gens_to_expr(&out);
                let proof = self.eq_trans_r(mul_e, ab_canon, out_canon, cong, dist);
                Some((out, mul_e, proof))
            }
        }
    }

    /// Cast the right operand of a `le`: given `h_le : le l r` and
    /// `h_eq : Eq R r r'`, build `le l r'`.
    fn le_cast_right(
        &mut self,
        l: ExprId,
        r: ExprId,
        rp: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        // motive := fun (x : R) (_ : Eq R r x) => le l x.
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_l_x = self.mk_le(l, x1);
            let x0 = self.kernel.bvar(0);
            let eq_r_x = self.mk_eq_r(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, le_l_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(r, motive, h_le, rp, h_eq)
    }

    /// Cast the left operand of a `le`: given `h_le : le l r` and
    /// `h_eq : Eq R l l'`, build `le l' r`.
    fn le_cast_left(
        &mut self,
        l: ExprId,
        lp: ExprId,
        r: ExprId,
        h_le: ExprId,
        h_eq: ExprId,
    ) -> ExprId {
        // motive := fun (x : R) (_ : Eq R l x) => le x r.
        let motive = {
            let x1 = self.kernel.bvar(1);
            let le_x_r = self.mk_le(x1, r);
            let x0 = self.kernel.bvar(0);
            let eq_l_x = self.mk_eq_r(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, le_x_r, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(l, motive, h_le, lp, h_eq)
    }

    /// `add_le_add a b c d h1 h2 : le (add a c) (add b d)`.
    fn add_le_add_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self.kernel.const_(self.arith.add_le_add, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `add_lt_add_of_le_of_lt a b c d h1 h2 : lt (add a c)(add b d)` from
    /// `h1 : le a b`, `h2 : lt c d`. Summing a non-strict with a strict ⇒ strict.
    fn add_lt_add_of_le_of_lt_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let ax = self
            .kernel
            .const_(self.arith.add_lt_add_of_le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, d);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// `le_of_lt a b h : le a b` from `h : lt a b`.
    fn le_of_lt_app(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        let ax = self.kernel.const_(self.arith.le_of_lt, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        self.kernel.app(e, h)
    }

    /// Derived `add_lt_add a b c d h1 h2 : lt (add a c)(add b d)` from
    /// `h1 : lt a b`, `h2 : lt c d`. No new axiom: weaken `h1` to `le a b`
    /// (`le_of_lt`) and apply [`Self::add_lt_add_of_le_of_lt_app`].
    fn add_lt_add_app(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        d: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let h1_le = self.le_of_lt_app(a, b, h1);
        self.add_lt_add_of_le_of_lt_app(a, b, c, d, h1_le, h2)
    }

    /// Cast the left operand of a `lt`: `h_lt : lt l r`, `h_eq : Eq R l l'` ⇒ `lt l' r`.
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
            let eq_l_x = self.mk_eq_r(l, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_l_x, lt_x_r, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(l, motive, h_lt, lp, h_eq)
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
        let ax = self.kernel.const_(self.arith.lt_of_lt_of_le, vec![]);
        let e = self.kernel.app(ax, a);
        let e = self.kernel.app(e, b);
        let e = self.kernel.app(e, c);
        let e = self.kernel.app(e, h1);
        self.kernel.app(e, h2)
    }

    /// Build a proof `lt zero K` where `K = gens_to_expr` of `n ≥ 1` `One` generators,
    /// i.e. `K = one + (one + … + (one + zero))`. Built by partial-sum induction:
    /// `lt zero one` (`zero_lt_one`), then for each extra `one`, extend `lt zero S` to
    /// `lt zero (one + S)` via `le S (one + S)` and `lt_of_lt_of_le`.
    fn lt_zero_ones(&mut self, n: i128) -> ExprId {
        debug_assert!(n >= 1);
        // S_1 = one + zero ; prove lt zero S_1 from zero_lt_one : lt zero one and
        // one =[symm add_zero one] one + zero.
        let one = self.mk_one();
        let zero = self.mk_zero();
        let one_zero = self.mk_add(one, zero); // gens_to_expr([One]) = one + zero
        let zlo = self.kernel.const_(self.arith.zero_lt_one, vec![]); // lt zero one
        // cast the rhs `one → one+zero` using symm (add_zero one) : Eq one (one+zero).
        let addz = self.add_zero_eq(one); // add one zero = one
        let eq_one_onezero = self.eq_symm_r(one_zero, one, addz); // one = one+zero
        // le_cast_right on lt? We only have le_cast for `le`. Build a lt-cast.
        let mut acc = self.lt_cast_right(zero, one, one_zero, zlo, eq_one_onezero); // lt zero (one+zero)
        let mut s_gens = vec![Gen::One];
        for _ in 1..n {
            // Extend acc : lt zero S to lt zero (one + S).
            let s = self.gens_to_expr(&s_gens);
            let mut new_gens = vec![Gen::One];
            new_gens.extend_from_slice(&s_gens);
            let new_s = self.gens_to_expr(&new_gens); // one + S
            // Need le S (one + S). Build via add_le_add: le zero one (le_of_lt zlo)
            //   and le S S (le_refl S) ⇒ le (zero + S)(one + S); then cast lhs zero+S → S.
            let le_zero_one = {
                let lo = self.kernel.const_(self.arith.le_of_lt, vec![]);
                let zlo2 = self.kernel.const_(self.arith.zero_lt_one, vec![]);
                let e = self.kernel.app(lo, zero);
                let e = self.kernel.app(e, one);
                self.kernel.app(e, zlo2)
            }; // le zero one
            let le_s_s = {
                let lr = self.kernel.const_(self.arith.le_refl, vec![]);
                self.kernel.app(lr, s)
            }; // le S S
            // add_le_add zero one S S : le (add zero S)(add one S)
            let combined = self.add_le_add_app(zero, one, s, s, le_zero_one, le_s_s);
            // cast lhs (add zero S) → S via add_comm + add_zero.
            let zs = self.mk_add(zero, s);
            let comm = self.add_comm_eq(zero, s); // add zero S = add S zero
            let addz_s = self.add_zero_eq(s); // add S zero = S
            let sz = self.mk_add(s, zero);
            let eq_zs_s = self.eq_trans_r(zs, sz, s, comm, addz_s); // add zero S = S
            let le_s_news = self.le_cast_left(zs, s, new_s, combined, eq_zs_s); // le S (one+S)
            // lt_of_lt_of_le zero S (one+S) acc le_s_news : lt zero (one+S).
            acc = self.lt_of_lt_of_le_app(zero, s, new_s, acc, le_s_news);
            s_gens = new_gens;
        }
        acc
    }

    /// Cast the right operand of a `lt`: `h_lt : lt l r`, `h_eq : Eq R r r'` ⇒ `lt l r'`.
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
            let eq_r_x = self.mk_eq_r(r, x0);
            let anon = self.kernel.anon();
            let inner = self.kernel.lam(anon, eq_r_x, lt_l_x, BinderInfo::Default);
            let r_ty = self.kernel.const_(self.arith.r, vec![]);
            self.kernel.lam(anon, r_ty, inner, BinderInfo::Default)
        };
        self.eq_rec_transport_r(r, motive, h_lt, rp, h_eq)
    }

    /// Scale-and-sum a list of integer-coefficient atoms `(Eᵢ, μᵢ)` (`μᵢ ≥ 1`) into a
    /// single `rel Lsum zero` proof, where `rel` is `le` when `strict == false` and
    /// `lt` when `strict == true`. Mirrors the non-strict summation inside
    /// [`try_general_farkas`], but routes through the strict combinators when `strict`:
    /// `add_lt_add` for the scale/fold steps and `lt_cast_*` for the renormalizations.
    /// The per-atom hypothesis is `hᵢ : rel Eᵢ zero` (same relation).
    ///
    /// Returns `(proof, gens)` where `gens` is the canonical generator list of `Lsum`
    /// (so `gens_to_expr(gens)` is the proof's LHS), or `None` if any atom has a
    /// non-integer coefficient/constant. The caller normalizes `gens` to the combined
    /// constant. `atoms` must be non-empty.
    fn sum_scaled_atoms(
        &mut self,
        atoms: &[(LinR, i128)],
        strict: bool,
    ) -> Result<Option<(ExprId, Vec<Gen>)>, ReconstructError> {
        let zero = self.mk_zero();
        let mut acc: Option<(ExprId, Vec<Gen>)> = None; // (rel-proof, gens)
        for (lin, mu) in atoms {
            let Some(base_gens) = LraReconstructCtx::lin_to_gens(lin) else {
                return Ok(None);
            };
            let base_expr = self.gens_to_expr(&base_gens);
            // hypothesis hᵢ : rel base_expr zero.
            let prop = if strict {
                self.mk_lt(base_expr, zero)
            } else {
                self.mk_le(base_expr, zero)
            };
            let h = self.hyp_axiom(prop)?;
            // Scale by μᵢ: fold hᵢ with itself μᵢ times, keeping RHS = zero and the LHS
            // in canonical generator form.
            let mut s_proof = h;
            let mut s_gens = base_gens.clone();
            let mut s_expr = base_expr;
            for _ in 1..*mu {
                let combined = if strict {
                    self.add_lt_add_app(s_expr, zero, base_expr, zero, s_proof, h)
                } else {
                    self.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, h)
                };
                let lhs = self.mk_add(s_expr, base_expr);
                // RHS (add zero zero) → zero.
                let azz = self.add_zero_eq(zero);
                let add_zz = self.mk_add(zero, zero);
                let combined = if strict {
                    self.lt_cast_right(lhs, add_zz, zero, combined, azz)
                } else {
                    self.le_cast_right(lhs, add_zz, zero, combined, azz)
                };
                // LHS (add s_expr base_expr) → canonical (s_gens ++ base_gens).
                let mut next_gens = s_gens.clone();
                next_gens.extend_from_slice(&base_gens);
                let append_proof = self.append_eq(&s_gens, &base_gens);
                let next_canon = self.gens_to_expr(&next_gens);
                s_proof = if strict {
                    self.lt_cast_left(lhs, next_canon, zero, combined, append_proof)
                } else {
                    self.le_cast_left(lhs, next_canon, zero, combined, append_proof)
                };
                s_gens = next_gens;
                s_expr = next_canon;
            }
            // Fold this scaled constraint into the accumulator.
            acc = Some(match acc {
                None => (s_proof, s_gens),
                Some((acc_proof, acc_gens)) => {
                    let acc_expr = self.gens_to_expr(&acc_gens);
                    let combined = if strict {
                        self.add_lt_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof)
                    } else {
                        self.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof)
                    };
                    let azz = self.add_zero_eq(zero);
                    let add_zz = self.mk_add(zero, zero);
                    let lhs = self.mk_add(acc_expr, s_expr);
                    let combined = if strict {
                        self.lt_cast_right(lhs, add_zz, zero, combined, azz)
                    } else {
                        self.le_cast_right(lhs, add_zz, zero, combined, azz)
                    };
                    let mut next_gens = acc_gens.clone();
                    next_gens.extend_from_slice(&s_gens);
                    let append_proof = self.append_eq(&acc_gens, &s_gens);
                    let next_canon = self.gens_to_expr(&next_gens);
                    let new_proof = if strict {
                        self.lt_cast_left(lhs, next_canon, zero, combined, append_proof)
                    } else {
                        self.le_cast_left(lhs, next_canon, zero, combined, append_proof)
                    };
                    (new_proof, next_gens)
                }
            });
        }
        Ok(acc)
    }

    /// Build the generator list of a [`LinR`] whose coefficients and constant are all
    /// integers: each variable `(i, c)` contributes `|c|` copies of `Var(i)`/`NegVar(i)`,
    /// then the constant contributes `|k|` copies of `One`/`NegOne`. Returns `None` if
    /// any coefficient or the constant is not an integer (outside this engine's scope).
    fn lin_to_gens(lin: &LinR) -> Option<Vec<Gen>> {
        let mut gens = Vec::new();
        for &(index, coeff) in &lin.coeffs {
            if coeff.denominator() != 1 {
                return None;
            }
            let n = coeff.numerator();
            let (g, count) = if n >= 0 {
                (Gen::Var(index), n)
            } else {
                (Gen::NegVar(index), -n)
            };
            for _ in 0..count {
                gens.push(g);
            }
        }
        if lin.constant.denominator() != 1 {
            return None;
        }
        let k = lin.constant.numerator();
        let (g, count) = if k >= 0 {
            (Gen::One, k)
        } else {
            (Gen::NegOne, -k)
        };
        for _ in 0..count {
            gens.push(g);
        }
        Some(gens)
    }
}

/// Reconstruct a small real `QF_LRA` `unsat` instance into a Lean proof term of
/// type `False` that the trusted [`Kernel`] type-checks, by way of its Farkas
/// (`la_generic`) certificate.
///
/// The instance is `assertions` over `arena`, a conjunction of linear-real order
/// constraints. The certificate is obtained from [`crate::lra_farkas_certificate`]
/// (the real, self-checked Fourier–Motzkin Farkas refutation), so this only
/// returns a term when the instance is genuinely `unsat`. The returned
/// [`ExprId`]'s inferred type is [`Kernel::def_eq`] to the prelude's `False`.
///
/// **Scope (slice 1):** only the *transitivity-reducible* two-constraint shape is
/// reconstructed — an instance equivalent to `e ≤ 0 ∧ 1 ≤ e` over a shared `R`
/// expression `e` with small `{-1,0,+1}` coefficients. This is the baby-Farkas
/// order chain (`le_trans` → `lt_of_le_of_lt` with `zero_lt_one` → `lt_irrefl`),
/// needing no ring sum. Any other cert shape (general multipliers, a ring
/// cancellation, more than two participating constraints, non-`{-1,0,+1}`
/// coefficients) is rejected with a clear error — a later slice.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] if `assertions` is not `unsat`
/// through the Farkas path or its shape is outside slice 1,
/// [`ReconstructError::UnsupportedTerm`] for a constraint outside the small linear
/// subset this slice models, and [`ReconstructError::KernelRejected`] when the
/// kernel's `infer` fails or the inferred proposition is not `def_eq` to `False`.
/// It never panics on out-of-scope input.
#[allow(dead_code)]
pub fn reconstruct_lra_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    // Obtain the REAL, self-checked Farkas certificate. `None` ⇒ the instance is
    // not unsat through the Farkas path (sat, or a trivially-false assertion).
    let certificate = match crate::lra_farkas_certificate(arena, assertions) {
        Ok(Some(cert)) => cert,
        Ok(None) => {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: "instance is not unsat through the Farkas path (sat or trivial)".to_owned(),
            });
        }
        Err(e) => {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: format!("LRA decision failed: {e}"),
            });
        }
    };
    // Strict-`<` cycle `e0<e1<…<e_{n-1}<e0` (n≥2): fold `lt_trans` to `lt e0 e0`,
    // then `lt_irrefl`. Tried first; falls through to the `≤` baby-Farkas shape.
    if let Some(proof) = try_strict_cycle(ctx, arena, assertions, &certificate)? {
        return Ok(proof);
    }
    // Mixed strict/non-strict Farkas: at least one used atom is strict (`<`) and the
    // combination is not a pure strict cycle. Sum the strict atoms into `lt Lst 0`, the
    // non-strict into `le Lne 0`, combine to `lt (Lst+Lne) 0`, normalize to the constant
    // `K ≥ 0`, and close (`lt_irrefl` directly for `K = 0`, or via `lt_trans` with
    // `0 < K` otherwise). Tried before the pure non-strict engine, which rejects strict
    // atoms.
    if let Some(proof) = try_mixed_farkas(ctx, &certificate)? {
        return Ok(proof);
    }
    // General Farkas over non-strict integer-coefficient constraints with arbitrary
    // nonnegative (rational, denominator-cleared) multipliers: scale every used
    // `Eᵢ ≤ 0` atom by an integer `μᵢ`, sum with `add_le_add`, normalize the sum's
    // variable terms to cancel (the ring engine), and close `K ≤ 0` against `0 < K`.
    if let Some(proof) = try_general_farkas(ctx, &certificate)? {
        return Ok(proof);
    }
    reconstruct_transitivity_refutation(ctx, arena, assertions, &certificate)
}

/// Reconstruct the **trivial single-square sum-of-squares** refutation
/// (ADR-0040, SOS slice 1): the one-variable real query `x*x < 0`, which is UNSAT
/// because a real square is never negative.
///
/// This is the simplest SOS reconstruction and needs **no ring normalizer** — the
/// SOS identity `x² = 1·x²` is trivial — so the proof is just unconditional
/// square-nonnegativity composed with one order step:
///
/// 1. `sq  : le zero (mul x x)` := `sq_nonneg x` (the prelude's unconditional
///    square-nonnegativity axiom applied to the variable term `x`).
/// 2. `hlt : lt (mul x x) zero` — the asserted atom `x*x < 0`, introduced as a
///    hypothesis axiom (mirroring how the LRA baby-Farkas path discharges its
///    asserted constraints via `LraReconstructCtx::hyp_axiom`).
/// 3. `chain : lt zero zero` := `lt_of_le_of_lt zero (mul x x) zero sq hlt`.
/// 4. `bad : False` := `lt_irrefl zero chain` (since
///    `lt_irrefl zero : Not (lt zero zero) = lt zero zero → False`).
///
/// The returned [`ExprId`] infers to `False` and is gated (`infer` + `def_eq
/// False`) here; a wrong reconstruction is [`ReconstructError::KernelRejected`],
/// never an accepted unsound proof.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedTerm`] for **anything but** the trivial
/// single-square shape `mul x x < 0` over one real variable (general SOS such as
/// `(x − y)² < 0` is a later slice and is declined here), or
/// [`ReconstructError::KernelRejected`] if the assembled term fails to kernel-check
/// to `False`.
pub fn reconstruct_sos_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    // Accept the single-square shape `ℓ*ℓ < 0` where `ℓ` is a linear form in
    // `lin_to_r`'s slice (a bare variable `x`, or `(x−y)`, etc.). The asserted lhs
    // is literally `ℓ·ℓ`, so no ring normalizer is needed.
    //
    // Otherwise try the degree-2 two-variable AM-GM sum form `x²+y²−2xy < 0` —
    // the first shape needing the ring normalizer (the lhs is a *sum* of
    // monomials, proven equal to `(x−y)·(x−y)` in the kernel before
    // square-nonnegativity applies).
    //
    // Anything else (a coefficient outside ±1, other monomial sets, ≥ 3 variables)
    // is declined here so we never claim success without a kernel-checked term.
    let Some(factor) = is_single_square_lt_zero(arena, assertions) else {
        // Fast path: the hard-coded two-variable AM-GM shape (kept working).
        if let Some((sx, sy)) = is_am_gm_two_var(arena, assertions) {
            return reconstruct_am_gm_two_var(ctx, sx, sy);
        }
        // General path: any query whose SOS certificate is a single perfect square
        // of a ±1-coefficient linear form (e.g. `(x+y)² < 0`, `(x−z)² < 0`). Driven
        // by the SOS certificate (not a per-shape IR matcher) and the degree-2 ring
        // normalizer. Declines (falls through to the error) for multi-square / `d≠1`
        // / scaled-coefficient certificates.
        if let Some(proof) = reconstruct_sos_single_unit_square(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // General path: any query whose SOS certificate is a SUM of several perfect
        // squares of ±1-coefficient linear forms (e.g. `x²+y² < 0`, `x²+y²+z² < 0`),
        // every `d = 1`, zero affine. Folds square-nonnegativity over the squares.
        if let Some(proof) = reconstruct_sos_multi_unit_square(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // General path: any query whose SOS certificate is a RATIONAL-weight sum of
        // squares `p = Σ dₖ·ℓₖ²` (rational weights, rational/integer linear forms,
        // zero affine) — unlocks 3-variable AM-GM. Clears denominators so the proof
        // reduces to the integer fold (`M·p = Σ(M·wₖ)(ℓₖ⁺)²`); no scaling lemma.
        if let Some(proof) = reconstruct_sos_rational_weight(ctx, arena, assertions)? {
            return Ok(proof);
        }
        // Strict-inequality DUAL: any query whose SOS certificate refutes `p > 0`
        // (`strict_lt == false`) — the certificate's squares decompose `−p`. Mirrors
        // the `p < 0` rational-weight fold, closing via the exact `sosK + mpK = 0`
        // cancellation (sosK = `−(M·p)`, mpK = `M·p`).
        if let Some(proof) = reconstruct_sos_rational_weight_gt(ctx, arena, assertions)? {
            return Ok(proof);
        }
        return Err(ReconstructError::UnsupportedTerm {
            term: "SOS reconstruction handles a single square `ℓ*ℓ < 0` of a ±1-coefficient \
                   linear form ℓ, the two-variable AM-GM sum form `x²+y²−2xy < 0`, any query \
                   whose SOS certificate is a single perfect square, a SUM of ±1-unit \
                   squares (every d=1, zero affine), and a RATIONAL-weight sum of squares \
                   (denominator-cleared); higher-degree / nonzero-affine SOS is a later slice"
                .to_owned(),
        });
    };

    // Map the repeated linear factor `ℓ` to its `R`-typed kernel term (the same
    // faithful encoding the LRA reconstruction trusts; the bare-variable case
    // `ℓ = x` collapses to a single `var_const`). `sq_nonneg` is ∀-valid, so it
    // discharges `0 ≤ ℓ·ℓ` for this `ℓ` regardless of its sign.
    let lin = real_to_lin(arena, factor).ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: "SOS single-square factor is not a linear form".to_owned(),
    })?;
    let ell = ctx.lin_to_r(&lin)?;
    let zero = ctx.mk_zero();
    let xx = ctx.mk_mul(ell, ell);

    // 1. sq : le zero (mul ℓ ℓ)  :=  sq_nonneg ℓ.
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };

    // 2. hlt : lt (mul ℓ ℓ) zero — the asserted atom `ℓ*ℓ < 0` as a hypothesis.
    let hlt = {
        let prop = ctx.mk_lt(xx, zero);
        ctx.hyp_axiom(prop)?
    };

    // 3. chain : lt zero zero  :=  lt_of_le_of_lt zero (mul ℓ ℓ) zero sq hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, xx);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, sq);
        ctx.kernel_mut().app(e, hlt)
    };

    // 4. bad : False  :=  lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_single_square".to_owned(),
            detail: format!("SOS infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_single_square".to_owned(),
            detail: "SOS single-square refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the degree-2 two-variable **AM-GM sum form** `x²+y²−2xy < 0` to a
/// kernel-checked `False` (ADR-0040, the first SOS shape needing the ring
/// normalizer). The asserted lhs is a *sum of monomials*, not a literal `ℓ·ℓ`,
/// so the crux is a kernel-proven ring identity `Eq R p ((x−y)·(x−y))` over which
/// square-nonnegativity is transported.
///
/// Variable symbols are mapped deterministically: `sx → index 0`, `sy → index 1`.
/// The faithful kernel encoding of the asserted lhs `RealSub(A, B)` is
/// `pK = add A (neg B)` with `A = add (mul x x)(mul y y)` and
/// `B = add (mul x y)(mul x y)` — denotationally `x² + y² − 2xy`.
///
/// The reconstruction:
/// 1. builds `pK`, `ellK = add x (neg y)`, `sqK = mul ellK ellK`;
/// 2. proves the ring identity `idK : Eq R pK sqK` (the crux, via
///    [`LraReconstructCtx`]'s additive+multiplicative `Eq R` engine);
/// 3. `sq : le zero sqK := sq_nonneg ellK`;
/// 4. transports nonnegativity back along `idK` to `lep : le zero pK`;
/// 5. closes `lt_of_le_of_lt 0 pK 0 lep hlt : lt 0 0` (with `hlt : lt pK 0` the
///    asserted atom) and refutes it with `lt_irrefl 0`.
///
/// Kernel-gated: the assembled term must `infer` to `False`.
#[allow(clippy::too_many_lines)]
fn reconstruct_am_gm_two_var(
    ctx: &mut LraReconstructCtx,
    _sx: axeyum_ir::SymbolId,
    _sy: axeyum_ir::SymbolId,
) -> Result<ExprId, ReconstructError> {
    // --- kernel atoms --------------------------------------------------------
    let xk = {
        let n = ctx.var_const(0);
        ctx.kernel_mut().const_(n, vec![])
    };
    let yk = {
        let n = ctx.var_const(1);
        ctx.kernel_mut().const_(n, vec![])
    };
    let nyk = ctx.mk_neg(yk);
    let ell = ctx.mk_add(xk, nyk); // x + (-y) = x − y
    let sqk = ctx.mk_mul(ell, ell); // (x−y)·(x−y)

    // Monomial atoms.
    let xx = ctx.mk_mul(xk, xk); // x·x
    let yy = ctx.mk_mul(yk, yk); // y·y
    let xy = ctx.mk_mul(xk, yk); // x·y
    let nxy = ctx.mk_neg(xy); // −(x·y)

    // pK = add (add xx yy) (neg (add xy xy)) — faithful `x²+y²−(xy+xy)`.
    let xx_yy = ctx.mk_add(xx, yy);
    let xy_xy = ctx.mk_add(xy, xy);
    let neg_xy_xy = ctx.mk_neg(xy_xy);
    let pk = ctx.mk_add(xx_yy, neg_xy_xy);

    // Canonical join target S = add xx (add yy (add nxy nxy)).
    let nxy_nxy = ctx.mk_add(nxy, nxy);
    let yy_tail = ctx.mk_add(yy, nxy_nxy);
    let s = ctx.mk_add(xx, yy_tail);

    // --- pK → S (purely additive) -------------------------------------------
    // step1: neg(add xy xy) ⟶ add nxy nxy  (lift neg over the inner add).
    let neg_add = ctx.neg_add_eq(xy, xy); // neg(xy+xy) = (-xy)+(-xy)
    let p_step1 = ctx.congr_add_right(xx_yy, neg_xy_xy, nxy_nxy, neg_add);
    // p1 = add (add xx yy) (add nxy nxy).
    let p1 = ctx.mk_add(xx_yy, nxy_nxy);
    // step2: reassociate (xx+yy)+(nxy+nxy) ⟶ xx+(yy+(nxy+nxy)) = S.
    let p_step2 = ctx.add_assoc_eq(xx, yy, nxy_nxy); // (xx+yy)+T = xx+(yy+T)
    let pk_to_s = ctx.eq_trans_r(pk, p1, s, p_step1, p_step2);

    // --- sqK → S (the ring expansion) ---------------------------------------
    // d1: mul ell ell = add (mul ell x)(mul ell (neg y))  (left_distrib on the
    // right operand ell = add x (neg y); `mul ell ell` IS `mul ell (add x (neg y))`).
    let a_term = ctx.mk_mul(ell, xk); // mul ell x
    let b_term = ctx.mk_mul(ell, nyk); // mul ell (neg y)
    let e1 = ctx.mk_add(a_term, b_term);
    let d1 = ctx.left_distrib_eq(ell, xk, nyk); // sqK = add A B

    // A = mul ell x ⟶ add xx nxy.
    let a_eq = {
        // mul (x+(-y)) x =[mul_comm] mul x (x+(-y))
        let comm = ctx.mul_comm_eq(ell, xk); // mul ell x = mul x ell
        let x_ell = ctx.mk_mul(xk, ell); // mul x (x+(-y))
        // mul x (x+(-y)) =[left_distrib] add (mul x x)(mul x (neg y)) = add xx (mul x (neg y))
        let ld = ctx.left_distrib_eq(xk, xk, nyk);
        let x_ny = ctx.mk_mul(xk, nyk); // mul x (neg y)
        let xx_xny = ctx.mk_add(xx, x_ny); // add xx (mul x (neg y))
        let comm_ld = ctx.eq_trans_r(a_term, x_ell, xx_xny, comm, ld);
        // mul x (neg y) =[mul_neg_right] neg (mul x y) = nxy.
        let mnr = ctx.mul_neg_right_eq(xk, yk); // mul x (neg y) = neg (x·y)
        let xx_nxy = ctx.mk_add(xx, nxy);
        let cong = ctx.congr_add_right(xx, x_ny, nxy, mnr); // add xx (x·(-y)) = add xx nxy
        ctx.eq_trans_r(a_term, xx_xny, xx_nxy, comm_ld, cong)
    };
    let xx_nxy = ctx.mk_add(xx, nxy);

    // B = mul ell (neg y) ⟶ add nxy yy.
    let b_eq = {
        // mul (x+(-y)) (neg y) =[mul_comm] mul (neg y) (x+(-y))
        let comm = ctx.mul_comm_eq(ell, nyk); // mul ell (neg y) = mul (neg y) ell
        let ny_ell = ctx.mk_mul(nyk, ell);
        // mul (neg y) (x+(-y)) =[left_distrib] add (mul (neg y) x)(mul (neg y)(neg y))
        let ld = ctx.left_distrib_eq(nyk, xk, nyk);
        let ny_x = ctx.mk_mul(nyk, xk); // mul (neg y) x
        let ny_ny = ctx.mk_mul(nyk, nyk); // mul (neg y)(neg y)
        let ny_x_plus = ctx.mk_add(ny_x, ny_ny);
        let comm_ld = ctx.eq_trans_r(b_term, ny_ell, ny_x_plus, comm, ld);
        // mul (neg y) x =[mul_neg_left] neg (mul y x) =[congr_neg mul_comm] neg (mul x y) = nxy.
        let mnl = ctx.mul_neg_left_eq(yk, xk); // mul (neg y) x = neg (y·x)
        let yx = ctx.mk_mul(yk, xk);
        let neg_yx = ctx.mk_neg(yx);
        let comm_yx = ctx.mul_comm_eq(yk, xk); // y·x = x·y
        let cong_neg = ctx.congr_neg(yx, xy, comm_yx); // neg(y·x) = neg(x·y) = nxy
        let ny_x_to_nxy = ctx.eq_trans_r(ny_x, neg_yx, nxy, mnl, cong_neg);
        // mul (neg y)(neg y) =[neg_mul_neg] mul y y = yy.
        let nmn = ctx.neg_mul_neg_eq(yk, yk); // (neg y)(neg y) = y·y = yy
        // congr both sides of `add (mul (neg y) x)(mul (neg y)(neg y))`.
        let nxy_plus = ctx.mk_add(nxy, ny_ny);
        let cong_l = ctx.congr_add_left(ny_x, nxy, ny_ny, ny_x_to_nxy);
        let nxy_yy = ctx.mk_add(nxy, yy);
        let cong_r = ctx.congr_add_right(nxy, ny_ny, yy, nmn);
        let cong_both = ctx.eq_trans_r(ny_x_plus, nxy_plus, nxy_yy, cong_l, cong_r);
        ctx.eq_trans_r(b_term, ny_x_plus, nxy_yy, comm_ld, cong_both)
    };
    let nxy_yy = ctx.mk_add(nxy, yy);

    // E1 = add A B ⟶ E2 = add (add xx nxy)(add nxy yy) (congr both sides).
    let e2 = ctx.mk_add(xx_nxy, nxy_yy);
    let e1_to_e2 = {
        let cong_l = ctx.congr_add_left(a_term, xx_nxy, b_term, a_eq);
        let mid = ctx.mk_add(xx_nxy, b_term);
        let cong_r = ctx.congr_add_right(xx_nxy, b_term, nxy_yy, b_eq);
        ctx.eq_trans_r(e1, mid, e2, cong_l, cong_r)
    };

    // E2 = (xx+nxy)+(nxy+yy) ⟶ S = xx+(yy+(nxy+nxy)).
    let e2_to_s = {
        // assoc: (xx+nxy)+(nxy+yy) = xx + (nxy + (nxy+yy)).
        let assoc = ctx.add_assoc_eq(xx, nxy, nxy_yy);
        let nxy_nxyyy = ctx.mk_add(nxy, nxy_yy); // nxy + (nxy + yy)
        let m1 = ctx.mk_add(xx, nxy_nxyyy); // xx + (nxy+(nxy+yy))
        // tail reorder: nxy+(nxy+yy) ⟶ (nxy+nxy)+yy ⟶ yy+(nxy+nxy).
        let assoc_tail = ctx.add_assoc_eq(nxy, nxy, yy); // (nxy+nxy)+yy = nxy+(nxy+yy)
        let nxynxy_yy = ctx.mk_add(nxy_nxy, yy); // (nxy+nxy)+yy
        let tail1 = ctx.eq_symm_r(nxynxy_yy, nxy_nxyyy, assoc_tail); // nxy+(nxy+yy) = (nxy+nxy)+yy
        let comm_tail = ctx.add_comm_eq(nxy_nxy, yy); // (nxy+nxy)+yy = yy+(nxy+nxy)
        let tail_eq = ctx.eq_trans_r(nxy_nxyyy, nxynxy_yy, yy_tail, tail1, comm_tail);
        // lift into xx + _ : m1 ⟶ S.
        let lift = ctx.congr_add_right(xx, nxy_nxyyy, yy_tail, tail_eq);
        ctx.eq_trans_r(e2, m1, s, assoc, lift)
    };

    // sqK ⟶ E1 ⟶ E2 ⟶ S.
    let sq_to_e2 = ctx.eq_trans_r(sqk, e1, e2, d1, e1_to_e2);
    let sqk_to_s = ctx.eq_trans_r(sqk, e2, s, sq_to_e2, e2_to_s);

    // --- idK : Eq R pK sqK  ⟵  trans (pK→S) (symm sqK→S) --------------------
    let s_to_sqk = ctx.eq_symm_r(sqk, s, sqk_to_s); // S = sqK
    let idk = ctx.eq_trans_r(pk, s, sqk, pk_to_s, s_to_sqk);

    // --- nonnegativity + order chain ----------------------------------------
    let zero = ctx.mk_zero();
    // sq : le zero sqK := sq_nonneg ell.
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };
    // lep : le zero pK — transport `sq` backwards along idK (rewrite sqK ⟶ pK,
    // i.e. cast the right operand of `le zero _` along symm idK : Eq R sqK pK).
    let id_sym = ctx.eq_symm_r(pk, sqk, idk); // Eq R sqK pK
    let lep = ctx.le_cast_right(zero, sqk, pk, sq, id_sym);

    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };

    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_am_gm_two_var".to_owned(),
            detail: format!("AM-GM SOS infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_am_gm_two_var".to_owned(),
            detail: "AM-GM SOS refutation did not infer to False".to_owned(),
        })
    }
}

/// Maximum integer coefficient magnitude the SOS-certificate reconstructor expands
/// into repeated monomial generators. `ℓ²` of a ±1-linear form has coefficients in
/// `{−2, −1, 0, 1, 2}` (the cross term `2xᵢxⱼ`), so a small bound suffices; a larger
/// one would only inflate proof size. Outside this bound we decline.
const SOS_MAX_COEFF: i128 = 16;

/// Build the [`RExpr`] for the certificate polynomial term `(factors, coeff)`'s
/// monomial (ignoring the sign/magnitude of `coeff`): a [`RExpr::One`] for the
/// constant, a [`RExpr::Var`] for a linear term, a [`RExpr::Mul`] of two vars for a
/// quadratic term, and a `Var·Var` for a square (`xᵢ²`). Returns `None` (decline)
/// for any factor of total degree ≥ 3 or an out-of-range/malformed shape.
fn cert_mono_to_rexpr(factors: &[(usize, u32)], n_vars: usize) -> Option<RExpr> {
    match factors {
        [] => Some(RExpr::One),
        [(i, 1)] if *i < n_vars => Some(RExpr::Var(*i)),
        [(i, 2)] if *i < n_vars => Some(RExpr::Mul(
            Box::new(RExpr::Var(*i)),
            Box::new(RExpr::Var(*i)),
        )),
        [(i, 1), (j, 1)] if *i < n_vars && *j < n_vars => Some(RExpr::Mul(
            Box::new(RExpr::Var(*i)),
            Box::new(RExpr::Var(*j)),
        )),
        _ => None,
    }
}

/// Build the [`RExpr`] for the **asserted polynomial** `p` from the certificate's
/// indexed monomials: a left-nested `add` over `coeff`-many copies of each monomial
/// (sign-adjusted), in the certificate's deterministic `BTreeMap` order. The result
/// is a faithful kernel encoding of `p` over canonical indices `var_const(i)` (the
/// SAME indices `ellK` uses). `None` (decline) on a non-integer coefficient, a
/// coefficient exceeding [`SOS_MAX_COEFF`] in magnitude, a degree-≥3 monomial, or an
/// empty polynomial.
fn cert_poly_to_rexpr(terms: &[(Vec<(usize, u32)>, Rational)], n_vars: usize) -> Option<RExpr> {
    let mut atoms: Vec<RExpr> = Vec::new();
    for (factors, coeff) in terms {
        if coeff.denominator() != 1 {
            return None; // non-integer coefficient — outside this slice
        }
        let c = coeff.numerator();
        if c == 0 {
            continue;
        }
        if c.abs() > SOS_MAX_COEFF {
            return None; // coefficient too large to expand into unit monomials
        }
        let base = cert_mono_to_rexpr(factors, n_vars)?;
        let count = c.unsigned_abs();
        for _ in 0..count {
            let term = if c < 0 {
                RExpr::Neg(Box::new(base.clone()))
            } else {
                base.clone()
            };
            atoms.push(term);
        }
    }
    let mut iter = atoms.into_iter();
    let first = iter.next()?; // empty ⇒ decline (no atom to refute)
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// Build the [`RExpr`] for the single square `ℓ = Σⱼ cⱼ·xⱼ` from its signed unit
/// coefficients (each `±1`): a left-nested `add` over `xⱼ` / `neg xⱼ`. `cⱼ` are
/// over the same canonical indices as [`cert_poly_to_rexpr`].
fn cert_square_to_rexpr(coeffs: &[(usize, i128)]) -> Option<RExpr> {
    let mut iter = coeffs.iter().map(|&(idx, c)| {
        if c < 0 {
            RExpr::Neg(Box::new(RExpr::Var(idx)))
        } else {
            RExpr::Var(idx)
        }
    });
    let first = iter.next()?;
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a SINGLE perfect square of a ±1-coefficient linear form
/// `ℓ = Σⱼ ±xⱼ` (with `d = 1` and a zero affine row). Generalizes
/// [`reconstruct_am_gm_two_var`] off the hard-coded `(x−y)²` shape via the degree-2
/// ring normalizer ([`LraReconstructCtx::normalize_deg2`]).
///
/// Returns:
/// - `Ok(Some(proof))` — a kernel-checked `False` (gated by `infer` + `def_eq`).
/// - `Ok(None)` — the certificate is not a single ±1-unit square (decline; the
///   caller falls through), or building `pK`/`ellK` hit this slice's bounds.
/// - `Err(_)` — only a genuine kernel rejection (a buggy normalizer would surface
///   here, never an unsound `False`).
///
/// The crux is the ring identity `idK : Eq R pK sqK`, assembled as
/// `trans (normalize pK) (symm (normalize sqK))` **after** confirming the two
/// normal forms are identical — which the certificate guarantees (`p = ℓ²` over ℚ)
/// but this function re-checks, declining if they disagree rather than fabricating.
fn reconstruct_sos_single_unit_square(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    // Obtain the self-checked SOS certificate of the (conjunction of) assertion(s).
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    // This slice handles only the `p < 0` (M PSD) atom shape, as a single ±1 square.
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(square_coeffs) = cert.single_unit_square() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Build pK (faithful encoding of the asserted polynomial p) and ellK (the square
    // root ℓ), both over the SAME canonical indices. `sqK = mul ellK ellK`.
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };
    let Some(ell_rexpr) = cert_square_to_rexpr(&square_coeffs) else {
        return Ok(None);
    };
    let sq_rexpr = RExpr::Mul(Box::new(ell_rexpr.clone()), Box::new(ell_rexpr.clone()));

    // Normalize both to canonical signed-monomial sums, each with its Eq-proof.
    let Some((p_gens, pk, p_to_canon)) = ctx.normalize_deg2(&p_rexpr) else {
        return Ok(None);
    };
    let Some((sq_gens, sqk, sq_to_canon)) = ctx.normalize_deg2(&sq_rexpr) else {
        return Ok(None);
    };

    // Re-check the certificate's promise `p = ℓ²` at the canonical-form level: the
    // two normal forms MUST be identical (the normalizer sorts deterministically, so
    // equal multisets of monomials ⇒ identical gen vectors). If they disagree, the
    // certificate/normalizer is not what we think — decline, never fabricate `idK`.
    if p_gens != sq_gens {
        return Ok(None);
    }

    // idK : Eq R pK sqK := trans (pK → canon) (symm (sqK → canon)).
    let canon = ctx.mono_gens_to_expr(&p_gens);
    let canon_to_sq = ctx.eq_symm_r(sqk, canon, sq_to_canon); // Eq R canon sqK
    let idk = ctx.eq_trans_r(pk, canon, sqk, p_to_canon, canon_to_sq); // Eq R pK sqK

    // Nonnegativity + order chain (mirrors `reconstruct_am_gm_two_var`).
    // ellK is the `mul` LHS/RHS of sqK; emit it directly (same hash-consed ExprId).
    let ell = ctx.emit_rexpr(&ell_rexpr);
    let zero = ctx.mk_zero();
    // sq : le zero sqK := sq_nonneg ell. (sqK = mul ell ell faithfully.)
    let sq = {
        let sq_nonneg_name = ctx.arith().sq_nonneg;
        let sq_nonneg = ctx.kernel_mut().const_(sq_nonneg_name, vec![]);
        ctx.kernel_mut().app(sq_nonneg, ell)
    };
    // lep : le zero pK — transport `sq` backward along symm idK (rewrite sqK ⟶ pK).
    let id_sym = ctx.eq_symm_r(pk, sqk, idk); // Eq R sqK pK
    let lep = ctx.le_cast_right(zero, sqk, pk, sq, id_sym);
    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };
    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate: the assembled term must kernel-infer to `False`. A buggy
    // normalizer makes this fail (KernelRejected), never an accepted unsound proof.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_single_unit_square".to_owned(),
            detail: format!("SOS certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_single_unit_square".to_owned(),
            detail: "SOS certificate refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a **SUM of perfect squares** of ±1-coefficient linear forms
/// `ℓ₁..ℓₘ` (every `D[k] = 1`, zero affine row). Generalizes
/// [`reconstruct_sos_single_unit_square`] (the `m = 1` case) by folding
/// square-nonnegativity over several squares.
///
/// Returns:
/// - `Ok(Some(proof))` — a kernel-checked `False` (gated by `infer` + `def_eq`).
/// - `Ok(None)` — the certificate is not a sum of ±1-unit squares (decline; the
///   caller falls through), or building the kernel terms hit this slice's bounds,
///   or the two normal forms disagree (never fabricate the ring identity).
/// - `Err(_)` — only a genuine kernel rejection.
///
/// Construction:
/// - `sosK = add (ℓ₁·ℓ₁) (add (ℓ₂·ℓ₂) (… (ℓₘ·ℓₘ)))` — a RIGHT-nested `add` of the
///   squares with the last square as the innermost leaf (NO trailing zero, so the
///   kernel `sosK` is exactly the faithful encoding the normalizer returns).
/// - `idK : Eq R pK sosK := trans (normalize pK) (symm (normalize sosK))`, only
///   after confirming the canonical gens are identical (else decline).
/// - `nn : le zero sosK` folds from the innermost (last) square outward. Base case
///   (the `m`-th square): `sq_nonneg ℓₘ : le zero (ℓₘ·ℓₘ)`. Then for each earlier
///   square `ℓₖ` (k = m-1 … 1) combine `sq_nonneg ℓₖ : le zero (ℓₖ·ℓₖ)` with the
///   running `le zero tail` via
///   `add_le_add zero (ℓₖ·ℓₖ) zero tail … : le (add zero zero)(add (ℓₖ·ℓₖ) tail)`,
///   then cast the lhs `add zero zero → zero` (`add_zero zero`) so the type stays
///   `le zero (add (ℓₖ·ℓₖ) tail)` — matching `sosK`'s exact right-nesting.
/// - transport `nn` along `idK` to `lep : le zero pK`, then `lt_of_le_of_lt` with
///   the asserted `hlt : lt pK zero` ⇒ `lt zero zero`, refuted by `lt_irrefl zero`.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_multi_unit_square(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(squares) = cert.unit_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Faithful encoding of the asserted polynomial p.
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the linear form ℓₖ as an RExpr (for emit) and the square sub-RExpr
    // (ℓₖ·ℓₖ).
    let mut ell_rexprs: Vec<RExpr> = Vec::with_capacity(squares.len());
    let mut sq_rexprs: Vec<RExpr> = Vec::with_capacity(squares.len());
    for sq_coeffs in &squares {
        let Some(ell) = cert_square_to_rexpr(sq_coeffs) else {
            return Ok(None);
        };
        sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
        ell_rexprs.push(ell);
    }

    // sosK as an RExpr: RIGHT-nested add over the squares, last square as the
    // innermost LEAF (no trailing zero). E.g. for m=3:
    //   add sq_0 (add sq_1 sq_2).
    // The kernel `sosK` is then EXACTLY the faithful encoding `normalize_deg2`
    // returns for this RExpr, so no bridge between the fold's `sosK` and the
    // normalized form is needed.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // Normalize p and the SOS sum; the canonical gens MUST agree (else decline).
    let Some((p_gens, pk, p_to_canon)) = ctx.normalize_deg2(&p_rexpr) else {
        return Ok(None);
    };
    let Some((sos_gens, sosk, sos_to_canon)) = ctx.normalize_deg2(&sos_rexpr) else {
        return Ok(None);
    };
    if p_gens != sos_gens {
        return Ok(None);
    }

    // idK : Eq R pK sosK := trans (pK → canon)(symm (sosK → canon)).
    let canon = ctx.mono_gens_to_expr(&p_gens);
    let canon_to_sos = ctx.eq_symm_r(sosk, canon, sos_to_canon); // Eq R canon sosK
    let idk = ctx.eq_trans_r(pk, canon, sosk, p_to_canon, canon_to_sos); // Eq R pK sosK

    // Kernel-level per-square ℓₖ and (ℓₖ·ℓₖ), emitted from the SAME RExprs so the
    // `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(squares.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(squares.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold: nn : le zero sosK, where
    //   sosK = add sq_0 (add sq_1 (… sq_{m-1})).  (right-nested, last = leaf)
    // Base: the LAST square's sq_nonneg gives `le zero sq_{m-1}`. Then fold the
    // earlier squares FROM LAST-1 DOWN TO FIRST, each step prepending one square to
    // the running `le zero tail`, casting `add zero zero → zero` on the lhs.
    // -------------------------------------------------------------------------
    let m = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    // Base: nn : le zero sq_{m-1}.
    let mut nn = sq_nonneg_of(ctx, ells[m - 1]);
    let mut tail = sqs[m - 1]; // running right-nested tail (matches sosK structurally)
    for idx in (0..m - 1).rev() {
        let sq = sqs[idx];
        // sq_k : le zero (mul ℓ ℓ).
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        // add_le_add zero (mul ℓ ℓ) zero tail sq_k nn
        //   : le (add zero zero)(add (mul ℓ ℓ) tail).
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        // Cast lhs (add zero zero) → zero via add_zero zero : Eq R (add zero zero) zero.
        let new_tail = ctx.mk_add(sq, tail); // add (mul ℓ ℓ) tail (= next sosK prefix)
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        // now nn : le zero (add (mul ℓ ℓ) tail) = le zero new_tail.
        tail = new_tail;
    }
    // nn : le zero sosK (= le zero tail, tail == sosk structurally).
    debug_assert_eq!(tail, sosk);

    // Transport nn backward along idK (rewrite sosK → pK) ⇒ lep : le zero pK.
    let id_sym = ctx.eq_symm_r(pk, sosk, idk); // Eq R sosK pK
    let lep = ctx.le_cast_right(zero, sosk, pk, nn, id_sym);

    // hlt : lt pK zero — the asserted atom `p < 0`.
    let hlt = {
        let prop = ctx.mk_lt(pk, zero);
        ctx.hyp_axiom(prop)?
    };
    // chain : lt zero zero := lt_of_le_of_lt zero pK zero lep hlt.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, pk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, hlt)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_multi_unit_square".to_owned(),
            detail: format!("SOS multi-square certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_multi_unit_square".to_owned(),
            detail: "SOS multi-square refutation did not infer to False".to_owned(),
        })
    }
}

/// Upper bound on the cleared denominator `M` and on any integer linear-form
/// coefficient the rational-weight SOS reconstructor will expand into repeated unit
/// monomials / repeated squares (the proof is linear in these magnitudes, so a large
/// value is declined — `Ok(None)` — rather than building a giant kernel term).
const SOS_RATIONAL_MAX: i128 = 64;

/// The least common multiple of `a` and `b` (both already nonnegative), returning
/// `None` on `i128` overflow. `lcm(0, _) = lcm(_, 0) = 0` is never needed here (all
/// denominators are ≥ 1), but `a = 0` is handled as the identity for folding.
fn checked_lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 {
        return Some(b);
    }
    if b == 0 {
        return Some(a);
    }
    let g = gcd_i128(a, b);
    // a / g is exact; multiply by b.
    (a / g).checked_mul(b)
}

/// Build the [`RExpr`] for an INTEGER-coefficient linear form `ℓ⁺ = Σⱼ cⱼ·xⱼ` from
/// signed coefficients `cⱼ` (any nonzero integer, not just ±1): a left-nested `add`
/// over `|cⱼ|` repeated copies of `xⱼ` (or `neg xⱼ` when `cⱼ < 0`). E.g.
/// `2x₀ − x₁` ⇒ `add (add x₀ x₀) (neg x₁)`. `None` (decline) on an empty list or any
/// `|cⱼ| > SOS_RATIONAL_MAX`.
fn int_lin_to_rexpr(coeffs: &[(usize, i128)]) -> Option<RExpr> {
    let mut atoms: Vec<RExpr> = Vec::new();
    for &(idx, c) in coeffs {
        if c == 0 {
            continue;
        }
        if c.unsigned_abs() > SOS_RATIONAL_MAX as u128 {
            return None; // coefficient too large to expand into unit copies
        }
        let count = c.unsigned_abs();
        for _ in 0..count {
            let atom = if c < 0 {
                RExpr::Neg(Box::new(RExpr::Var(idx)))
            } else {
                RExpr::Var(idx)
            };
            atoms.push(atom);
        }
    }
    let mut iter = atoms.into_iter();
    let first = iter.next()?;
    let mut acc = first;
    for t in iter {
        acc = RExpr::Add(Box::new(acc), Box::new(t));
    }
    Some(acc)
}

/// From the certificate's rational SOS decomposition `p = Σₖ dₖ·ℓₖ²` (each
/// `(dₖ, [(j, cₖⱼ)])` with `dₖ > 0` rational and `cₖⱼ` rational), clear all
/// denominators to land entirely in the integer machinery:
///
/// 1. For each square, let `Cₖ = LCM(denominators of cₖⱼ)`; the INTEGER form is
///    `ℓₖ⁺ = Cₖ·ℓₖ` with coefficients `cₖⱼ⁺ = Cₖ·cₖⱼ`. Then
///    `dₖ·ℓₖ² = wₖ·(ℓₖ⁺)²` with `wₖ = dₖ/Cₖ²` (rational, > 0).
/// 2. Let `M = LCM(denominators of all wₖ)`. Then `M·wₖ` is a **nonnegative
///    integer** and `M·p = Σₖ (M·wₖ)·(ℓₖ⁺)²`.
///
/// Returns `Some((M, [(M·wₖ, [(j, cₖⱼ⁺)])]))` — the cleared multiplier `M` and, per
/// square, its integer repetition weight `M·wₖ` and integer-coefficient form — or
/// `None` (decline) on any `i128`/`Rational` overflow, or if `M`, a weight `M·wₖ`, or
/// a form coefficient `|cₖⱼ⁺|` exceeds [`SOS_RATIONAL_MAX`] (keeps the proof bounded).
#[allow(clippy::type_complexity)]
pub(super) fn clear_rational_sos_denominators(
    squares: &[(Rational, Vec<(usize, Rational)>)],
) -> Option<(i128, Vec<(i128, Vec<(usize, i128)>)>)> {
    // Phase 1: per-square integer form `ℓₖ⁺` and rational weight `wₖ = dₖ/Cₖ²`.
    let mut int_squares: Vec<(Rational, Vec<(usize, i128)>)> = Vec::with_capacity(squares.len());
    for (dk, coeffs) in squares {
        // Cₖ = LCM of the variable-coefficient denominators.
        let mut ck: i128 = 1;
        for &(_, c) in coeffs {
            ck = checked_lcm(ck, c.denominator())?;
            if ck > SOS_RATIONAL_MAX {
                return None;
            }
        }
        // Integer form coefficients cₖⱼ⁺ = Cₖ·cₖⱼ (exact integers by construction).
        let ck_rat = Rational::integer(ck);
        let mut int_coeffs: Vec<(usize, i128)> = Vec::with_capacity(coeffs.len());
        for &(j, c) in coeffs {
            let scaled = c.checked_mul(ck_rat)?;
            if scaled.denominator() != 1 {
                return None; // should be integral after clearing; defensive
            }
            let num = scaled.numerator();
            if num == 0 {
                continue;
            }
            if num.unsigned_abs() > SOS_RATIONAL_MAX as u128 {
                return None;
            }
            int_coeffs.push((j, num));
        }
        if int_coeffs.is_empty() {
            return None; // a zero form refutes nothing
        }
        // wₖ = dₖ / Cₖ² (rational, > 0).
        let ck_sq = ck_rat.checked_mul(ck_rat)?;
        let wk = dk.checked_div(ck_sq)?;
        if wk.is_zero() || wk.numerator() < 0 {
            return None;
        }
        int_squares.push((wk, int_coeffs));
    }
    if int_squares.is_empty() {
        return None;
    }
    // Phase 2: M = LCM of all wₖ denominators.
    let mut m: i128 = 1;
    for (wk, _) in &int_squares {
        m = checked_lcm(m, wk.denominator())?;
        if m > SOS_RATIONAL_MAX {
            return None;
        }
    }
    let m_rat = Rational::integer(m);
    // Per square: integer repetition weight M·wₖ.
    let mut out: Vec<(i128, Vec<(usize, i128)>)> = Vec::with_capacity(int_squares.len());
    for (wk, int_coeffs) in int_squares {
        let mwk = wk.checked_mul(m_rat)?;
        if mwk.denominator() != 1 {
            return None; // M·wₖ must be integral by construction; defensive
        }
        let weight = mwk.numerator();
        if weight <= 0 || weight > SOS_RATIONAL_MAX {
            return None;
        }
        out.push((weight, int_coeffs));
    }
    Some((m, out))
}

/// Reconstruct, **from the SOS certificate**, any strict query `p < 0` whose
/// certificate is a RATIONAL-weight sum of squares `p = Σₖ dₖ·ℓₖ²` (with `dₖ > 0`
/// rational and `ℓₖ` a rational/integer-coefficient linear form, zero affine row) —
/// the slice that unlocks 3-variable AM-GM. Generalizes
/// [`reconstruct_sos_multi_unit_square`] (the integer-weight / ±1-form special case)
/// by **clearing denominators** so everything reduces to the existing integer fold:
/// no scaling lemma is needed.
///
/// Let `M·p = Σₖ (M·wₖ)·(ℓₖ⁺)²` be the cleared identity from
/// [`clear_rational_sos_denominators`] (every `M·wₖ` a nonnegative integer, every
/// `ℓₖ⁺` an integer-coefficient form). Then:
/// - `sosK` = the right-nested `add` of the squares `(ℓₖ⁺·ℓₖ⁺)`, each repeated `M·wₖ`
///   times, last copy as the innermost leaf.
/// - `mpK` = `M` right-nested copies of the asserted `p` (`p + p + … + p`).
/// - `idK : Eq R mpK sosK` via the degree-2 ring normalizer (both sides normalized;
///   canonical gens must agree, else decline — the certificate guarantees it, we
///   re-check it over the kernel, NEVER fabricate the identity).
/// - `nn : le zero sosK` — the existing integer-weight nonnegativity fold over the
///   repeated squares.
/// - `mneg : lt mpK zero` — fold the asserted `hlt : lt p zero` `M` times via
///   `add_lt_add`, casting `add zero zero → zero` on the right at each step so the
///   nesting matches `mpK`.
/// - transport `nn` along `idK` to `lep : le zero mpK`, then `lt_of_le_of_lt zero mpK
///   zero lep mneg : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(Some(proof))` (kernel-gated `infer` + `def_eq False`), `Ok(None)` to
/// decline (not this shape, or a bound/overflow/identity-mismatch), or `Err(_)` only
/// on a genuine kernel rejection.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_rational_weight(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    if !cert.strict_lt() {
        return Ok(None);
    }
    let Some(rat_squares) = cert.rational_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Clear all denominators: M·p = Σ (M·wₖ)·(ℓₖ⁺)².
    let Some((m, cleared)) = clear_rational_sos_denominators(&rat_squares) else {
        return Ok(None);
    };
    debug_assert!(m >= 1);

    // Faithful encoding of the asserted polynomial p (integer-coefficient).
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the integer form ℓₖ⁺ as an RExpr and the square (ℓₖ⁺·ℓₖ⁺), each
    // repeated M·wₖ times (flattened, so the integer-weight fold sees one square per
    // copy — exactly the existing machinery).
    let mut ell_rexprs: Vec<RExpr> = Vec::new();
    let mut sq_rexprs: Vec<RExpr> = Vec::new();
    for (weight, int_coeffs) in &cleared {
        let Some(ell) = int_lin_to_rexpr(int_coeffs) else {
            return Ok(None);
        };
        for _ in 0..*weight {
            sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
            ell_rexprs.push(ell.clone());
        }
    }

    // sosK as an RExpr: RIGHT-nested add over all (repeated) squares, last as the
    // innermost leaf (no trailing zero), matching `normalize_deg2`'s faithful form.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // mpK as an RExpr: M RIGHT-nested copies of p (p + (p + (… + p))), last as leaf.
    let mut mp_rexpr = p_rexpr.clone();
    for _ in 1..m {
        mp_rexpr = RExpr::Add(Box::new(p_rexpr.clone()), Box::new(mp_rexpr));
    }

    // Normalize M·p and the SOS sum; the canonical gens MUST agree (else decline —
    // re-proving M·p = Σ(M·wₖ)(ℓₖ⁺)² over the kernel, never fabricated).
    let Some((mp_gens, mpk, mp_to_canon)) = ctx.normalize_deg2(&mp_rexpr) else {
        return Ok(None);
    };
    let Some((sos_gens, sosk, sos_to_canon)) = ctx.normalize_deg2(&sos_rexpr) else {
        return Ok(None);
    };
    if mp_gens != sos_gens {
        return Ok(None);
    }

    // idK : Eq R mpK sosK := trans (mpK → canon)(symm (sosK → canon)).
    let canon = ctx.mono_gens_to_expr(&mp_gens);
    let canon_to_sos = ctx.eq_symm_r(sosk, canon, sos_to_canon); // Eq R canon sosK
    let idk = ctx.eq_trans_r(mpk, canon, sosk, mp_to_canon, canon_to_sos); // Eq R mpK sosK

    // Kernel-level per-square ℓₖ⁺ and (ℓₖ⁺·ℓₖ⁺), emitted from the SAME RExprs so the
    // `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(ell_rexprs.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(sq_rexprs.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold (existing integer-weight machinery): nn : le zero sosK.
    // sosK = add sq_0 (add sq_1 (… sq_{N-1})). Base = sq_nonneg of the LAST square;
    // fold earlier squares from last-1 down to first, casting `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let nsq = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    let mut nn = sq_nonneg_of(ctx, ells[nsq - 1]);
    let mut tail = sqs[nsq - 1];
    for idx in (0..nsq - 1).rev() {
        let sq = sqs[idx];
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        let new_tail = ctx.mk_add(sq, tail);
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero);
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        tail = new_tail;
    }
    debug_assert_eq!(tail, sosk);

    // Transport nn backward along idK (rewrite sosK → mpK) ⇒ lep : le zero mpK.
    let id_sym = ctx.eq_symm_r(mpk, sosk, idk); // Eq R sosK mpK
    let lep = ctx.le_cast_right(zero, sosk, mpk, nn, id_sym);

    // -------------------------------------------------------------------------
    // Negativity M-fold: mneg : lt mpK zero, where
    //   mpK = add p (add p (… p)).  (M right-nested copies, last = leaf)
    // The asserted atom is `hlt : lt p zero`. Seed from the INNERMOST p (the leaf),
    // then fold the earlier copies from M-2 down to 0: combine `hlt : lt p zero` with
    // the running `lt tail zero` via `add_lt_add p zero tail zero hlt acc :
    // lt (add p tail)(add zero zero)`, then cast the RIGHT side
    // `add zero zero → zero` so the type stays `lt (add p tail) zero` — matching
    // `mpK`'s exact right-nesting.
    // -------------------------------------------------------------------------
    // The leaf `p` ExprId used inside mpK (each copy, incl. the innermost, is exactly
    // the faithful encoding of `p_rexpr` — hash-consed identical).
    let p_leaf = ctx.emit_rexpr(&p_rexpr);
    // hlt : lt p zero — the asserted atom `p < 0` over the faithful encoding of p.
    let hlt = {
        let p_prop = ctx.mk_lt(p_leaf, zero);
        ctx.hyp_axiom(p_prop)?
    };
    let mut mneg = hlt; // lt p zero (p_leaf)
    let mut mtail = p_leaf; // running right-nested tail (matches mpK structurally)
    for _ in 1..m {
        // add_lt_add p zero tail zero hlt mneg : lt (add p tail)(add zero zero).
        let combined = ctx.add_lt_add_app(p_leaf, zero, mtail, zero, hlt, mneg);
        let new_tail = ctx.mk_add(p_leaf, mtail); // add p tail (next mpK prefix)
        let add_zz = ctx.mk_add(zero, zero);
        let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        mneg = ctx.lt_cast_right(new_tail, add_zz, zero, combined, azz);
        mtail = new_tail;
    }
    debug_assert_eq!(mtail, mpk);

    // chain : lt zero zero := lt_of_le_of_lt zero mpK zero lep mneg.
    let chain = {
        let ax_name = ctx.arith().lt_of_le_of_lt;
        let ax = ctx.kernel_mut().const_(ax_name, vec![]);
        let e = ctx.kernel_mut().app(ax, zero);
        let e = ctx.kernel_mut().app(e, mpk);
        let e = ctx.kernel_mut().app(e, zero);
        let e = ctx.kernel_mut().app(e, lep);
        ctx.kernel_mut().app(e, mneg)
    };
    // bad : False := lt_irrefl zero chain.
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, chain)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_rational_weight".to_owned(),
            detail: format!("SOS rational-weight certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_rational_weight".to_owned(),
            detail: "SOS rational-weight refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct, **from the SOS certificate**, any STRICT query `p > 0` whose
/// certificate is a rational-weight sum of squares of `−p`. This is the `p > 0`
/// (`strict_lt == false`) dual of [`reconstruct_sos_rational_weight`]: the
/// self-checked certificate certifies `−M ⪰ 0`, so its squares decompose **`−p`**
/// (`−p = Σ dₖ ℓₖ²`, i.e. `p ≤ 0` everywhere), contradicting the asserted `p > 0`.
///
/// Clearing denominators (the SAME [`clear_rational_sos_denominators`] machinery)
/// gives the integer identity `sosK := Σ (M·wₖ)(ℓₖ⁺)² = M·(−p) = −(M·p)`. With
/// `mpK := p + p + … + p` (`M` right-nested copies of `p`):
/// - `nn : le zero sosK` — the SAME integer-weight nonnegativity fold over
///   `sq_nonneg`, `add_le_add`, and the `add zero zero → zero` cast. Only needs
///   `0 ≤ sosK`, which holds regardless of what `sosK` denotes.
/// - `mppos : lt zero mpK` — fold the asserted `hlt : lt zero p` (`0 < p`) `M`
///   times via `add_lt_add` (both premises `lt`, so `0+0 < p+tail`), casting the
///   LEFT `add zero zero → zero` each step so the nesting matches `mpK`.
/// - `combined : lt zero (add sosK mpK)` via `add_lt_add_of_le_of_lt zero sosK zero
///   mpK nn mppos` (summing `0 ≤ sosK` with `0 < mpK`), casting the LEFT `add zero
///   zero → zero`.
/// - `cancel : Eq R (add sosK mpK) zero` — `normalize_deg2(add sosK mpK)` MUST
///   yield EMPTY canonical gens (since `sosK = −(M·p)` and `mpK = M·p` cancel
///   exactly), whose canonical form is the kernel `zero`. If the gens are NOT empty,
///   the certificate/clearing disagree — decline (`Ok(None)`), never fabricate.
/// - `lt_cast_right combined cancel : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(Some(proof))` (kernel-gated `infer` + `def_eq False`), `Ok(None)` to
/// decline (not this shape — including `p < 0`, handled by the strict sibling — or a
/// bound/overflow/cancellation mismatch), or `Err(_)` only on a genuine kernel
/// rejection.
#[allow(clippy::too_many_lines)]
fn reconstruct_sos_rational_weight_gt(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ExprId>, ReconstructError> {
    let Some(cert) = crate::nra_real_root::sos_refute_with_certificate(arena, assertions) else {
        return Ok(None);
    };
    // This path owns the `p > 0` (`−M` PSD) dual; the `p < 0` case is the strict
    // sibling's.
    if cert.strict_lt() {
        return Ok(None);
    }
    let Some(rat_squares) = cert.rational_squares() else {
        return Ok(None);
    };
    let n_vars = cert.n_vars();

    // Clear all denominators: `sosK = Σ (M·wₖ)·(ℓₖ⁺)²`. Since the certificate's
    // squares decompose `−p`, this `sosK` equals `M·(−p) = −(M·p)`.
    let Some((m, cleared)) = clear_rational_sos_denominators(&rat_squares) else {
        return Ok(None);
    };
    debug_assert!(m >= 1);

    // Faithful encoding of the asserted polynomial `p` (integer-coefficient).
    let Some(p_rexpr) = cert_poly_to_rexpr(cert.poly_terms(), n_vars) else {
        return Ok(None);
    };

    // Per-square: the integer form `ℓₖ⁺` and the square `(ℓₖ⁺·ℓₖ⁺)`, each repeated
    // `M·wₖ` times (flattened, so the integer-weight fold sees one square per copy).
    let mut ell_rexprs: Vec<RExpr> = Vec::new();
    let mut sq_rexprs: Vec<RExpr> = Vec::new();
    for (weight, int_coeffs) in &cleared {
        let Some(ell) = int_lin_to_rexpr(int_coeffs) else {
            return Ok(None);
        };
        for _ in 0..*weight {
            sq_rexprs.push(RExpr::Mul(Box::new(ell.clone()), Box::new(ell.clone())));
            ell_rexprs.push(ell.clone());
        }
    }

    // `sosK` as an RExpr: RIGHT-nested add over all (repeated) squares, last as the
    // innermost leaf (no trailing zero), matching `normalize_deg2`'s faithful form.
    let Some((last, init)) = sq_rexprs.split_last() else {
        return Ok(None);
    };
    let mut sos_rexpr = last.clone();
    for r in init.iter().rev() {
        sos_rexpr = RExpr::Add(Box::new(r.clone()), Box::new(sos_rexpr));
    }

    // `mpK` as an RExpr: M RIGHT-nested copies of p (p + (p + (… + p))), last = leaf.
    let mut mp_rexpr = p_rexpr.clone();
    for _ in 1..m {
        mp_rexpr = RExpr::Add(Box::new(p_rexpr.clone()), Box::new(mp_rexpr));
    }

    // Kernel-level per-square `ℓₖ⁺` and `(ℓₖ⁺·ℓₖ⁺)`, emitted from the SAME RExprs so
    // the `mul`/`add` ExprIds are hash-consed identical to those inside `sosK`.
    let zero = ctx.mk_zero();
    let mut ells: Vec<ExprId> = Vec::with_capacity(ell_rexprs.len());
    let mut sqs: Vec<ExprId> = Vec::with_capacity(sq_rexprs.len());
    for ell_rexpr in &ell_rexprs {
        let ell = ctx.emit_rexpr(ell_rexpr);
        ells.push(ell);
        sqs.push(ctx.mk_mul(ell, ell));
    }

    // `sosK` as a kernel ExprId: emit from the faithful RExpr (hash-consed identical
    // to the right-nested `add` of `sqs`).
    let sosk = ctx.emit_rexpr(&sos_rexpr);
    // `mpK` as a kernel ExprId: M right-nested copies of `p` (the leaf `p` is the
    // faithful encoding of `p_rexpr`).
    let p_leaf = ctx.emit_rexpr(&p_rexpr);
    let mut mpk = p_leaf;
    for _ in 1..m {
        mpk = ctx.mk_add(p_leaf, mpk);
    }

    // -------------------------------------------------------------------------
    // Nonnegativity fold (existing integer-weight machinery): nn : le zero sosK.
    // sosK = add sq_0 (add sq_1 (… sq_{N-1})). Base = sq_nonneg of the LAST square;
    // fold earlier squares from last-1 down to first, casting `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let nsq = sqs.len();
    let sq_nonneg_of = |ctx: &mut LraReconstructCtx, ell: ExprId| -> ExprId {
        let name = ctx.arith().sq_nonneg;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().app(f, ell) // le zero (mul ell ell)
    };
    let mut nn = sq_nonneg_of(ctx, ells[nsq - 1]);
    let mut tail = sqs[nsq - 1];
    for idx in (0..nsq - 1).rev() {
        let sq = sqs[idx];
        let sq_k = sq_nonneg_of(ctx, ells[idx]);
        let combined = ctx.add_le_add_app(zero, sq, zero, tail, sq_k, nn);
        let new_tail = ctx.mk_add(sq, tail);
        let lhs = ctx.mk_add(zero, zero);
        let add_zero_zero = ctx.add_zero_eq(zero);
        nn = ctx.le_cast_left(lhs, zero, new_tail, combined, add_zero_zero);
        tail = new_tail;
    }
    debug_assert_eq!(tail, sosk);

    // -------------------------------------------------------------------------
    // Positivity M-fold: mppos : lt zero mpK, where mpK = add p (add p (… p)).
    // The asserted atom is `hlt : lt zero p` (`0 < p`). Seed from the INNERMOST p
    // (the leaf), then fold the earlier copies from M-2 down to 0: combine
    // `hlt : lt zero p` with the running `lt zero tail` via
    // `add_lt_add zero p zero tail hlt acc : lt (add zero zero)(add p tail)`, then
    // cast the LEFT side `add zero zero → zero` so the type stays `lt zero (add p
    // tail)` — matching mpK's exact right-nesting.
    // -------------------------------------------------------------------------
    // hlt : lt zero p — the asserted atom `0 < p` over the faithful encoding of p.
    let hlt = {
        let p_prop = ctx.mk_lt(zero, p_leaf);
        ctx.hyp_axiom(p_prop)?
    };
    let mut mppos = hlt; // lt zero p (p_leaf)
    let mut mtail = p_leaf; // running right-nested tail (matches mpK structurally)
    for _ in 1..m {
        // add_lt_add zero p zero tail hlt mppos : lt (add zero zero)(add p tail).
        let combined = ctx.add_lt_add_app(zero, p_leaf, zero, mtail, hlt, mppos);
        let new_tail = ctx.mk_add(p_leaf, mtail); // add p tail (next mpK prefix)
        let add_zz = ctx.mk_add(zero, zero);
        let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
        mppos = ctx.lt_cast_left(add_zz, zero, new_tail, combined, azz);
        mtail = new_tail;
    }
    debug_assert_eq!(mtail, mpk);

    // -------------------------------------------------------------------------
    // Combine: add_lt_add_of_le_of_lt zero sosK zero mpK nn mppos
    //   : lt (add zero zero)(add sosK mpK). Cast the LEFT `add zero zero → zero`.
    // -------------------------------------------------------------------------
    let combined_lt = ctx.add_lt_add_of_le_of_lt_app(zero, sosk, zero, mpk, nn, mppos);
    let add_zz = ctx.mk_add(zero, zero);
    let azz = ctx.add_zero_eq(zero); // Eq R (add zero zero) zero
    let sos_plus_mp = ctx.mk_add(sosk, mpk);
    let combined = ctx.lt_cast_left(add_zz, zero, sos_plus_mp, combined_lt, azz);
    // combined : lt zero (add sosK mpK).

    // -------------------------------------------------------------------------
    // Cancellation identity: cancel : Eq R (add sosK mpK) zero. Since sosK = −(M·p)
    // and mpK = M·p, the degree-2 normal form of `add sosK mpK` has EMPTY canonical
    // gens, whose canonical form is the kernel `zero`. The normalizer returns
    // `proof : Eq R (add sosK mpK) (mono_gens_to_expr canon_gens)`; if `canon_gens`
    // is empty, that target IS `zero` (mono_gens_to_expr([]) = mk_zero). If the gens
    // are NOT empty (cancellation failed ⇒ certificate/clearing mismatch), decline —
    // never fabricate the identity.
    // -------------------------------------------------------------------------
    let cancel_rexpr = RExpr::Add(Box::new(sos_rexpr.clone()), Box::new(mp_rexpr.clone()));
    let Some((cancel_gens, cancel_kexpr, cancel_proof)) = ctx.normalize_deg2(&cancel_rexpr) else {
        return Ok(None);
    };
    if !cancel_gens.is_empty() {
        return Ok(None);
    }
    // `cancel_kexpr` is the faithful `add sosK mpK`; assert it matches the combined
    // term so the cast is well-typed (hash-consing makes this an equality of ExprIds).
    if cancel_kexpr != sos_plus_mp {
        return Ok(None);
    }
    // cancel_proof : Eq R (add sosK mpK) zero (canon of empty gens = zero).
    let cancel = cancel_proof;

    // lt_cast_right combined cancel : lt zero zero.
    let lt_zero_zero = ctx.lt_cast_right(zero, sos_plus_mp, zero, combined, cancel);
    // bad : False := lt_irrefl zero (lt zero zero).
    let proof = {
        let irrefl_name = ctx.arith().lt_irrefl;
        let irrefl = ctx.kernel_mut().const_(irrefl_name, vec![]);
        let e = ctx.kernel_mut().app(irrefl, zero);
        ctx.kernel_mut().app(e, lt_zero_zero)
    };

    // Soundness gate.
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "sos_rational_weight_gt".to_owned(),
            detail: format!("SOS rational-weight (p>0) certificate infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "sos_rational_weight_gt".to_owned(),
            detail: "SOS rational-weight (p>0) refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the **general** non-strict Farkas refutation. Given the certificate's
/// `≤`-atoms `Eᵢ ≤ 0` (with integer coefficients) and nonnegative rational
/// multipliers `λᵢ`, this:
///
/// 1. clears the multipliers' denominators to integers `μᵢ ≥ 0` (the scaled
///    certificate is an equally-valid refutation);
/// 2. for each used atom declares the hypothesis axiom `hᵢ : le Eᵢ zero`, where `Eᵢ`
///    is the atom's expression in canonical generator form;
/// 3. scales `hᵢ` by `μᵢ` and sums all of them with `add_le_add`, renormalizing the
///    right-hand side back to `zero` at each step, to reach `le Lsum zero`;
/// 4. proves `Eq R Lsum K` with the ring engine (all variable generators cancel,
///    leaving the positive constant `K = Σ μᵢ cᵢ` as a sum of `one`s) and casts to
///    `le K zero`;
/// 5. builds `lt zero K` and closes `lt_of_lt_of_le zero K zero (lt zero K)(le K zero)
///    : lt zero zero`, refuted by `lt_irrefl zero`.
///
/// Returns `Ok(None)` (to fall through to the other shapes) when an atom is strict,
/// has a non-integer coefficient/constant, or the combined constant is not a positive
/// integer — those are outside this engine's non-strict integer scope. The result is
/// kernel-gated (`infer` + `def_eq False`).
#[allow(dead_code, clippy::too_many_lines)]
pub(super) fn try_general_farkas(
    ctx: &mut LraReconstructCtx,
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    // Used atoms (positive multiplier) with their LinR forms; reject strict /
    // non-integer atoms by falling through.
    let mut used: Vec<(LinR, Rational)> = Vec::new();
    for (atom, m) in certificate.atoms.iter().zip(&certificate.multipliers) {
        if m.is_zero() {
            continue;
        }
        if atom.strict {
            return Ok(None); // mixed/strict combination is not this engine's shape
        }
        let lin = LinR {
            coeffs: atom.coeffs.clone(),
            constant: atom.constant,
        };
        // Integer coefficients/constant only.
        if lin.coeffs.iter().any(|(_, c)| c.denominator() != 1) || lin.constant.denominator() != 1 {
            return Ok(None);
        }
        used.push((lin, *m));
    }
    if used.is_empty() {
        return Ok(None);
    }

    // Clear multiplier denominators: μ = λ · L where L = lcm of denominators. Any
    // `i128` overflow in the denominator-clearing / scaling ⇒ fall through (`None`).
    let mut lcm: i128 = 1;
    for (_, m) in &used {
        let Some(next) = lcm_i128(lcm, m.denominator()) else {
            return Ok(None);
        };
        lcm = next;
    }
    let factor = Rational::integer(lcm);
    let mut scaled: Vec<(LinR, i128)> = Vec::with_capacity(used.len());
    for (lin, m) in &used {
        let Some(mu) = m.checked_mul(factor) else {
            return Ok(None);
        };
        // mu is a nonnegative integer by construction.
        if mu.denominator() != 1 || mu.numerator() <= 0 {
            return Ok(None);
        }
        scaled.push((lin.clone(), mu.numerator()));
    }

    // The combined constant K = Σ μᵢ · constantᵢ (variables provably cancel). The
    // refutation needs K to be a positive integer.
    let mut k_total = Rational::zero();
    let mut combined = LinR::default();
    for (lin, mu) in &scaled {
        let (Some(s), Some(prod)) = (
            scale_lin(lin, Rational::integer(*mu)),
            lin.constant.checked_mul(Rational::integer(*mu)),
        ) else {
            return Ok(None);
        };
        let Some(next) = combined.add(&s) else {
            return Ok(None);
        };
        combined = next;
        let Some(kt) = k_total.checked_add(prod) else {
            return Ok(None);
        };
        k_total = kt;
    }
    if !combined.coeffs.is_empty() {
        // Variables did not cancel — not a genuine Farkas refutation shape.
        return Ok(None);
    }
    if k_total.denominator() != 1 || k_total.numerator() <= 0 {
        return Ok(None);
    }
    let k_int = k_total.numerator();

    // Build the scaled-and-summed `le Lsum zero`, carrying `acc_gens` (the canonical
    // generators of `Lsum`) and `acc_canon_proof : Eq R Lsum (gens_to_expr acc_gens)`.
    let zero = ctx.mk_zero();
    let mut acc: Option<(ExprId, Vec<Gen>, ExprId)> = None; // (le-proof, gens, canon-proof)
    for (lin, mu) in &scaled {
        let Some(base_gens) = LraReconstructCtx::lin_to_gens(lin) else {
            return Ok(None);
        };
        let base_expr = ctx.gens_to_expr(&base_gens);
        // hypothesis hᵢ : le base_expr zero.
        let prop = ctx.mk_le(base_expr, zero);
        let h = ctx.hyp_axiom(prop)?;
        // Scale by μᵢ: combine hᵢ with itself μᵢ times, keeping RHS = zero and the
        // LHS in canonical generator form.
        let mut s_proof = h;
        let mut s_gens = base_gens.clone();
        let mut s_expr = base_expr; // canonical (= gens_to_expr s_gens)
        for _ in 1..*mu {
            // add_le_add s_expr zero base_expr zero s_proof h : le (add s_expr base_expr)(add zero zero)
            let combined_le = ctx.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, h);
            let lhs = ctx.mk_add(s_expr, base_expr);
            // RHS (add zero zero) → zero via add_zero zero.
            let azz = ctx.add_zero_eq(zero); // add zero zero = zero
            let add_zz = ctx.mk_add(zero, zero);
            let combined_le = ctx.le_cast_right(lhs, add_zz, zero, combined_le, azz);
            // LHS (add s_expr base_expr) → canonical (s_gens ++ base_gens).
            let mut next_gens = s_gens.clone();
            next_gens.extend_from_slice(&base_gens);
            let append_proof = ctx.append_eq(&s_gens, &base_gens);
            let next_canon = ctx.gens_to_expr(&next_gens);
            s_proof = ctx.le_cast_left(lhs, next_canon, zero, combined_le, append_proof);
            s_gens = next_gens;
            s_expr = next_canon;
        }
        // Fold this scaled constraint into the accumulator.
        acc = Some(match acc {
            None => (s_proof, s_gens, {
                // canon-proof is refl since s_expr is already canonical.
                ctx.eq_refl_r(s_expr)
            }),
            Some((acc_proof, acc_gens, _acc_canon_proof)) => {
                let acc_expr = ctx.gens_to_expr(&acc_gens);
                // add_le_add acc_expr zero s_expr zero acc_proof s_proof
                let combined_le =
                    ctx.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof);
                let azz = ctx.add_zero_eq(zero);
                let add_zz = ctx.mk_add(zero, zero);
                let lhs = ctx.mk_add(acc_expr, s_expr);
                let combined_le = ctx.le_cast_right(lhs, add_zz, zero, combined_le, azz);
                // LHS (add acc_expr s_expr) → canonical (acc_gens ++ s_gens).
                let mut next_gens = acc_gens.clone();
                next_gens.extend_from_slice(&s_gens);
                let append_proof = ctx.append_eq(&acc_gens, &s_gens);
                let next_canon = ctx.gens_to_expr(&next_gens);
                let new_proof = ctx.le_cast_left(lhs, next_canon, zero, combined_le, append_proof);
                (new_proof, next_gens, ctx.eq_refl_r(next_canon))
            }
        });
    }

    let (le_lsum_zero, all_gens, _canon) = acc.expect("at least one used atom");
    // Normalize all_gens: variables cancel, leaving exactly k_int `One`s.
    let lsum_canon = ctx.gens_to_expr(&all_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&all_gens); // Eq R lsum_canon (gens_to_expr norm_gens)
    // The normalized generators must be exactly `k_int` `One`s (positive constant).
    if norm_gens.len() as i128 != k_int || norm_gens.iter().any(|g| *g != Gen::One) {
        return Ok(None);
    }
    let k_expr = ctx.gens_to_expr(&norm_gens);
    // Cast `le lsum_canon zero` along `lsum_canon = k_expr` ⇒ `le k_expr zero`.
    let le_k_zero = ctx.le_cast_left(lsum_canon, k_expr, zero, le_lsum_zero, norm_proof);
    // lt zero K.
    let lt_zero_k = ctx.lt_zero_ones(k_int);
    // lt_of_lt_of_le zero K zero (lt zero K)(le K zero) : lt zero zero.
    let lt_zero_zero = ctx.lt_of_lt_of_le_app(zero, k_expr, zero, lt_zero_k, le_k_zero);
    // lt_irrefl zero : Not (lt zero zero); apply ⇒ False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e = ctx.kernel.app(irrefl, zero);
        ctx.kernel.app(e, lt_zero_zero)
    };
    // Soundness gate.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("general-Farkas infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "general-Farkas refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct a **mixed** strict/non-strict Farkas refutation: the certificate uses
/// at least one strict (`<`) atom with a positive multiplier and is *not* a pure strict
/// cycle (which [`try_strict_cycle`] handles). All used atoms have integer coefficients;
/// multipliers are nonnegative rationals.
///
/// 1. Clear all used multipliers' denominators to integers `μᵢ ≥ 1`.
/// 2. Partition the used atoms by strictness. Sum the non-strict ones (if any) into
///    `le Lne zero` and the strict ones into `lt Lst zero`, each via
///    [`LraReconstructCtx::sum_scaled_atoms`].
/// 3. Combine into one strict inequality `lt Lsum zero`: with both groups present,
///    `add_lt_add_of_le_of_lt (Lne) zero (Lst) zero hle hlt : lt (add Lne Lst)(add zero
///    zero)`, renormalized to `lt (Lne++Lst) zero`; with only strict atoms, `Lsum = Lst`.
/// 4. Normalize `Lsum`'s generators (variables cancel) to the combined constant
///    `K = Σ μᵢ cᵢ`, which must be a **nonnegative** integer (a strict `Σ < 0` with
///    `Σ = K ≥ 0` is the contradiction).
/// 5. Close: `K = 0` gives `lt zero zero` directly (refuted by `lt_irrefl zero`); `K > 0`
///    gives `lt K zero`, and with `lt zero K` (`lt_zero_ones`) `lt_trans zero K zero`
///    yields `lt zero zero`, again refuted by `lt_irrefl zero`.
///
/// Returns `Ok(None)` (fall through) when **no** used atom is strict (the pure non-strict
/// engine owns that), an atom has a non-integer coefficient/constant, variables do not
/// cancel, or `K` is negative. Kernel-gated (`infer` + `def_eq False`).
#[allow(dead_code, clippy::too_many_lines)]
pub(super) fn try_mixed_farkas(
    ctx: &mut LraReconstructCtx,
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    // Used atoms (positive multiplier) with their LinR + strictness; reject
    // non-integer atoms by falling through.
    let mut used: Vec<(LinR, Rational, bool)> = Vec::new();
    let mut any_strict = false;
    for (atom, m) in certificate.atoms.iter().zip(&certificate.multipliers) {
        if m.is_zero() {
            continue;
        }
        let lin = LinR {
            coeffs: atom.coeffs.clone(),
            constant: atom.constant,
        };
        if lin.coeffs.iter().any(|(_, c)| c.denominator() != 1) || lin.constant.denominator() != 1 {
            return Ok(None);
        }
        any_strict |= atom.strict;
        used.push((lin, *m, atom.strict));
    }
    // This engine only owns the mixed case (≥1 used strict atom). Pure non-strict
    // certificates fall through to `try_general_farkas`.
    if !any_strict || used.is_empty() {
        return Ok(None);
    }

    // Clear all multiplier denominators: μ = λ · L where L = lcm of denominators.
    // Any `i128` overflow in denominator-clearing / scaling ⇒ fall through (`None`).
    let mut lcm: i128 = 1;
    for (_, m, _) in &used {
        let Some(next) = lcm_i128(lcm, m.denominator()) else {
            return Ok(None);
        };
        lcm = next;
    }
    let factor = Rational::integer(lcm);
    let mut strict_atoms: Vec<(LinR, i128)> = Vec::new();
    let mut nonstrict_atoms: Vec<(LinR, i128)> = Vec::new();
    let mut k_total = Rational::zero();
    let mut combined_coeffs = LinR::default();
    for (lin, m, strict) in &used {
        let Some(mu) = m.checked_mul(factor) else {
            return Ok(None);
        };
        if mu.denominator() != 1 || mu.numerator() <= 0 {
            return Ok(None);
        }
        let mu = mu.numerator();
        let (Some(s), Some(prod)) = (
            scale_lin(lin, Rational::integer(mu)),
            lin.constant.checked_mul(Rational::integer(mu)),
        ) else {
            return Ok(None);
        };
        let Some(next) = combined_coeffs.add(&s) else {
            return Ok(None);
        };
        combined_coeffs = next;
        let Some(kt) = k_total.checked_add(prod) else {
            return Ok(None);
        };
        k_total = kt;
        if *strict {
            strict_atoms.push((lin.clone(), mu));
        } else {
            nonstrict_atoms.push((lin.clone(), mu));
        }
    }
    // A genuine refutation cancels all variables, and the strict combined constant must
    // satisfy `K ≥ 0` (the strict sum says `Σ < 0`, refuting `Σ = K ≥ 0`).
    if !combined_coeffs.coeffs.is_empty() {
        return Ok(None);
    }
    if k_total.denominator() != 1 || k_total.numerator() < 0 {
        return Ok(None);
    }
    let k_int = k_total.numerator();
    // `any_strict` ⇒ there is at least one strict atom to sum.
    if strict_atoms.is_empty() {
        return Ok(None);
    }

    let zero = ctx.mk_zero();
    // Strict sub-sum: lt Lst zero (+ its canonical generators).
    let Some((mut lt_proof, mut sum_gens)) = ctx.sum_scaled_atoms(&strict_atoms, true)? else {
        return Ok(None);
    };
    // Fold in the non-strict sub-sum (if any) to keep the result strict.
    if !nonstrict_atoms.is_empty() {
        let Some((le_proof, ne_gens)) = ctx.sum_scaled_atoms(&nonstrict_atoms, false)? else {
            return Ok(None);
        };
        let ne_expr = ctx.gens_to_expr(&ne_gens);
        let st_expr = ctx.gens_to_expr(&sum_gens);
        // add_lt_add_of_le_of_lt ne zero st zero (le ne 0)(lt st 0)
        //   : lt (add ne st)(add zero zero).
        let combined =
            ctx.add_lt_add_of_le_of_lt_app(ne_expr, zero, st_expr, zero, le_proof, lt_proof);
        let azz = ctx.add_zero_eq(zero);
        let add_zz = ctx.mk_add(zero, zero);
        let lhs = ctx.mk_add(ne_expr, st_expr);
        let combined = ctx.lt_cast_right(lhs, add_zz, zero, combined, azz);
        // LHS (add ne st) → canonical (ne_gens ++ st_gens).
        let mut next_gens = ne_gens.clone();
        next_gens.extend_from_slice(&sum_gens);
        let append_proof = ctx.append_eq(&ne_gens, &sum_gens);
        let next_canon = ctx.gens_to_expr(&next_gens);
        lt_proof = ctx.lt_cast_left(lhs, next_canon, zero, combined, append_proof);
        sum_gens = next_gens;
    }

    // Normalize the combined sum: variables cancel, leaving exactly `k_int` `One`s.
    let lsum_canon = ctx.gens_to_expr(&sum_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&sum_gens); // Eq R lsum_canon (gens_to_expr norm_gens)
    if norm_gens.len() as i128 != k_int || norm_gens.iter().any(|g| *g != Gen::One) {
        return Ok(None);
    }
    let k_expr = ctx.gens_to_expr(&norm_gens); // `zero` when k_int == 0.
    // Cast `lt lsum_canon zero` along `lsum_canon = k_expr` ⇒ `lt k_expr zero`.
    let lt_k_zero = ctx.lt_cast_left(lsum_canon, k_expr, zero, lt_proof, norm_proof);
    // Reach `lt zero zero`.
    let lt_zero_zero = if k_int == 0 {
        // k_expr is `zero` (gens_to_expr([]) = zero), so `lt_k_zero : lt zero zero`.
        lt_k_zero
    } else {
        // lt zero K (lt_zero_ones) and lt K zero ⇒ lt_trans zero K zero : lt zero zero.
        let lt_zero_k = ctx.lt_zero_ones(k_int);
        let ax = ctx.kernel.const_(ctx.arith.lt_trans, vec![]);
        let e = ctx.kernel.app(ax, zero);
        let e = ctx.kernel.app(e, k_expr);
        let e = ctx.kernel.app(e, zero);
        let e = ctx.kernel.app(e, lt_zero_k);
        ctx.kernel.app(e, lt_k_zero)
    };
    // lt_irrefl zero : Not (lt zero zero); apply ⇒ False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e = ctx.kernel.app(irrefl, zero);
        ctx.kernel.app(e, lt_zero_zero)
    };
    // Soundness gate.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("mixed-Farkas infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "mixed-Farkas refutation did not infer to False".to_owned(),
        })
    }
}

/// `lcm(a, b)` over `i128` (positive inputs; denominators are positive).
/// Declines (`None`) on any `i128` overflow.
fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd_i128(a.checked_abs()?, b.checked_abs()?);
    // a / g * b, with g | a exactly.
    (a.checked_abs()? / g).checked_mul(b.checked_abs()?)
}

/// `gcd(a, b)` over nonnegative `i128`.
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Reconstruct a strict-`<` **cycle** refutation: the `n ≥ 2` participating
/// constraints (unit multipliers) form a directed cycle `e0 < e1 < … < e_{n-1} < e0`.
/// Fold `lt_trans` around it to `lt e0 e0`, then `lt_irrefl e0` ⇒ `False`. Generalizes
/// the `n = 2` antisymmetry. Returns `Ok(None)` if the participating constraints are
/// not all strict-`<` or do not form a single cycle; kernel-gated (`infer` + `def_eq
/// False`), so a wrong term is `KernelRejected`, never accepted.
fn try_strict_cycle(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &crate::FarkasCertificate,
) -> Result<Option<ExprId>, ReconstructError> {
    let mut participating: Vec<usize> = certificate
        .origins
        .iter()
        .zip(&certificate.multipliers)
        .filter(|(_, m)| !m.is_zero())
        .map(|(&o, _)| o)
        .collect();
    participating.sort_unstable();
    participating.dedup();
    if participating.len() < 2 {
        return Ok(None);
    }
    // Cycles use each constraint once (unit multiplier).
    for (o, m) in certificate.origins.iter().zip(&certificate.multipliers) {
        if participating.contains(o) && !m.is_zero() && *m != Rational::integer(1) {
            return Ok(None);
        }
    }
    // Parse each participating assertion as a strict edge `l < r`.
    let mut edges: Vec<(LinR, LinR)> = Vec::with_capacity(participating.len());
    for &i in &participating {
        match as_lt_constraint(arena, assertions[i]) {
            Some(c) => edges.push(c),
            None => return Ok(None),
        }
    }
    // Order into one cycle: from edge 0, follow `r → next edge whose l == r`.
    let n = edges.len();
    let mut used = vec![false; n];
    let mut order: Vec<usize> = vec![0];
    used[0] = true;
    let mut cur_rhs = edges[0].1.clone();
    for _ in 1..n {
        let Some(j) = (0..n).find(|&j| !used[j] && edges[j].0 == cur_rhs) else {
            return Ok(None);
        };
        used[j] = true;
        order.push(j);
        cur_rhs = edges[j].1.clone();
    }
    // Must close: last RHS == first edge's LHS.
    if cur_rhs != edges[order[0]].0 {
        return Ok(None);
    }
    // Nodes e_k = LHS of the k-th edge in cycle order; edge k is `e_k < e_{(k+1)%n}`.
    let nodes: Vec<ExprId> = order
        .iter()
        .map(|&k| ctx.lin_to_r(&edges[k].0))
        .collect::<Result<_, _>>()?;
    let e0 = nodes[0];
    // h_k : lt e_k e_{(k+1)%n}; fold lt_trans into `acc : lt e0 e_{(k+1)%n}`.
    let mut acc = {
        let p = ctx.mk_lt(nodes[0], nodes[1 % n]);
        ctx.hyp_axiom(p)?
    };
    for k in 1..n {
        let mid = nodes[k];
        let to = nodes[(k + 1) % n];
        let p = ctx.mk_lt(mid, to);
        let hk = ctx.hyp_axiom(p)?;
        let tr = ctx.kernel.const_(ctx.arith.lt_trans, vec![]);
        let e = ctx.kernel.app(tr, e0);
        let e = ctx.kernel.app(e, mid);
        let e = ctx.kernel.app(e, to);
        let e = ctx.kernel.app(e, acc);
        acc = ctx.kernel.app(e, hk);
    }
    // acc : lt e0 e0 ; lt_irrefl e0 acc : False.
    let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
    let e = ctx.kernel.app(irrefl, e0);
    let proof = ctx.kernel.app(e, acc);
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(Some(proof))
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "strict-cycle refutation did not infer to False".to_owned(),
        })
    }
}

/// Reconstruct the transitivity-reducible (`e ≤ 0 ∧ 1 ≤ e`) baby-Farkas shape.
///
/// The two participating constraints (those with a positive Farkas multiplier) are
/// re-linearized from the *original* assertion atoms into [`LinR`] form. The shape
/// is accepted only when, for a shared expression `e`, one constraint is `e ≤ 0`
/// and the other is `1 ≤ e` (equivalently `1 - e ≤ 0`), with the multipliers
/// witnessing the same refutation. The reconstruction is the pure order chain.
#[allow(dead_code)]
fn reconstruct_transitivity_refutation(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &crate::FarkasCertificate,
) -> Result<ExprId, ReconstructError> {
    // The participating assertion indices: those whose atoms carry a nonzero
    // multiplier. Determinism: origins/multipliers are in atom order.
    let mut participating: Vec<usize> = certificate
        .origins
        .iter()
        .zip(&certificate.multipliers)
        .filter(|(_, m)| !m.is_zero())
        .map(|(&origin, _)| origin)
        .collect();
    participating.sort_unstable();
    participating.dedup();

    let [lo_or_hi_a, lo_or_hi_b] = participating.as_slice() else {
        return Err(ReconstructError::MalformedStep {
            rule: "la_generic".to_owned(),
            detail: format!(
                "slice 1 reconstructs the two-constraint transitivity shape; \
                 {} constraints participate in the certificate",
                participating.len()
            ),
        });
    };

    // Slice 1 reconstructs all-unit (`λ = 1`) multipliers (the baby-Farkas chain
    // does not scale). A non-unit multiplier needs the (deferred) ring normalizer.
    for (origin, m) in certificate.origins.iter().zip(&certificate.multipliers) {
        if (*origin == *lo_or_hi_a || *origin == *lo_or_hi_b)
            && !m.is_zero()
            && *m != Rational::integer(1)
        {
            return Err(ReconstructError::MalformedStep {
                rule: "la_generic".to_owned(),
                detail: format!(
                    "slice 1 reconstructs unit (λ=1) multipliers only; got {}/{} \
                     (the scaling/ring-cancellation normalizer is a later slice)",
                    m.numerator(),
                    m.denominator()
                ),
            });
        }
    }

    // (Strict-`<` antisymmetry is handled upstream by `try_strict_cycle`, the n=2 case.)

    // Re-linearize the two participating assertion atoms into `le L R` shape, as
    // (L − R ≤ 0)-style `LinR`s, but keeping the original two sides so we can match
    // `e ≤ 0` and `1 ≤ e` structurally.
    let (lo_t, hi_t) = (assertions[*lo_or_hi_a], assertions[*lo_or_hi_b]);
    let c0 = as_le_constraint(arena, lo_t).ok_or_else(|| ReconstructError::MalformedStep {
        rule: "la_generic".to_owned(),
        detail: "a participating assertion is not a non-strict `(<= L R)` constraint".to_owned(),
    })?;
    let c1 = as_le_constraint(arena, hi_t).ok_or_else(|| ReconstructError::MalformedStep {
        rule: "la_generic".to_owned(),
        detail: "a participating assertion is not a non-strict `(<= L R)` constraint".to_owned(),
    })?;

    // Identify which is the upper bound `e ≤ 0` and which the lower `1 ≤ e`.
    // c = (left, right) with the relation `left ≤ right`.
    let (e_expr, _matched) =
        match_transitivity_pair(&c0, &c1).ok_or_else(|| ReconstructError::MalformedStep {
            rule: "la_generic".to_owned(),
            detail: "the two constraints are not the transitivity shape `e ≤ 0 ∧ 1 ≤ e`".to_owned(),
        })?;

    // Build the shared `R` expression `e` and the hypothesis Props.
    let e = ctx.lin_to_r(&e_expr)?;
    let zero = ctx.mk_zero();
    let one = ctx.mk_one();

    // h_hi : le e zero  (the upper bound `e ≤ 0`).
    let le_e_zero = ctx.mk_le(e, zero);
    let h_hi = ctx.hyp_axiom(le_e_zero)?;
    // h_lo : le one e   (the lower bound `1 ≤ e`).
    let le_one_e = ctx.mk_le(one, e);
    let h_lo = ctx.hyp_axiom(le_one_e)?;

    // step1 := le_trans one e zero h_lo h_hi : le one zero.
    let step1 = {
        let tr = ctx.kernel.const_(ctx.arith.le_trans, vec![]);
        let e1 = ctx.kernel.app(tr, one);
        let e1 = ctx.kernel.app(e1, e);
        let e1 = ctx.kernel.app(e1, zero);
        let e1 = ctx.kernel.app(e1, h_lo);
        ctx.kernel.app(e1, h_hi)
    };
    // step2 := lt_of_le_of_lt one zero one step1 zero_lt_one : lt one one.
    let step2 = {
        let ax = ctx.kernel.const_(ctx.arith.lt_of_le_of_lt, vec![]);
        let e2 = ctx.kernel.app(ax, one);
        let e2 = ctx.kernel.app(e2, zero);
        let e2 = ctx.kernel.app(e2, one);
        let e2 = ctx.kernel.app(e2, step1);
        let zlo = ctx.kernel.const_(ctx.arith.zero_lt_one, vec![]);
        ctx.kernel.app(e2, zlo)
    };
    // refute := lt_irrefl one step2 : False.
    let proof = {
        let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
        let e3 = ctx.kernel.app(irrefl, one); // Not (lt one one)
        ctx.kernel.app(e3, step2) // applied to (lt one one) ⇒ False
    };

    // Soundness gate: infer the term and require it `def_eq` to `False`.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: format!("infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "la_generic".to_owned(),
            detail: "inferred proposition is not def-eq to `False`".to_owned(),
        })
    }
}

/// Reconstruct a **Boolean-structured (disjunctive) `QF_LRA`** refutation: a
/// conjunctive linear-real system plus exactly one clause `(L₁ ∨ L₂)` of
/// non-strict literals, each leaf `conj ∧ Lᵢ` conjunctive-Farkas-refutable. The
/// refutation is a kernel case-split (`Or.rec`) on `hor : Enc(L₁ ∨ L₂)`; each
/// branch reuses the conjunctive general-Farkas fold (with the branch literal as
/// the bound hypothesis) to derive `False`, and the eliminator combines them.
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] when `assertions` is not the disjunctive
/// shape (no single binary clause, a strict / out-of-slice branch literal, or a
/// leaf that is not non-strict-general-Farkas-refutable), or
/// [`ReconstructError::KernelRejected`] if the assembled term fails to kernel-check
/// to `False`. Decision logic is untouched — this only certifies an already-decided
/// `unsat`.
pub(super) fn reconstruct_disjunctive_lra_proof(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    let Some((conj, l1, l2, syms)) = split_disjunctive_lra(arena, assertions) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "disjunctive-LRA reconstruction needs exactly one binary clause \
                   `(L₁ ∨ L₂)` of non-strict linear-real literals plus conjunctive \
                   real-linear assertions"
                .to_owned(),
        });
    };

    // Encode each branch literal `Enc(Lᵢ) = le Eᵢ zero` (Eᵢ canonical over the
    // shared symbol map), and the clause `Or (Enc L₁) (Enc L₂)` as `hor`.
    let zero = ctx.mk_zero();
    let e1 = ctx.gens_to_expr(&l1.gens);
    let e2 = ctx.gens_to_expr(&l2.gens);
    let enc1 = ctx.mk_le(e1, zero);
    let enc2 = ctx.mk_le(e2, zero);
    let or_prop = {
        let or = ctx.kernel.const_(ctx.arith.logic.or, vec![]);
        let e = ctx.kernel.app(or, enc1);
        ctx.kernel.app(e, enc2)
    };
    let hor = ctx.hyp_axiom(or_prop)?;

    // Build each branch's `False` proof as a function of the bound literal `hᵢ`.
    let minor1 = disjunctive_branch_minor(ctx, arena, &conj, &l1, enc1, &syms)?;
    let minor2 = disjunctive_branch_minor(ctx, arena, &conj, &l2, enc2, &syms)?;

    // motive := fun (_ : Or enc1 enc2) => False.
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    let motive = {
        let anon = ctx.kernel.anon();
        ctx.kernel.lam(anon, or_prop, false_, BinderInfo::Default)
    };
    // Or.rec enc1 enc2 motive minor1 minor2 hor : False.
    let proof = {
        let rec = ctx.kernel.const_(ctx.arith.logic.or_rec, vec![]);
        let e = ctx.kernel.app(rec, enc1);
        let e = ctx.kernel.app(e, enc2);
        let e = ctx.kernel.app(e, motive);
        let e = ctx.kernel.app(e, minor1);
        let e = ctx.kernel.app(e, minor2);
        ctx.kernel.app(e, hor)
    };

    // Soundness gate: the assembled case-split must kernel-infer to `False`.
    let inferred = ctx
        .kernel
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "disjunctive_la_generic".to_owned(),
            detail: format!("Or.rec case-split infer failed: {e:?}"),
        })?;
    let false_ = ctx.kernel.const_(ctx.arith.logic.false_, vec![]);
    if ctx.kernel.def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "disjunctive-LRA case-split did not infer to False".to_owned(),
        })
    }
}

/// Build the `Or.rec` minor premise `fun (hᵢ : enc_lit) => branchᵢ` for one branch
/// of the disjunctive-LRA case split: bind the branch literal `Lᵢ` as a fresh free
/// variable, reconstruct `branchᵢ : False` over `conj ∧ Lᵢ` (general Farkas, the
/// branch literal supplied as that bound `hᵢ`), then abstract `hᵢ` into the lambda.
fn disjunctive_branch_minor(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    conj: &[TermId],
    lit: &BranchLiteral,
    enc_lit: ExprId,
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<ExprId, ReconstructError> {
    let fvar_id = ctx.fresh_fvar_id();
    let h_branch = ctx.kernel.fvar(fvar_id);
    let body = disjunctive_branch_false(ctx, arena, conj, lit, h_branch, syms)?;
    let body = ctx.kernel.abstract_fvars(body, &[fvar_id]);
    let anon = ctx.kernel.anon();
    Ok(ctx.kernel.lam(anon, enc_lit, body, BinderInfo::Default))
}

/// Reconstruct `branchᵢ : False` for the leaf `conj ∧ Lᵢ` via the conjunctive
/// general-Farkas fold, with the branch literal `Lᵢ`'s `le Eᵢ zero` hypothesis
/// supplied as the external proof `h_branch` (the bound `Or.rec` hypothesis) and
/// every conjunctive atom discharged via a fresh `hyp_axiom`. Declines (with an
/// error) when the leaf's certificate is outside the non-strict integer general
/// Farkas slice (a strict used atom, a non-integer coefficient, an overflow, or a
/// non-`±1`-generator branch literal).
fn disjunctive_branch_false(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    conj: &[TermId],
    lit: &BranchLiteral,
    h_branch: ExprId,
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<ExprId, ReconstructError> {
    // Re-decide the leaf to obtain self-checked Farkas multipliers (decision logic
    // is unchanged; we only read its certificate). The leaf is `conj ++ [Lᵢ]`.
    let mut leaf: Vec<TermId> = conj.to_vec();
    leaf.push(lit.term);
    let branch_origin = conj.len(); // index of `Lᵢ` in the leaf assertion slice
    let Ok(Some(cert)) = crate::lra_farkas_certificate(arena, &leaf) else {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "a disjunctive leaf is not conjunctive-Farkas-refutable".to_owned(),
        });
    };

    // Collect the used (positive-multiplier) atoms, mapping each to global symbol
    // indices and clearing the multiplier denominators to integers `μ ≥ 1`. The
    // branch-literal atom (origin == branch_origin) carries the external `h_branch`
    // proof; every other atom gets a fresh `hyp_axiom`. Strict / non-integer /
    // overflow ⇒ decline (this slice is non-strict integer general Farkas).
    let atoms = collect_branch_farkas_atoms(ctx, &cert, branch_origin, h_branch, &lit.gens, syms)?;
    let Some(atoms) = atoms else {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "a disjunctive leaf is outside the non-strict integer general-Farkas slice"
                .to_owned(),
        });
    };
    branch_general_farkas_close(ctx, &atoms)
}

/// One scaled atom of a branch's general-Farkas fold: its canonical base
/// generators `Eⱼ` (the literal denotes `Eⱼ ≤ 0`), the integer multiplier `μⱼ ≥ 1`,
/// and a proof `hⱼ : le (gens_to_expr Eⱼ) zero` (either a fresh `hyp_axiom` for a
/// conjunctive atom, or the bound `Or.rec` hypothesis for the branch literal).
struct BranchAtom {
    gens: Vec<Gen>,
    mu: i128,
    proof: ExprId,
}

/// Translate a leaf's [`FarkasCertificate`] into the [`BranchAtom`] list for the
/// general-Farkas fold, over the **global** symbol indices (so the branch
/// literal's encoding matches the `Or.rec` binding `enc_lit`). Returns `Ok(None)`
/// when the certificate is outside the non-strict integer general-Farkas slice.
fn collect_branch_farkas_atoms(
    ctx: &mut LraReconstructCtx,
    cert: &crate::FarkasCertificate,
    branch_origin: usize,
    h_branch: ExprId,
    branch_gens: &[Gen],
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Result<Option<Vec<BranchAtom>>, ReconstructError> {
    let zero = ctx.mk_zero();
    let mut out: Vec<BranchAtom> = Vec::new();
    for ((atom, m), origin) in cert.atoms.iter().zip(&cert.multipliers).zip(&cert.origins) {
        if m.is_zero() {
            continue;
        }
        if atom.strict {
            return Ok(None); // strict atoms are a later slice
        }
        // Clear the multiplier denominator: μ must be a positive integer.
        if m.denominator() != 1 || m.numerator() <= 0 {
            return Ok(None);
        }
        let mu = m.numerator();
        // Canonical generators of this atom's `E ≤ 0`, over global symbol indices.
        let gens = if *origin == branch_origin {
            branch_gens.to_vec()
        } else {
            let Some(g) = farkas_atom_to_global_gens(atom, &cert.vars, syms) else {
                return Ok(None);
            };
            g
        };
        // The atom's hypothesis proof: the bound `h_branch` for the branch literal,
        // a fresh `hyp_axiom : le base_expr zero` otherwise.
        let proof = if *origin == branch_origin {
            h_branch
        } else {
            let base_expr = ctx.gens_to_expr(&gens);
            let prop = ctx.mk_le(base_expr, zero);
            ctx.hyp_axiom(prop)?
        };
        out.push(BranchAtom { gens, mu, proof });
    }
    if out.is_empty() {
        return Ok(None);
    }
    Ok(Some(out))
}

/// Canonical generators of a [`FarkasAtom`]'s `E ≤ 0` over the **shared** symbol
/// index map `syms`: each coefficient pair `(local_idx, c)` is re-keyed through the
/// certificate's `vars[local_idx]` symbol to the shared index the kernel constants
/// (and the branch literal's encoding) use. Returns `None` on a non-integer
/// coefficient/constant or a symbol missing from the shared map (outside scope).
fn farkas_atom_to_global_gens(
    atom: &crate::FarkasAtom,
    vars: &[axeyum_ir::SymbolId],
    syms: &BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<Vec<Gen>> {
    let mut coeffs: Vec<(usize, Rational)> = Vec::with_capacity(atom.coeffs.len());
    for &(local_idx, c) in &atom.coeffs {
        let symbol = *vars.get(local_idx)?;
        let global_idx = *syms.get(&symbol)?;
        coeffs.push((global_idx, c));
    }
    let lin = LinR {
        coeffs,
        constant: atom.constant,
    };
    LraReconstructCtx::lin_to_gens(&lin)
}

/// The fold: combine the [`BranchAtom`]s into `False`. Mirrors the conjunctive
/// `try_general_farkas` engine (scale each atom by `μ` via `add_le_add`, sum to
/// `le Lsum zero`, normalize the generators so variables cancel to a positive
/// constant `K`, and close `K ≤ 0` against `0 < K`), but takes externally-built
/// per-atom proofs (so the branch literal flows in as the bound hypothesis). The
/// conjunctive path is left byte-identical.
fn branch_general_farkas_close(
    ctx: &mut LraReconstructCtx,
    atoms: &[BranchAtom],
) -> Result<ExprId, ReconstructError> {
    let zero = ctx.mk_zero();
    let mut acc: Option<(ExprId, Vec<Gen>)> = None; // (le-proof, gens)
    for atom in atoms {
        let base_gens = &atom.gens;
        let base_expr = ctx.gens_to_expr(base_gens);
        // Scale by μ: combine the atom's proof with itself μ times (RHS stays zero,
        // LHS kept in canonical generator form).
        let mut s_proof = atom.proof;
        let mut s_gens = base_gens.clone();
        let mut s_expr = base_expr;
        for _ in 1..atom.mu {
            let combined = ctx.add_le_add_app(s_expr, zero, base_expr, zero, s_proof, atom.proof);
            let lhs = ctx.mk_add(s_expr, base_expr);
            let azz = ctx.add_zero_eq(zero);
            let add_zz = ctx.mk_add(zero, zero);
            let combined = ctx.le_cast_right(lhs, add_zz, zero, combined, azz);
            let mut next_gens = s_gens.clone();
            next_gens.extend_from_slice(base_gens);
            let append_proof = ctx.append_eq(&s_gens, base_gens);
            let next_canon = ctx.gens_to_expr(&next_gens);
            s_proof = ctx.le_cast_left(lhs, next_canon, zero, combined, append_proof);
            s_gens = next_gens;
            s_expr = next_canon;
        }
        acc = Some(match acc {
            None => (s_proof, s_gens),
            Some((acc_proof, acc_gens)) => {
                let acc_expr = ctx.gens_to_expr(&acc_gens);
                let combined = ctx.add_le_add_app(acc_expr, zero, s_expr, zero, acc_proof, s_proof);
                let azz = ctx.add_zero_eq(zero);
                let add_zz = ctx.mk_add(zero, zero);
                let lhs = ctx.mk_add(acc_expr, s_expr);
                let combined = ctx.le_cast_right(lhs, add_zz, zero, combined, azz);
                let mut next_gens = acc_gens.clone();
                next_gens.extend_from_slice(&s_gens);
                let append_proof = ctx.append_eq(&acc_gens, &s_gens);
                let next_canon = ctx.gens_to_expr(&next_gens);
                let new_proof = ctx.le_cast_left(lhs, next_canon, zero, combined, append_proof);
                (new_proof, next_gens)
            }
        });
    }
    let (le_lsum_zero, all_gens) = acc.expect("at least one branch atom");
    // Normalize: variables cancel, leaving exactly `K` `One`s with `K > 0`.
    let lsum_canon = ctx.gens_to_expr(&all_gens);
    let (norm_gens, norm_proof) = ctx.normalize_gens(&all_gens);
    let k_int = i128::try_from(norm_gens.len()).map_err(|_| ReconstructError::MalformedStep {
        rule: "disjunctive_la_generic".to_owned(),
        detail: "normalized constant overflows i128".to_owned(),
    })?;
    if k_int <= 0 || norm_gens.iter().any(|g| *g != Gen::One) {
        return Err(ReconstructError::MalformedStep {
            rule: "disjunctive_la_generic".to_owned(),
            detail: "branch Farkas combination did not reduce to a positive constant".to_owned(),
        });
    }
    let k_expr = ctx.gens_to_expr(&norm_gens);
    let le_k_zero = ctx.le_cast_left(lsum_canon, k_expr, zero, le_lsum_zero, norm_proof);
    let lt_zero_k = ctx.lt_zero_ones(k_int);
    let lt_zero_zero = ctx.lt_of_lt_of_le_app(zero, k_expr, zero, lt_zero_k, le_k_zero);
    let irrefl = ctx.kernel.const_(ctx.arith.lt_irrefl, vec![]);
    let e = ctx.kernel.app(irrefl, zero);
    Ok(ctx.kernel.app(e, lt_zero_zero))
}

// ===========================================================================
// Boolean-structured (disjunctive) QF_LRA reconstruction.
//
// The conjunctive Farkas path (`reconstruct_lra_proof`) handles only assertion
// sets that the conjunctive decision procedure can collect — a top-level
// positive `Or` is reported `Unsupported` by `lra_farkas_certificate`, so a
// disjunctive UNSAT carries NO Lean proof there. This block closes the smallest
// uncovered disjunctive shape: a conjunctive linear-real system plus exactly one
// clause `(L₁ ∨ L₂)` of NON-STRICT linear-real literals, where each leaf
// `conj ∧ Lᵢ` is conjunctive-Farkas-refutable.
//
// The reconstruction is a kernel case-split (`Or.rec`, the eliminator behind
// `Or.elim`) on a hypothesis `hor : Enc(L₁ ∨ L₂)`. Each minor premise binds the
// branch literal `hᵢ : Enc(Lᵢ)` as a free variable, reuses the conjunctive
// general-Farkas fold to derive `branchᵢ : False` (the conjunctive atoms remain
// the verbatim `hyp_axiom` hypotheses; only the branch literal flows in as the
// bound `hᵢ`), then abstracts `hᵢ` into a `fun (hᵢ : Enc Lᵢ) => branchᵢ` lambda.
// The kernel `infer`s the assembled `Or.rec … hor : False`; a wrong fold ⇒
// `KernelRejected`, never a wrong `False`. The only added axioms are the
// conjunctive constraint hypotheses and `hor` (the verbatim disjunction).
// ===========================================================================

/// A non-strict real linear literal `Lᵢ` already normalized to `E ≤ 0` form, as
/// the canonical generators of `E` (over a *shared* symbol→index map) plus the
/// originating IR [`TermId`]. Built by [`disjunctive_branch_literal`].
#[derive(Debug, Clone)]
struct BranchLiteral {
    /// Canonical generators of `E` where the literal denotes `E ≤ 0`.
    gens: Vec<Gen>,
    /// The original IR atom (a real `≤`/`≥`), used to drive the per-leaf
    /// conjunctive decision procedure.
    term: TermId,
}

/// Normalize a non-strict real literal `term` (`l ≤ r` / `l ≥ r`) to `E ≤ 0` and
/// return its canonical generators over the **shared** symbol→index map `syms`
/// (so two literals / the conjunctive atoms agree on every variable's kernel
/// constant). `E = l − r` for `≤`, `E = r − l` for `≥`. Returns `None` for a
/// strict / non-real / out-of-slice literal (any coefficient outside the
/// generator alphabet ±1·var, ±1).
fn disjunctive_branch_literal(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<BranchLiteral> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let l = real_to_lin_inner(arena, args[0], syms)?;
    let r = real_to_lin_inner(arena, args[1], syms)?;
    // `l ≤ r` ⇒ `l − r ≤ 0`; `l ≥ r` ⇒ `r − l ≤ 0`. Strict / non-comparison: decline.
    let e = match op {
        IrOp::RealLe => l.sub(&r)?,
        IrOp::RealGe => r.sub(&l)?,
        _ => return None,
    };
    let gens = LraReconstructCtx::lin_to_gens(&e)?;
    Some(BranchLiteral { gens, term })
}

/// The structural decomposition of a disjunctive-LRA query (the output of
/// [`split_disjunctive_lra`]): the conjunctive assertion [`TermId`]s, the two
/// parsed branch literals of the single clause, and the shared symbol→index map
/// over which every literal's and conjunctive atom's variables are encoded.
type DisjunctiveSplit = (
    Vec<TermId>,
    BranchLiteral,
    BranchLiteral,
    BTreeMap<axeyum_ir::SymbolId, usize>,
);

/// Split `assertions` into `(conj, l1, l2, syms)` for the disjunctive-LRA shape:
/// **exactly one** assertion is a binary `Or` of two non-strict real-linear
/// literals, and every other assertion is a conjunctive real-linear constraint
/// (`≤`/`<`/`=`/`≥`/`>`). Returns the conjunctive [`TermId`]s and the two parsed
/// branch literals (over a shared symbol→index map). `None` if the shape does not
/// hold (no clause, more than one clause, a strict / out-of-slice branch literal,
/// or a non-linear conjunctive assertion).
fn split_disjunctive_lra(arena: &TermArena, assertions: &[TermId]) -> Option<DisjunctiveSplit> {
    let mut syms: BTreeMap<axeyum_ir::SymbolId, usize> = BTreeMap::new();
    let mut conj: Vec<TermId> = Vec::new();
    let mut clause: Option<(BranchLiteral, BranchLiteral)> = None;
    for &a in assertions {
        if let IrTermNode::App {
            op: IrOp::BoolOr,
            args,
        } = arena.node(a)
        {
            if args.len() != 2 || clause.is_some() {
                return None; // not binary, or a second clause — out of this slice
            }
            let l1 = disjunctive_branch_literal(arena, args[0], &mut syms)?;
            let l2 = disjunctive_branch_literal(arena, args[1], &mut syms)?;
            clause = Some((l1, l2));
        } else {
            // A conjunctive assertion: it must be a real-linear constraint so the
            // shared symbol map covers its variables (and the leaf decides cleanly).
            if as_le_constraint(arena, a).is_none()
                && as_lt_constraint(arena, a).is_none()
                && !is_real_eq_constraint(arena, a, &mut syms)
            {
                return None;
            }
            // Thread the conjunctive variables through the shared map too.
            register_real_vars(arena, a, &mut syms);
            conj.push(a);
        }
    }
    let (l1, l2) = clause?;
    Some((conj, l1, l2, syms))
}

/// Whether `term` is a real equality `a = b` over the linear subset, threading its
/// variables into the shared `syms` map.
fn is_real_eq_constraint(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> bool {
    let IrTermNode::App { op: IrOp::Eq, args } = arena.node(term) else {
        return false;
    };
    if args.len() != 2 || arena.sort_of(args[0]) != IrSort::Real {
        return false;
    }
    real_to_lin_inner(arena, args[0], syms).is_some()
        && real_to_lin_inner(arena, args[1], syms).is_some()
}

/// Register every real variable reachable in `term` into the shared symbol→index
/// map (in first-seen order), so the kernel constant for a symbol is the same
/// whether it appears in a conjunctive atom or a branch literal.
fn register_real_vars(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let IrTermNode::Symbol(s) = arena.node(t)
            && arena.sort_of(t) == IrSort::Real
        {
            let next = syms.len();
            syms.entry(*s).or_insert(next);
        }
        if let IrTermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
}

/// Detect the **disjunctive-LRA refutation** shape: the [`split_disjunctive_lra`]
/// structure holds **and** each leaf `conj ∧ Lᵢ` is conjunctive-Farkas-refutable
/// (`unsat`). A satisfiable disjunctive set (some leaf is `sat`) returns `false`
/// so no fabricated proof is routed. The whole set being UNSAT follows from both
/// leaves being UNSAT (`(L₁ ∨ L₂) ∧ conj` is unsat iff `conj ∧ L₁` and
/// `conj ∧ L₂` are both unsat).
#[must_use]
pub(super) fn is_disjunctive_lra_refutation(arena: &TermArena, assertions: &[TermId]) -> bool {
    let Some((conj, l1, l2, _syms)) = split_disjunctive_lra(arena, assertions) else {
        return false;
    };
    leaf_is_farkas_unsat(arena, &conj, l1.term) && leaf_is_farkas_unsat(arena, &conj, l2.term)
}

/// Whether the leaf `conj ∧ literal` has a (self-checked) conjunctive Farkas
/// refutation. Any decision error / `sat` / `unknown` ⇒ `false` (decline).
fn leaf_is_farkas_unsat(arena: &TermArena, conj: &[TermId], literal: TermId) -> bool {
    let mut leaf: Vec<TermId> = conj.to_vec();
    leaf.push(literal);
    matches!(crate::lra_farkas_certificate(arena, &leaf), Ok(Some(_)))
}

/// A non-strict `(<= left right)` constraint as `(left_lin, right_lin)` linear
/// forms, or `None` if `term` is not a real `≤`/`≥` over the linear subset this
/// slice handles. A `≥` is normalized by swapping sides into `≤` form.
#[allow(dead_code)]
fn as_le_constraint(arena: &TermArena, term: TermId) -> Option<(LinR, LinR)> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (real_to_lin(arena, args[0])?, real_to_lin(arena, args[1])?);
    match op {
        IrOp::RealLe => Some((l, r)),
        IrOp::RealGe => Some((r, l)),
        _ => None,
    }
}

/// Parse a strict real comparison `(< L R)` / `(> L R)` into `(L, R)` with the
/// relation `L < R` (`>` swapped), each side a [`LinR`]. Returns `None` for a
/// non-strict or non-real-comparison term.
fn as_lt_constraint(arena: &TermArena, term: TermId) -> Option<(LinR, LinR)> {
    let IrTermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (real_to_lin(arena, args[0])?, real_to_lin(arena, args[1])?);
    match op {
        IrOp::RealLt => Some((l, r)),
        IrOp::RealGt => Some((r, l)),
        _ => None,
    }
}

/// Lower an IR real term to a [`LinR`] over dense variable indices keyed by symbol,
/// for the linear subset (`Symbol`, `RealConst`, `RealNeg`, `RealAdd`, `RealSub`,
/// and `RealMul` with a constant factor). Returns `None` outside that fragment.
#[allow(dead_code)]
pub(super) fn real_to_lin(arena: &TermArena, term: TermId) -> Option<LinR> {
    real_to_lin_inner(arena, term, &mut BTreeMap::new())
}

/// As [`real_to_lin`], threading the (symbol → dense index) memo so repeated
/// variables share an index, in first-seen order.
#[allow(dead_code)]
fn real_to_lin_inner(
    arena: &TermArena,
    term: TermId,
    vars: &mut BTreeMap<axeyum_ir::SymbolId, usize>,
) -> Option<LinR> {
    match arena.node(term) {
        IrTermNode::RealConst(value) => Some(LinR::constant(*value)),
        IrTermNode::Symbol(symbol) if arena.sort_of(term) == IrSort::Real => {
            let next = vars.len();
            let index = *vars.entry(*symbol).or_insert(next);
            Some(LinR::var(index))
        }
        IrTermNode::App {
            op: IrOp::RealNeg,
            args,
        } => real_to_lin_inner(arena, args[0], vars)?.neg(),
        IrTermNode::App {
            op: IrOp::RealAdd,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            a.add(&b)
        }
        IrTermNode::App {
            op: IrOp::RealSub,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            a.sub(&b)
        }
        IrTermNode::App {
            op: IrOp::RealMul,
            args,
        } => {
            let a = real_to_lin_inner(arena, args[0], vars)?;
            let b = real_to_lin_inner(arena, args[1], vars)?;
            // Linear: one factor must be a bare constant.
            if a.coeffs.is_empty() {
                scale_lin(&b, a.constant)
            } else if b.coeffs.is_empty() {
                scale_lin(&a, b.constant)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Scale a [`LinR`] by a constant factor, declining (`None`) on any `i128`
/// overflow (the caller then falls back to a non-reconstruction path / decline).
#[allow(dead_code)]
fn scale_lin(lin: &LinR, factor: Rational) -> Option<LinR> {
    if factor.is_zero() {
        return Some(LinR::constant(Rational::zero()));
    }
    let mut coeffs = Vec::with_capacity(lin.coeffs.len());
    for &(i, c) in &lin.coeffs {
        coeffs.push((i, c.checked_mul(factor)?));
    }
    Some(LinR {
        coeffs,
        constant: lin.constant.checked_mul(factor)?,
    })
}

/// Match two `≤`-constraints `(l0 ≤ r0)`, `(l1 ≤ r1)` as the transitivity shape
/// `e ≤ 0 ∧ 1 ≤ e` for a shared bare-variable expression `e`. Returns `(e, ())`
/// (the shared expression as a [`LinR`]) when matched, else `None`.
///
/// Slice 1 fixes `e` to a single bare variable so the order chain stays the literal
/// baby-Farkas shape (`le one e`, `le e zero`); the general affine `e` and scaled
/// multipliers are a later slice.
#[allow(dead_code)]
fn match_transitivity_pair(c0: &(LinR, LinR), c1: &(LinR, LinR)) -> Option<(LinR, ())> {
    // Normalize each constraint `l ≤ r` to `(e, role)` where role is upper bound
    // `e ≤ 0` (r is 0, l is the bare var) or lower bound `1 ≤ e` (l is 1, r is the
    // bare var).
    let classify = |c: &(LinR, LinR)| -> Option<(usize, Bound)> {
        let (l, r) = c;
        if let Some(v) = l.as_bare_var()
            && r.is_constant_eq(Rational::zero())
        {
            return Some((v, Bound::Upper)); // v ≤ 0
        }
        if let Some(v) = r.as_bare_var()
            && l.is_constant_eq(Rational::integer(1))
        {
            return Some((v, Bound::Lower)); // 1 ≤ v
        }
        None
    };
    let (v0, b0) = classify(c0)?;
    let (v1, b1) = classify(c1)?;
    if v0 != v1 || b0 == b1 {
        return None; // must be the SAME variable, one upper and one lower bound
    }
    Some((LinR::var(v0), ()))
}

/// Which bound a transitivity constraint plays in `e ≤ 0 ∧ 1 ≤ e`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
enum Bound {
    /// `e ≤ 0` (an upper bound on `e`).
    Upper,
    /// `1 ≤ e` (a lower bound on `e`).
    Lower,
}
