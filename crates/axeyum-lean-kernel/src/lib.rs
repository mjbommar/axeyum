//! In-tree Rust Lean kernel for Axeyum — data-structure slice (ADR-0036).
//!
//! The north star is Z3 **and Lean** parity: every `unsat`/`valid` result
//! should carry a machine-checkable proof a Lean-grade kernel accepts. This
//! crate is the first slice of that kernel: the term language plus its de Bruijn
//! machinery. WHNF reduction, definitional equality, and type checking are the
//! **next** slice and are intentionally absent here.
//!
//! The semantics are ported from `nanoda_lib` (a faithful Rust reimplementation
//! of the Lean 4 kernel), but adapted to axeyum's idioms: nanoda's
//! lifetime-tagged arena (`Level<'a>`, `ExprPtr<'a>`) is replaced by a
//! `Vec`-backed hash-consing interner returning lifetime-free `Copy` ids
//! ([`NameId`]/[`LevelId`]/[`ExprId`]), mirroring `axeyum-ir`. No `'a` lifetimes
//! leak into public APIs (Hard Rule). The interner is deterministic: ids are
//! assigned in insertion order and no hash-map iteration order is observable.
//!
//! ## Contents
//!
//! - [`NameNode`] — hierarchical names (`Anonymous`/`Str`/`Num`).
//! - [`LevelNode`] — universe levels with `simplify`, `subst`, and the
//!   antisymmetric `leq`/`is_equiv` comparison.
//! - [`ExprNode`] — locally-nameless expressions with de Bruijn
//!   `instantiate`/`abstract`/`lift`, driven by cached loose-bvar / free-var
//!   metadata.
//!
//! ## Example
//!
//! Build the identity lambda `fun x => x` and instantiate its body with a
//! constant, recovering the constant:
//!
//! ```
//! use axeyum_lean_kernel::{BinderInfo, Kernel};
//!
//! let mut k = Kernel::new();
//! let n = k.anon();
//! let ty = k.sort_zero();
//! let body = k.bvar(0); // de Bruijn 0: the bound `x`
//! let id_fn = k.lam(n, ty, body, BinderInfo::Default);
//!
//! // Take the lambda apart and instantiate `body` with a concrete argument.
//! let c_name = k.name_str(n, "c");
//! let c = k.const_(c_name, vec![]);
//! let inner = k.lam_body(id_fn).unwrap();
//! assert_eq!(k.instantiate(inner, &[c]), c);
//! ```

#![forbid(unsafe_code)]

mod env;
mod expr;
mod inductive;
mod level;
mod name;
mod prelude;
mod tc;

use std::collections::HashMap;
use std::fmt;

pub use env::{Declaration, Environment, RecRule, ReducibilityHint};
pub use expr::{BinderInfo, ExprId, ExprNode, Lit};
pub use level::{LevelId, LevelNode};
pub use name::{NameId, NameNode};
pub use prelude::{LogicPrelude, build_logic_prelude};
pub use tc::{KernelError, LocalContext, LocalDecl};

use expr::ExprMeta;

/// The interning arena and term builder for the Lean kernel.
///
/// Owns three hash-consed tables ([`NameNode`], [`LevelNode`], [`ExprNode`]).
/// Structurally equal nodes intern to the same id; ids are dense and assigned in
/// insertion order, so identical construction sequences are reproducible
/// (determinism rule). Handles are lifetime-free `Copy` ids and must not be
/// mixed across kernels.
#[derive(Debug, Default)]
pub struct Kernel {
    names: Vec<NameNode>,
    name_intern: HashMap<NameNode, NameId>,

    levels: Vec<LevelNode>,
    level_intern: HashMap<LevelNode, LevelId>,

    exprs: Vec<ExprNode>,
    expr_meta: Vec<ExprMeta>,
    expr_intern: HashMap<ExprNode, ExprId>,

    /// The global declaration environment (ADR-0036, slice 3). Declarations are
    /// admitted only through the type-checked [`Kernel::add_declaration`] gate.
    env: Environment,
}

// ---------------------------------------------------------------------------
// Interner core
// ---------------------------------------------------------------------------

impl Kernel {
    /// Creates an empty kernel.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn intern_name(&mut self, node: NameNode) -> NameId {
        if let Some(&id) = self.name_intern.get(&node) {
            return id;
        }
        let id = NameId(u32::try_from(self.names.len()).expect("name count fits u32"));
        self.names.push(node.clone());
        self.name_intern.insert(node, id);
        id
    }

    fn intern_level(&mut self, node: LevelNode) -> LevelId {
        if let Some(&id) = self.level_intern.get(&node) {
            return id;
        }
        let id = LevelId(u32::try_from(self.levels.len()).expect("level count fits u32"));
        self.levels.push(node.clone());
        self.level_intern.insert(node, id);
        id
    }

    fn intern_expr(&mut self, node: ExprNode) -> ExprId {
        if let Some(&id) = self.expr_intern.get(&node) {
            return id;
        }
        let meta = self.compute_expr_meta(&node);
        let id = ExprId(u32::try_from(self.exprs.len()).expect("expr count fits u32"));
        self.exprs.push(node.clone());
        self.expr_meta.push(meta);
        self.expr_intern.insert(node, id);
        id
    }

    /// The structural node of an interned name.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn name_node(&self, id: NameId) -> &NameNode {
        &self.names[id.index()]
    }

    /// The structural node of an interned level.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn level_node(&self, id: LevelId) -> &LevelNode {
        &self.levels[id.index()]
    }

    /// The structural node of an interned expression.
    ///
    /// # Panics
    ///
    /// Panics if `id` does not belong to this kernel.
    #[must_use]
    pub fn expr_node(&self, id: ExprId) -> &ExprNode {
        &self.exprs[id.index()]
    }

    /// A shared reference to the global declaration [`Environment`].
    #[must_use]
    pub fn environment(&self) -> &Environment {
        &self.env
    }
}

// ---------------------------------------------------------------------------
// Name builders
// ---------------------------------------------------------------------------

impl Kernel {
    /// The anonymous (empty) root name.
    pub fn anon(&mut self) -> NameId {
        self.intern_name(NameNode::Anonymous)
    }

    /// Appends string component `s` to `parent`.
    pub fn name_str(&mut self, parent: NameId, s: impl Into<String>) -> NameId {
        self.intern_name(NameNode::Str(parent, s.into()))
    }

    /// Appends numeric component `n` to `parent`.
    pub fn name_num(&mut self, parent: NameId, n: u64) -> NameId {
        self.intern_name(NameNode::Num(parent, n))
    }

    /// A wrapper that renders an interned name in dotted form (`a.b.1`) via
    /// [`fmt::Display`].
    #[must_use]
    pub fn display_name(&self, id: NameId) -> NameDisplay<'_> {
        NameDisplay { kernel: self, id }
    }
}

/// A [`fmt::Display`] adapter for an interned [`NameId`], printing the dotted
/// form (e.g. `a.b.1`). The anonymous name prints as `[anonymous]`.
#[derive(Debug, Clone, Copy)]
pub struct NameDisplay<'k> {
    kernel: &'k Kernel,
    id: NameId,
}

impl fmt::Display for NameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn go(k: &Kernel, id: NameId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match k.name_node(id) {
                NameNode::Anonymous => write!(f, "[anonymous]"),
                NameNode::Str(parent, s) => write_component(k, *parent, f, |f| write!(f, "{s}")),
                NameNode::Num(parent, n) => write_component(k, *parent, f, |f| write!(f, "{n}")),
            }
        }

        fn write_component(
            k: &Kernel,
            parent: NameId,
            f: &mut fmt::Formatter<'_>,
            write_self: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
        ) -> fmt::Result {
            if matches!(k.name_node(parent), NameNode::Anonymous) {
                write_self(f)
            } else {
                go(k, parent, f)?;
                write!(f, ".")?;
                write_self(f)
            }
        }

        go(self.kernel, self.id, f)
    }
}

// ---------------------------------------------------------------------------
// Level builders
// ---------------------------------------------------------------------------

impl Kernel {
    /// The level `0` (`Zero`).
    pub fn level_zero(&mut self) -> LevelId {
        self.intern_level(LevelNode::Zero)
    }

    /// `Succ l`.
    pub fn level_succ(&mut self, l: LevelId) -> LevelId {
        self.intern_level(LevelNode::Succ(l))
    }

    /// `Max l r`.
    pub fn level_max(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.intern_level(LevelNode::Max(l, r))
    }

    /// `IMax l r`.
    pub fn level_imax(&mut self, l: LevelId, r: LevelId) -> LevelId {
        self.intern_level(LevelNode::IMax(l, r))
    }

    /// A universe parameter named `name`.
    pub fn level_param(&mut self, name: NameId) -> LevelId {
        self.intern_level(LevelNode::Param(name))
    }

    /// `Succ^n l` — apply `Succ` `n` times to `l`.
    pub fn level_offset(&mut self, mut l: LevelId, n: u64) -> LevelId {
        for _ in 0..n {
            l = self.level_succ(l);
        }
        l
    }

    /// Peels leading `Succ`s, returning the inner level and the count peeled.
    #[must_use]
    pub fn level_succs(&self, mut l: LevelId) -> (LevelId, usize) {
        let mut n = 0;
        while let LevelNode::Succ(pred) = self.level_node(l) {
            l = *pred;
            n += 1;
        }
        (l, n)
    }
}

// ---------------------------------------------------------------------------
// Level operations (ported from nanoda level.rs)
// ---------------------------------------------------------------------------

impl Kernel {
    /// `combining l r` — the smart `Max` constructor used by [`Kernel::simplify`].
    fn combining(&mut self, l: LevelId, r: LevelId) -> LevelId {
        match (self.level_node(l).clone(), self.level_node(r).clone()) {
            (LevelNode::Zero, _) => r,
            (_, LevelNode::Zero) => l,
            (LevelNode::Succ(lp), LevelNode::Succ(rp)) => {
                let pred = self.combining(lp, rp);
                self.level_succ(pred)
            }
            _ => self.level_max(l, r),
        }
    }

    /// Normalize a level to a canonical form. Idempotent: `simplify(simplify l)
    /// == simplify l`.
    pub fn simplify(&mut self, l: LevelId) -> LevelId {
        match self.level_node(l).clone() {
            LevelNode::Zero | LevelNode::Param(_) => l,
            LevelNode::Succ(val) => {
                let val = self.simplify(val);
                self.level_succ(val)
            }
            LevelNode::Max(lhs, rhs) => {
                let lhs = self.simplify(lhs);
                let rhs = self.simplify(rhs);
                self.combining(lhs, rhs)
            }
            LevelNode::IMax(lhs, rhs) => {
                let l_simp = self.simplify(lhs);
                let r_simp = self.simplify(rhs);
                if self.is_definitely_zero(l_simp) || self.is_definitely_one(l_simp) {
                    r_simp
                } else {
                    match self.level_node(r_simp).clone() {
                        LevelNode::Zero => r_simp,
                        LevelNode::Succ(_) => self.combining(l_simp, r_simp),
                        _ => self.level_imax(l_simp, r_simp),
                    }
                }
            }
        }
    }

    /// Syntactic check: is this level literally `Zero`?
    fn is_definitely_zero(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Zero)
    }

    /// Syntactic check: is this level literally `Succ Zero`?
    fn is_definitely_one(&self, l: LevelId) -> bool {
        match self.level_node(l) {
            LevelNode::Succ(pred) => self.is_definitely_zero(*pred),
            _ => false,
        }
    }

    fn is_param_level(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Param(_))
    }

    fn is_any_max(&self, l: LevelId) -> bool {
        matches!(self.level_node(l), LevelNode::Max(..) | LevelNode::IMax(..))
    }

    /// Substitute universe parameters in `l` according to `subst`
    /// (`Param(name) -> level`). Parameters not present in `subst` are kept.
    pub fn substitute_level(&mut self, l: LevelId, subst: &[(NameId, LevelId)]) -> LevelId {
        match self.level_node(l).clone() {
            LevelNode::Zero => l,
            LevelNode::Succ(val) => {
                let val = self.substitute_level(val, subst);
                self.level_succ(val)
            }
            LevelNode::Max(lhs, rhs) => {
                let lhs = self.substitute_level(lhs, subst);
                let rhs = self.substitute_level(rhs, subst);
                self.level_max(lhs, rhs)
            }
            LevelNode::IMax(lhs, rhs) => {
                let lhs = self.substitute_level(lhs, subst);
                let rhs = self.substitute_level(rhs, subst);
                self.level_imax(lhs, rhs)
            }
            LevelNode::Param(name) => {
                for &(k, v) in subst {
                    if k == name {
                        return v;
                    }
                }
                l
            }
        }
    }

    /// Substitute universe parameters **inside an expression** `e`, replacing
    /// every `Param` named in `subst` wherever a level appears (`Sort` levels
    /// and `Const` universe arguments). Bound/free variables, literals, and the
    /// term structure are otherwise unchanged.
    ///
    /// This is the expression-level analogue of [`Kernel::substitute_level`],
    /// ported from nanoda's `subst_expr_levels`. It is used for universe
    /// instantiation: a `Const(name, level_args)` instantiates the
    /// declaration's `uparams` with `level_args` by substituting in the
    /// declaration's type (and, when δ-unfolding, its value).
    pub fn substitute_expr_levels(&mut self, e: ExprId, subst: &[(NameId, LevelId)]) -> ExprId {
        match self.expr_node(e).clone() {
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::Sort(level) => {
                let level = self.substitute_level(level, subst);
                self.sort(level)
            }
            ExprNode::Const(name, levels) => {
                let levels = levels
                    .into_iter()
                    .map(|l| self.substitute_level(l, subst))
                    .collect();
                self.const_(name, levels)
            }
            ExprNode::App(f, a) => {
                let f = self.substitute_expr_levels(f, subst);
                let a = self.substitute_expr_levels(a, subst);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.substitute_expr_levels(ty, subst);
                let body = self.substitute_expr_levels(body, subst);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.substitute_expr_levels(ty, subst);
                let body = self.substitute_expr_levels(body, subst);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.substitute_expr_levels(ty, subst);
                let val = self.substitute_expr_levels(val, subst);
                let body = self.substitute_expr_levels(body, subst);
                self.let_(name, ty, val, body)
            }
        }
    }

    /// `subst` then `simplify` — the substitution used by `leq_imax_by_cases`.
    fn subst_simp(&mut self, l: LevelId, subst: &[(NameId, LevelId)]) -> LevelId {
        let l = self.substitute_level(l, subst);
        self.simplify(l)
    }

    /// Case split on whether a parameter is zero or non-zero, requiring the
    /// inequality under both substitutions.
    fn leq_imax_by_cases(
        &mut self,
        param: NameId,
        lhs: LevelId,
        rhs: LevelId,
        diff: isize,
    ) -> bool {
        let zero = self.level_zero();
        let param_lvl = self.level_param(param);
        let succ_param = self.level_succ(param_lvl);

        let to_zero = [(param, zero)];
        let to_succ = [(param, succ_param)];

        let lhs_0 = self.subst_simp(lhs, &to_zero);
        let rhs_0 = self.subst_simp(rhs, &to_zero);
        let lhs_s = self.subst_simp(lhs, &to_succ);
        let rhs_s = self.subst_simp(rhs, &to_succ);

        self.leq_core(lhs_0, rhs_0, diff) && self.leq_core(lhs_s, rhs_s, diff)
    }

    /// Core of the `<=` test on simplified levels. `diff` tracks how many more
    /// `Succ`s have been stripped from the right than the left (more positive ⇒
    /// the right side is larger).
    ///
    /// Ported line-for-line from nanoda's `leq_core`.
    fn leq_core(&mut self, l_in: LevelId, r_in: LevelId, diff: isize) -> bool {
        match (self.level_node(l_in).clone(), self.level_node(r_in).clone()) {
            (LevelNode::Zero, _) if diff >= 0 => true,
            (_, LevelNode::Zero) if diff < 0 => false,
            (LevelNode::Param(a), LevelNode::Param(x)) => a == x && diff >= 0,
            (LevelNode::Param(_), LevelNode::Zero) => false,
            (LevelNode::Zero, LevelNode::Param(_)) => diff >= 0,
            (LevelNode::Succ(s), _) => self.leq_core(s, r_in, diff - 1),
            (_, LevelNode::Succ(s)) => self.leq_core(l_in, s, diff + 1),
            (LevelNode::Max(a, b), _) => {
                self.leq_core(a, r_in, diff) && self.leq_core(b, r_in, diff)
            }
            // nanoda has these as two separate arms (Param|Max) and (Zero|Max)
            // with identical bodies; merged here as an or-pattern.
            (LevelNode::Param(_) | LevelNode::Zero, LevelNode::Max(x, y)) => {
                self.leq_core(l_in, x, diff) || self.leq_core(l_in, y, diff)
            }
            (LevelNode::IMax(a, b), LevelNode::IMax(x, y)) if a == x && b == y && diff >= 0 => true,
            (LevelNode::IMax(_, b), _) if self.is_param_level(b) => {
                let LevelNode::Param(p) = self.level_node(b).clone() else {
                    unreachable!()
                };
                self.leq_imax_by_cases(p, l_in, r_in, diff)
            }
            (_, LevelNode::IMax(_, y)) if self.is_param_level(y) => {
                let LevelNode::Param(p) = self.level_node(y).clone() else {
                    unreachable!()
                };
                self.leq_imax_by_cases(p, l_in, r_in, diff)
            }
            (LevelNode::IMax(a, b), _) if self.is_any_max(b) => match self.level_node(b).clone() {
                LevelNode::IMax(x, y) => {
                    let new_lhs = self.level_imax(a, y);
                    let new_rhs = self.level_imax(x, y);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    self.leq_core(new_max, r_in, diff)
                }
                LevelNode::Max(x, y) => {
                    let new_lhs = self.level_imax(a, x);
                    let new_rhs = self.level_imax(a, y);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    let new_max = self.simplify(new_max);
                    self.leq_core(new_max, r_in, diff)
                }
                _ => unreachable!(),
            },
            (_, LevelNode::IMax(x, y)) if self.is_any_max(y) => match self.level_node(y).clone() {
                LevelNode::IMax(j, k) => {
                    let new_lhs = self.level_imax(x, k);
                    let new_rhs = self.level_imax(j, k);
                    let new_max = self.level_max(new_lhs, new_rhs);
                    self.leq_core(l_in, new_max, diff)
                }
                LevelNode::Max(j, k) => {
                    let new_lhs = self.level_imax(x, j);
                    let new_rhs = self.level_imax(x, k);
                    let new_rhs = self.level_max(new_lhs, new_rhs);
                    let new_rhs = self.simplify(new_rhs);
                    self.leq_core(l_in, new_rhs, diff)
                }
                _ => unreachable!(),
            },
            _ => unreachable!("leq_core: unhandled level pair"),
        }
    }

    /// `l <= r` on universe levels (simplifies both, then runs the core
    /// antisymmetric comparison).
    pub fn level_leq(&mut self, l: LevelId, r: LevelId) -> bool {
        let l = self.simplify(l);
        let r = self.simplify(r);
        self.leq_core(l, r, 0)
    }

    /// Antisymmetric equivalence: `l <= r` and `r <= l`.
    pub fn level_is_equiv(&mut self, l: LevelId, r: LevelId) -> bool {
        self.level_leq(l, r) && self.level_leq(r, l)
    }

    /// `l <= 0`, i.e. `l` is provably the zero universe.
    pub fn level_is_zero(&mut self, l: LevelId) -> bool {
        let zero = self.level_zero();
        self.level_leq(l, zero)
    }

    /// `1 <= l`, i.e. `l` is provably non-zero.
    pub fn level_is_nonzero(&mut self, l: LevelId) -> bool {
        let zero = self.level_zero();
        let one = self.level_succ(zero);
        self.level_leq(one, l)
    }
}

// ---------------------------------------------------------------------------
// Expr builders (compute and cache metadata at intern time)
// ---------------------------------------------------------------------------

impl Kernel {
    fn compute_expr_meta(&self, node: &ExprNode) -> ExprMeta {
        match node {
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => ExprMeta {
                num_loose_bvars: 0,
                has_fvars: false,
            },
            ExprNode::FVar(_) => ExprMeta {
                num_loose_bvars: 0,
                has_fvars: true,
            },
            // A `BVar(i)` is loose relative to its own position; one node above
            // it (under one binder) it has loose-range `i + 1`. Binders below
            // decrement via the binder cases here.
            ExprNode::BVar(i) => ExprMeta {
                num_loose_bvars: i + 1,
                has_fvars: false,
            },
            ExprNode::App(f, a) => {
                let mf = self.expr_meta[f.index()];
                let ma = self.expr_meta[a.index()];
                ExprMeta {
                    num_loose_bvars: mf.num_loose_bvars.max(ma.num_loose_bvars),
                    has_fvars: mf.has_fvars || ma.has_fvars,
                }
            }
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                let mt = self.expr_meta[ty.index()];
                let mb = self.expr_meta[body.index()];
                // The binder consumes one loose level in `body`.
                let body_loose = mb.num_loose_bvars.saturating_sub(1);
                ExprMeta {
                    num_loose_bvars: mt.num_loose_bvars.max(body_loose),
                    has_fvars: mt.has_fvars || mb.has_fvars,
                }
            }
            ExprNode::Let(_, ty, val, body) => {
                let mt = self.expr_meta[ty.index()];
                let mv = self.expr_meta[val.index()];
                let mb = self.expr_meta[body.index()];
                let body_loose = mb.num_loose_bvars.saturating_sub(1);
                ExprMeta {
                    num_loose_bvars: mt.num_loose_bvars.max(mv.num_loose_bvars).max(body_loose),
                    has_fvars: mt.has_fvars || mv.has_fvars || mb.has_fvars,
                }
            }
        }
    }

    /// A bound variable with de Bruijn index `idx`.
    pub fn bvar(&mut self, idx: u32) -> ExprId {
        self.intern_expr(ExprNode::BVar(idx))
    }

    /// A free/local variable with unique id `id`.
    pub fn fvar(&mut self, id: u64) -> ExprId {
        self.intern_expr(ExprNode::FVar(id))
    }

    /// A type universe `Sort level`.
    pub fn sort(&mut self, level: LevelId) -> ExprId {
        self.intern_expr(ExprNode::Sort(level))
    }

    /// `Sort 0` (i.e. `Prop`).
    pub fn sort_zero(&mut self) -> ExprId {
        let z = self.level_zero();
        self.sort(z)
    }

    /// A constant reference `name.{levels}`.
    pub fn const_(&mut self, name: NameId, levels: Vec<LevelId>) -> ExprId {
        self.intern_expr(ExprNode::Const(name, levels))
    }

    /// Application `fun arg`.
    pub fn app(&mut self, fun: ExprId, arg: ExprId) -> ExprId {
        self.intern_expr(ExprNode::App(fun, arg))
    }

    /// `fun (name : ty) => body`.
    pub fn lam(&mut self, name: NameId, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
        self.intern_expr(ExprNode::Lam(name, ty, body, info))
    }

    /// `(name : ty) -> body`.
    pub fn pi(&mut self, name: NameId, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
        self.intern_expr(ExprNode::Pi(name, ty, body, info))
    }

    /// `let name : ty := val; body`.
    pub fn let_(&mut self, name: NameId, ty: ExprId, val: ExprId, body: ExprId) -> ExprId {
        self.intern_expr(ExprNode::Let(name, ty, val, body))
    }

    /// A literal expression.
    pub fn lit(&mut self, lit: Lit) -> ExprId {
        self.intern_expr(ExprNode::Lit(lit))
    }

    /// The body of a `Lam`, or `None` if `e` is not a lambda.
    #[must_use]
    pub fn lam_body(&self, e: ExprId) -> Option<ExprId> {
        match self.expr_node(e) {
            ExprNode::Lam(_, _, body, _) => Some(*body),
            _ => None,
        }
    }

    /// The body of a `Pi`, or `None` if `e` is not a pi.
    #[must_use]
    pub fn pi_body(&self, e: ExprId) -> Option<ExprId> {
        match self.expr_node(e) {
            ExprNode::Pi(_, _, body, _) => Some(*body),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Expr metadata queries
// ---------------------------------------------------------------------------

impl Kernel {
    /// One more than the largest loose de Bruijn index escaping `e` (`0` ⇒
    /// closed). This is nanoda's `num_loose_bvars`.
    #[must_use]
    pub fn num_loose_bvars(&self, e: ExprId) -> u32 {
        self.expr_meta[e.index()].num_loose_bvars
    }

    /// Whether `e` has any loose (escaping) bound variables.
    #[must_use]
    pub fn has_loose_bvars(&self, e: ExprId) -> bool {
        self.num_loose_bvars(e) > 0
    }

    /// The half-open range `0..num_loose_bvars(e)` of loose de Bruijn indices
    /// that may escape `e`.
    #[must_use]
    pub fn loose_bvar_range(&self, e: ExprId) -> std::ops::Range<u32> {
        0..self.num_loose_bvars(e)
    }

    /// Whether any free variable occurs in `e`.
    #[must_use]
    pub fn has_fvars(&self, e: ExprId) -> bool {
        self.expr_meta[e.index()].has_fvars
    }
}

// ---------------------------------------------------------------------------
// De Bruijn operations (ported from nanoda expr.rs)
// ---------------------------------------------------------------------------

impl Kernel {
    /// Replace loose bound variables in `e` with the expressions in `subst`.
    ///
    /// `subst` substitutes the outermost loose bvars: a loose `BVar(offset + i)`
    /// at binder depth `offset` is replaced by `subst[subst.len() - 1 - i]`
    /// (matching nanoda's `substs.iter().rev().nth(i)`), with no shifting of the
    /// substituted terms (they are assumed closed at the substitution site, as
    /// in nanoda's β/ζ reduction usage). A loose index past the end of `subst`
    /// is left unchanged.
    ///
    /// On a closed expression this is the identity.
    pub fn instantiate(&mut self, e: ExprId, subst: &[ExprId]) -> ExprId {
        self.instantiate_aux(e, subst, 0)
    }

    fn instantiate_aux(&mut self, e: ExprId, subst: &[ExprId], offset: u32) -> ExprId {
        if self.num_loose_bvars(e) <= offset {
            return e;
        }
        match self.expr_node(e).clone() {
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::BVar(idx) => {
                debug_assert!(idx >= offset);
                let i = (idx - offset) as usize;
                subst.iter().rev().nth(i).copied().unwrap_or(e)
            }
            ExprNode::App(f, a) => {
                let f = self.instantiate_aux(f, subst, offset);
                let a = self.instantiate_aux(a, subst, offset);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.instantiate_aux(ty, subst, offset);
                let body = self.instantiate_aux(body, subst, offset + 1);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.instantiate_aux(ty, subst, offset);
                let body = self.instantiate_aux(body, subst, offset + 1);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.instantiate_aux(ty, subst, offset);
                let val = self.instantiate_aux(val, subst, offset);
                let body = self.instantiate_aux(body, subst, offset + 1);
                self.let_(name, ty, val, body)
            }
        }
    }

    /// Replace the free variables in `fvars` with loose bound variables.
    ///
    /// The inverse of [`Kernel::instantiate`]: when going *under* binders, each
    /// `FVar(fvars[j])` becomes `BVar(offset + (len-1-position))` so that the
    /// last entry of `fvars` (the innermost binder) maps to the lowest index.
    /// This matches nanoda's `abstr`: `locals.iter().rev().position(..)`.
    pub fn abstract_fvars(&mut self, e: ExprId, fvars: &[u64]) -> ExprId {
        self.abstract_aux(e, fvars, 0)
    }

    fn abstract_aux(&mut self, e: ExprId, fvars: &[u64], offset: u32) -> ExprId {
        if !self.has_fvars(e) {
            return e;
        }
        match self.expr_node(e).clone() {
            ExprNode::FVar(id) => match fvars.iter().rev().position(|&x| x == id) {
                Some(pos) => self.bvar(u32::try_from(pos).expect("fvar count fits u32") + offset),
                None => e,
            },
            ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::Lit(_) => e,
            ExprNode::App(f, a) => {
                let f = self.abstract_aux(f, fvars, offset);
                let a = self.abstract_aux(a, fvars, offset);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.abstract_aux(ty, fvars, offset);
                let body = self.abstract_aux(body, fvars, offset + 1);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.abstract_aux(ty, fvars, offset);
                let body = self.abstract_aux(body, fvars, offset + 1);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.abstract_aux(ty, fvars, offset);
                let val = self.abstract_aux(val, fvars, offset);
                let body = self.abstract_aux(body, fvars, offset + 1);
                self.let_(name, ty, val, body)
            }
        }
    }

    /// Shift loose bound variables in `e` by `amount`, only those whose index is
    /// `>= cutoff` (the standard lifting operation used when moving an
    /// expression under `amount` extra binders).
    pub fn lift_loose_bvars(&mut self, e: ExprId, cutoff: u32, amount: u32) -> ExprId {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e;
        }
        match self.expr_node(e).clone() {
            ExprNode::BVar(idx) => {
                if idx >= cutoff {
                    self.bvar(idx + amount)
                } else {
                    e
                }
            }
            ExprNode::Sort(_) | ExprNode::Const(..) | ExprNode::FVar(_) | ExprNode::Lit(_) => e,
            ExprNode::App(f, a) => {
                let f = self.lift_loose_bvars(f, cutoff, amount);
                let a = self.lift_loose_bvars(a, cutoff, amount);
                self.app(f, a)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, val, body) => {
                let ty = self.lift_loose_bvars(ty, cutoff, amount);
                let val = self.lift_loose_bvars(val, cutoff, amount);
                let body = self.lift_loose_bvars(body, cutoff + 1, amount);
                self.let_(name, ty, val, body)
            }
        }
    }
}

#[cfg(test)]
mod tests;
