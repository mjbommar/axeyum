//! The ordered-ring interface's **equality slot** (ADR-0468 phase R3).
//!
//! Today's [`generalize_over_ordered_ring`](super::generalize_over_ordered_ring)
//! abstracts the `Real` package's 30 declarations out of a Farkas refutation.
//! Nine of those 30 are stated with the kernel's own `Eq` — `add_comm`,
//! `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`, `mul_one`,
//! `mul_zero`, `left_distrib` — and the proof term *uses* `Eq` structurally: every
//! rewrite is an `Eq.rec` transport. That is fine as long as the intended model
//! interprets ring equality by `Eq`.
//!
//! ADR-0468 constructs ℝ as a **setoid**: `CReal.Equiv`, a defined relation on
//! regular ℚ-sequences, is real-number equality, and `Eq CReal` is not. That
//! choice is what buys the construction its **zero** trusted declarations — a
//! quotient would need `Quot.sound`, Dedekind cuts `propext` + `funext`. So a
//! refutation generalized over the ring interface can only be instantiated at the
//! constructed ℝ if the interface takes equality as a **parameter**.
//!
//! This module declares that parameter as a package of axioms, so the ordinary
//! reconstruction machinery — which builds proofs against declared constants and
//! λ-abstracts them at the end — can produce a setoid-shaped refutation with no
//! new abstraction mechanism:
//!
//! ```text
//! eq        : R → R → Prop            add_congr : eq a b → eq c d → eq (add a c) (add b d)
//! eq_refl   : eq a a                  mul_congr : eq a b → eq c d → eq (mul a c) (mul b d)
//! eq_symm   : eq a b → eq b a         neg_congr : eq a b → eq (neg a) (neg b)
//! eq_trans  : eq a b → eq b c → eq a c  le_congr : eq a b → eq c d → le a c → le b d
//!                                     lt_congr  : eq a b → eq c d → lt a c → lt b d
//! ```
//!
//! plus the nine `Eq`-laws **rewritten through `eq`**. Those nine types are not
//! written out here: they are computed from the environment by replacing the
//! partial application `Eq Real` with the `eq` symbol
//! ([`rewrite_eq_at_real`]), so a change to a `Real` law changes its setoid
//! counterpart rather than silently disagreeing with it. The rewrite is checked
//! to have actually fired on each of the nine.
//!
//! ## Why the five congruences are exactly five
//!
//! Not a design preference — a measurement. Every `Eq.rec` in the LRA/SOS
//! reconstruction sits inside one of eleven helper methods, and those eleven
//! collapse onto `symm`, `trans`, `add`-congruence (left and right), `mul`-congruence
//! (left and right), `neg`-congruence, `le`-cast (left and right) and `lt`-cast
//! (left and right). One-sided congruence is the two-sided form with `eq_refl` on
//! the other argument, so the two-sided form is what gets bound.
//!
//! ## Instantiating back at `Eq`
//!
//! ## What the round trip does and does not establish
//!
//! [`super::specialize_setoid_to_eq`] shows the 39-binder interface is at least
//! as strong as the 30-binder one: instantiate the slot at `Eq` and today's
//! statement comes back, so nothing was weakened and no downstream consumer of
//! the `Eq` form loses anything. It does **not** show the interface is
//! satisfiable by an equality that is not `Eq` — that is ADR-0468 phase R4,
//! where `CReal` supplies the slot from `CReal.Equiv` and its congruences, and
//! it is the phase that turns "usable in principle" into a model. What this
//! module removes is the obstacle: the proof term no longer mentions `Eq`
//! ([`super::residual_eq_constants`] measures it), so there is nothing left in
//! it that a defined equality cannot interpret.
//!
//! [`EqSetoidWitnesses`] declares the five generic lemmas that make the kernel's
//! `Eq` a model of this interface at an *arbitrary* carrier — `symm`, `trans`,
//! unary and binary congruence, and relation-congruence — each proved from
//! `Eq.rec` and therefore axiom-free. Because they are generic in the carrier,
//! supplying them takes no de Bruijn surgery at the use site: the witness for
//! `add_congr` is literally `congr₂ R add` applied to two bound variables.

use axeyum_lean_kernel::{
    ArithPrelude, BinderInfo, Declaration, ExprId, ExprNode, Kernel, KernelError, LogicPrelude,
    NameId,
};

use std::collections::HashMap;

use crate::reconstruct::ReconstructError;

/// Wrap a trusted-gate rejection as a reconstruction error.
fn rejected(rule: &str, what: &str, e: &KernelError) -> ReconstructError {
    ReconstructError::KernelRejected {
        rule: rule.to_owned(),
        detail: format!("{what} did not admit: {e:?}"),
    }
}

// ---------------------------------------------------------------------------
// A free-variable telescope builder.
//
// Every type and proof below is a ∀/λ telescope whose later binders mention
// earlier ones. Writing those with raw de Bruijn indices is where this kind of
// code goes wrong silently, so binders are introduced as FREE variables and
// closed in one pass by `Kernel::abstract_fvars`, which is the operation that
// knows the index arithmetic (including the shifts under nested binders inside a
// motive).
// ---------------------------------------------------------------------------

/// Binders introduced as free variables, closed into a ∀- or λ-telescope.
struct Tele {
    ids: Vec<u64>,
    tys: Vec<ExprId>,
    names: Vec<&'static str>,
}

impl Tele {
    fn new() -> Self {
        Self {
            ids: Vec::new(),
            tys: Vec::new(),
            names: Vec::new(),
        }
    }

    /// Introduce `name : ty` (where `ty` may mention earlier binders' free
    /// variables) and return its free-variable occurrence.
    fn bind(
        &mut self,
        kernel: &mut Kernel,
        next: &mut u64,
        name: &'static str,
        ty: ExprId,
    ) -> ExprId {
        let id = *next;
        *next += 1;
        self.ids.push(id);
        self.tys.push(ty);
        self.names.push(name);
        kernel.fvar(id)
    }

    fn close(&self, kernel: &mut Kernel, body: ExprId, lambda: bool) -> ExprId {
        let mut out = kernel.abstract_fvars(body, &self.ids);
        for position in (0..self.ids.len()).rev() {
            let ty = kernel.abstract_fvars(self.tys[position], &self.ids[..position]);
            let anon = kernel.anon();
            let name = kernel.name_str(anon, self.names[position]);
            out = if lambda {
                kernel.lam(name, ty, out, BinderInfo::Default)
            } else {
                kernel.pi(name, ty, out, BinderInfo::Default)
            };
        }
        out
    }

    fn close_pi(&self, kernel: &mut Kernel, body: ExprId) -> ExprId {
        self.close(kernel, body, false)
    }

    fn close_lam(&self, kernel: &mut Kernel, body: ExprId) -> ExprId {
        self.close(kernel, body, true)
    }
}

fn apply(kernel: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
    let mut out = head;
    for &arg in args {
        out = kernel.app(out, arg);
    }
    out
}

fn arrow(kernel: &mut Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.pi(anon, dom, cod, BinderInfo::Default)
}

fn prop(kernel: &mut Kernel) -> ExprId {
    let z = kernel.level_zero();
    kernel.sort(z)
}

fn type1(kernel: &mut Kernel) -> ExprId {
    let z = kernel.level_zero();
    let one = kernel.level_succ(z);
    kernel.sort(one)
}

// ---------------------------------------------------------------------------
// The equality slot, as declared axioms over the `Real` package.
// ---------------------------------------------------------------------------

/// The nine equality-interface declarations and the nine `Eq`-laws restated
/// through them: eighteen axioms, all under the `Real.Setoid` namespace.
///
/// These are declared into a reconstruction kernel on demand
/// (`LraReconstructCtx::enable_setoid_equality`). They are **not** part of
/// `build_arith_prelude` and do not change `real: axiom=30`: like the variable
/// and hypothesis axioms the LRA route already mints, they exist only to be
/// λ-abstracted back out of the finished proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetoidEq {
    /// `eq : Real → Real → Prop` — ring equality as a *parameter*.
    pub eq: NameId,
    /// `eq_refl : ∀ (a : Real), eq a a`.
    pub eq_refl: NameId,
    /// `eq_symm : ∀ (a b : Real), eq a b → eq b a`.
    pub eq_symm: NameId,
    /// `eq_trans : ∀ (a b c : Real), eq a b → eq b c → eq a c`.
    pub eq_trans: NameId,
    /// `add_congr : ∀ (a b c d : Real), eq a b → eq c d → eq (add a c) (add b d)`.
    pub add_congr: NameId,
    /// `mul_congr : ∀ (a b c d : Real), eq a b → eq c d → eq (mul a c) (mul b d)`.
    pub mul_congr: NameId,
    /// `neg_congr : ∀ (a b : Real), eq a b → eq (neg a) (neg b)`.
    pub neg_congr: NameId,
    /// `le_congr : ∀ (a b c d : Real), eq a b → eq c d → le a c → le b d`.
    pub le_congr: NameId,
    /// `lt_congr : ∀ (a b c d : Real), eq a b → eq c d → lt a c → lt b d`.
    pub lt_congr: NameId,

    // The nine `Eq`-laws, restated through `eq`. Each type is COMPUTED from the
    // corresponding `Real` declaration, never written out here.
    /// `Real.add_comm` with `Eq Real` replaced by `eq`.
    pub add_comm: NameId,
    /// `Real.add_assoc` with `Eq Real` replaced by `eq`.
    pub add_assoc: NameId,
    /// `Real.add_zero` with `Eq Real` replaced by `eq`.
    pub add_zero: NameId,
    /// `Real.add_neg` with `Eq Real` replaced by `eq`.
    pub add_neg: NameId,
    /// `Real.mul_comm` with `Eq Real` replaced by `eq`.
    pub mul_comm: NameId,
    /// `Real.mul_assoc` with `Eq Real` replaced by `eq`.
    pub mul_assoc: NameId,
    /// `Real.mul_one` with `Eq Real` replaced by `eq`.
    pub mul_one: NameId,
    /// `Real.mul_zero` with `Eq Real` replaced by `eq`.
    pub mul_zero: NameId,
    /// `Real.left_distrib` with `Eq Real` replaced by `eq`.
    pub left_distrib: NameId,
}

/// How many declarations the equality slot adds to the ring telescope: the
/// relation, its three equivalence laws, and the five congruences.
pub const EQUALITY_SLOT_BINDERS: usize = 9;

/// Declare the equality slot into `kernel`, over an already-built `arith`.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] from the trusted gate — which type-checks every axiom type,
/// so a malformed congruence statement is rejected here rather than surfacing as
/// a mysterious proof failure later. Also errors when the `Eq`→`eq` rewrite fails
/// to fire on one of the nine laws, which would mean the `Real` package no longer
/// has the shape this module was measured against.
#[allow(clippy::too_many_lines)]
pub fn declare_setoid_equality(
    kernel: &mut Kernel,
    arith: &ArithPrelude,
) -> Result<SetoidEq, ReconstructError> {
    let ns = kernel.name_str(arith.r, "Setoid");
    let r_ty = kernel.const_(arith.r, vec![]);
    let mut next_fvar: u64 = 0;

    // eq : Real → Real → Prop.
    let eq = {
        let p = prop(kernel);
        let inner = arrow(kernel, r_ty, p);
        let ty = arrow(kernel, r_ty, inner);
        declare(kernel, ns, "eq", ty)?
    };
    let eq_c = kernel.const_(eq, vec![]);
    let mk_eq = |kernel: &mut Kernel, x: ExprId, y: ExprId| {
        let c = kernel.const_(eq, vec![]);
        apply(kernel, c, &[x, y])
    };
    let mk_bin = |kernel: &mut Kernel, op: NameId, x: ExprId, y: ExprId| {
        let c = kernel.const_(op, vec![]);
        apply(kernel, c, &[x, y])
    };

    // eq_refl : ∀ (a : Real), eq a a.
    let eq_refl = {
        let mut t = Tele::new();
        let a = t.bind(kernel, &mut next_fvar, "a", r_ty);
        let body = mk_eq(kernel, a, a);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, "eq_refl", ty)?
    };

    // eq_symm : ∀ (a b : Real), eq a b → eq b a.
    let eq_symm = {
        let mut t = Tele::new();
        let a = t.bind(kernel, &mut next_fvar, "a", r_ty);
        let b = t.bind(kernel, &mut next_fvar, "b", r_ty);
        let hyp = mk_eq(kernel, a, b);
        let concl = mk_eq(kernel, b, a);
        let body = arrow(kernel, hyp, concl);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, "eq_symm", ty)?
    };

    // eq_trans : ∀ (a b c : Real), eq a b → eq b c → eq a c.
    let eq_trans = {
        let mut t = Tele::new();
        let a = t.bind(kernel, &mut next_fvar, "a", r_ty);
        let b = t.bind(kernel, &mut next_fvar, "b", r_ty);
        let c = t.bind(kernel, &mut next_fvar, "c", r_ty);
        let h1 = mk_eq(kernel, a, b);
        let h2 = mk_eq(kernel, b, c);
        let concl = mk_eq(kernel, a, c);
        let inner = arrow(kernel, h2, concl);
        let body = arrow(kernel, h1, inner);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, "eq_trans", ty)?
    };

    // add_congr / mul_congr : ∀ (a b c d), eq a b → eq c d → eq (op a c)(op b d).
    let binary_congr = |kernel: &mut Kernel, next: &mut u64, op: NameId, leaf: &'static str| {
        let mut t = Tele::new();
        let a = t.bind(kernel, next, "a", r_ty);
        let b = t.bind(kernel, next, "b", r_ty);
        let c = t.bind(kernel, next, "c", r_ty);
        let d = t.bind(kernel, next, "d", r_ty);
        let h1 = mk_eq(kernel, a, b);
        let h2 = mk_eq(kernel, c, d);
        let lhs = mk_bin(kernel, op, a, c);
        let rhs = mk_bin(kernel, op, b, d);
        let concl = mk_eq(kernel, lhs, rhs);
        let inner = arrow(kernel, h2, concl);
        let body = arrow(kernel, h1, inner);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, leaf, ty)
    };
    let add_congr = binary_congr(kernel, &mut next_fvar, arith.add, "add_congr")?;
    let mul_congr = binary_congr(kernel, &mut next_fvar, arith.mul, "mul_congr")?;

    // neg_congr : ∀ (a b : Real), eq a b → eq (neg a)(neg b).
    let neg_congr = {
        let mut t = Tele::new();
        let a = t.bind(kernel, &mut next_fvar, "a", r_ty);
        let b = t.bind(kernel, &mut next_fvar, "b", r_ty);
        let hyp = mk_eq(kernel, a, b);
        let neg = kernel.const_(arith.neg, vec![]);
        let na = kernel.app(neg, a);
        let neg = kernel.const_(arith.neg, vec![]);
        let nb = kernel.app(neg, b);
        let concl = mk_eq(kernel, na, nb);
        let body = arrow(kernel, hyp, concl);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, "neg_congr", ty)?
    };

    // le_congr / lt_congr : ∀ (a b c d), eq a b → eq c d → rel a c → rel b d.
    let relation_congr = |kernel: &mut Kernel, next: &mut u64, rel: NameId, leaf: &'static str| {
        let mut t = Tele::new();
        let a = t.bind(kernel, next, "a", r_ty);
        let b = t.bind(kernel, next, "b", r_ty);
        let c = t.bind(kernel, next, "c", r_ty);
        let d = t.bind(kernel, next, "d", r_ty);
        let h1 = mk_eq(kernel, a, b);
        let h2 = mk_eq(kernel, c, d);
        let premise = mk_bin(kernel, rel, a, c);
        let concl = mk_bin(kernel, rel, b, d);
        let innermost = arrow(kernel, premise, concl);
        let inner = arrow(kernel, h2, innermost);
        let body = arrow(kernel, h1, inner);
        let ty = t.close_pi(kernel, body);
        declare(kernel, ns, leaf, ty)
    };
    let le_congr = relation_congr(kernel, &mut next_fvar, arith.le, "le_congr")?;
    let lt_congr = relation_congr(kernel, &mut next_fvar, arith.lt, "lt_congr")?;

    // The nine Eq-laws, restated through `eq`. Types are COMPUTED.
    let restate = |kernel: &mut Kernel,
                   law: NameId,
                   leaf: &'static str|
     -> Result<NameId, ReconstructError> {
        let declared = kernel
            .environment()
            .get(law)
            .map(Declaration::ty)
            .expect("a Real law is in the environment");
        let (rewritten, fired) =
            rewrite_eq_at_real(kernel, declared, arith.logic.eq, arith.r, eq_c);
        if !fired {
            return Err(ReconstructError::KernelRejected {
                rule: "setoid_equality".to_owned(),
                detail: format!(
                    "`{}` does not mention `Eq Real`, so restating it through the equality slot \
                     would be a no-op: the Real package no longer has the shape this module was \
                     measured against",
                    kernel.display_name(law)
                ),
            });
        }
        declare(kernel, ns, leaf, rewritten)
    };
    let add_comm = restate(kernel, arith.add_comm, "add_comm")?;
    let add_assoc = restate(kernel, arith.add_assoc, "add_assoc")?;
    let add_zero = restate(kernel, arith.add_zero, "add_zero")?;
    let add_neg = restate(kernel, arith.add_neg, "add_neg")?;
    let mul_comm = restate(kernel, arith.mul_comm, "mul_comm")?;
    let mul_assoc = restate(kernel, arith.mul_assoc, "mul_assoc")?;
    let mul_one = restate(kernel, arith.mul_one, "mul_one")?;
    let mul_zero = restate(kernel, arith.mul_zero, "mul_zero")?;
    let left_distrib = restate(kernel, arith.left_distrib, "left_distrib")?;

    Ok(SetoidEq {
        eq,
        eq_refl,
        eq_symm,
        eq_trans,
        add_congr,
        mul_congr,
        neg_congr,
        le_congr,
        lt_congr,
        add_comm,
        add_assoc,
        add_zero,
        add_neg,
        mul_comm,
        mul_assoc,
        mul_one,
        mul_zero,
        left_distrib,
    })
}

fn declare(
    kernel: &mut Kernel,
    ns: NameId,
    leaf: &'static str,
    ty: ExprId,
) -> Result<NameId, ReconstructError> {
    let name = kernel.name_str(ns, leaf);
    kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty,
        })
        .map_err(|e| rejected("setoid_equality", leaf, &e))?;
    Ok(name)
}

/// Replace every occurrence of the partial application `Eq Real` by `eq`.
///
/// Returns the rewritten expression and whether the pattern fired at least once.
/// Only the two-argument-short spine `App(Const(Eq, [1]), Const(Real))` is
/// matched, so the result is *syntactically* interchangeable: instantiating the
/// resulting `eq` back at `Eq Real` reproduces the input node for node, with no
/// β-redex in between. That is what makes the round trip in
/// [`super::specialize_setoid_to_eq`] an identity rather than a defeq.
fn rewrite_eq_at_real(
    kernel: &mut Kernel,
    e: ExprId,
    eq_name: NameId,
    real: NameId,
    replacement: ExprId,
) -> (ExprId, bool) {
    let mut memo = HashMap::new();
    let mut fired = false;
    let out = rewrite_aux(kernel, e, eq_name, real, replacement, &mut fired, &mut memo);
    (out, fired)
}

fn rewrite_aux(
    kernel: &mut Kernel,
    e: ExprId,
    eq_name: NameId,
    real: NameId,
    replacement: ExprId,
    fired: &mut bool,
    memo: &mut HashMap<ExprId, ExprId>,
) -> ExprId {
    if let Some(&hit) = memo.get(&e) {
        return hit;
    }
    let rebuilt = match kernel.expr_node(e).clone() {
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Lit(_)
        | ExprNode::Const(..) => e,
        ExprNode::App(fun, arg) => {
            if matches!(kernel.expr_node(fun), ExprNode::Const(n, _) if *n == eq_name)
                && matches!(kernel.expr_node(arg), ExprNode::Const(n, _) if *n == real)
            {
                *fired = true;
                replacement
            } else {
                let fun = rewrite_aux(kernel, fun, eq_name, real, replacement, fired, memo);
                let arg = rewrite_aux(kernel, arg, eq_name, real, replacement, fired, memo);
                kernel.app(fun, arg)
            }
        }
        ExprNode::Proj(ty, field, structure) => {
            let structure = rewrite_aux(kernel, structure, eq_name, real, replacement, fired, memo);
            kernel.proj(ty, field, structure)
        }
        ExprNode::Lam(name, ty, body, info) => {
            let ty = rewrite_aux(kernel, ty, eq_name, real, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, real, replacement, fired, memo);
            kernel.lam(name, ty, body, info)
        }
        ExprNode::Pi(name, ty, body, info) => {
            let ty = rewrite_aux(kernel, ty, eq_name, real, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, real, replacement, fired, memo);
            kernel.pi(name, ty, body, info)
        }
        ExprNode::Let(name, ty, value, body) => {
            let ty = rewrite_aux(kernel, ty, eq_name, real, replacement, fired, memo);
            let value = rewrite_aux(kernel, value, eq_name, real, replacement, fired, memo);
            let body = rewrite_aux(kernel, body, eq_name, real, replacement, fired, memo);
            kernel.let_(name, ty, value, body)
        }
    };
    memo.insert(e, rebuilt);
    rebuilt
}

// ---------------------------------------------------------------------------
// `Eq` as a model of the equality slot, at an arbitrary carrier.
// ---------------------------------------------------------------------------

/// The five generic lemmas that make the kernel's `Eq` satisfy the equality
/// slot's laws at **any** `Type`-valued carrier, each proved from `Eq.rec` and so
/// carrying an empty axiom footprint.
///
/// Generic in the carrier on purpose: with these, instantiating a
/// setoid-generalized refutation at `Eq` is nine applications of constants to
/// bound variables, with no de Bruijn surgery and nothing written out per
/// fixture.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EqSetoidWitnesses {
    /// `∀ (α : Type) (a b : α), Eq α a b → Eq α b a`.
    pub symm: NameId,
    /// `∀ (α : Type) (a b c : α), Eq α a b → Eq α b c → Eq α a c`.
    pub trans: NameId,
    /// `∀ (α : Type) (f : α → α) (a b : α), Eq α a b → Eq α (f a) (f b)`.
    pub congr1: NameId,
    /// `∀ (α : Type) (f : α → α → α) (a b c d : α),
    ///   Eq α a b → Eq α c d → Eq α (f a c) (f b d)`.
    pub congr2: NameId,
    /// `∀ (α : Type) (p : α → α → Prop) (a b c d : α),
    ///   Eq α a b → Eq α c d → p a c → p b d`.
    pub rel_congr: NameId,
}

/// Declare the five witnesses under `ns`, proving each from `Eq.rec`.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the kernel declines a witness — which is where a wrong
/// motive would surface, since each is admitted as a `Theorem` whose stated type
/// the kernel re-derives from the term.
// Five short proofs that share one set of `Eq.rec` builders. Splitting them
// would duplicate those builders per lemma without making any one of them
// independently testable -- the test is that all five admit.
#[allow(clippy::too_many_lines)]
pub fn declare_eq_setoid_witnesses(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    ns: NameId,
) -> Result<EqSetoidWitnesses, ReconstructError> {
    let mut next_fvar: u64 = 1_000_000;
    let ty1 = type1(kernel);
    let p0 = prop(kernel);

    let mk_eq = |kernel: &mut Kernel, alpha: ExprId, x: ExprId, y: ExprId| {
        let z = kernel.level_zero();
        let one = kernel.level_succ(z);
        let c = kernel.const_(logic.eq, vec![one]);
        apply(kernel, c, &[alpha, x, y])
    };
    let mk_refl = |kernel: &mut Kernel, alpha: ExprId, x: ExprId| {
        let z = kernel.level_zero();
        let one = kernel.level_succ(z);
        let c = kernel.const_(logic.eq_refl, vec![one]);
        apply(kernel, c, &[alpha, x])
    };
    // `Eq.rec α p motive refl_case q h : motive q h`, with the motive in `Prop`.
    let mk_rec = |kernel: &mut Kernel,
                  alpha: ExprId,
                  p: ExprId,
                  motive: ExprId,
                  refl_case: ExprId,
                  q: ExprId,
                  h: ExprId| {
        let z = kernel.level_zero();
        let one = kernel.level_succ(z);
        let c = kernel.const_(logic.eq_rec, vec![z, one]);
        apply(kernel, c, &[alpha, p, motive, refl_case, q, h])
    };
    // `fun (x : α) (_ : Eq α p x) => <build x>` — `x` is `BVar(1)` in the body.
    let mk_motive = |kernel: &mut Kernel,
                     alpha: ExprId,
                     p: ExprId,
                     build: &dyn Fn(&mut Kernel, ExprId) -> ExprId| {
        let x_outer = kernel.bvar(1);
        let body = build(kernel, x_outer);
        let x_inner = kernel.bvar(0);
        let dom = mk_eq(kernel, alpha, p, x_inner);
        let anon = kernel.anon();
        let inner = kernel.lam(anon, dom, body, BinderInfo::Default);
        kernel.lam(anon, alpha, inner, BinderInfo::Default)
    };

    // symm α a b h := Eq.rec α a (fun x _ => Eq α x a) (Eq.refl α a) b h.
    let symm = {
        let mut t = Tele::new();
        let alpha = t.bind(kernel, &mut next_fvar, "α", ty1);
        let a = t.bind(kernel, &mut next_fvar, "a", alpha);
        let b = t.bind(kernel, &mut next_fvar, "b", alpha);
        let hyp_ty = mk_eq(kernel, alpha, a, b);
        let h = t.bind(kernel, &mut next_fvar, "h", hyp_ty);
        let motive = mk_motive(kernel, alpha, a, &|kernel, x| mk_eq(kernel, alpha, x, a));
        let refl_case = mk_refl(kernel, alpha, a);
        let body = mk_rec(kernel, alpha, a, motive, refl_case, b, h);
        let concl = mk_eq(kernel, alpha, b, a);
        admit(kernel, ns, "symm", &t, body, concl)?
    };
    // trans α a b c h1 h2 := Eq.rec α b (fun x _ => Eq α a x) h1 c h2.
    let trans = {
        let mut t = Tele::new();
        let alpha = t.bind(kernel, &mut next_fvar, "α", ty1);
        let a = t.bind(kernel, &mut next_fvar, "a", alpha);
        let b = t.bind(kernel, &mut next_fvar, "b", alpha);
        let c = t.bind(kernel, &mut next_fvar, "c", alpha);
        let h1_ty = mk_eq(kernel, alpha, a, b);
        let h1 = t.bind(kernel, &mut next_fvar, "h₁", h1_ty);
        let h2_ty = mk_eq(kernel, alpha, b, c);
        let h2 = t.bind(kernel, &mut next_fvar, "h₂", h2_ty);
        let motive = mk_motive(kernel, alpha, b, &|kernel, x| mk_eq(kernel, alpha, a, x));
        let body = mk_rec(kernel, alpha, b, motive, h1, c, h2);
        let concl = mk_eq(kernel, alpha, a, c);
        admit(kernel, ns, "trans", &t, body, concl)?
    };
    // congr1 α f a b h := Eq.rec α a (fun x _ => Eq α (f a)(f x)) (Eq.refl α (f a)) b h.
    let congr1 = {
        let mut t = Tele::new();
        let alpha = t.bind(kernel, &mut next_fvar, "α", ty1);
        let f_ty = arrow(kernel, alpha, alpha);
        let f = t.bind(kernel, &mut next_fvar, "f", f_ty);
        let a = t.bind(kernel, &mut next_fvar, "a", alpha);
        let b = t.bind(kernel, &mut next_fvar, "b", alpha);
        let hyp_ty = mk_eq(kernel, alpha, a, b);
        let h = t.bind(kernel, &mut next_fvar, "h", hyp_ty);
        let fa = kernel.app(f, a);
        let motive = mk_motive(kernel, alpha, a, &|kernel, x| {
            let fx = kernel.app(f, x);
            mk_eq(kernel, alpha, fa, fx)
        });
        let refl_case = mk_refl(kernel, alpha, fa);
        let body = mk_rec(kernel, alpha, a, motive, refl_case, b, h);
        let fb = kernel.app(f, b);
        let concl = mk_eq(kernel, alpha, fa, fb);
        admit(kernel, ns, "congr1", &t, body, concl)?
    };
    // congr2 α f a b c d h1 h2 := trans (f a c) (f b c) (f b d) <left> <right>.
    let congr2 = {
        let mut t = Tele::new();
        let alpha = t.bind(kernel, &mut next_fvar, "α", ty1);
        let f_ty = {
            let inner = arrow(kernel, alpha, alpha);
            arrow(kernel, alpha, inner)
        };
        let f = t.bind(kernel, &mut next_fvar, "f", f_ty);
        let a = t.bind(kernel, &mut next_fvar, "a", alpha);
        let b = t.bind(kernel, &mut next_fvar, "b", alpha);
        let c = t.bind(kernel, &mut next_fvar, "c", alpha);
        let d = t.bind(kernel, &mut next_fvar, "d", alpha);
        let h1_ty = mk_eq(kernel, alpha, a, b);
        let h1 = t.bind(kernel, &mut next_fvar, "h₁", h1_ty);
        let h2_ty = mk_eq(kernel, alpha, c, d);
        let h2 = t.bind(kernel, &mut next_fvar, "h₂", h2_ty);
        let fac = apply_bin(kernel, f, a, c);
        let fbc = apply_bin(kernel, f, b, c);
        let fbd = apply_bin(kernel, f, b, d);
        // left : Eq α (f a c) (f b c), by transporting the FIRST argument.
        let left = {
            let motive = mk_motive(kernel, alpha, a, &|kernel, x| {
                let fxc = apply_bin(kernel, f, x, c);
                mk_eq(kernel, alpha, fac, fxc)
            });
            let refl_case = mk_refl(kernel, alpha, fac);
            mk_rec(kernel, alpha, a, motive, refl_case, b, h1)
        };
        // right : Eq α (f b c) (f b d), by transporting the SECOND.
        let right = {
            let motive = mk_motive(kernel, alpha, c, &|kernel, x| {
                let fbx = apply_bin(kernel, f, b, x);
                mk_eq(kernel, alpha, fbc, fbx)
            });
            let refl_case = mk_refl(kernel, alpha, fbc);
            mk_rec(kernel, alpha, c, motive, refl_case, d, h2)
        };
        let trans_c = kernel.const_(trans, vec![]);
        let body = apply(kernel, trans_c, &[alpha, fac, fbc, fbd, left, right]);
        let concl = mk_eq(kernel, alpha, fac, fbd);
        admit(kernel, ns, "congr2", &t, body, concl)?
    };
    // rel_congr α p a b c d h1 h2 h3 := transport h3 : p a c along h1 then h2.
    let rel_congr = {
        let mut t = Tele::new();
        let alpha = t.bind(kernel, &mut next_fvar, "α", ty1);
        let p_ty = {
            let inner = arrow(kernel, alpha, p0);
            arrow(kernel, alpha, inner)
        };
        let p = t.bind(kernel, &mut next_fvar, "p", p_ty);
        let a = t.bind(kernel, &mut next_fvar, "a", alpha);
        let b = t.bind(kernel, &mut next_fvar, "b", alpha);
        let c = t.bind(kernel, &mut next_fvar, "c", alpha);
        let d = t.bind(kernel, &mut next_fvar, "d", alpha);
        let h1_ty = mk_eq(kernel, alpha, a, b);
        let h1 = t.bind(kernel, &mut next_fvar, "h₁", h1_ty);
        let h2_ty = mk_eq(kernel, alpha, c, d);
        let h2 = t.bind(kernel, &mut next_fvar, "h₂", h2_ty);
        let h3_ty = apply_bin(kernel, p, a, c);
        let h3 = t.bind(kernel, &mut next_fvar, "h₃", h3_ty);
        // step : p b c.
        let step = {
            let motive = mk_motive(kernel, alpha, a, &|kernel, x| apply_bin(kernel, p, x, c));
            mk_rec(kernel, alpha, a, motive, h3, b, h1)
        };
        let body = {
            let motive = mk_motive(kernel, alpha, c, &|kernel, x| apply_bin(kernel, p, b, x));
            mk_rec(kernel, alpha, c, motive, step, d, h2)
        };
        let concl = apply_bin(kernel, p, b, d);
        admit(kernel, ns, "rel_congr", &t, body, concl)?
    };

    Ok(EqSetoidWitnesses {
        symm,
        trans,
        congr1,
        congr2,
        rel_congr,
    })
}

fn apply_bin(kernel: &mut Kernel, f: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let e = kernel.app(f, x);
    kernel.app(e, y)
}

/// Close `body : concl` over `t` and admit it as a theorem under `ns.leaf`.
fn admit(
    kernel: &mut Kernel,
    ns: NameId,
    leaf: &'static str,
    t: &Tele,
    body: ExprId,
    concl: ExprId,
) -> Result<NameId, ReconstructError> {
    let value = t.close_lam(kernel, body);
    let ty = t.close_pi(kernel, concl);
    let name = kernel.name_str(ns, leaf);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|e| rejected("eq_setoid_witness", leaf, &e))?;
    Ok(name)
}
