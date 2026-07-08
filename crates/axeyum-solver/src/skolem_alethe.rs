//! Alethe proof **emission** for top-level **existential** skolemization
//! refutations (the first quantified-`unsat` slice that *certifies* the
//! skolemization step, P3.7).
//!
//! ## The obligation
//!
//! A top-level existential `∃x. P(x)` is **skolemized** to `P(sk)` for a fresh
//! constant `sk` (this is what [`crate::solve`]'s read-only
//! `skolemize_top_existentials` does, *trusted*). When the skolemized query
//! `{P(sk_1), …, P(sk_m)} ∪ Γ` is `unsat` — refuted by the universal/EUF
//! machinery — the original `{∃x.P_1(x), …} ∪ Γ` is `unsat` too. This module
//! makes that step **checkable**:
//!
//! - it produces a self-validating Alethe proof of the *skolemized* refutation
//!   (where each `sk_k` is an ordinary uninterpreted constant and each `P(sk_k)`
//!   is an `assume`d EUF unit), reusing [`crate::prove_quant_unsat_alethe`]
//!   verbatim; and
//! - it returns, alongside, a **skolemization certificate**: for each existential
//!   the bound-variable name, its single-equality body `P` (with the bound
//!   variable free), and the fresh skolem constant `sk_k`.
//!
//! The companion reconstruction
//! ([`crate::reconstruct::reconstruct_skolem_unsat_proof`]) reconstructs the
//! skolemized refutation **parametric in the `sk_k`** and wraps it in
//! `Exists.elim`, substituting each `sk_k` with the `Exists.elim`-bound witness
//! and each `P(sk_k)` assumption with the bound hypothesis — yielding a
//! kernel-checked `False` over the *original* `∃` assertions.
//!
//! ## This slice's boundary
//!
//! Each top-level existential body `P` must be a single equality `(= l r)` (so
//! `P(sk)` is exactly one `assume`d EUF unit, the parametric handle the
//! reconstruction abstracts). Multiple existentials and a mix with universals
//! and EUF side facts are supported; a non-equality existential body, a nested
//! quantifier under the existential, or a refutation outside the EUF/universal
//! reach yields `None`.

use axeyum_cnf::{AletheCommand, AletheTerm};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// One skolemized top-level existential, recorded so the reconstruction can
/// rebuild `Exists α p` and the `Exists.elim` wrapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkolemRecord {
    /// The bound-variable name `x` of `∃x. P(x)`.
    pub bound_var: String,
    /// The body `P` as an Alethe term with the bound variable **free** (as
    /// `Const(bound_var)`). The reconstruction renders the predicate
    /// `p := fun (x : α) => ⟦P x⟧` and the proposition `Exists α p` from this.
    pub body: AletheTerm,
    /// The fresh skolem constant `sk` substituted for the bound variable. In the
    /// skolemized refutation `Const(sk)` is an ordinary atom and the unit
    /// `P(sk) = body[x := sk]` is an `assume`d EUF hypothesis.
    pub skolem_name: String,
}

/// A skolemization refutation certificate: the checkable Alethe proof of the
/// *skolemized* refutation plus the per-existential [`SkolemRecord`]s.
#[derive(Debug, Clone)]
pub struct SkolemCert {
    /// The self-validated Alethe commands refuting the skolemized query (the
    /// [`crate::prove_quant_unsat_alethe`] shape).
    pub commands: Vec<AletheCommand>,
    /// The skolemized existentials, in assertion order.
    pub skolems: Vec<SkolemRecord>,
}

/// Emit a checkable skolemization refutation certificate for a query whose
/// top-level assertions include one or more existentials `∃x. (= l r)`, or
/// `None` if the query is not in this slice (no top-level existential with a
/// single-equality body, a body / side assertion with a nested quantifier, an
/// unsupported term shape, or no EUF/universal refutation of the skolemized
/// query).
///
/// The skolem constants are named `!skq_0`, `!skq_1`, … (the `!` prefix keeps
/// them out of the source namespace), one per top-level existential in assertion
/// order.
///
/// # Determinism
///
/// The skolem names and the ordering of [`SkolemCert::skolems`] are a
/// deterministic function of the assertion order; the embedded Alethe proof's
/// ids are those of [`crate::prove_quant_unsat_alethe`].
#[must_use]
pub fn prove_skolem_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<SkolemCert> {
    // Partition into top-level existentials and everything else.
    let mut skolems: Vec<SkolemRecord> = Vec::new();
    // The skolemized assertion set fed to the universal/EUF emitter.
    let mut skolemized: Vec<TermId> = Vec::with_capacity(assertions.len());
    let mut have_exists = false;

    for (k, &a) in assertions.iter().enumerate() {
        if let TermNode::App {
            op: Op::Exists(sym),
            args,
        } = arena.node(a)
        {
            let (sym, body) = (*sym, args[0]);
            // This slice: the body must be a single equality and quantifier-free.
            if !is_equality(arena, body) || contains_quantifier(arena, body) {
                return None;
            }
            let bound_var = arena.symbol(sym).0.to_owned();
            let sort = arena.symbol(sym).1;
            // The Alethe of the body with the bound variable free.
            let body_alethe = term_to_alethe(arena, body)?;
            // Fresh skolem constant of the bound variable's sort.
            let skolem_name = format!("!skq_{k}");
            let skolem = arena.declare_internal(&skolem_name, sort).ok()?;
            let skolem_term = arena.var(skolem);
            let inst = substitute(arena, body, sym, skolem_term)?;
            skolemized.push(inst);
            skolems.push(SkolemRecord {
                bound_var,
                body: body_alethe,
                skolem_name,
            });
            have_exists = true;
        } else {
            if contains_quantifier(arena, a) && !is_top_level_forall(arena, a) {
                // A buried existential (or non-prenex residual) is out of slice.
                // (Top-level universals are fine — the inner emitter handles them.)
                return None;
            }
            skolemized.push(a);
        }
    }
    if !have_exists {
        return None;
    }

    // Refute the skolemized query. The skolem constants are ordinary atoms there;
    // each `P(sk)` is an `assume`d unit. If the skolemized set still has a
    // top-level universal, use the universal+EUF emitter; otherwise the query is
    // pure EUF (a pure-∃ refutation), so use the EUF emitter directly. Both proof
    // shapes are reconstructed by [`crate::reconstruct_quant_unsat_proof`] (its
    // ground tail *is* the EUF walk).
    let has_universal = skolemized.iter().any(|&t| is_top_level_forall(arena, t));
    let commands = if has_universal {
        crate::prove_quant_unsat_alethe(arena, &skolemized)?
    } else {
        crate::prove_qf_uf_unsat_alethe(arena, &skolemized)?
    };
    Some(SkolemCert { commands, skolems })
}

/// Whether `term` is a 2-ary equality `(= l r)`.
fn is_equality(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::Eq, args } if args.len() == 2
    )
}

/// Whether `term` is a top-level universal `∀x. …` (not buried).
fn is_top_level_forall(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App {
            op: Op::Forall(_),
            ..
        }
    )
}

/// Whether `term` contains a quantifier anywhere in its subtree.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App { op, args } => {
            matches!(op, Op::Forall(_) | Op::Exists(_))
                || args.iter().any(|&a| contains_quantifier(arena, a))
        }
        _ => false,
    }
}

/// Substitute `replacement` for every occurrence of `var` in `term`. Mirrors the
/// universal emitter's `substitute` (this module's bodies are quantifier-free,
/// so no capture is possible).
fn substitute(
    arena: &mut TermArena,
    term: TermId,
    var: axeyum_ir::SymbolId,
    replacement: TermId,
) -> Option<TermId> {
    match arena.node(term) {
        TermNode::Symbol(s) if *s == var => Some(replacement),
        TermNode::Symbol(_)
        | TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => Some(term),
        TermNode::App { args, .. } => {
            let args = args.clone();
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(substitute(arena, a, var, replacement)?);
            }
            Some(arena.rebuild_with_args(term, &new_args))
        }
    }
}

/// Converts an IR term to an [`AletheTerm`], matching the universal emitter's
/// translator (symbol → `Const(name)`; `(= a b)` → `App("=", …)`; `not` →
/// `App("not", …)`; `apply(f, …)` → `App(f_name, …)`; constants → distinguishing
/// `Const`s). `None` for an unsupported shape.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BoolConst(b) => Some(AletheTerm::Const(format!("#bool:{b}"))),
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(format!("#bv{width}:{value}")))
        }
        TermNode::WideBvConst(w) => Some(AletheTerm::Const(format!("#wbv:{w:?}"))),
        TermNode::IntConst(i) => Some(AletheTerm::Const(format!("#int:{i}"))),
        TermNode::RealConst(r) => Some(AletheTerm::Const(format!("#real:{r:?}"))),
        TermNode::App { op, args } => {
            let head = match op {
                Op::Eq => "=".to_owned(),
                Op::BoolNot => "not".to_owned(),
                Op::Apply(func) => arena.function(*func).0.to_owned(),
                other => format!("{other:?}"),
            };
            let mut converted = Vec::with_capacity(args.len());
            for &arg in args {
                converted.push(term_to_alethe(arena, arg)?);
            }
            Some(AletheTerm::App(head, converted))
        }
    }
}

#[cfg(test)]
#[allow(clippy::similar_names, clippy::many_single_char_names)]
mod tests {
    use super::prove_skolem_unsat_alethe;
    use axeyum_ir::{Sort, TermArena};

    /// `∃x.(f x = c) ∧ ∀y.¬(f y = c)` — skolemize `∃` to `f(!skq_0)=c`,
    /// instantiate `∀` at `!skq_0` → `¬(f !skq_0 = c)`, contradiction. The
    /// emitter returns a certificate whose embedded Alethe self-validates and
    /// whose single skolem record describes `∃x.(f x = c)`.
    #[test]
    fn exists_forall_emits() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let y = arena.declare("y", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

        // ∃x. f(x) = c.
        let xv = arena.var(x);
        let cv = arena.var(c);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let exists = arena.exists(x, fx_eq_c).unwrap();
        // ∀y. ¬(f(y) = c).
        let yv = arena.var(y);
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_eq_c = arena.eq(fy, cv).unwrap();
        let not_fy_eq_c = arena.not(fy_eq_c).unwrap();
        let forall = arena.forall(y, not_fy_eq_c).unwrap();

        let cert = prove_skolem_unsat_alethe(&mut arena, &[exists, forall])
            .expect("emits a skolemization refutation certificate");
        assert_eq!(cert.skolems.len(), 1);
        assert_eq!(cert.skolems[0].bound_var, "x");
        assert_eq!(cert.skolems[0].skolem_name, "!skq_0");
        // The embedded skolemized proof derives the empty clause.
        assert!(!cert.commands.is_empty());
    }

    /// A query with no top-level existential yields `None` (this is the forall /
    /// EUF emitter's job, not the skolemizer's).
    #[test]
    fn no_existential_is_none() {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let a = arena.declare("a", alpha).unwrap();
        let b = arena.declare("b", alpha).unwrap();
        let av = arena.var(a);
        let bv = arena.var(b);
        let a_eq_b = arena.eq(av, bv).unwrap();
        assert!(prove_skolem_unsat_alethe(&mut arena, &[a_eq_b]).is_none());
    }
}
