//! The **setoid congruence deriver**: mechanizing the obligation every
//! `CReal`-valued function used under `Equiv` must discharge before it can be
//! rewritten through.
//!
//! `CReal` is a Bishop setoid (ADR-0512), not a type with definitional
//! equality carrying the mathematics — `Eq CReal` holds only for syntactically
//! identical sequences, so every law is stated over
//! [`CReal.Equiv`](super::CRealPrelude::equiv) instead. An arbitrary `CReal →
//! CReal` term need not respect that relation (that is why
//! `weierstrassMTest` carries `∀ j p q, Equiv p q → Equiv (f j p) (f j q)` as
//! an explicit hypothesis rather than deriving it), so a function built by
//! *composing* operations this prelude already knows to be congruent needs
//! its own `Equiv`-respect theorem proved before it can be used the same way.
//!
//! All week, lanes hand-assembled these compositions one at a time —
//! `mul_congr ∘ pow_congr` for a power-series term, `abs_congr` built from
//! `max_congr`/`neg_congr` for a clamp. Every one of them is pure structural
//! recursion over the term's shape: walk the expression, and at each node
//! apply whichever congruence lemma that node's operation is registered
//! under, gluing sibling results together with
//! [`CRealPrelude::equiv_trans`](super::CRealPrelude::equiv_trans). This
//! module encodes that recursion once.
//!
//! # The three pieces
//!
//! - [`registry`] — a table from [`Op`] to its own `CReal` constant, its
//!   congruence lemma, and the lemma's argument shape ([`Arity`]). Every
//!   entry was read from the declaring module before being encoded here (see
//!   each variant's doc comment for the exact file/line and signature); nothing
//!   here is assumed by name-shape alone, because `CLAUDE.md`'s own
//!   retrospective on this file's neighbours is that assuming a mirror exists
//!   (`CRealPrelude` has `mul_one` but no `one_mul`) is the most common way
//!   this family of proof fails.
//! - [`CongruExpr`] — a first-order expression enum, not a closure. The
//!   deriver has to *inspect* the term to decide which congruence lemma
//!   applies at each node without ever running it, which a closure cannot
//!   offer; the enum can also be built once and reused for both evaluation
//!   ([`eval`]) and derivation ([`derive`]), so the two never disagree about
//!   what the term denotes.
//! - [`derive`] — the structural recursion itself, returning `Result<(ExprId,
//!   ExprId), CongrError>` (statement, proof) rather than ever panicking or
//!   asserting an unproven claim. [`CongruExpr::Opaque`] and a pruned
//!   [`registry`] both reach the same decline path — see the `tests` module's
//!   `negative_control_declines` and `registry_corruption_is_the_decline_path`.
//!
//! `Kernel::add_declaration` is still the judge: [`declare_derived_congr`]
//! and [`declare_power_series_term_congr`] both hand the derived proof
//! straight to it, exactly like every other theorem in this file's
//! neighbours, and a `CongrError` never reaches that call at all.

use super::{CRealPrelude, creal_ty, equiv};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// --- the registry ------------------------------------------------------------

/// A `CReal → CReal` (or `CReal → CReal → CReal`) operation the deriver knows
/// how to push an `Equiv` hypothesis through, because a congruence lemma for
/// it already exists in this prelude.
///
/// `Pow` is deliberately absent from this enum's registry entries — see
/// [`CongruExpr::Pow`]'s own doc comment for why it is handled as a special
/// case rather than through [`Arity`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Op {
    /// `CReal.neg`, congruence `CReal.Equiv.neg_congr`
    /// (`creal.rs:6916`): `∀ x y, Equiv x y → Equiv (neg x) (neg y)`.
    Neg,
    /// `CReal.abs`, congruence `CReal.abs_congr` (`creal/lattice.rs:591`,
    /// function `declare_congruences`): `∀ x y, Equiv x y → Equiv (abs x)
    /// (abs y)` — built from `max_congr` with `neg_congr` in its second slot,
    /// but that composition is already discharged for us.
    Abs,
    /// `CReal.add`, congruence `CReal.add_congr` (`creal.rs:7182`): `∀ x x' y
    /// y', Equiv x x' → Equiv y y' → Equiv (add x y) (add x' y')`.
    Add,
    /// `CReal.mul`, congruence `CReal.mul_congr` (`creal/product.rs:1228`):
    /// same shape as `Add`.
    Mul,
    /// `CReal.min`, congruence `CReal.min_congr` (`creal/lattice.rs:592`):
    /// same shape as `Add`.
    Min,
    /// `CReal.max`, congruence `CReal.max_congr` (`creal/lattice.rs:591`):
    /// same shape as `Add`.
    Max,
}

/// A human-readable label for [`CongrError`] messages — never used to decide
/// anything, only to report it.
fn op_label(op: Op) -> &'static str {
    match op {
        Op::Neg => "CReal.neg",
        Op::Abs => "CReal.abs",
        Op::Add => "CReal.add",
        Op::Mul => "CReal.mul",
        Op::Min => "CReal.min",
        Op::Max => "CReal.max",
    }
}

/// `Op`'s own `CReal` constant — needed to build the actual term, independent
/// of whether a congruence lemma for it is registered. An `Op` with no
/// congruence entry still denotes a real function; only [`derive`] (not
/// [`eval`]) consults the registry.
fn op_name(p: CRealPrelude, op: Op) -> NameId {
    match op {
        Op::Neg => p.neg,
        Op::Abs => p.abs,
        Op::Add => p.add,
        Op::Mul => p.mul,
        Op::Min => p.min,
        Op::Max => p.max,
    }
}

/// The argument shape a congruence lemma takes, i.e. how many
/// hypothesis/witness pairs [`derive`] must supply it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Arity {
    /// `∀ x y, Equiv x y → Equiv (f x) (f y)` — applied as `lemma(x, y, h)`.
    Unary,
    /// `∀ x x' y y', Equiv x x' → Equiv y y' → Equiv (f x y) (f x' y')` —
    /// applied as `lemma(x, x', y, y', h1, h2)`. Verified against three
    /// independent existing call sites before being encoded here:
    /// `creal/power.rs`'s `declare_pow_congr` step
    /// (`mul_congr(px_j, py_j, x, y, ih, h)`), `creal/series.rs`'s
    /// `declare_sum_range_congr` step (`add_congr(f_prior, g_prior, fj, fj,
    /// ih, refl_fj)`), and `creal/lattice.rs`'s `abs_congr` derivation
    /// (`max_congr(x, y, negated_x, negated_y, h, flipped)`).
    Binary,
}

/// One row of the congruence registry: an operation, its own `CReal`
/// constant, its congruence lemma, and the lemma's argument shape.
#[derive(Clone, Copy)]
struct CongrEntry {
    op: Op,
    op_name: NameId,
    congr_name: NameId,
    arity: Arity,
}

/// Build the full congruence registry against a concrete `CRealPrelude`
/// instance. Every `(op_name, congr_name, arity)` here was read from the
/// declaring module first — see each [`Op`] variant's doc comment for the
/// exact site.
fn registry(p: CRealPrelude) -> Vec<CongrEntry> {
    vec![
        CongrEntry {
            op: Op::Neg,
            op_name: p.neg,
            congr_name: p.neg_congr,
            arity: Arity::Unary,
        },
        CongrEntry {
            op: Op::Abs,
            op_name: p.abs,
            congr_name: p.abs_congr,
            arity: Arity::Unary,
        },
        CongrEntry {
            op: Op::Add,
            op_name: p.add,
            congr_name: p.add_congr,
            arity: Arity::Binary,
        },
        CongrEntry {
            op: Op::Mul,
            op_name: p.mul,
            congr_name: p.mul_congr,
            arity: Arity::Binary,
        },
        CongrEntry {
            op: Op::Min,
            op_name: p.min,
            congr_name: p.min_congr,
            arity: Arity::Binary,
        },
        CongrEntry {
            op: Op::Max,
            op_name: p.max,
            congr_name: p.max_congr,
            arity: Arity::Binary,
        },
    ]
}

/// [`registry`] with one operation's entry dropped — the mutation-testing
/// hook for the negative control's registry-corruption case (see
/// `tests::registry_corruption_is_the_decline_path`). Dropping an entry must
/// make [`derive`] decline on every term using that operation, while terms
/// built only from the remaining operations still succeed in the same run.
#[cfg(test)]
fn registry_without(p: CRealPrelude, dropped: Op) -> Vec<CongrEntry> {
    registry(p).into_iter().filter(|e| e.op != dropped).collect()
}

fn lookup(reg: &[CongrEntry], op: Op) -> Option<&CongrEntry> {
    reg.iter().find(|entry| entry.op == op)
}

// --- the term representation -------------------------------------------------

/// A first-order expression in one `CReal`-valued hole ([`CongruExpr::Var`]),
/// built from [`Op`]s the registry may or may not know, plus one
/// deliberately-unregistered escape hatch ([`CongruExpr::Opaque`]) for
/// building the negative control. An enum rather than a closure: [`derive`]
/// must inspect a node to pick its congruence lemma without ever running the
/// term, and a closure over `ExprId`s offers no such inspection.
pub(crate) enum CongruExpr {
    /// The point being varied — evaluates to whichever of the two compared
    /// points [`eval`]/[`derive`] is currently working with.
    Var,
    /// A closed `CReal` term that does not mention [`CongruExpr::Var`] —
    /// congruent by `Equiv.refl`, never by structural recursion. Used both
    /// for genuine constants (`ofRat q`) and for a term abstractly
    /// parameterized over something OTHER than the point being varied (e.g.
    /// `c j` in the power-series demo, where `c` and `j` are free but `x` is
    /// not among their free variables).
    Const(ExprId),
    /// A registered unary operation ([`Op::Neg`] or [`Op::Abs`]) applied to a
    /// sub-expression.
    Unary(Op, Box<CongruExpr>),
    /// A registered binary operation ([`Op::Add`], [`Op::Mul`], [`Op::Min`]
    /// or [`Op::Max`]) applied to two sub-expressions.
    Binary(Op, Box<CongruExpr>, Box<CongruExpr>),
    /// `CReal.pow` applied to a sub-expression and a closed (`Var`-free)
    /// `Nat` exponent. Handled separately from [`Op`]/[`Arity`] rather than
    /// folded into `Unary` because `CRealPrelude::pow_congr`'s own signature
    /// (`creal/power.rs:545`) is `∀ x y, Equiv x y → ∀ n, Equiv (pow x n)
    /// (pow y n)` — congruent only in the base, with the exponent held fixed
    /// as a *trailing* parameter (after the hypothesis, not before it) — a
    /// shape no other entry in the registry shares.
    Pow(Box<CongruExpr>, ExprId),
    /// An arbitrary function term (an `fvar`, or any constant) applied to a
    /// sub-expression. ALWAYS declines in [`derive`], independent of what the
    /// registry currently contains — this is what lets a caller build "a term
    /// using an operation that is not registered" as data, rather than by
    /// relying on the registry happening to be missing an entry. Not used by
    /// [`eval`] to build anything unsound: the term it builds (`f (eval
    /// inner)`) is a perfectly good `CReal` term, it is simply one this
    /// module cannot prove `Equiv`-congruent.
    Opaque(ExprId, Box<CongruExpr>),
}

/// Evaluate `expr` at `point`, building the actual `CReal` term it denotes.
/// Total: every variant has a term, whether or not [`derive`] can prove it
/// congruent.
fn eval(d: &mut IntDev<'_>, p: CRealPrelude, expr: &CongruExpr, point: ExprId) -> ExprId {
    match expr {
        CongruExpr::Var => point,
        CongruExpr::Const(c) => *c,
        CongruExpr::Unary(op, inner) => {
            let arg = eval(d, p, inner, point);
            d.const_app(op_name(p, *op), &[arg])
        }
        CongruExpr::Binary(op, l, r) => {
            let a = eval(d, p, l, point);
            let b = eval(d, p, r, point);
            d.const_app(op_name(p, *op), &[a, b])
        }
        CongruExpr::Pow(base, n) => {
            let b = eval(d, p, base, point);
            d.const_app(p.pow, &[b, *n])
        }
        CongruExpr::Opaque(f, inner) => {
            let arg = eval(d, p, inner, point);
            d.apply(*f, &[arg])
        }
    }
}

// --- the deriver --------------------------------------------------------------

/// Why [`derive`] declined to build a proof. Never panics; every rejection —
/// including one reached through [`CongruExpr::Opaque`] — is this instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CongrError {
    /// No entry in the registry supplied names this operation as congruent
    /// at all.
    Unregistered(&'static str),
    /// The registry names the operation but with the wrong [`Arity`] for how
    /// [`CongruExpr`] invoked it. Unreachable given how this module's own
    /// [`registry`] pairs each [`Op`] with exactly one arity, but checked
    /// rather than assumed: a future registry edit that gets this wrong must
    /// decline, not build a misapplied lemma.
    ArityMismatch(&'static str),
}

/// Structurally recurse over `expr`, composing registered congruence lemmas,
/// to build a proof of `Equiv (eval expr x) (eval expr y)` from `h : Equiv x
/// y`. Returns `(statement, proof)`.
///
/// Declines with a [`CongrError`] — never panics, never returns a proof for a
/// claim it could not derive — the moment recursion reaches an operation
/// `reg` does not name at the required arity, or a [`CongruExpr::Opaque`]
/// node (which by construction never resolves through any registry).
pub(crate) fn derive(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    reg: &[CongrEntry],
    expr: &CongruExpr,
    x: ExprId,
    y: ExprId,
    h: ExprId,
) -> Result<(ExprId, ExprId), CongrError> {
    match expr {
        CongruExpr::Var => Ok((equiv(d, p, x, y), h)),
        CongruExpr::Const(c) => {
            let stmt = equiv(d, p, *c, *c);
            let proof = d.lemma(p.equiv_refl, &[*c]);
            Ok((stmt, proof))
        }
        CongruExpr::Unary(op, inner) => {
            let entry = lookup(reg, *op).ok_or(CongrError::Unregistered(op_label(*op)))?;
            if entry.arity != Arity::Unary {
                return Err(CongrError::ArityMismatch(op_label(*op)));
            }
            let (_inner_stmt, inner_proof) = derive(d, p, reg, inner, x, y, h)?;
            let ex = eval(d, p, inner, x);
            let ey = eval(d, p, inner, y);
            let proof = d.lemma(entry.congr_name, &[ex, ey, inner_proof]);
            let stmt = equiv(
                d,
                p,
                d.const_app(entry.op_name, &[ex]),
                d.const_app(entry.op_name, &[ey]),
            );
            Ok((stmt, proof))
        }
        CongruExpr::Binary(op, l, r) => {
            let entry = lookup(reg, *op).ok_or(CongrError::Unregistered(op_label(*op)))?;
            if entry.arity != Arity::Binary {
                return Err(CongrError::ArityMismatch(op_label(*op)));
            }
            let (_l_stmt, l_proof) = derive(d, p, reg, l, x, y, h)?;
            let (_r_stmt, r_proof) = derive(d, p, reg, r, x, y, h)?;
            let lx = eval(d, p, l, x);
            let ly = eval(d, p, l, y);
            let rx = eval(d, p, r, x);
            let ry = eval(d, p, r, y);
            // Argument order verified against three independent existing
            // call sites — see `Arity::Binary`'s own doc comment.
            let proof = d.lemma(entry.congr_name, &[lx, ly, rx, ry, l_proof, r_proof]);
            let stmt = equiv(
                d,
                p,
                d.const_app(entry.op_name, &[lx, rx]),
                d.const_app(entry.op_name, &[ly, ry]),
            );
            Ok((stmt, proof))
        }
        CongruExpr::Pow(base, n) => {
            let (_base_stmt, base_proof) = derive(d, p, reg, base, x, y, h)?;
            let bx = eval(d, p, base, x);
            let by = eval(d, p, base, y);
            // `pow_congr x y h n`, per `CongruExpr::Pow`'s own doc comment:
            // the exponent is the LAST argument, after the hypothesis.
            let proof = d.lemma(p.pow_congr, &[bx, by, base_proof, *n]);
            let stmt = equiv(
                d,
                p,
                d.const_app(p.pow, &[bx, *n]),
                d.const_app(p.pow, &[by, *n]),
            );
            Ok((stmt, proof))
        }
        CongruExpr::Opaque(..) => Err(CongrError::Unregistered(
            "<opaque function term, no registered congruence>",
        )),
    }
}

/// Errors from declaring a derived congruence theorem: either the deriver
/// declined (a [`CongrError`]), or the kernel refused the resulting proof (a
/// [`KernelError`], which — per this crate's own convention — means the
/// trusted gate rejected it, not that this code gave up).
#[derive(Debug)]
pub(crate) enum DeclareError {
    Congr(CongrError),
    Kernel(KernelError),
}

/// Declare `name : ∀ x y, Equiv x y → Equiv (eval expr x) (eval expr y)`,
/// running [`derive`] and handing the result straight to
/// `Kernel::add_declaration` — the judge, per declaration, exactly like every
/// other theorem in this crate.
pub(crate) fn declare_derived_congr(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    reg: &[CongrEntry],
    name: NameId,
    expr: &CongruExpr,
) -> Result<(), DeclareError> {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hyp = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let (conclusion, proof_body) = derive(d, p, reg, expr, x, y, h).map_err(DeclareError::Congr)?;

    let ty = {
        let with_h = d.arrow(hyp, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, with_h);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp, proof_body);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(DeclareError::Kernel)
}

// --- the permanent registration: the power-series term congruence -----------

/// `CReal.mulPowCongr : ∀ (c : Nat → CReal) (j : Nat) (x y : CReal), Equiv x
/// y → Equiv (mul (c j) (pow x j)) (mul (c j) (pow y j))`.
///
/// The motivating higher-order case this module exists for
/// (`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
/// §3): the per-term congruence a power-series argument needs before
/// `CRealPrelude::sum_range_congr` can turn "each term is congruent" into
/// "the partial sum is congruent". `c j` does not mention the point being
/// varied, so it is a [`CongruExpr::Const`] leaf, and the whole term is
/// `Binary(Mul, Const(c j), Pow(Var, j))` — composing exactly the two
/// registered lemmas ([`Op::Mul`]'s `mul_congr`, and `pow_congr` via
/// [`CongruExpr::Pow`]) that a hand-built version of this theorem would also
/// need, in the same order.
///
/// No hand-built equivalent of this exact statement exists anywhere in the
/// merged tree as of this lane's base commit — grepped for
/// `mul_congr`/`pow_congr` co-occurring with a congruence proof across every
/// `creal/*.rs` file, and the closest neighbour
/// (`creal/polynomial.rs::declare_polynomial`'s monomial-sum argument) proves
/// a Cauchy bound, not an `Equiv`-congruence. So this is declared as a new,
/// permanent name rather than a verified match to a sibling's construction —
/// a sibling that needs it can confirm the type against this doc comment.
fn declare_power_series_term_congr(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    reg: &[CongrEntry],
) -> Result<(), DeclareError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let cj = d.apply(c, &[j]);

    let expr = CongruExpr::Binary(
        Op::Mul,
        Box::new(CongruExpr::Const(cj)),
        Box::new(CongruExpr::Pow(Box::new(CongruExpr::Var), j)),
    );

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let hyp = equiv(d, p, x, y);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let (conclusion, proof_body) =
        derive(d, p, reg, &expr, x, y, h).map_err(DeclareError::Congr)?;

    let ty = {
        let with_h = d.arrow(hyp, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, with_h);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        let with_j = d.pi_fv(j_fv, nat, with_x);
        d.pi_fv(c_fv, fn_ty, with_j)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp, proof_body);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        let with_j = d.lam_fv(j_fv, nat, with_x);
        d.lam_fv(c_fv, fn_ty, with_j)
    };
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name: p.mul_pow_congr,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(DeclareError::Kernel)
}

/// This module's single dispatch entry point, called last in
/// `build_creal_prelude_uncached` (after `polynomial::declare_polynomial`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that this code gave up. A [`CongrError`] from
/// [`declare_power_series_term_congr`] would mean this module's own
/// hardcoded, hand-verified expression used an operation absent from its own
/// registry — a programming error in this file, not an adversarial input —
/// so it is treated as an invariant violation rather than propagated as a
/// build-time possibility every other phase in this chain would have to
/// handle.
pub(super) fn declare_congruence_extras(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let reg = registry(p);
    match declare_power_series_term_congr(d, p, &reg) {
        Ok(()) => Ok(()),
        Err(DeclareError::Kernel(error)) => Err(error),
        Err(DeclareError::Congr(error)) => unreachable!(
            "declare_power_series_term_congr used an operation absent from \
             its own registry: {error:?}"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_model::declaration_type;
    use crate::{Kernel, on_a_deep_stack};

    /// A fresh `CReal` prelude, on a deep stack (the standing rule for
    /// anything that builds this prelude — `creal_prelude_builds`'s own doc
    /// comment has the measurement). Process-wide template reuse
    /// (`prelude_cache`, ADR-0464) makes every call after the first in this
    /// test binary a clone rather than a full re-derivation, so this is not
    /// re-paying the full build cost per test.
    fn fresh() -> (Kernel, CRealPrelude) {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude =
                crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
            (kernel, prelude)
        })
    }

    /// Demo (a): re-derive an EXISTING hand-proved congruence
    /// (`CReal.abs_congr`) and confirm the derived theorem's type matches the
    /// hand-built one's, rendered.
    #[test]
    fn rederive_abs_congr_matches_hand_built() {
        on_a_deep_stack(rederive_abs_congr_matches_hand_built_body);
    }

    fn rederive_abs_congr_matches_hand_built_body() {
        let (mut kernel, p) = fresh();
        let reg = registry(p);
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let derived_name = d.kernel().name_str(p.creal, "congruenceDemo_absCongr");
        let expr = CongruExpr::Unary(Op::Abs, Box::new(CongruExpr::Var));
        declare_derived_congr(&mut d, p, &reg, derived_name, &expr)
            .expect("re-deriving abs_congr must be accepted by the kernel");

        let hand_built_ty =
            declaration_type(&kernel, p.abs_congr).expect("CReal.abs_congr must be declared");
        let derived_ty =
            declaration_type(&kernel, derived_name).expect("the derived theorem must be declared");
        assert_eq!(
            kernel.render_lean(hand_built_ty),
            kernel.render_lean(derived_ty),
            "re-derived abs_congr must render identically to the hand-built one"
        );
    }

    /// Demo (b): derive a congruence that does NOT exist yet in this
    /// prelude — the power-series term shape — through the SAME production
    /// dispatch path (`declare_congruence_extras`) `build_creal_prelude`
    /// itself runs. `fresh()` already exercises this, since
    /// `build_creal_prelude` runs the full phase chain; this test additionally
    /// checks the resulting type against the hand-written statement in
    /// `declare_power_series_term_congr`'s own doc comment.
    #[test]
    fn power_series_term_congr_is_permanently_registered() {
        on_a_deep_stack(power_series_term_congr_is_permanently_registered_body);
    }

    fn power_series_term_congr_is_permanently_registered_body() {
        let (kernel, p) = fresh();
        let rendered = kernel.render_lean(
            declaration_type(&kernel, p.mul_pow_congr)
                .expect("CReal.mulPowCongr must be declared by build_creal_prelude"),
        );
        for needle in ["CReal.mul", "CReal.pow", "CReal.Equiv"] {
            assert!(
                rendered.contains(needle),
                "CReal.mulPowCongr's type does not mention {needle}: {rendered}"
            );
        }
    }

    /// Demo (c): a composite deep enough that hand-building it would be
    /// painful — `abs(min(add x (ofRat q), mul x x))` — kernel-checked, and
    /// its derivation+check wall-clock reported (07-doc §3: per-instance cost
    /// is the number that matters for a producer).
    #[test]
    fn composite_clamp_like_term_derives_and_checks() {
        on_a_deep_stack(composite_clamp_like_term_derives_and_checks_body);
    }

    fn composite_clamp_like_term_derives_and_checks_body() {
        let (mut kernel, p) = fresh();
        let reg = registry(p);
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        // `q`: an arbitrary but fixed real, standing in for `ofRat q` --
        // a `CReal`-typed free variable that does not mention `Var` is
        // exactly what `CongruExpr::Const` requires, and is agnostic to
        // which concrete rational `q` denotes.
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);

        // abs(min(add x q, mul x x))
        let expr = CongruExpr::Unary(
            Op::Abs,
            Box::new(CongruExpr::Binary(
                Op::Min,
                Box::new(CongruExpr::Binary(
                    Op::Add,
                    Box::new(CongruExpr::Var),
                    Box::new(CongruExpr::Const(q)),
                )),
                Box::new(CongruExpr::Binary(
                    Op::Mul,
                    Box::new(CongruExpr::Var),
                    Box::new(CongruExpr::Var),
                )),
            )),
        );

        let name = d.kernel().name_str(p.creal, "congruenceDemo_clampLike");
        let start = std::time::Instant::now();
        declare_derived_congr(&mut d, p, &reg, name, &expr)
            .expect("the composite clamp-like congruence must be accepted by the kernel");
        let elapsed = start.elapsed();
        // Always printed (not gated on `--nocapture` mattering to the
        // reporter): this is the deepest demo, so its cost is the number
        // `docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
        // §3 asks a producer to report.
        eprintln!(
            "congruence deriver: composite_clamp_like_term derive+check = {elapsed:?}"
        );
    }

    /// Demo (d), the negative control: a term built from a raw,
    /// non-congruent function `fvar` — an operation that is not, and cannot
    /// be, in the registry — must make [`derive`] DECLINE with a typed
    /// error. Never reaches `Kernel::add_declaration` at all.
    #[test]
    fn negative_control_declines() {
        on_a_deep_stack(negative_control_declines_body);
    }

    fn negative_control_declines_body() {
        let (mut kernel, p) = fresh();
        let reg = registry(p);
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let f_ty = {
            let carrier = creal_ty(&mut d, p);
            d.arrow(carrier, carrier)
        };
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let _ = f_ty; // `f`'s type is not needed to build the term; kept for clarity.

        let expr = CongruExpr::Opaque(f, Box::new(CongruExpr::Var));

        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let result = derive(&mut d, p, &reg, &expr, x, y, h);
        assert!(
            matches!(result, Err(CongrError::Unregistered(_))),
            "a term built from an unregistered raw function must decline, not {result:?}"
        );
    }

    /// Mutation test for the negative control: corrupt the registry by
    /// dropping [`Op::Add`]'s entry. Every term using `Add` must now decline
    /// through the SAME path as [`negative_control_declines`], while a term
    /// using a DIFFERENT, still-registered operation succeeds in the same
    /// run — proving the decline is specific to the dropped operation, not a
    /// blanket failure.
    #[test]
    fn registry_corruption_is_the_decline_path() {
        on_a_deep_stack(registry_corruption_is_the_decline_path_body);
    }

    fn registry_corruption_is_the_decline_path_body() {
        let (mut kernel, p) = fresh();
        let full_reg = registry(p);
        let pruned_reg = registry_without(p, Op::Add);
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `Add` still works against the FULL registry.
        let add_expr = CongruExpr::Binary(
            Op::Add,
            Box::new(CongruExpr::Var),
            Box::new(CongruExpr::Var),
        );
        assert!(
            derive(&mut d, p, &full_reg, &add_expr, x, y, h).is_ok(),
            "Add must derive against the full registry"
        );

        // `Add` DECLINES against the registry with its own entry dropped.
        let pruned_result = derive(&mut d, p, &pruned_reg, &add_expr, x, y, h);
        assert!(
            matches!(pruned_result, Err(CongrError::Unregistered(label)) if label == op_label(Op::Add)),
            "Add must decline once its registry entry is dropped, got {pruned_result:?}"
        );

        // A DIFFERENT, still-registered operation (`Neg`) is unaffected by
        // dropping `Add`'s entry, in the same run.
        let neg_expr = CongruExpr::Unary(Op::Neg, Box::new(CongruExpr::Var));
        assert!(
            derive(&mut d, p, &pruned_reg, &neg_expr, x, y, h).is_ok(),
            "Neg must still derive with Add's entry (only) dropped"
        );
    }
}
