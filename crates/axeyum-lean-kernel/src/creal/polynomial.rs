//! `CReal.polyEval` and its algebra — the polynomial infrastructure Spivak
//! Chapter 20 (Taylor polynomials) needs, and that did not exist over `CReal`
//! before this file.
//!
//! # Step 0: what already existed
//!
//! `CReal.uniformly_continuous_poly_example` (`creal/uniform_continuity.rs`)
//! is the only `poly*`-named thing in the `CReal` prelude before this file,
//! and it is **not** a polynomial layer: it is one fixed concrete
//! polynomial, `x -> x^2 + x + 1`, assembled by hand from
//! `uniformly_continuous_{sq,id,const,add}` to prove uniform continuity on
//! `[0,1]`. It carries no `polyEval`, no coefficient function, no addition or
//! scaling of polynomials, and nothing about degree. Confirmed by a full
//! grep of `crates/axeyum-lean-kernel/src/creal/` for `poly`/`Poly`
//! (case-insensitive): the only other hits before this file are in that one
//! module.
//!
//! Two general polynomial layers already exist elsewhere in this kernel —
//! `Rat.polyEval` (`rat_prelude/polynomial.rs`, the original precedent) and
//! `Complex.polyEval` (`complex/poly.rs`, landed the same session, over a
//! field whose `Equiv` is literal componentwise equality rather than a
//! Cauchy-sequence setoid). This file inherits both files' design decisions
//! rather than relitigating them; see their own module docs for reasoning
//! this one does not repeat.
//!
//! # The representation
//!
//! Same shape as `Complex.polyEval`/`Rat.polyEval`: a coefficient function
//! `Nat -> CReal` plus an explicit bound `n : Nat`. This kernel has no
//! `List`/tuple type, and [`CRealPrelude::sum_range`] itself already takes
//! (function, bound) in exactly this shape.
//!
//! `n` is **not** a computed degree, and the case for that is if anything
//! stronger here than for `Complex`: `CReal.Equiv` and `CReal.le` are BOTH
//! undecidable (`creal/ivt.rs` refutes exact roots with two kernel-computed
//! counterexamples for exactly this reason), so no total function could
//! extract a "true" degree from an arbitrary coefficient function even in
//! principle. `n` is a bound the caller supplies; where a proof needs
//! coefficients to vanish beyond it, that is the explicit hypothesis
//! [`declare_poly_degree_lt`] states, never something derived from `c`/`n`
//! alone.
//!
//! # `polyEval`: sum of monomials, not Horner
//!
//! `polyEval c n x := sumRange (fun i => mul (c i) (pow x i)) n` — identical
//! reasoning to `Complex.polyEval`'s own module doc: a Horner fold needs
//! highest-coefficient-first processing, which means either a `Nat.sub`
//! inside the recursion index or a concrete accumulator that partially
//! normalizes against a symbolic recursion variable and never
//! re-synchronizes — precisely the "concrete witness costs more than a
//! symbolic one" trap that turned one `CReal` declaration this session from
//! 14.8s to a 1 GiB release-mode stack overflow (`declare_e_converges`, see
//! the kernel-facts note in `creal/exponential.rs`'s own history). The
//! sum-of-monomials form needs no subtraction anywhere: `sumRange`'s own
//! recursion goes forward from `Nat.zero`, `polyEval_zero`/`polyEval_succ`
//! close by `Eq.refl` alone (pure ι-reduction), and the only index ever used
//! is the recursion variable itself.
//!
//! # What is proved
//!
//! - [`declare_poly_eval`] / [`declare_poly_eval_equations`]: the definition
//!   and its two ι-reduction equations.
//! - [`declare_poly_add`] / [`declare_poly_eval_poly_add`]: a first-class
//!   pointwise `polyAdd` operation and its evaluation homomorphism, at one
//!   shared bound `n` for both operands — `eval (add p q) x ~ add (eval p x)
//!   (eval q x)`. Route: pointwise `mul (add ci gi) xi ~ add (mul ci xi) (mul
//!   gi xi)` via the shared [`super::ring_helpers::right_distrib`] helper,
//!   lifted through `sumRange` via [`CRealPrelude::sum_range_congr`], then
//!   [`CRealPrelude::sum_range_add`] splits the combined sum.
//! - [`declare_poly_scale`] / [`declare_poly_eval_poly_scale`]: likewise for
//!   scalar multiplication, via [`CRealPrelude::mul_assoc`] pointwise
//!   (`mul (mul a ci) xi ~ mul a (mul ci xi)`) and
//!   [`CRealPrelude::mul_sum_range`].
//! - [`declare_poly_degree_lt`] and its two preservation theorems: a
//!   `Prop`-valued "vanishes from `n` on" predicate, preserved by
//!   `polyAdd`/`polyScale` at a shared bound. No `Nat.max` is used or
//!   available in this kernel; widening one operand's bound up to the
//!   other's is left to `Nat.le` transitivity at the call site.
//!
//! Every homomorphism below is proved **symbolically**, over free variables,
//! never only at concrete instantiations — `creal_tests.rs` additionally
//! checks a concrete instance of each as corroboration, per the standing
//! rule that a concrete check alone can hide a defeq-shaped gap a symbolic
//! one would expose.
//!
//! # What is *not* attempted here, and precisely why
//!
//! **`polyMul` (the Cauchy product) and its evaluation homomorphism.** Exactly
//! the gap `Complex.poly`'s own module doc records, for the identical reason:
//! the natural convolution
//! `polyMul c g k := sumRange (fun i => mul (c i) (g (Nat.sub k i))) (Nat.succ k)`
//! is only the *correct* coefficient of the product under a
//! [`declare_poly_degree_lt`]-style hypothesis on **both** factors, and
//! proving the evaluation homomorphism needs, beyond what this file proves:
//! padding both sums up to a shared bound
//! (`CRealPrelude::sum_range_split`, which — like the diagonal/corner
//! decomposition `Complex`'s copy uses — has no `CReal` counterpart yet), and
//! a fresh corner-vanishing argument. Left undeclared rather than
//! declared-but-unproved-about: an operation with no theorem connecting it to
//! `polyEval` would be dead weight in a checked kernel.
//!
//! **The Taylor polynomial as an object, and the integral-form remainder.**
//! Sized and reported separately (session report), not attempted in this
//! file: the natural next step is a Taylor polynomial built from a sequence
//! of `n`-th derivative values at a point `a`, `taylorPoly a coeffs n := fun x
//! => polyEval (fun i => scale (coeffs i) (invFactorial i)) n (add x (neg
//! a))`, which needs a `1/i!` scalar in `CReal` (`CReal.ofRat (Rat.ofNat 1 /
//! Rat.ofNat (Nat.factorial i))` or similar) that this file does not build.

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Height for `CReal.polyEval`: above [`CRealPrelude::pow`]'s
/// `DERIVED_HEIGHT + 42` and [`CRealPrelude::sum_range`]'s
/// `DERIVED_HEIGHT + 41` — the two definitions `polyEval`'s value embeds —
/// and comfortably above every height declared anywhere else in this prelude
/// so far (the highest in use elsewhere is `DERIVED_HEIGHT + 100`,
/// `creal/crossing.rs`), mirroring `Complex.polyEval`'s own
/// height-above-its-callees convention.
const POLY_EVAL_HEIGHT: u16 = super::DERIVED_HEIGHT + 101;
/// Height for `CReal.polyAdd`/`CReal.polyScale`/`CReal.polyDegreeLt`: each
/// embeds only leaf operations (`add`/`mul`/`zero`, `Nat.le`), so one height
/// above [`super::DERIVED_HEIGHT`] already exceeds every leaf height they
/// call — mirroring `Complex.poly`'s `POLY_COMBINATOR_HEIGHT` exactly.
const POLY_COMBINATOR_HEIGHT: u16 = super::DERIVED_HEIGHT + 1;

/// Declare `CReal.polyEval` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_polynomial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_poly_eval(d, p)?;
    declare_poly_eval_equations(d, p)?;
    declare_poly_add(d, p)?;
    declare_poly_eval_poly_add(d, p)?;
    declare_poly_scale(d, p)?;
    declare_poly_eval_poly_scale(d, p)?;
    declare_poly_degree_lt(d, p)?;
    declare_poly_degree_lt_poly_add(d, p)?;
    declare_poly_degree_lt_poly_scale(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

/// `Eq.{1} CReal a b`. Local private restatement of the identical helper
/// already private to `creal/series.rs` — a sibling module's `fn` (no `pub`)
/// is not visible here, and this is a two-line generic `Eq` builder, exactly
/// the kind of trivial per-file duplication `creal/ring_helpers.rs`'s own
/// module doc describes as the established convention in this tree.
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a`. See [`creal_eq`] for why this is a local copy.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// `CReal.Equiv a b`.
fn equiv(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.equiv, &[a, b])
}

/// `fun i => mul (c i) (pow x i)` — one polynomial's summand function, the
/// argument [`CRealPrelude::sum_range`] evaluates. Mirrors
/// `complex::poly::poly_summand`/`rat_prelude::polynomial::poly_summand`
/// exactly.
fn poly_summand(d: &mut IntDev<'_>, p: CRealPrelude, c: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let xi = d.const_app(p.pow, &[x, i]);
    let body = d.const_app(p.mul, &[ci, xi]);
    d.lam_fv(i_fv, nat, body)
}

/// `Equiv.trans` chained through `steps`, each `(next, proof : Equiv current
/// next)`, starting from `start`. Returns `(final, proof : Equiv start
/// final)`. Mirrors `complex::poly::zchain`/`creal::ring_helpers::echain`'s
/// shape (a local copy for the same reason [`creal_eq`] is).
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    (current, proof)
}

// ---------------------------------------------------------------------------
// `CReal.polyEval`.
// ---------------------------------------------------------------------------

/// `CReal.polyEval : (Nat → CReal) → Nat → CReal → CReal`, `polyEval c n x :=
/// sumRange (fun i => mul (c i) (pow x i)) n` — a plain (not recursive)
/// definition, unlike `CReal.sumRange`/`CReal.pow` themselves.
fn declare_poly_eval(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let summand = poly_summand(d, p, c, x);
    let body = d.const_app(p.sum_range, &[summand, n]);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        let with_n = d.lam_fv(n_fv, nat, with_x);
        d.lam_fv(c_fv, fn_ty, with_n)
    };
    let ty = {
        let over_x = d.arrow(carrier, carrier);
        let over_n = d.arrow(nat, over_x);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.polynomial.poly_eval,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_EVAL_HEIGHT),
    })
}

/// `CReal.polyEval_zero`/`CReal.polyEval_succ`: the defining equations, each
/// closed by `Eq.refl` alone. `polyEval c n x` δ-unfolds to `sumRange (fun i
/// => mul (c i) (pow x i)) n`, which then ι/β-reduces exactly as
/// [`CRealPrelude::sum_range_zero`]/[`CRealPrelude::sum_range_succ`]'s own
/// two equations do — no lemma from elsewhere in this prelude is invoked.
fn declare_poly_eval_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    // polyEval_zero : ∀ c x, Eq CReal (polyEval c Nat.zero x) zero.
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let zero_n = d.zero();
        let lhs = d.const_app(p.polynomial.poly_eval, &[c, zero_n, x]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt_inner = creal_eq(d, p, lhs, zero_c);
        let proof_inner = creal_eq_refl(d, p, zero_c);

        let ty = {
            let inner = d.pi_fv(x_fv, carrier, stmt_inner);
            d.pi_fv(c_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(x_fv, carrier, proof_inner);
            d.lam_fv(c_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.polynomial.poly_eval_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // polyEval_succ : ∀ c n x,
    //   Eq CReal (polyEval c (Nat.succ n) x)
    //     (add (polyEval c n x) (mul (c n) (pow x n))).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let sn = d.succ(n);
        let lhs = d.const_app(p.polynomial.poly_eval, &[c, sn, x]);
        let prior = d.const_app(p.polynomial.poly_eval, &[c, n, x]);
        let cn = d.apply(c, &[n]);
        let xn = d.const_app(p.pow, &[x, n]);
        let term_n = d.const_app(p.mul, &[cn, xn]);
        let rhs = d.const_app(p.add, &[prior, term_n]);
        let stmt_inner = creal_eq(d, p, lhs, rhs);
        let proof_inner = creal_eq_refl(d, p, rhs);

        let ty = {
            let over_x = d.pi_fv(x_fv, carrier, stmt_inner);
            let over_n = d.pi_fv(n_fv, nat, over_x);
            d.pi_fv(c_fv, fn_ty, over_n)
        };
        let value = {
            let over_x = d.lam_fv(x_fv, carrier, proof_inner);
            let over_n = d.lam_fv(n_fv, nat, over_x);
            d.lam_fv(c_fv, fn_ty, over_n)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.polynomial.poly_eval_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// `CReal.polyAdd` and its evaluation homomorphism.
// ---------------------------------------------------------------------------

/// `CReal.polyAdd : (Nat → CReal) → (Nat → CReal) → (Nat → CReal) := fun c g
/// i => add (c i) (g i)` — pointwise coefficient addition, a first-class
/// named operation.
fn declare_poly_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let gi = d.apply(g, &[i]);
    let body = d.const_app(p.add, &[ci, gi]);
    let inner = d.lam_fv(i_fv, nat, body);

    let value = {
        let with_g = d.lam_fv(g_fv, fn_ty, inner);
        d.lam_fv(c_fv, fn_ty, with_g)
    };
    let ty = {
        let over_g = d.arrow(fn_ty, fn_ty);
        d.arrow(fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.polynomial.poly_add,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `fun i => add (f i) (g i)`, built with `p` in scope.
fn combined_add(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = d.const_app(p.add, &[fi, gi]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => mul a (f i)`, built with `p` in scope.
fn scaled_mul(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let body = d.const_app(p.mul, &[a, fi]);
    d.lam_fv(i_fv, nat, body)
}

/// `CReal.polyEval_polyAdd : ∀ c g n x, Equiv (polyEval (polyAdd c g) n x)
/// (add (polyEval c n x) (polyEval g n x))` — evaluation is a homomorphism
/// from `(polyAdd, polyEval)` to `(add, ·)`, at the same bound `n` for both
/// operands.
///
/// Route: pointwise right-distributivity (`mul (add (c i) (g i)) (pow x i) ~
/// add (mul (c i) (pow x i)) (mul (g i) (pow x i))`, via the shared
/// [`right_distrib`] helper rather than re-deriving it from
/// [`CRealPrelude::left_distrib`] plus [`CRealPrelude::mul_comm`] by hand)
/// lifted to the sums via [`CRealPrelude::sum_range_congr`], then
/// [`CRealPrelude::sum_range_add`] splits the combined sum. Mirrors
/// `Complex.polyEval_polyAdd`'s route exactly.
fn declare_poly_eval_poly_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let poly_add_cg = d.const_app(p.polynomial.poly_add, &[c, g]);
    let summand_added = poly_summand(d, p, poly_add_cg, x);
    let summand_c = poly_summand(d, p, c, x);
    let summand_g = poly_summand(d, p, g, x);
    let combined_summands = combined_add(d, p, summand_c, summand_g);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let gi = d.apply(g, &[i]);
        let xi = d.const_app(p.pow, &[x, i]);
        let body = right_distrib(d, p, ci, gi, xi);
        d.lam_fv(i_fv, nat, body)
    };

    let h1 = d.lemma(
        p.sum_range_congr,
        &[summand_added, combined_summands, n, pointwise],
    );
    let h2 = d.lemma(p.sum_range_add, &[summand_c, summand_g, n]);

    let start = d.const_app(p.sum_range, &[summand_added, n]);
    let mid = d.const_app(p.sum_range, &[combined_summands, n]);
    let sum_c = d.const_app(p.sum_range, &[summand_c, n]);
    let sum_g = d.const_app(p.sum_range, &[summand_g, n]);
    let final_rhs = d.const_app(p.add, &[sum_c, sum_g]);

    let (_e, proof) = echain(d, p, start, &[(mid, h1), (final_rhs, h2)]);

    let lhs_stmt = d.const_app(p.polynomial.poly_eval, &[poly_add_cg, n, x]);
    let eval_c = d.const_app(p.polynomial.poly_eval, &[c, n, x]);
    let eval_g = d.const_app(p.polynomial.poly_eval, &[g, n, x]);
    let rhs_stmt = d.const_app(p.add, &[eval_c, eval_g]);
    let stmt = equiv(d, p, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_x);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let over_n = d.lam_fv(n_fv, nat, over_x);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(c_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polynomial.poly_eval_poly_add,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.polyScale` and its evaluation homomorphism.
// ---------------------------------------------------------------------------

/// `CReal.polyScale : CReal → (Nat → CReal) → (Nat → CReal) := fun a c i =>
/// mul a (c i)` — scaling every coefficient by a constant, a first-class
/// named operation.
fn declare_poly_scale(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let body = d.const_app(p.mul, &[a, ci]);
    let inner = d.lam_fv(i_fv, nat, body);

    let value = {
        let with_c = d.lam_fv(c_fv, fn_ty, inner);
        d.lam_fv(a_fv, carrier, with_c)
    };
    let ty = {
        let over_c = d.arrow(fn_ty, fn_ty);
        d.arrow(carrier, over_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.polynomial.poly_scale,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `CReal.polyEval_polyScale : ∀ a c n x, Equiv (polyEval (polyScale a c) n
/// x) (mul a (polyEval c n x))` — evaluation is a homomorphism from
/// `(polyScale, polyEval)` to `(mul, ·)`.
///
/// Route: pointwise re-association (`mul (mul a (c i)) (pow x i) ~ mul a
/// (mul (c i) (pow x i))`, exactly [`CRealPrelude::mul_assoc`]'s own
/// statement) lifted to the sums via [`CRealPrelude::sum_range_congr`], then
/// [`CRealPrelude::mul_sum_range`] symm'd (that lemma runs `mul a (sumRange f
/// n) ~ sumRange (fun i => mul a (f i)) n`, the opposite direction from what
/// is needed here). Mirrors `Complex.polyEval_polyScale`'s route exactly.
fn declare_poly_eval_poly_scale(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let poly_scale_ac = d.const_app(p.polynomial.poly_scale, &[a, c]);
    let summand_scaled = poly_summand(d, p, poly_scale_ac, x);
    let summand_c = poly_summand(d, p, c, x);
    let scaled_summand = scaled_mul(d, p, a, summand_c);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let xi = d.const_app(p.pow, &[x, i]);
        let body = d.lemma(p.mul_assoc, &[a, ci, xi]);
        d.lam_fv(i_fv, nat, body)
    };

    let h1 = d.lemma(
        p.sum_range_congr,
        &[summand_scaled, scaled_summand, n, pointwise],
    );
    let h2 = d.lemma(p.mul_sum_range, &[a, summand_c, n]);
    // h2 : Equiv (mul a (sumRange summand_c n)) (sumRange scaled_summand n)
    let sum_summand_c = d.const_app(p.sum_range, &[summand_c, n]);
    let sum_scaled_summand = d.const_app(p.sum_range, &[scaled_summand, n]);
    let mul_a_sum = d.const_app(p.mul, &[a, sum_summand_c]);
    let h2_symm = d.lemma(p.equiv_symm, &[mul_a_sum, sum_scaled_summand, h2]);

    let start = d.const_app(p.sum_range, &[summand_scaled, n]);
    let mid = sum_scaled_summand;
    let final_rhs = mul_a_sum;

    let (_e, proof) = echain(d, p, start, &[(mid, h1), (final_rhs, h2_symm)]);

    let lhs_stmt = d.const_app(p.polynomial.poly_eval, &[poly_scale_ac, n, x]);
    let eval_c = d.const_app(p.polynomial.poly_eval, &[c, n, x]);
    let rhs_stmt = d.const_app(p.mul, &[a, eval_c]);
    let stmt = equiv(d, p, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_x);
        let over_c = d.pi_fv(c_fv, fn_ty, over_n);
        d.pi_fv(a_fv, carrier, over_c)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let over_n = d.lam_fv(n_fv, nat, over_x);
        let over_c = d.lam_fv(c_fv, fn_ty, over_n);
        d.lam_fv(a_fv, carrier, over_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polynomial.poly_eval_poly_scale,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.polyDegreeLt` and preservation under `polyAdd`/`polyScale`.
// ---------------------------------------------------------------------------

/// `CReal.polyDegreeLt : (Nat → CReal) → Nat → Prop := fun c n => ∀ i,
/// Nat.le n i → Equiv (c i) zero` — "`c`'s coefficients vanish from index `n`
/// on", the honest stand-in for a *computed* degree bound (ruled out by
/// `CReal.Equiv`'s undecidability): a **hypothesis** a caller supplies, never
/// a fact derived from `c`/`n` alone.
fn declare_poly_degree_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);
    let prop = d.kernel().sort_zero();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let le_ni = d.le(n, i);
    let ci = d.apply(c, &[i]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let concl = equiv(d, p, ci, zero_c);
    let inner = d.arrow(le_ni, concl);
    let body_i = d.pi_fv(i_fv, nat, inner);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body_i);
        d.lam_fv(c_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.polynomial.poly_degree_lt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `CReal.polyDegreeLt c n`, applied.
fn poly_degree_lt_applied(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.polynomial.poly_degree_lt, &[f, n])
}

/// `CReal.polyDegreeLt_polyAdd : ∀ c g n, polyDegreeLt c n → polyDegreeLt g n
/// → polyDegreeLt (polyAdd c g) n` — the degree bound of a sum is preserved
/// at the same bound (no `Nat.max` is used or available in this kernel).
///
/// No induction: for `i` with `Nat.le n i`, [`CRealPrelude::add_congr`]
/// combines the two vanishing hypotheses into `Equiv (add (c i) (g i)) (add
/// zero zero)`, and [`CRealPrelude::add_zero`] at `zero` closes `Equiv (add
/// zero zero) zero`.
fn declare_poly_degree_lt_poly_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let le_ni = d.le(n, i);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let ci = d.apply(c, &[i]);
    let gi = d.apply(g, &[i]);

    // hc_i : Equiv (c i) zero, from hc applied to i, hi.
    let hc_i = d.apply(hc, &[i, hi]);
    let hg_i = d.apply(hg, &[i, hi]);
    let add_step = d.lemma(p.add_congr, &[ci, zero_c, gi, zero_c, hc_i, hg_i]);
    // add_step : Equiv (add ci gi) (add zero zero)
    let zero_zero = d.const_app(p.add, &[zero_c, zero_c]);
    let add_zero_step = d.lemma(p.add_zero, &[zero_c]);
    // add_zero_step : Equiv (add zero zero) zero
    let ci_gi = d.const_app(p.add, &[ci, gi]);
    let (_e, proof_i) = echain(
        d,
        p,
        ci_gi,
        &[(zero_zero, add_step), (zero_c, add_zero_step)],
    );

    let body_i = d.lam_fv(hi_fv, le_ni, proof_i);

    let degree_lt_c = poly_degree_lt_applied(d, p, c, n);
    let degree_lt_g = poly_degree_lt_applied(d, p, g, n);
    let poly_add_cg = d.const_app(p.polynomial.poly_add, &[c, g]);
    let degree_lt_add = poly_degree_lt_applied(d, p, poly_add_cg, n);

    let value = {
        let over_i = d.lam_fv(i_fv, nat, body_i);
        let over_hg = d.lam_fv(hg_fv, degree_lt_g, over_i);
        let over_hc = d.lam_fv(hc_fv, degree_lt_c, over_hg);
        let over_n = d.lam_fv(n_fv, nat, over_hc);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(c_fv, fn_ty, over_g)
    };
    let ty = {
        let after_hg = d.arrow(degree_lt_g, degree_lt_add);
        let after_hc = d.arrow(degree_lt_c, after_hg);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polynomial.poly_degree_lt_poly_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.polyDegreeLt_polyScale : ∀ a c n, polyDegreeLt c n → polyDegreeLt
/// (polyScale a c) n`.
///
/// No induction: for `i` with `Nat.le n i`, [`CRealPrelude::mul_congr`] (with
/// [`CRealPrelude::equiv_refl`] on `a`) combines the vanishing hypothesis
/// into `Equiv (mul a (c i)) (mul a zero)`, and [`CRealPrelude::mul_zero`] at
/// `a` closes `Equiv (mul a zero) zero`.
fn declare_poly_degree_lt_poly_scale(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let le_ni = d.le(n, i);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let ci = d.apply(c, &[i]);

    let hc_i = d.apply(hc, &[i, hi]);
    let a_refl = d.lemma(p.equiv_refl, &[a]);
    let mul_step = d.lemma(p.mul_congr, &[a, a, ci, zero_c, a_refl, hc_i]);
    // mul_step : Equiv (mul a ci) (mul a zero)
    let mul_a_zero = d.const_app(p.mul, &[a, zero_c]);
    let mul_zero_step = d.lemma(p.mul_zero, &[a]);
    // mul_zero_step : Equiv (mul a zero) zero
    let a_ci = d.const_app(p.mul, &[a, ci]);
    let (_e, proof_i) = echain(
        d,
        p,
        a_ci,
        &[(mul_a_zero, mul_step), (zero_c, mul_zero_step)],
    );

    let body_i = d.lam_fv(hi_fv, le_ni, proof_i);

    let concl_stmt = {
        let ci2 = d.apply(c, &[i]);
        let scaled_i = d.const_app(p.mul, &[a, ci2]);
        equiv(d, p, scaled_i, zero_c)
    };
    let degree_lt_c = poly_degree_lt_applied(d, p, c, n);

    let value = {
        let over_i = d.lam_fv(i_fv, nat, body_i);
        let over_hc = d.lam_fv(hc_fv, degree_lt_c, over_i);
        let over_n = d.lam_fv(n_fv, nat, over_hc);
        let over_c = d.lam_fv(c_fv, fn_ty, over_n);
        d.lam_fv(a_fv, carrier, over_c)
    };
    let ty = {
        let arrow_inner = d.arrow(le_ni, concl_stmt);
        let over_i = d.pi_fv(i_fv, nat, arrow_inner);
        let after_hc = d.arrow(degree_lt_c, over_i);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_c = d.pi_fv(c_fv, fn_ty, over_n);
        d.pi_fv(a_fv, carrier, over_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.polynomial.poly_degree_lt_poly_scale,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/polynomial.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolynomialNames {
    /// `CReal.polyEval : (Nat → CReal) → Nat → CReal → CReal` — `polyEval c n
    /// x := sumRange (fun i => mul (c i) (pow x i)) n`, sum of monomials, not
    /// Horner. See `creal/polynomial.rs`'s module doc for why.
    pub poly_eval: NameId,
    /// `CReal.polyEval_zero : ∀ c x, Eq CReal (polyEval c Nat.zero x) zero`.
    /// Closes by `Eq.refl` alone.
    pub poly_eval_zero: NameId,
    /// `CReal.polyEval_succ : ∀ c n x, Eq CReal (polyEval c (Nat.succ n) x)
    /// (add (polyEval c n x) (mul (c n) (pow x n)))`. Closes by `Eq.refl`
    /// alone.
    pub poly_eval_succ: NameId,
    /// `CReal.polyAdd : (Nat → CReal) → (Nat → CReal) → (Nat → CReal) := fun
    /// c g i => add (c i) (g i)` — pointwise coefficient addition.
    pub poly_add: NameId,
    /// `CReal.polyEval_polyAdd : ∀ c g n x, Equiv (polyEval (polyAdd c g) n
    /// x) (add (polyEval c n x) (polyEval g n x))` — evaluation is a
    /// homomorphism from `(polyAdd, polyEval)` to `(add, ·)`, at one shared
    /// bound `n` for both operands.
    pub poly_eval_poly_add: NameId,
    /// `CReal.polyScale : CReal → (Nat → CReal) → (Nat → CReal) := fun a c i
    /// => mul a (c i)` — scaling every coefficient by a constant.
    pub poly_scale: NameId,
    /// `CReal.polyEval_polyScale : ∀ a c n x, Equiv (polyEval (polyScale a c)
    /// n x) (mul a (polyEval c n x))` — evaluation is a homomorphism from
    /// `(polyScale, polyEval)` to `(mul, ·)`.
    pub poly_eval_poly_scale: NameId,
    /// `CReal.polyDegreeLt : (Nat → CReal) → Nat → Prop := fun c n => ∀ i,
    /// Nat.le n i → Equiv (c i) zero` — the honest stand-in for a *computed*
    /// degree bound, ruled out by `CReal.Equiv`'s undecidability: a
    /// **hypothesis** a caller supplies, never derived from `c`/`n` alone.
    pub poly_degree_lt: NameId,
    /// `CReal.polyDegreeLt_polyAdd : ∀ c g n, polyDegreeLt c n →
    /// polyDegreeLt g n → polyDegreeLt (polyAdd c g) n` — preserved at the
    /// same bound (no `Nat.max` is used or available in this kernel).
    pub poly_degree_lt_poly_add: NameId,
    /// `CReal.polyDegreeLt_polyScale : ∀ a c n, polyDegreeLt c n →
    /// polyDegreeLt (polyScale a c) n`.
    pub poly_degree_lt_poly_scale: NameId,
}

impl PolynomialNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            poly_eval: kernel.name_str(creal, "polyEval"),
            poly_eval_zero: kernel.name_str(creal, "polyEval_zero"),
            poly_eval_succ: kernel.name_str(creal, "polyEval_succ"),
            poly_add: kernel.name_str(creal, "polyAdd"),
            poly_eval_poly_add: kernel.name_str(creal, "polyEval_polyAdd"),
            poly_scale: kernel.name_str(creal, "polyScale"),
            poly_eval_poly_scale: kernel.name_str(creal, "polyEval_polyScale"),
            poly_degree_lt: kernel.name_str(creal, "polyDegreeLt"),
            poly_degree_lt_poly_add: kernel.name_str(creal, "polyDegreeLt_polyAdd"),
            poly_degree_lt_poly_scale: kernel.name_str(creal, "polyDegreeLt_polyScale"),
        }
    }
}
