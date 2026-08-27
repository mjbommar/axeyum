//! `Complex.polyEval` and its algebra — the polynomial infrastructure
//! Chapter 25–27 needs and that did not exist at all before this file.
//!
//! Confirmed by grep against a positive control before writing anything:
//! `Complex.conj*`/`Complex.add_pow` matched fine, `poly`/`degree`/`horner`
//! (case-insensitive) matched **nothing** under `Complex.*` anywhere in the
//! kernel's declared-name inventory (`prelude_theorem_inventory
//! --include-constructed`). The only `poly*` hits anywhere were
//! `Rat.polyEval*` (`rat_prelude/polynomial.rs`) and one unrelated
//! `CReal.uniformly_continuous_poly_example`.
//!
//! # The representation
//!
//! This kernel has no `List` and no tuple type (`Complex.mk` itself takes
//! two separate `CReal` arguments for exactly this reason), so a polynomial
//! here is a **coefficient function** `Nat → Complex` together with an
//! explicit bound `n : Nat` — the same shape `Rat.polyEval`
//! (`rat_prelude/polynomial.rs`) already uses, and
//! [`ComplexPrelude::sum_range`] itself takes (a function plus a bound).
//!
//! `n` is deliberately **not** a computed degree. `Complex.Equiv` is a
//! `Prop`, not decidable, so nothing can test whether a coefficient is zero,
//! and no total function `(Nat → Complex) → Nat` could extract a "true"
//! degree from an arbitrary coefficient function. `n` is a bound the caller
//! chooses, and where a proof needs to know coefficients vanish beyond it,
//! that is an explicit hypothesis ([`declare_poly_degree_lt`]) — the same
//! idiom [`ComplexPrelude::inv`]'s `PosBound` witness and
//! [`ComplexPrelude::geom_series_div`]'s modulus witness already use: a
//! supplied witness, never something derived from `c`/`n` alone.
//!
//! # `polyEval`: sum of monomials, not Horner
//!
//! `polyEval c n x := sumRange (fun i => mul (c i) (pow x i)) n`.
//!
//! A Horner fold (`(⋯((c_{n-1}·x + c_{n-2})·x + ⋯)·x + c_0`) does fewer
//! multiplications on paper, but it processes coefficients **highest index
//! first**. Built as a structural recursion on `n` (the only recursion this
//! kernel's `Nat.rec` gives for free), that means either counting down —
//! introducing `Nat.sub` into the recursion index, which
//! [`ComplexPrelude::sum_range_diagonal`]'s own module doc already shows is
//! real bookkeeping once subtraction sits inside a recursion — or an
//! accumulator fold whose step multiplies a *symbolic* accumulator by `x`
//! and adds a coefficient looked up at a **subtracted** index. That is
//! exactly the documented "concrete witness costs more than a symbolic one"
//! shape: index arithmetic that partially normalizes against the recursion
//! variable and does not re-synchronize, the pattern that turned one
//! declaration elsewhere in this kernel from 14.8s to a 1 GiB release-mode
//! stack overflow.
//!
//! The sum-of-monomials form needs no subtraction anywhere. `sumRange`'s own
//! recursion goes **forward** from `Nat.zero`; `polyEval_zero`/`polyEval_succ`
//! close by `Eq.refl` alone (ι-reduction only, no lemma, exactly
//! [`ComplexPrelude::sum_range_zero`]/[`ComplexPrelude::sum_range_succ`]'s own
//! shape); and the only index ever used is the recursion variable itself —
//! "symbolic left, literal right", never a derived index. This is the same
//! reduction-cost argument `Rat.polyEval`'s own module doc makes; this file
//! inherits it rather than re-deriving it.
//!
//! # What is proved
//!
//! - [`declare_poly_eval`] / [`declare_poly_eval_equations`]: the definition
//!   and its two ι-reduction equations.
//! - [`declare_poly_add`] / [`declare_poly_eval_poly_add`]: a first-class
//!   pointwise `polyAdd` operation and its evaluation homomorphism, **at one
//!   shared bound** for both operands — `eval (add p q) x ≡ add (eval p x)
//!   (eval q x)`.
//! - [`declare_poly_scale`] / [`declare_poly_eval_poly_scale`]: likewise for
//!   scalar multiplication.
//! - [`declare_poly_degree_lt`] and the two preservation theorems: a
//!   `Prop`-valued "vanishes from `n` on" predicate standing in for a
//!   computed degree bound, preserved by `polyAdd`/`polyScale` at a shared
//!   bound. No `Nat.max` is used or available in this kernel; widening one
//!   operand's bound up to the other's first is left to `Nat.le`
//!   transitivity at the call site, not proved here.
//!
//! Every homomorphism below is proved **symbolically**, over free variables,
//! never only at concrete instantiations — `complex_tests.rs` additionally
//! checks a concrete instance of each as corroboration, per the standing
//! rule that a concrete check alone can hide a defeq-shaped gap a symbolic
//! one would expose.
//!
//! # What is *not* attempted here, and precisely why
//!
//! **`polyMul` (the Cauchy product) and its evaluation homomorphism.** The
//! natural per-coefficient convolution,
//! `polyMul c g k := sumRange (fun i => mul (c i) (g (Nat.sub k i))) (Nat.succ k)`,
//! is only the *correct* coefficient of `c(x)·g(x)` at index `k` if `c`/`g`
//! are the zero function beyond their own bounds — an arbitrary `Nat →
//! Complex` need not be, since nothing in this representation forces it.
//! Proving
//! `Equiv (mul (polyEval c m x) (polyEval g n x)) (polyEval (polyMul c g) (Nat.add m n) x)`
//! under explicit [`declare_poly_degree_lt`]-style hypotheses for both
//! factors needs, beyond what this file proves:
//!
//! 1. Padding each sum up to the shared bound `Nat.add m n`:
//!    [`ComplexPrelude::sum_range_split`] splits `sumRange f (Nat.add m n)`
//!    into the kept prefix plus a tail; the tail must be shown to vanish
//!    termwise from the `polyDegreeLt` hypothesis
//!    ([`ComplexPrelude::mul_congr`]/[`ComplexPrelude::mul_comm`]/
//!    [`ComplexPrelude::mul_zero`] turn each vanishing coefficient into a
//!    vanishing summand, and the private `sum_range_const_zero_proof` helper
//!    this module has access to but does not use collapses the resulting
//!    all-zero sum) — plus commuting `Nat.add m n` against `Nat.add n m` for
//!    whichever operand needs the other order.
//! 2. [`ComplexPrelude::sum_range_mul_eq_diag_add_corner`] then relates the
//!    padded product to a diagonal (antidiagonal-convolution) term plus a
//!    **corner** term — the module's own doc records that the identity
//!    *without* the corner is FALSE, refuted by hand at `n = 2`.
//! 3. The corner term must *itself* be shown to vanish under the same
//!    `polyDegreeLt` hypotheses (it sums products `f i · g j` with `i, j`
//!    individually below the padded bound but `i + j` at or beyond it) — a
//!    genuinely new vanishing argument, not a reassembly of anything
//!    `sum_range_mul_eq_diag_add_corner` already proves.
//!
//! `polyMul` is left undeclared rather than declared-but-unproved-about: an
//! operation with no theorem connecting it to `polyEval` would be dead
//! weight sitting in a checked kernel.
//!
//! **The factor theorem**
//! (`polyEval p n a ~ zero → ∃ q, ∀ x, Equiv (polyEval p n x) (mul (add x (neg a)) (polyEval q (Nat.sub n 1) x))`)
//! needs `polyMul`/a division construction just to *state* honestly, and —
//! per this kernel's `Exists.rec` being `Prop`-only, so it cannot eliminate
//! an existential into the *data* `q` — needs `q` **computed** by an
//! explicit synthetic-division recursion, not extracted from a proof of
//! existence. That is a further, separate development layered on top of
//! `polyMul`. Not attempted; blocked on both of the above.

use super::{
    CExpr, ComplexPrelude, complex_eq, complex_eq_refl, complex_ty, corner_inner_c, corner_row_c,
    corner_sum_c, diag_inner_c, diag_t_fn_c, diag_triangle_sum_c, nat_eq_to_complex_equiv,
    render_c, ring_law_proof, shifted_c, sum_range_const_zero_proof, zeq, zero_fn,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatOps, NatPrelude};

/// Height for `Complex.polyEval`: above [`super::DERIVED_HEIGHT`] `+ 11`
/// (`Complex.ofNat`, the highest height declared in this file before this
/// module runs) and in particular above [`ComplexPrelude::pow`]'s `+ 9` and
/// [`ComplexPrelude::sum_range`]'s `+ 10` — the two definitions `polyEval`'s
/// value embeds, mirroring `Rat.polyEval`'s own height-above-its-callees
/// convention (`rat_prelude/polynomial.rs`'s `POLY_EVAL_HEIGHT`).
const POLY_EVAL_HEIGHT: u16 = super::DERIVED_HEIGHT + 13;
/// Height for `Complex.polyAdd`/`Complex.polyScale`/`Complex.polyDegreeLt`:
/// each embeds only leaf operations (`add`/`mul`/`zero`, `Nat.le`), so one
/// height above [`super::DERIVED_HEIGHT`] already exceeds every leaf height
/// they call.
const POLY_COMBINATOR_HEIGHT: u16 = super::DERIVED_HEIGHT + 1;
/// Height for `Complex.polyMul`: its value embeds only `sum_range`, `mul`,
/// `sub` and `succ` (no `pow`), so it needs the same margin above
/// [`ComplexPrelude::sum_range`]'s `+10` that [`POLY_EVAL_HEIGHT`] already
/// gives `polyEval` — reused verbatim rather than re-deriving a tighter bound.
const POLY_MUL_HEIGHT: u16 = POLY_EVAL_HEIGHT;

/// Declare `Complex.polyEval` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_polynomial(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    declare_poly_eval(d, p)?;
    declare_poly_eval_equations(d, p)?;
    declare_poly_add(d, p)?;
    declare_poly_eval_poly_add(d, p)?;
    declare_poly_scale(d, p)?;
    declare_poly_eval_poly_scale(d, p)?;
    declare_poly_degree_lt(d, p)?;
    declare_poly_degree_lt_poly_add(d, p)?;
    declare_poly_degree_lt_poly_scale(d, p)?;
    declare_poly_mul(d, p)?;
    declare_poly_eval_poly_mul(d, p)
}

// ---------------------------------------------------------------------------
// shared term builders
// ---------------------------------------------------------------------------

/// `fun i => mul (c i) (pow x i)` — one polynomial's summand function, the
/// argument [`ComplexPrelude::sum_range`] evaluates. Mirrors
/// `rat_prelude::polynomial::poly_summand` exactly.
fn poly_summand(d: &mut IntDev<'_>, p: ComplexPrelude, c: ExprId, x: ExprId) -> ExprId {
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
/// final)`. Mirrors `rat_prelude::ops::rchain`'s shape for `Complex.Equiv`.
fn zchain(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
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
// `Complex.polyEval`.
// ---------------------------------------------------------------------------

/// `Complex.polyEval : (Nat → Complex) → Nat → Complex → Complex`,
/// `polyEval c n x := sumRange (fun i => mul (c i) (pow x i)) n` — a plain
/// (not recursive) definition, unlike `Complex.sumRange`/`Complex.pow`
/// themselves.
fn declare_poly_eval(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
        name: p.poly_eval,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_EVAL_HEIGHT),
    })
}

/// `Complex.polyEval_zero`/`Complex.polyEval_succ`: the defining equations,
/// each closed by `Eq.refl` alone. `polyEval c n x` δ-unfolds to `sumRange
/// (fun i => mul (c i) (pow x i)) n`, which then ι/β-reduces exactly as
/// [`ComplexPrelude::sum_range_zero`]/[`ComplexPrelude::sum_range_succ`]'s
/// own two equations do — no lemma from elsewhere in this prelude is
/// invoked, the unfolding chain does the whole job.
fn declare_poly_eval_equations(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    // polyEval_zero : ∀ c x, Eq Complex (polyEval c Nat.zero x) zero.
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let zero_n = d.zero();
        let lhs = d.const_app(p.poly_eval, &[c, zero_n, x]);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        let stmt_inner = complex_eq(d, p, lhs, zero_c);
        let proof_inner = complex_eq_refl(d, p, zero_c);

        let ty = {
            let inner = d.pi_fv(x_fv, carrier, stmt_inner);
            d.pi_fv(c_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(x_fv, carrier, proof_inner);
            d.lam_fv(c_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.poly_eval_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // polyEval_succ : ∀ c n x,
    //   Eq Complex (polyEval c (Nat.succ n) x)
    //     (add (polyEval c n x) (mul (c n) (pow x n))).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let sn = d.succ(n);
        let lhs = d.const_app(p.poly_eval, &[c, sn, x]);
        let prior = d.const_app(p.poly_eval, &[c, n, x]);
        let cn = d.apply(c, &[n]);
        let xn = d.const_app(p.pow, &[x, n]);
        let term_n = d.const_app(p.mul, &[cn, xn]);
        let rhs = d.const_app(p.add, &[prior, term_n]);
        let stmt_inner = complex_eq(d, p, lhs, rhs);
        let proof_inner = complex_eq_refl(d, p, rhs);

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
            name: p.poly_eval_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// `Complex.polyAdd` and its evaluation homomorphism.
// ---------------------------------------------------------------------------

/// `Complex.polyAdd : (Nat → Complex) → (Nat → Complex) → (Nat → Complex) :=
/// fun c g i => add (c i) (g i)` — pointwise coefficient addition, a
/// first-class named operation.
fn declare_poly_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
        name: p.poly_add,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `Complex.polyEval_polyAdd : ∀ c g n x, Equiv (polyEval (polyAdd c g) n x)
/// (add (polyEval c n x) (polyEval g n x))` — evaluation is a homomorphism
/// from `(polyAdd, polyEval)` to `(add, ·)`, **at the same bound `n` for both
/// operands** (see the module doc for exactly where padding to a common
/// bound stops being free).
///
/// Route: pointwise right-distributivity (`mul (add (c i) (g i)) (pow x i) ~
/// add (mul (c i) (pow x i)) (mul (g i) (pow x i))`, decided by the `ring`
/// calculus over the three opaque atoms `c i`, `g i`, `pow x i` rather than
/// derived by hand from [`ComplexPrelude::left_distrib`] plus
/// [`ComplexPrelude::mul_comm`] twice) lifted to the sums via
/// [`ComplexPrelude::sum_range_congr`], then
/// [`ComplexPrelude::sum_range_add`] splits the combined sum. Mirrors
/// `Rat.polyEval_add`'s route (`rat_prelude/polynomial.rs`) exactly.
fn declare_poly_eval_poly_add(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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

    let poly_add_cg = d.const_app(p.poly_add, &[c, g]);
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
        let ci_v = CExpr::var(d, p, ci);
        let gi_v = CExpr::var(d, p, gi);
        let xi_v = CExpr::var(d, p, xi);
        let lhs = CExpr::mul(CExpr::add(ci_v.clone(), gi_v.clone()), xi_v.clone());
        let rhs = CExpr::add(CExpr::mul(ci_v, xi_v.clone()), CExpr::mul(gi_v, xi_v));
        let body = ring_law_proof(d, p, &lhs, &rhs);
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

    let (_e, proof) = zchain(d, p, start, &[(mid, h1), (final_rhs, h2)]);

    let lhs_stmt = d.const_app(p.poly_eval, &[poly_add_cg, n, x]);
    let eval_c = d.const_app(p.poly_eval, &[c, n, x]);
    let eval_g = d.const_app(p.poly_eval, &[g, n, x]);
    let rhs_stmt = d.const_app(p.add, &[eval_c, eval_g]);
    let stmt = zeq(d, p, lhs_stmt, rhs_stmt);

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
        name: p.poly_eval_poly_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun i => add (f i) (g i)`, built with `p` in scope (the proof-site
/// counterpart of [`combined`], which [`declare_poly_add`] itself uses via
/// a direct inline body since it does not need a `ComplexPrelude` closure).
fn combined_add(d: &mut IntDev<'_>, p: ComplexPrelude, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = d.const_app(p.add, &[fi, gi]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => mul a (f i)`, built with `p` in scope — the proof-site
/// counterpart of [`scaled`].
fn scaled_mul(d: &mut IntDev<'_>, p: ComplexPrelude, a: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let body = d.const_app(p.mul, &[a, fi]);
    d.lam_fv(i_fv, nat, body)
}

// ---------------------------------------------------------------------------
// `Complex.polyScale` and its evaluation homomorphism.
// ---------------------------------------------------------------------------

/// `Complex.polyScale : Complex → (Nat → Complex) → (Nat → Complex) := fun a
/// c i => mul a (c i)` — scaling every coefficient by a constant, a
/// first-class named operation.
fn declare_poly_scale(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
        name: p.poly_scale,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `Complex.polyEval_polyScale : ∀ a c n x, Equiv (polyEval (polyScale a c) n
/// x) (mul a (polyEval c n x))` — evaluation is a homomorphism from
/// `(polyScale, polyEval)` to `(mul, ·)`.
///
/// Route: pointwise re-association (`mul (mul a (c i)) (pow x i) ~ mul a
/// (mul (c i) (pow x i))`, decided by the `ring` calculus) lifted to the
/// sums via [`ComplexPrelude::sum_range_congr`], then
/// [`ComplexPrelude::mul_sum_range`] symm'd (that lemma runs `mul a
/// (sumRange f n) ~ sumRange (fun i => mul a (f i)) n`, the opposite
/// direction from what is needed here). Mirrors `Rat.polyEval_smul`'s route
/// (`rat_prelude/polynomial.rs`) exactly.
fn declare_poly_eval_poly_scale(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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

    let poly_scale_ac = d.const_app(p.poly_scale, &[a, c]);
    let summand_scaled = poly_summand(d, p, poly_scale_ac, x);
    let summand_c = poly_summand(d, p, c, x);
    let scaled_summand = scaled_mul(d, p, a, summand_c);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let xi = d.const_app(p.pow, &[x, i]);
        let a_v = CExpr::var(d, p, a);
        let ci_v = CExpr::var(d, p, ci);
        let xi_v = CExpr::var(d, p, xi);
        let lhs = CExpr::mul(CExpr::mul(a_v.clone(), ci_v.clone()), xi_v.clone());
        let rhs = CExpr::mul(a_v, CExpr::mul(ci_v, xi_v));
        let body = ring_law_proof(d, p, &lhs, &rhs);
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

    let (_e, proof) = zchain(d, p, start, &[(mid, h1), (final_rhs, h2_symm)]);

    let lhs_stmt = d.const_app(p.poly_eval, &[poly_scale_ac, n, x]);
    let eval_c = d.const_app(p.poly_eval, &[c, n, x]);
    let rhs_stmt = d.const_app(p.mul, &[a, eval_c]);
    let stmt = zeq(d, p, lhs_stmt, rhs_stmt);

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
        name: p.poly_eval_poly_scale,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `Complex.polyDegreeLt` and preservation under `polyAdd`/`polyScale`.
// ---------------------------------------------------------------------------

/// `Complex.polyDegreeLt : (Nat → Complex) → Nat → Prop := fun c n => ∀ i,
/// Nat.le n i → Equiv (c i) zero` — "`c`'s coefficients vanish from index `n`
/// on", the honest stand-in for a *computed* degree bound (ruled out by
/// `Complex.Equiv`'s undecidability): a **hypothesis** a caller supplies,
/// never a fact derived from `c`/`n` alone.
fn declare_poly_degree_lt(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
    let concl = zeq(d, p, ci, zero_c);
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
        name: p.poly_degree_lt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_COMBINATOR_HEIGHT),
    })
}

/// `Complex.polyDegreeLt_polyAdd : ∀ c g n, polyDegreeLt c n → polyDegreeLt g
/// n → polyDegreeLt (polyAdd c g) n` — the degree bound of a sum is
/// preserved **at the same bound** (no `Nat.max` is used or available in
/// this kernel).
///
/// No induction: for `i` with `Nat.le n i`, [`ComplexPrelude::add_congr`]
/// combines the two vanishing hypotheses into `Equiv (add (c i) (g i)) (add
/// zero zero)`, and [`ComplexPrelude::add_zero`] at `zero` closes `Equiv
/// (add zero zero) zero`.
fn declare_poly_degree_lt_poly_add(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
    let (_e, proof_i) = zchain(
        d,
        p,
        ci_gi,
        &[(zero_zero, add_step), (zero_c, add_zero_step)],
    );

    let body_i = d.lam_fv(hi_fv, le_ni, proof_i);

    let degree_lt_c = poly_degree_lt_applied(d, p, c, n);
    let degree_lt_g = poly_degree_lt_applied(d, p, g, n);
    let poly_add_cg = d.const_app(p.poly_add, &[c, g]);
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
        name: p.poly_degree_lt_poly_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.polyDegreeLt c n`, applied — `d.pi_fv`'d body over a fresh `i`.
/// Built as a standalone helper because [`declare_poly_degree_lt_poly_add`]/
/// [`declare_poly_degree_lt_poly_scale`] both need the *type* `polyDegreeLt f
/// n` as an arrow's domain, not just a term applying it.
fn poly_degree_lt_applied(d: &mut IntDev<'_>, p: ComplexPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.poly_degree_lt, &[f, n])
}

/// `Complex.polyDegreeLt_polyScale : ∀ a c n, polyDegreeLt c n →
/// polyDegreeLt (polyScale a c) n`.
///
/// No induction: for `i` with `Nat.le n i`, [`ComplexPrelude::mul_congr`]
/// (with [`ComplexPrelude::equiv_refl`] on `a`) combines the vanishing
/// hypothesis into `Equiv (mul a (c i)) (mul a zero)`, and
/// [`ComplexPrelude::mul_zero`] at `a` closes `Equiv (mul a zero) zero`.
fn declare_poly_degree_lt_poly_scale(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
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
    let (_e, proof_i) = zchain(
        d,
        p,
        a_ci,
        &[(mul_a_zero, mul_step), (zero_c, mul_zero_step)],
    );

    let body_i = d.lam_fv(hi_fv, le_ni, proof_i);

    let concl_stmt = {
        let ci2 = d.apply(c, &[i]);
        let scaled_i = d.const_app(p.mul, &[a, ci2]);
        zeq(d, p, scaled_i, zero_c)
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
        name: p.poly_degree_lt_poly_scale,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `Complex.polyMul` — the finite Cauchy product.
// ---------------------------------------------------------------------------

/// `Complex.polyMul : (Nat → Complex) → (Nat → Complex) → (Nat → Complex) :=
/// fun c g k => sumRange (fun i => mul (c i) (g (Nat.sub k i))) (Nat.succ k)`
/// — the antidiagonal convolution, a first-class named operation. See
/// [`poly`]'s module doc for why this is the *natural* definition and
/// [`ComplexPrelude::poly_eval_poly_mul`] for the vanishing hypotheses that
/// make it the *correct* one.
fn declare_poly_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let ki = d.sub(k, i);
    let gki = d.apply(g, &[ki]);
    let term = d.const_app(p.mul, &[ci, gki]);
    let summand = d.lam_fv(i_fv, nat, term);
    let sk = d.succ(k);
    let body_k = d.const_app(p.sum_range, &[summand, sk]);
    let inner = d.lam_fv(k_fv, nat, body_k);

    let value = {
        let with_g = d.lam_fv(g_fv, fn_ty, inner);
        d.lam_fv(c_fv, fn_ty, with_g)
    };
    let ty = {
        let over_g = d.arrow(fn_ty, fn_ty);
        d.arrow(fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.poly_mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_MUL_HEIGHT),
    })
}

/// `Equiv (sumRange (poly_summand coeffs x) (Nat.add base extra))
/// (sumRange (poly_summand coeffs x) base)` given `hyp : polyDegreeLt coeffs
/// base` — pads a `polyEval` sum up to `Nat.add base extra` and shows the
/// padding is free: every added term's index is `Nat.add base k ≥ base`
/// ([`crate::nat_prelude::NatPrelude::le_add_right`], unconditionally, no
/// case split needed), hence `Equiv`-zero by `hyp`, hence the whole
/// [`Self::sum_range_congr`]'d tail is `Equiv`-zero
/// ([`sum_range_const_zero_proof`]), hence [`ComplexPrelude::add_zero`]
/// erases it from [`ComplexPrelude::sum_range_split`]'s own decomposition.
fn poly_pad_up(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    coeffs: ExprId,
    x: ExprId,
    base: ExprId,
    extra: ExprId,
    hyp: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let summand = poly_summand(d, p, coeffs, x);
    let tail = shifted_c(d, summand, base);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let base_k = d.add(base, k);
        let ck = d.apply(coeffs, &[base_k]);
        let xk = d.const_app(p.pow, &[x, base_k]);
        let zero_c = d.kernel().const_(p.zero, vec![]);

        let nat_p = d.prelude();
        let le_base_bk = d.lemma(nat_p.le_add_right, &[base, k]);
        let h_ck = d.apply(hyp, &[base_k, le_base_bk]);
        // h_ck : Equiv(ck, zero)

        let refl_xk = d.lemma(p.equiv_refl, &[xk]);
        let step1 = d.lemma(p.mul_congr, &[ck, zero_c, xk, xk, h_ck, refl_xk]);
        let ck_xk = d.const_app(p.mul, &[ck, xk]);

        let xk_v = CExpr::var(d, p, xk);
        let mid_c = CExpr::mul(CExpr::Zero, xk_v);
        let mid_term = render_c(d, p, &mid_c);
        let h_ring = ring_law_proof(d, p, &mid_c, &CExpr::Zero);

        let body = d.lemma(p.equiv_trans, &[ck_xk, mid_term, zero_c, step1, h_ring]);
        d.lam_fv(k_fv, nat, body)
    };

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let zfn = zero_fn(d, p);
    let h_pw = d.lemma(p.sum_range_congr, &[tail, zfn, extra, pointwise]);
    let sum_tail = d.const_app(p.sum_range, &[tail, extra]);
    let sum_zfn = d.const_app(p.sum_range, &[zfn, extra]);
    let h_zfn = sum_range_const_zero_proof(d, p, extra);
    let h_tail_zero = d.lemma(p.equiv_trans, &[sum_tail, sum_zfn, zero_c, h_pw, h_zfn]);
    // h_tail_zero : Equiv(sumRange(tail,extra), zero)

    let base_extra = d.add(base, extra);
    let h_split = d.lemma(p.sum_range_split, &[summand, base, extra]);
    // h_split : Equiv(sumRange(summand, add(base,extra)),
    //                 add(sumRange(summand,base), sumRange(tail,extra)))
    let sum_base = d.const_app(p.sum_range, &[summand, base]);
    let sum_be = d.const_app(p.sum_range, &[summand, base_extra]);
    let add_result = d.const_app(p.add, &[sum_base, sum_tail]);

    let refl_sum_base = d.lemma(p.equiv_refl, &[sum_base]);
    let h_add_congr = d.lemma(
        p.add_congr,
        &[
            sum_base,
            sum_base,
            sum_tail,
            zero_c,
            refl_sum_base,
            h_tail_zero,
        ],
    );
    let add_base_zero = d.const_app(p.add, &[sum_base, zero_c]);
    let h_add_zero = d.lemma(p.add_zero, &[sum_base]);
    let step_a = d.lemma(
        p.equiv_trans,
        &[add_result, add_base_zero, sum_base, h_add_congr, h_add_zero],
    );
    d.lemma(
        p.equiv_trans,
        &[sum_be, add_result, sum_base, h_split, step_a],
    )
}

/// `Equiv (pow x k) (mul (pow x i) (pow x (Nat.sub k i)))`, given `le_i_k :
/// Nat.le i k` — restores `k = Nat.add i (Nat.sub k i)`
/// ([`crate::nat_prelude::NatPrelude::sub_add_cancel`] plus `add_comm`)
/// lifted into `Complex` via [`nat_eq_to_complex_equiv`], then splits via
/// [`ComplexPrelude::pow_add`].
fn pow_split(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    x: ExprId,
    i: ExprId,
    k: ExprId,
    le_i_k: ExprId,
) -> ExprId {
    let nat_p = d.prelude();
    let sub_ki = d.sub(k, i);

    let h_restore = d.lemma(nat_p.sub_add_cancel, &[i, k, le_i_k]);
    // h_restore : Eq Nat (add sub_ki i) k
    let add_sub_i = d.add(sub_ki, i);
    let h_k_eq_addsubi = d.symm(add_sub_i, k, h_restore);
    // h_k_eq_addsubi : Eq Nat k (add sub_ki i)

    let h_comm = d.lemma(nat_p.add_comm, &[sub_ki, i]);
    // h_comm : Eq Nat (add sub_ki i) (add i sub_ki)
    let add_i_sub = d.add(i, sub_ki);
    let h_k_eq = d.trans(k, add_sub_i, add_i_sub, h_k_eq_addsubi, h_comm);
    // h_k_eq : Eq Nat k (add i sub_ki)

    let target_f = |dd: &mut IntDev<'_>, xx: ExprId| dd.const_app(p.pow, &[x, xx]);
    let h_pow_eq = nat_eq_to_complex_equiv(d, p, k, add_i_sub, h_k_eq, &target_f);
    // h_pow_eq : Equiv(pow x k, pow x (add i sub_ki))
    let h_pow_add = d.lemma(p.pow_add, &[x, i, sub_ki]);
    // h_pow_add : Equiv(pow x (add i sub_ki), mul(pow x i, pow x sub_ki))

    let pow_x_k = d.const_app(p.pow, &[x, k]);
    let pow_x_addisub = d.const_app(p.pow, &[x, add_i_sub]);
    let pow_x_i = d.const_app(p.pow, &[x, i]);
    let pow_x_subki = d.const_app(p.pow, &[x, sub_ki]);
    let mul_result = d.const_app(p.mul, &[pow_x_i, pow_x_subki]);
    d.lemma(
        p.equiv_trans,
        &[pow_x_k, pow_x_addisub, mul_result, h_pow_eq, h_pow_add],
    )
}

/// The corner-vanishing pointwise fact's `Equiv (mul (mul (c i) (pow x i))
/// (mul (zero_c) (pow x _))) zero` half: `hc_i : Equiv (c i, zero)` collapses
/// the WHOLE product via [`ComplexPrelude::mul_congr`] then `ring_law_proof`
/// (a single `mul (zero, atom)` reduction).
fn corner_zero_from_c(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    ci: ExprId,
    xi: ExprId,
    gxj: ExprId,
    hc_i: ExprId,
) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let refl_xi = d.lemma(p.equiv_refl, &[xi]);
    let step1 = d.lemma(p.mul_congr, &[ci, zero_c, xi, xi, hc_i, refl_xi]);
    // step1 : Equiv(mul(ci,xi), mul(zero,xi))
    let cxi = d.const_app(p.mul, &[ci, xi]);
    let zero_xi = d.const_app(p.mul, &[zero_c, xi]);
    let refl_gxj = d.lemma(p.equiv_refl, &[gxj]);
    let step2 = d.lemma(p.mul_congr, &[cxi, zero_xi, gxj, gxj, step1, refl_gxj]);
    // step2 : Equiv(mul(cxi,gxj), mul(zero_xi,gxj))
    let full = d.const_app(p.mul, &[cxi, gxj]);

    let xi_v = CExpr::var(d, p, xi);
    let gxj_v = CExpr::var(d, p, gxj);
    let mid_c = CExpr::mul(CExpr::mul(CExpr::Zero, xi_v), gxj_v);
    let mid_term = render_c(d, p, &mid_c);
    let h_ring = ring_law_proof(d, p, &mid_c, &CExpr::Zero);
    d.lemma(p.equiv_trans, &[full, mid_term, zero_c, step2, h_ring])
}

/// The other half of the corner-vanishing pointwise fact: `hg_j : Equiv (g
/// j, zero)` collapses `mul (mul (c i) (pow x i)) (mul (g j) (pow x j))` to
/// zero via the SECOND factor instead.
fn corner_zero_from_g(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    ci: ExprId,
    xi: ExprId,
    gj: ExprId,
    xj: ExprId,
    hg_j: ExprId,
) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let refl_xj = d.lemma(p.equiv_refl, &[xj]);
    let step1 = d.lemma(p.mul_congr, &[gj, zero_c, xj, xj, hg_j, refl_xj]);
    // step1 : Equiv(mul(gj,xj), mul(zero,xj))
    let gxj = d.const_app(p.mul, &[gj, xj]);
    let zero_xj = d.const_app(p.mul, &[zero_c, xj]);
    let cxi = d.const_app(p.mul, &[ci, xi]);
    let refl_cxi = d.lemma(p.equiv_refl, &[cxi]);
    let step2 = d.lemma(p.mul_congr, &[cxi, cxi, gxj, zero_xj, refl_cxi, step1]);
    // step2 : Equiv(mul(cxi,gxj), mul(cxi,zero_xj))
    let full = d.const_app(p.mul, &[cxi, gxj]);

    let cxi_v = CExpr::var(d, p, cxi);
    let xj_v = CExpr::var(d, p, xj);
    let mid_c = CExpr::mul(cxi_v, CExpr::mul(CExpr::Zero, xj_v));
    let mid_term = render_c(d, p, &mid_c);
    let h_ring = ring_law_proof(d, p, &mid_c, &CExpr::Zero);
    d.lemma(p.equiv_trans, &[full, mid_term, zero_c, step2, h_ring])
}

/// `False`, from `h1 : Nat.lt i m`, `h2 : Nat.lt j n`, where `j = Nat.add
/// (Nat.sub bound i) k` and `bound = Nat.add m n` — the contradiction the
/// corner region's own geometry forces.
///
/// `Nat.sub_add_cancel` (at `le_i_bound : Nat.le i bound`) restores `Nat.add
/// (Nat.sub bound i) i = bound`; combined with `Nat.add_assoc`/`Nat.add_comm`
/// this gives `Nat.add i j = Nat.add bound k`, hence (via
/// [`crate::nat_prelude::NatPrelude::le_add_right`] plus a transport) `Nat.le
/// bound (Nat.add i j)`. Independently, `h1`/`h2` combine (via
/// `add_le_add_left`/`add_le_add_right`/`succ_add`) into `Nat.lt (Nat.add i
/// j) bound`. The two contradict via `Nat.lt_of_lt_of_le` then
/// `Nat.lt_irrefl`.
#[allow(clippy::too_many_arguments)]
fn corner_index_contradiction(
    d: &mut IntDev<'_>,
    nat_p: NatPrelude,
    m: ExprId,
    n: ExprId,
    bound: ExprId,
    i: ExprId,
    j: ExprId,
    k: ExprId,
    sub_bound_i: ExprId,
    le_i_bound: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    // ----- Nat.le bound (Nat.add i j) ---------------------------------------
    let h_restore = d.lemma(nat_p.sub_add_cancel, &[i, bound, le_i_bound]);
    // h_restore : Eq Nat (add sub_bound_i i) bound
    let h_assoc = d.lemma(nat_p.add_assoc, &[i, sub_bound_i, k]);
    // h_assoc : Eq Nat (add (add i sub_bound_i) k) (add i (add sub_bound_i k))
    //         = Eq Nat (add (add i sub_bound_i) k) (add i j)
    let add_i_subi = d.add(i, sub_bound_i);
    let lhs_l = d.add(add_i_subi, k);
    let add_i_j = d.add(i, j);

    let h_comm = d.lemma(nat_p.add_comm, &[i, sub_bound_i]);
    // h_comm : Eq Nat (add i sub_bound_i) (add sub_bound_i i)
    let add_subi_i = d.add(sub_bound_i, i);
    let h_comm_k = d.congr(add_i_subi, add_subi_i, h_comm, &|dd, xx| dd.add(xx, k));
    // h_comm_k : Eq Nat (add add_i_subi k) (add add_subi_i k)
    let mid_l = d.add(add_subi_i, k);
    let h_restore_k = d.congr(add_subi_i, bound, h_restore, &|dd, xx| dd.add(xx, k));
    // h_restore_k : Eq Nat (add add_subi_i k) (add bound k)
    let bound_k = d.add(bound, k);
    let h_lhs_to_boundk = d.trans(lhs_l, mid_l, bound_k, h_comm_k, h_restore_k);
    // h_lhs_to_boundk : Eq Nat lhs_l bound_k

    let h_assoc_symm = d.symm(lhs_l, add_i_j, h_assoc);
    // h_assoc_symm : Eq Nat add_i_j lhs_l
    let h_ij_eq_boundk = d.trans(add_i_j, lhs_l, bound_k, h_assoc_symm, h_lhs_to_boundk);
    // h_ij_eq_boundk : Eq Nat add_i_j bound_k
    let h_boundk_eq_ij = d.symm(add_i_j, bound_k, h_ij_eq_boundk);
    // h_boundk_eq_ij : Eq Nat bound_k add_i_j

    let le_bound_boundk = d.lemma(nat_p.le_add_right, &[bound, k]);
    // le_bound_boundk : Le bound bound_k
    let motive_le = d.eq_motive(bound_k, &|dd, xx| dd.le(bound, xx));
    let h_ge = d.transport(bound_k, motive_le, le_bound_boundk, add_i_j, h_boundk_eq_ij);
    // h_ge : Le bound add_i_j

    // ----- Nat.lt (Nat.add i j) bound ---------------------------------------
    let succ_i = d.succ(i);
    let step1 = d.lemma(nat_p.add_le_add_right, &[j, succ_i, m, h1]);
    // step1 : Le (add succ_i j) (add m j)
    let le_j_n = {
        let sj = d.succ(j);
        let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
        d.lemma(nat_p.le_trans, &[j, sj, n, le_succ_j, h2])
    };
    // le_j_n : Le j n
    let step2 = d.lemma(nat_p.add_le_add_left, &[m, j, n, le_j_n]);
    // step2 : Le (add m j) bound
    let add_succi_j = d.add(succ_i, j);
    let add_m_j = d.add(m, j);
    let step3 = d.lemma(nat_p.le_trans, &[add_succi_j, add_m_j, bound, step1, step2]);
    // step3 : Le (add succ_i j) bound

    let h_succ_add = d.lemma(nat_p.succ_add, &[i, j]);
    // h_succ_add : Eq Nat (add succ_i j) (succ (add i j))
    let succ_add_i_j = d.succ(add_i_j);
    let motive_le2 = d.eq_motive(add_succi_j, &|dd, xx| dd.le(xx, bound));
    let h_lt_contra = d.transport(add_succi_j, motive_le2, step3, succ_add_i_j, h_succ_add);
    // h_lt_contra : Le (succ add_i_j) bound = Lt add_i_j bound

    // ----- contradiction ------------------------------------------------------
    let lt_ij_ij = d.lemma(
        nat_p.lt_of_lt_of_le,
        &[add_i_j, bound, add_i_j, h_lt_contra, h_ge],
    );
    d.lemma(nat_p.lt_irrefl, &[add_i_j, lt_ij_ij])
}

/// For fixed `i` (a corner row, `Nat.lt i bound`) and `k` (a position within
/// it), with `j := Nat.add (Nat.sub bound i) k` the index landing in `g`,
/// show `Equiv (mul (mul (c i) (pow x i)) (mul (g j) (pow x j))) zero`, given
/// `hc : polyDegreeLt c m`, `hg : polyDegreeLt g n`, `bound = Nat.add m n`.
///
/// Case split `Nat.lt_or_ge i m`: `Nat.le m i` finishes via
/// [`corner_zero_from_c`]. `Nat.lt i m` splits again, `Nat.lt_or_ge j n`:
/// `Nat.le n j` finishes via [`corner_zero_from_g`]; `Nat.lt j n` is
/// impossible ([`corner_index_contradiction`]) — `i < m ∧ j < n` would force
/// `i + j < bound`, but every corner index satisfies `i + j ≥ bound`.
#[allow(clippy::too_many_arguments)]
fn corner_term_zero(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    g: ExprId,
    m: ExprId,
    n: ExprId,
    x: ExprId,
    hc: ExprId,
    hg: ExprId,
    bound: ExprId,
    i: ExprId,
    k: ExprId,
    hi_bound: ExprId,
) -> ExprId {
    let nat_p = d.prelude();

    let si = d.succ(i);
    let le_succ_i = d.lemma(nat_p.le_succ, &[i]);
    let le_i_bound = d.lemma(nat_p.le_trans, &[i, si, bound, le_succ_i, hi_bound]);

    let sub_bound_i = d.sub(bound, i);
    let j = d.add(sub_bound_i, k);

    let ci = d.apply(c, &[i]);
    let xi = d.const_app(p.pow, &[x, i]);
    let gj = d.apply(g, &[j]);
    let xj = d.const_app(p.pow, &[x, j]);
    let gxj = d.const_app(p.mul, &[gj, xj]);
    let cxi = d.const_app(p.mul, &[ci, xi]);
    let full = d.const_app(p.mul, &[cxi, gxj]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let goal = zeq(d, p, full, zero_c);

    let logic = p.creal.rat.int.logic;

    let split_i = d.lemma(nat_p.lt_or_ge, &[i, m]);
    let lt_i_m = d.lt(i, m);
    let le_m_i = d.le(m, i);

    let branch_ge = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hc_i = d.apply(hc, &[i, h]);
        let body = corner_zero_from_c(d, p, ci, xi, gxj, hc_i);
        d.lam_fv(h_fv, le_m_i, body)
    };

    let branch_lt = {
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let split_j = d.lemma(nat_p.lt_or_ge, &[j, n]);
        let lt_j_n = d.lt(j, n);
        let le_n_j = d.le(n, j);

        let sub_branch_ge = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let hg_j = d.apply(hg, &[j, h2]);
            let body = corner_zero_from_g(d, p, ci, xi, gj, xj, hg_j);
            d.lam_fv(h2_fv, le_n_j, body)
        };
        let sub_branch_lt = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let false_proof = corner_index_contradiction(
                d,
                nat_p,
                m,
                n,
                bound,
                i,
                j,
                k,
                sub_bound_i,
                le_i_bound,
                h1,
                h2,
            );
            let body = d.absurd(goal, false_proof);
            d.lam_fv(h2_fv, lt_j_n, body)
        };
        let body = d.const_app(
            logic.or_elim,
            &[lt_j_n, le_n_j, goal, split_j, sub_branch_lt, sub_branch_ge],
        );
        d.lam_fv(h1_fv, lt_i_m, body)
    };

    d.const_app(
        logic.or_elim,
        &[lt_i_m, le_m_i, goal, split_i, branch_lt, branch_ge],
    )
}

/// `Equiv (corner_sum_c big_f bound) zero` — the corner mass of the padded
/// rectangle vanishes under `hc : polyDegreeLt c m`, `hg : polyDegreeLt g n`
/// (`bound = Nat.add m n`, `big_f i j = mul (mul (c i) (pow x i)) (mul (g j)
/// (pow x j))`). Nested [`ComplexPrelude::sum_range_congr_lt`] (outer over
/// rows `i < bound`, inner over positions `k < i`) reduces every summand to
/// [`corner_term_zero`], then [`sum_range_const_zero_proof`] collapses the
/// resulting all-zero sums.
#[allow(clippy::too_many_arguments)]
fn corner_sum_vanishes(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    g: ExprId,
    m: ExprId,
    n: ExprId,
    x: ExprId,
    hc: ExprId,
    hg: ExprId,
    bound: ExprId,
    big_f: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let row_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hib_fv = d.fresh_fvar();
        let hib = d.kernel().fvar(hib_fv);

        let inner_pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hki_fv = d.fresh_fvar();
            let hki = d.kernel().fvar(hki_fv);
            let term_zero = corner_term_zero(d, p, c, g, m, n, x, hc, hg, bound, i, k, hib);
            let inner_lt_i = d.lt(k, i);
            let with_hki = d.lam_fv(hki_fv, inner_lt_i, term_zero);
            let _ = hki; // bound but unused inside term_zero
            d.lam_fv(k_fv, nat, with_hki)
        };

        let corner_i = corner_inner_c(d, big_f, i, bound);
        let zfn = zero_fn(d, p);
        let h1 = d.lemma(p.sum_range_congr_lt, &[corner_i, zfn, i, inner_pointwise]);
        let sum_corner_i = d.const_app(p.sum_range, &[corner_i, i]);
        let sum_zfn_i = d.const_app(p.sum_range, &[zfn, i]);
        let h2 = sum_range_const_zero_proof(d, p, i);
        let body = d.lemma(p.equiv_trans, &[sum_corner_i, sum_zfn_i, zero_c, h1, h2]);

        let hyp_ty = d.lt(i, bound);
        let with_hib = d.lam_fv(hib_fv, hyp_ty, body);
        d.lam_fv(i_fv, nat, with_hib)
    };

    let corner_row = corner_row_c(d, p, big_f, bound);
    let zfn2 = zero_fn(d, p);
    let h_outer = d.lemma(
        p.sum_range_congr_lt,
        &[corner_row, zfn2, bound, row_pointwise],
    );
    let sum_corner = d.const_app(p.sum_range, &[corner_row, bound]);
    let sum_zfn2 = d.const_app(p.sum_range, &[zfn2, bound]);
    let h_final = sum_range_const_zero_proof(d, p, bound);
    d.lemma(
        p.equiv_trans,
        &[sum_corner, sum_zfn2, zero_c, h_outer, h_final],
    )
}

/// The per-row pointwise fact `poly_mul_pointwise` needs: for `i` with
/// `Nat.lt i (Nat.succ k)` (hence `Nat.le i k`), `Equiv (mul (pow x k) (mul
/// (c i) (g (Nat.sub k i)))) (mul (mul (c i) (pow x i)) (mul (g (Nat.sub k
/// i)) (pow x (Nat.sub k i))))` — [`pow_split`] plus a four-atom
/// `ring_law_proof` rearrangement.
fn poly_mul_row_pointwise(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    g: ExprId,
    x: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let nat_p = d.prelude();
    let sk = d.succ(k);
    let xk = d.const_app(p.pow, &[x, k]);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hik_fv = d.fresh_fvar();
    let hik = d.kernel().fvar(hik_fv);

    let le_i_k = d.lemma(nat_p.le_of_succ_le_succ, &[i, k, hik]);

    let ki = d.sub(k, i);
    let ci = d.apply(c, &[i]);
    let gki = d.apply(g, &[ki]);
    let h_i = d.const_app(p.mul, &[ci, gki]);

    let xpow_split = pow_split(d, p, x, i, k, le_i_k);
    // xpow_split : Equiv(xk, mul(x^i, x^{k-i}))
    let refl_hi = d.lemma(p.equiv_refl, &[h_i]);
    let xi = d.const_app(p.pow, &[x, i]);
    let xki = d.const_app(p.pow, &[x, ki]);
    let x_prod = d.const_app(p.mul, &[xi, xki]);
    let step1 = d.lemma(p.mul_congr, &[xk, x_prod, h_i, h_i, xpow_split, refl_hi]);
    // step1 : Equiv(mul(xk,h_i), mul(x_prod,h_i))
    let mul_xk_hi = d.const_app(p.mul, &[xk, h_i]);

    let xi_v = CExpr::var(d, p, xi);
    let xki_v = CExpr::var(d, p, xki);
    let ci_v = CExpr::var(d, p, ci);
    let gki_v = CExpr::var(d, p, gki);
    let lhs_c = CExpr::mul(
        CExpr::mul(xi_v.clone(), xki_v.clone()),
        CExpr::mul(ci_v.clone(), gki_v.clone()),
    );
    let rhs_c = CExpr::mul(CExpr::mul(ci_v, xi_v), CExpr::mul(gki_v, xki_v));
    let lhs_term = render_c(d, p, &lhs_c);
    let rhs_term = render_c(d, p, &rhs_c);
    let ring_step = ring_law_proof(d, p, &lhs_c, &rhs_c);

    let step_final = d.lemma(
        p.equiv_trans,
        &[mul_xk_hi, lhs_term, rhs_term, step1, ring_step],
    );

    let hyp_ty = d.lt(i, sk);
    let with_hik = d.lam_fv(hik_fv, hyp_ty, step_final);
    let _ = hik;
    d.lam_fv(i_fv, nat, with_hik)
}

/// `Equiv (mul (polyMul c g applied k) (pow x k)) (diag_t_fn_c big_f applied
/// k)` — one antidiagonal's worth of `polyMul`'s convolution, scaled by `x^k`,
/// equals the corresponding antidiagonal term of the `(fc, fg)` rectangle
/// decomposition. Unconditional in `k`: [`ComplexPrelude::mul_comm`] then
/// [`ComplexPrelude::mul_sum_range`] moves `pow x k` inside the sum, then
/// [`ComplexPrelude::sum_range_congr_lt`] with [`poly_mul_row_pointwise`]
/// matches every term.
fn poly_mul_k_pointwise(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
    c: ExprId,
    g: ExprId,
    x: ExprId,
    big_f: ExprId,
    k: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let sk = d.succ(k);

    let h_summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let ki = d.sub(k, i);
        let gki = d.apply(g, &[ki]);
        let body = d.const_app(p.mul, &[ci, gki]);
        d.lam_fv(i_fv, nat, body)
    };
    let s_k = d.const_app(p.sum_range, &[h_summand, sk]);
    let xk = d.const_app(p.pow, &[x, k]);

    let step_a = d.lemma(p.mul_comm, &[s_k, xk]);
    let mul_sk_xk = d.const_app(p.mul, &[s_k, xk]);
    let mul_xk_sk = d.const_app(p.mul, &[xk, s_k]);

    let step_b = d.lemma(p.mul_sum_range, &[xk, h_summand, sk]);
    let scaled_summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_val = d.apply(h_summand, &[i]);
        let body = d.const_app(p.mul, &[xk, hi_val]);
        d.lam_fv(i_fv, nat, body)
    };
    let sum_scaled = d.const_app(p.sum_range, &[scaled_summand, sk]);

    let diag_inner_k = diag_inner_c(d, big_f, k);
    let pointwise = poly_mul_row_pointwise(d, p, c, g, x, k);
    let step_c = d.lemma(
        p.sum_range_congr_lt,
        &[scaled_summand, diag_inner_k, sk, pointwise],
    );
    let sum_diag_k = d.const_app(p.sum_range, &[diag_inner_k, sk]);

    let t1 = d.lemma(
        p.equiv_trans,
        &[mul_sk_xk, mul_xk_sk, sum_scaled, step_a, step_b],
    );
    d.lemma(
        p.equiv_trans,
        &[mul_sk_xk, sum_scaled, sum_diag_k, t1, step_c],
    )
}

/// `Complex.polyEval_polyMul`: see [`ComplexPrelude::poly_eval_poly_mul`] for
/// the statement and route.
fn declare_poly_eval_poly_mul(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let degree_lt_c = poly_degree_lt_applied(d, p, c, m);
    let degree_lt_g = poly_degree_lt_applied(d, p, g, n);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let bound = d.add(m, n);

    let fc = poly_summand(d, p, c, x);
    let fg = poly_summand(d, p, g, x);
    let big_f = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(fc, &[i]);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let gj = d.apply(fg, &[j]);
        let body = d.const_app(p.mul, &[fi, gj]);
        let inner = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, inner)
    };

    // ----- padding -----------------------------------------------------------
    let h_pad_c = poly_pad_up(d, p, c, x, m, n, hc);
    // h_pad_c : Equiv(sumRange(fc,bound), sumRange(fc,m))

    let h_pad_g0 = poly_pad_up(d, p, g, x, n, m, hg);
    // h_pad_g0 : Equiv(sumRange(fg,add(n,m)), sumRange(fg,n))
    let nat_p = d.prelude();
    let h_comm_nm = d.lemma(nat_p.add_comm, &[n, m]);
    // h_comm_nm : Eq Nat (add n m) (add m n) = Eq Nat (add n m) bound
    let add_n_m = d.add(n, m);
    let target_g = |dd: &mut IntDev<'_>, xx: ExprId| dd.const_app(p.sum_range, &[fg, xx]);
    let h_reindex = nat_eq_to_complex_equiv(d, p, add_n_m, bound, h_comm_nm, &target_g);
    // h_reindex : Equiv(sumRange(fg,add_n_m), sumRange(fg,bound))
    let sum_fg_anm = d.const_app(p.sum_range, &[fg, add_n_m]);
    let sum_fg_bound = d.const_app(p.sum_range, &[fg, bound]);
    let h_reindex_symm = d.lemma(p.equiv_symm, &[sum_fg_anm, sum_fg_bound, h_reindex]);
    let sum_fg_n = d.const_app(p.sum_range, &[fg, n]);
    let h_pad_g = d.lemma(
        p.equiv_trans,
        &[sum_fg_bound, sum_fg_anm, sum_fg_n, h_reindex_symm, h_pad_g0],
    );
    // h_pad_g : Equiv(sumRange(fg,bound), sumRange(fg,n))

    // ----- combine the two padded factors -------------------------------------
    let sum_fc_bound = d.const_app(p.sum_range, &[fc, bound]);
    let sum_fc_m = d.const_app(p.sum_range, &[fc, m]);
    let h_mul_pad = d.lemma(
        p.mul_congr,
        &[
            sum_fc_bound,
            sum_fc_m,
            sum_fg_bound,
            sum_fg_n,
            h_pad_c,
            h_pad_g,
        ],
    );
    // h_mul_pad : Equiv(mul(sum_fc_bound,sum_fg_bound), mul(sum_fc_m,sum_fg_n))

    // ----- diagonal + corner at the shared bound ------------------------------
    let h_diag_corner = d.lemma(p.sum_range_mul_eq_diag_add_corner, &[fc, fg, bound]);
    let triangle = diag_triangle_sum_c(d, p, big_f, bound);
    let corner = corner_sum_c(d, p, big_f, bound);
    let add_tri_corner = d.const_app(p.add, &[triangle, corner]);

    let h_corner_zero = corner_sum_vanishes(d, p, c, g, m, n, x, hc, hg, bound, big_f);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let refl_tri = d.lemma(p.equiv_refl, &[triangle]);
    let h_add_congr = d.lemma(
        p.add_congr,
        &[triangle, triangle, corner, zero_c, refl_tri, h_corner_zero],
    );
    let tri_plus_zero = d.const_app(p.add, &[triangle, zero_c]);
    let h_add_zero = d.lemma(p.add_zero, &[triangle]);
    let h_simplify = d.lemma(
        p.equiv_trans,
        &[
            add_tri_corner,
            tri_plus_zero,
            triangle,
            h_add_congr,
            h_add_zero,
        ],
    );

    let mul_bound = d.const_app(p.mul, &[sum_fc_bound, sum_fg_bound]);
    let h_mul_eq_triangle = d.lemma(
        p.equiv_trans,
        &[
            mul_bound,
            add_tri_corner,
            triangle,
            h_diag_corner,
            h_simplify,
        ],
    );
    // h_mul_eq_triangle : Equiv(mul_bound, triangle)

    // ----- polyMul's antidiagonal convolution equals the triangle sum --------
    let poly_mul_cg = d.const_app(p.poly_mul, &[c, g]);
    let poly_mul_summand = poly_summand(d, p, poly_mul_cg, x);
    let diag_t_fn = diag_t_fn_c(d, p, big_f);
    let pointwise_k = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = poly_mul_k_pointwise(d, p, c, g, x, big_f, k);
        d.lam_fv(k_fv, nat, body)
    };
    let h_pm_tri = d.lemma(
        p.sum_range_congr,
        &[poly_mul_summand, diag_t_fn, bound, pointwise_k],
    );
    let sum_pm_bound = d.const_app(p.sum_range, &[poly_mul_summand, bound]);

    // ----- assemble ------------------------------------------------------------
    let target_rhs = d.const_app(p.mul, &[sum_fc_m, sum_fg_n]);
    let h_tri_symm = d.lemma(p.equiv_symm, &[mul_bound, triangle, h_mul_eq_triangle]);
    let h_final1 = d.lemma(
        p.equiv_trans,
        &[sum_pm_bound, triangle, mul_bound, h_pm_tri, h_tri_symm],
    );
    let h_final = d.lemma(
        p.equiv_trans,
        &[sum_pm_bound, mul_bound, target_rhs, h_final1, h_mul_pad],
    );

    let lhs_stmt = d.const_app(p.poly_eval, &[poly_mul_cg, bound, x]);
    let eval_c_m = d.const_app(p.poly_eval, &[c, m, x]);
    let eval_g_n = d.const_app(p.poly_eval, &[g, n, x]);
    let rhs_stmt = d.const_app(p.mul, &[eval_c_m, eval_g_n]);
    let stmt = zeq(d, p, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, stmt);
        let after_hg = d.arrow(degree_lt_g, over_x);
        let after_hc = d.arrow(degree_lt_c, after_hg);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, h_final);
        let after_hg = d.lam_fv(hg_fv, degree_lt_g, over_x);
        let after_hc = d.lam_fv(hc_fv, degree_lt_c, after_hg);
        let over_n = d.lam_fv(n_fv, nat, after_hc);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(c_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.poly_eval_poly_mul,
        uparams: vec![],
        ty,
        value,
    })
}
