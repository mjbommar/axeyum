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

use super::{CExpr, ComplexPrelude, complex_eq, complex_eq_refl, complex_ty, ring_law_proof, zeq};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

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
    declare_poly_degree_lt_poly_scale(d, p)
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
