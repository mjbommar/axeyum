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
//! # `polyMul`, `hornerFromTop`, `factorQuotient`
//!
//! **This section used to say `polyMul` and the factor theorem were not
//! attempted — that became false as the file grew and nobody updated the
//! doc. It is corrected here rather than left to mislead the next reader.**
//!
//! [`declare_poly_mul`]/[`declare_poly_degree_lt_poly_mul`]/
//! [`declare_poly_eval_poly_mul`] give `polyMul` (the finite Cauchy product)
//! and its evaluation homomorphism `Equiv (mul (polyEval c m x) (polyEval g n
//! x)) (polyEval (polyMul c g) (Nat.add m n) x)`, under `polyDegreeLt`
//! hypotheses for both factors — padding each sum to the shared bound via
//! [`ComplexPrelude::sum_range_split`], decomposing via
//! [`ComplexPrelude::sum_range_mul_eq_diag_add_corner`] (the identity
//! *without* the corner term is FALSE, refuted by hand at `n = 2`), and
//! showing the corner vanishes.
//!
//! **The factor theorem's computed quotient.** `Exists.rec` is `Prop`-only,
//! so a proof of `∃ q, …` cannot hand back `q` as *data* — the quotient in
//! `p ≡ polyMul (X − a) q` must be **computed**, not extracted. The design:
//! grow the DIVIDEND's bound via `Nat.rec` directly, reusing `c` at smaller
//! bounds so the "new" top coefficient at each step is `c`'s own `Nat.rec`
//! index, never a subtracted one — as opposed to the backward synthetic-
//! division recursion (`q_k` needs `p_{k+1}` and `q_{k+1}`, inherently
//! top-down), where every "ascending on a reversed index" reformulation just
//! relocates the `Nat.sub` dependency into indexing `c` rather than
//! eliminating it.
//!
//! [`declare_horner_from_top`] builds `Complex.hornerFromTop c a m j` this
//! way: a nested `Nat.rec` (outer on `m`, inner on `j`, mirroring
//! [`ComplexPrelude::pow`]'s own construction — `NatOps::induct` cannot
//! produce this, its motive is `Prop`-only) whose only reference to `c` is
//! `c (succ m)`, `m`'s own index. [`declare_factor_quotient`] then
//! re-indexes this top-down family into the forward (bottom-up) coefficient
//! function `polyMul`/`polyEval` expect, via **one** top-level `Nat.sub`
//! rather than a subtraction embedded in a recursion.
//!
//! That reindexing has a boundary bug on the first attempt, found and fixed
//! here — worth recording because it is exactly the "quietly wrong at a
//! boundary" shape `Nat.sub`'s truncation invites. `fun k => hornerFromTop c
//! a n (Nat.sub n (Nat.succ k))` sends every `k ≥ n` to the SAME index `0`
//! (truncation), and `hornerFromTop c a n 0` is `c n` — the polynomial's own
//! leading coefficient, generically nonzero. Confirmed by hand at `c = X² −
//! 1`: this formula gives `q 2 = c 2 = 1`, refuting `polyDegreeLt q 2`
//! outright. The fix ([`poly::PolyNames::factor_quotient`]'s doc has the full
//! derivation) prepends a forced `zero` base and shifts `hornerFromTop`'s own
//! index down by one, so truncation lands on the forced zero **by
//! construction**, not by coincidence. [`declare_factor_quotient_degree_lt`]
//! proves `polyDegreeLt (factorQuotient c a n) n` from this, and
//! `complex_tests.rs`'s `factor_quotient_reproduces_x_plus_one_at_the_root_and_not_elsewhere`
//! corroborates it concretely: at a genuine `X² − 1` and the root `a = 1`,
//! `factorQuotient` reproduces `X + 1`'s coefficients exactly (including the
//! `q 2 = 0` boundary); at the non-root `a = 2`, the correct value (`q 0 =
//! 2`) is accepted and the root-case value (`1`) at that same call is
//! REJECTED — a non-vacuous refutation, since the accept/reject pair is about
//! the same call with two different claimed answers.
//!
//! **The row-growth claim, corrected, and the sum-level bridge it was
//! gesturing at.** This section used to claim the natural induction needed a
//! NEW fact — `s^{(m+1)}_k = s^{(m)}_k + a^{m+1-k}·p_{m+1}` for every `k ≤
//! m` — and called it "not attempted". That was imprecise in a way worth
//! recording rather than silently fixing: read against `hornerFromTop`'s OWN
//! indexing (`j` counts UP from the top — `j = 0` is the leading coefficient
//! `c (succ m)` — not down from some fixed window), the claimed relation
//! *is* [`declare_horner_from_top_equations`]'s `hornerFromTop_succ_succ`,
//! already proved by `Eq.refl` at the time that paragraph was written.
//! Growing the bound does not "change every value in the row" in any sense
//! that needed a new lemma — it is exactly one ι-reduction step of a
//! recursion that was already total.
//!
//! What THAT defeq-level fact does not give for free is any connection to
//! `polyEval`'s `sumRange`-shaped value — a nested `Nat.rec` and a
//! `sumRange` fold are structurally unrelated data, and nothing above
//! bridges them. [`declare_horner_from_top_diag_eq_poly_eval`] is that
//! bridge: `Equiv (hornerFromTop c a n n) (polyEval c (Nat.succ n) a)`,
//! proved by induction on `n` (base case: both sides reduce, via
//! `hornerFromTop_zero`/`polyEval_zero`/`polyEval_succ`/`pow_zero`, each an
//! `Eq` lifted to `Equiv`, plus a `ring_law_proof` collapse, to `c 0`; step:
//! `hornerFromTop_succ_succ`/`polyEval_succ` unfold one term each, the
//! inductive hypothesis rewrites in via `add_congr`, and a `mul_comm`-shaped
//! `ring_law_proof` closes the one remaining mismatch). Corroborated
//! concretely in `complex_tests.rs`'s
//! `horner_from_top_diag_matches_poly_eval_at_a_nonzero_middle_coefficient`
//! at a three-term polynomial with a NONZERO middle coefficient (`X² − 1`'s
//! is zero, and would have made this lemma's `a`-dependence invisible to a
//! concrete check).
//!
//! **STILL NOT attempted: the general symbolic factor theorem itself**
//! (`polyEval p (succ n) a ~ zero → ∀ x, Equiv (polyEval p (succ n) x)
//! (polyEval (polyMul (X − a) (factorQuotient p a n)) (Nat.add 2 n) x)`), and
//! the diagonal bridge above does not close it by itself. It supplies one
//! anchor point — `hornerFromTop c a n n` (the value `factorQuotient c a n
//! 0` reduces to) is literally `polyEval c (succ n) a`, the very quantity the
//! factor hypothesis says vanishes — but the theorem needs a sum over ALL of
//! `factorQuotient c a n`'s coefficients, not just its bottom one, matched
//! term-by-term against a telescoping rearrangement of `polyEval c (succ n)
//! x`. A naive induction on `n` that reuses the smaller `factorQuotient c a
//! n` wholesale still does not close it: `factorQuotient c a (succ n)` and
//! `factorQuotient c a n` differ at every SHARED index `k ≤ n − 1` by a
//! correction term `a^{n-k}·c(succ n)` (the new top coefficient's
//! contribution), so the induction has to carry that correction explicitly
//! rather than treat the smaller quotient as reusable as-is. Landing that,
//! plus the `Nat.add`-ordering and [`poly_pad_up`] bookkeeping
//! [`declare_poly_eval_poly_mul`] already needs for a bound mismatch of `+1`
//! (`Nat.add 2 n = n + 2`, one more than `p`'s own `succ n`), remains real,
//! sized work.

use super::{
    CExpr, ComplexPrelude, complex_eq, complex_eq_refl, complex_eq_to_equiv, complex_ty,
    corner_inner_c, corner_row_c, corner_sum_c, diag_inner_c, diag_t_fn_c, diag_triangle_sum_c,
    nat_eq_to_complex_equiv, render_c, ring_law_proof, shifted_c, sum_range_const_zero_proof, zeq,
    zero_fn,
};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::{NatOps, NatPrelude};

/// The names [`declare_polynomial`] declares, owned by this module rather
/// than by [`ComplexPrelude`] directly.
///
/// This is Part B of
/// `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`: no
/// step outside this file requires any of these 21 names (checked against
/// every other `BuildStep`'s `requires` list), so a new declaration added
/// inside `poly.rs` needs a new field here and a new line in
/// [`declare_polynomial`]'s call sequence -- never a hub edit in
/// `complex.rs`'s struct, `STEPS` table, or `intern_names`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PolyNames {
    pub poly_eval: NameId,
    pub poly_eval_zero: NameId,
    pub poly_eval_succ: NameId,
    pub poly_add: NameId,
    pub poly_eval_poly_add: NameId,
    pub poly_scale: NameId,
    pub poly_eval_poly_scale: NameId,
    pub poly_degree_lt: NameId,
    pub poly_degree_lt_poly_add: NameId,
    pub poly_degree_lt_poly_scale: NameId,
    pub poly_mul: NameId,
    pub poly_degree_lt_poly_mul: NameId,
    pub poly_eval_poly_mul: NameId,
    pub horner_from_top: NameId,
    pub horner_from_top_zero: NameId,
    pub horner_from_top_succ_zero: NameId,
    pub horner_from_top_succ_succ: NameId,
    pub factor_quotient: NameId,
    pub factor_quotient_degree_lt: NameId,
    pub horner_from_top_diag_eq_poly_eval: NameId,
    pub factor_quotient_succ_eq: NameId,
}

/// Interns this module's 21 names under `complex` (e.g. `Complex.polyEval`).
/// Called once from [`super::intern_names`] as `poly: poly::intern_names(kernel, complex)`.
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> PolyNames {
    PolyNames {
        poly_eval: kernel.name_str(complex, "polyEval"),
        poly_eval_zero: kernel.name_str(complex, "polyEval_zero"),
        poly_eval_succ: kernel.name_str(complex, "polyEval_succ"),
        poly_add: kernel.name_str(complex, "polyAdd"),
        poly_eval_poly_add: kernel.name_str(complex, "polyEval_polyAdd"),
        poly_scale: kernel.name_str(complex, "polyScale"),
        poly_eval_poly_scale: kernel.name_str(complex, "polyEval_polyScale"),
        poly_degree_lt: kernel.name_str(complex, "polyDegreeLt"),
        poly_degree_lt_poly_add: kernel.name_str(complex, "polyDegreeLt_polyAdd"),
        poly_degree_lt_poly_scale: kernel.name_str(complex, "polyDegreeLt_polyScale"),
        poly_mul: kernel.name_str(complex, "polyMul"),
        poly_degree_lt_poly_mul: kernel.name_str(complex, "polyDegreeLt_polyMul"),
        poly_eval_poly_mul: kernel.name_str(complex, "polyEval_polyMul"),
        horner_from_top: kernel.name_str(complex, "hornerFromTop"),
        horner_from_top_zero: kernel.name_str(complex, "hornerFromTop_zero"),
        horner_from_top_succ_zero: kernel.name_str(complex, "hornerFromTop_succ_zero"),
        horner_from_top_succ_succ: kernel.name_str(complex, "hornerFromTop_succ_succ"),
        factor_quotient: kernel.name_str(complex, "factorQuotient"),
        factor_quotient_degree_lt: kernel.name_str(complex, "factorQuotient_degreeLt"),
        horner_from_top_diag_eq_poly_eval: kernel
            .name_str(complex, "hornerFromTop_diag_eq_polyEval"),
        factor_quotient_succ_eq: kernel.name_str(complex, "factorQuotient_succ_eq"),
    }
}

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
/// Height for `Complex.hornerFromTop`: its value embeds only `add`, `mul`
/// and [`ComplexPrelude::pow`] (`+9`) — no `sum_range`/`poly_eval`/`poly_mul`
/// callee — so one above [`POLY_EVAL_HEIGHT`] keeps it strictly above every
/// height declared in this file so far, with margin to spare.
const HORNER_HEIGHT: u16 = POLY_EVAL_HEIGHT + 1;
/// Height for `Complex.factorQuotient`: its value embeds [`Self::horner_from_top`]
/// via [`HORNER_HEIGHT`], so it needs strictly more.
///
/// [`Self::horner_from_top`]: super::poly::PolyNames::horner_from_top
const FACTOR_QUOTIENT_HEIGHT: u16 = HORNER_HEIGHT + 1;

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
    declare_poly_degree_lt_poly_mul(d, p)?;
    declare_poly_eval_poly_mul(d, p)?;
    declare_horner_from_top(d, p)?;
    declare_horner_from_top_equations(d, p)?;
    declare_horner_from_top_diag_eq_poly_eval(d, p)?;
    declare_factor_quotient(d, p)?;
    declare_factor_quotient_succ_eq(d, p)?;
    declare_factor_quotient_degree_lt(d, p)
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
        name: p.poly.poly_eval,
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
        let lhs = d.const_app(p.poly.poly_eval, &[c, zero_n, x]);
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
            name: p.poly.poly_eval_zero,
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
        let lhs = d.const_app(p.poly.poly_eval, &[c, sn, x]);
        let prior = d.const_app(p.poly.poly_eval, &[c, n, x]);
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
            name: p.poly.poly_eval_succ,
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
        name: p.poly.poly_add,
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

    let poly_add_cg = d.const_app(p.poly.poly_add, &[c, g]);
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

    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_add_cg, n, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, n, x]);
    let eval_g = d.const_app(p.poly.poly_eval, &[g, n, x]);
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
        name: p.poly.poly_eval_poly_add,
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
        name: p.poly.poly_scale,
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

    let poly_scale_ac = d.const_app(p.poly.poly_scale, &[a, c]);
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

    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_scale_ac, n, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, n, x]);
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
        name: p.poly.poly_eval_poly_scale,
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
        name: p.poly.poly_degree_lt,
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
    let poly_add_cg = d.const_app(p.poly.poly_add, &[c, g]);
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
        name: p.poly.poly_degree_lt_poly_add,
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
    d.const_app(p.poly.poly_degree_lt, &[f, n])
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
        name: p.poly.poly_degree_lt_poly_scale,
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
/// [`poly::PolyNames::poly_eval_poly_mul`] for the vanishing hypotheses that
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
        name: p.poly.poly_mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_MUL_HEIGHT),
    })
}

/// `Complex.polyDegreeLt_polyMul` — see [`poly::PolyNames::poly_degree_lt_poly_mul`]
/// for the statement and route. Sized by the predecessor as "a smaller,
/// structurally similar case split" to [`corner_term_zero`]: for `k` with
/// `Nat.le (Nat.add m n) k`, every index `i` of `polyMul c g k`'s
/// convolution — unconditionally in `i`, no bound on it is needed — satisfies
/// `Nat.le m i ∨ Nat.le n (Nat.sub k i)`, via `Nat.lt_or_ge i m`:
///
/// - `Nat.le m i`: `hc` gives `c i ≡ zero`; [`poly_pad_up`]'s two-atom
///   `mul_congr` + `ring_law_proof` pattern (not [`corner_zero_from_c`]'s
///   four-atom nested one — `polyMul`'s summand is a plain product) collapses
///   the term.
/// - `Nat.lt i m`: derives `Nat.le n (Nat.sub k i)` from `Nat.le (Nat.add m
///   n) k` and `Nat.lt i m` — `add_le_add_right` plus `succ_add` first give
///   `Nat.le (Nat.add i n) k`, then the SAME `sub_add_cancel` +
///   restore-and-transport technique [`corner_index_contradiction`] uses to
///   reintroduce a subtracted index cancels `i` back off via
///   [`crate::nat_prelude::NatPrelude::le_of_add_le_add_right`], proving a
///   genuine fact here instead of `False`. `hg` then gives `g (Nat.sub k i) ≡
///   zero`.
fn declare_poly_degree_lt_poly_mul(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);
    let nat_p = d.prelude();
    let logic = p.creal.rat.int.logic;

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let bound = d.add(m, n);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let sk = d.succ(k);

    // ----- the per-index pointwise fact, unconditional in `i` ---------------
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let ki = d.sub(k, i);
        let gki = d.apply(g, &[ki]);
        let term = d.const_app(p.mul, &[ci, gki]);
        let goal = zeq(d, p, term, zero_c);

        let split_i = d.lemma(nat_p.lt_or_ge, &[i, m]);
        let lt_i_m = d.lt(i, m);
        let le_m_i = d.le(m, i);

        let branch_ge = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hc_i = d.apply(hc, &[i, h]);
            // hc_i : Equiv(ci, zero)
            let refl_gki = d.lemma(p.equiv_refl, &[gki]);
            let step1 = d.lemma(p.mul_congr, &[ci, zero_c, gki, gki, hc_i, refl_gki]);
            // step1 : Equiv(mul(ci,gki), mul(zero,gki))

            let gki_v = CExpr::var(d, p, gki);
            let mid_c = CExpr::mul(CExpr::Zero, gki_v);
            let mid_term = render_c(d, p, &mid_c);
            let h_ring = ring_law_proof(d, p, &mid_c, &CExpr::Zero);

            let body = d.lemma(p.equiv_trans, &[term, mid_term, zero_c, step1, h_ring]);
            d.lam_fv(h_fv, le_m_i, body)
        };

        let branch_lt = {
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            // h1 : Nat.lt i m (defeq Le (succ i) m)

            // ----- Le (add i n) k -------------------------------------------
            let succ_i = d.succ(i);
            let step1 = d.lemma(nat_p.add_le_add_right, &[n, succ_i, m, h1]);
            // step1 : Le (add succ_i n) (add m n) = Le (add succ_i n) bound
            let add_succi_n = d.add(succ_i, n);
            let step2 = d.lemma(nat_p.le_trans, &[add_succi_n, bound, k, step1, hk]);
            // step2 : Le (add succ_i n) k

            let h_succ_add = d.lemma(nat_p.succ_add, &[i, n]);
            // h_succ_add : Eq Nat (add succ_i n) (succ (add i n))
            let add_i_n = d.add(i, n);
            let succ_add_i_n = d.succ(add_i_n);
            let motive1 = d.eq_motive(add_succi_n, &|dd, xx| dd.le(xx, k));
            let step3 = d.transport(add_succi_n, motive1, step2, succ_add_i_n, h_succ_add);
            // step3 : Le (succ add_i_n) k = Nat.lt add_i_n k

            let le_add_in_k = {
                let s_addin = d.succ(add_i_n);
                let le_succ_addin = d.lemma(nat_p.le_succ, &[add_i_n]);
                d.lemma(nat_p.le_trans, &[add_i_n, s_addin, k, le_succ_addin, step3])
            };
            // le_add_in_k : Le (add i n) k

            // ----- Le n (sub k i) --------------------------------------------
            let le_i_addin = d.lemma(nat_p.le_add_right, &[i, n]);
            // le_i_addin : Le i (add i n)
            let le_i_k = d.lemma(nat_p.le_trans, &[i, add_i_n, k, le_i_addin, le_add_in_k]);
            // le_i_k : Le i k

            let h_restore = d.lemma(nat_p.sub_add_cancel, &[i, k, le_i_k]);
            // h_restore : Eq Nat (add ki i) k
            let add_ki_i = d.add(ki, i);
            let h_restore_symm = d.symm(add_ki_i, k, h_restore);
            // h_restore_symm : Eq Nat k (add ki i)

            let h_comm = d.lemma(nat_p.add_comm, &[i, n]);
            // h_comm : Eq Nat (add i n) (add n i)
            let add_n_i = d.add(n, i);
            let motive2 = d.eq_motive(add_i_n, &|dd, xx| dd.le(xx, k));
            let step4 = d.transport(add_i_n, motive2, le_add_in_k, add_n_i, h_comm);
            // step4 : Le (add n i) k

            let motive3 = d.eq_motive(k, &|dd, xx| dd.le(add_n_i, xx));
            let step5 = d.transport(k, motive3, step4, add_ki_i, h_restore_symm);
            // step5 : Le (add n i) (add ki i)

            let hn_le_ki = d.lemma(nat_p.le_of_add_le_add_right, &[i, n, ki, step5]);
            // hn_le_ki : Le n ki

            let hg_j = d.apply(hg, &[ki, hn_le_ki]);
            // hg_j : Equiv(gki, zero)
            let refl_ci = d.lemma(p.equiv_refl, &[ci]);
            let step6 = d.lemma(p.mul_congr, &[ci, ci, gki, zero_c, refl_ci, hg_j]);
            // step6 : Equiv(mul(ci,gki), mul(ci,zero))

            let ci_v = CExpr::var(d, p, ci);
            let mid_c2 = CExpr::mul(ci_v, CExpr::Zero);
            let mid_term2 = render_c(d, p, &mid_c2);
            let h_ring2 = ring_law_proof(d, p, &mid_c2, &CExpr::Zero);

            let body = d.lemma(p.equiv_trans, &[term, mid_term2, zero_c, step6, h_ring2]);
            d.lam_fv(h1_fv, lt_i_m, body)
        };

        let case_proof = d.const_app(
            logic.or_elim,
            &[lt_i_m, le_m_i, goal, split_i, branch_lt, branch_ge],
        );
        d.lam_fv(i_fv, nat, case_proof)
    };

    // ----- collapse the sum ---------------------------------------------------
    let poly_mul_summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let ki = d.sub(k, i);
        let gki = d.apply(g, &[ki]);
        let body = d.const_app(p.mul, &[ci, gki]);
        d.lam_fv(i_fv, nat, body)
    };
    let zfn = zero_fn(d, p);
    let h1 = d.lemma(p.sum_range_congr, &[poly_mul_summand, zfn, sk, pointwise]);
    let sum_pm_sk = d.const_app(p.sum_range, &[poly_mul_summand, sk]);
    let sum_zfn_sk = d.const_app(p.sum_range, &[zfn, sk]);
    let h2 = sum_range_const_zero_proof(d, p, sk);
    let final_proof = d.lemma(p.equiv_trans, &[sum_pm_sk, sum_zfn_sk, zero_c, h1, h2]);

    let le_bound_k = d.le(bound, k);
    let poly_mul_cg = d.const_app(p.poly.poly_mul, &[c, g]);
    let degree_lt_c = poly_degree_lt_applied(d, p, c, m);
    let degree_lt_g = poly_degree_lt_applied(d, p, g, n);
    let degree_lt_mul = poly_degree_lt_applied(d, p, poly_mul_cg, bound);

    let value = {
        let over_hk = d.lam_fv(hk_fv, le_bound_k, final_proof);
        let over_k = d.lam_fv(k_fv, nat, over_hk);
        let over_hg = d.lam_fv(hg_fv, degree_lt_g, over_k);
        let over_hc = d.lam_fv(hc_fv, degree_lt_c, over_hg);
        let over_n = d.lam_fv(n_fv, nat, over_hc);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(c_fv, fn_ty, over_g)
    };
    let ty = {
        let after_hg = d.arrow(degree_lt_g, degree_lt_mul);
        let after_hc = d.arrow(degree_lt_c, after_hg);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.poly.poly_degree_lt_poly_mul,
        uparams: vec![],
        ty,
        value,
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

/// `Complex.polyEval_polyMul`: see [`poly::PolyNames::poly_eval_poly_mul`] for
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
    let poly_mul_cg = d.const_app(p.poly.poly_mul, &[c, g]);
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

    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_mul_cg, bound, x]);
    let eval_c_m = d.const_app(p.poly.poly_eval, &[c, m, x]);
    let eval_g_n = d.const_app(p.poly.poly_eval, &[g, n, x]);
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
        name: p.poly.poly_eval_poly_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// The factor theorem's computed quotient: `hornerFromTop` / `factorQuotient`.
//
// See [`poly::PolyNames::horner_from_top`]/[`poly::PolyNames::factor_quotient`]
// for the exact recurrences and the boundary bug the `factorQuotient` shape
// was chosen to avoid. This section builds the two definitions and the two
// theorems about them; the general symbolic factor theorem itself
// (`polyEval p (succ n) a ~ zero -> p ~ polyMul (X-a) (factorQuotient p a n)`)
// is NOT attempted here — see the module doc above this line for exactly
// what is missing and why.
// ---------------------------------------------------------------------------

/// `Complex.hornerFromTop c a m j`, built by a nested `Nat.rec` (outer on
/// `m`, inner on `j`) at `Complex`'s own universe — see
/// [`poly::PolyNames::horner_from_top`] for the recurrence.
fn declare_horner_from_top(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    use crate::BinderInfo;

    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);
    let rec_name = d.prelude().rec;

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    // outer motive: fun _ : Nat => (Nat -> Complex)
    let outer_motive = d.kernel().lam(anon, nat, fn_ty, BinderInfo::Default);
    let outer_rec = d.kernel().const_(rec_name, vec![one_level]);

    // outer base (m = 0): fun j => c 0 -- ignores j entirely.
    let outer_base = {
        let zero_n = d.zero();
        let c0 = d.apply(c, &[zero_n]);
        let j_fv = d.fresh_fvar();
        d.lam_fv(j_fv, nat, c0)
    };

    // outer step (m -> succ m, ih = hornerFromTop c a m):
    //   fun m ih => fun j => Nat.rec(motive Complex)
    //       (c (succ m))
    //       (fun j' _ => add (ih j') (mul (pow a (succ j')) (c (succ m))))
    //       j
    let outer_step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);

        let succ_m = d.succ(m);
        let c_succ_m = d.apply(c, &[succ_m]);

        let inner_motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
        let inner_rec = d.kernel().const_(rec_name, vec![one_level]);
        let inner_base = c_succ_m;
        let inner_step = {
            let jp_fv = d.fresh_fvar();
            let jp = d.kernel().fvar(jp_fv);
            let jih_fv = d.fresh_fvar();
            let ih_jp = d.apply(ih, &[jp]);
            let succ_jp = d.succ(jp);
            let pow_a_succjp = d.const_app(p.pow, &[a, succ_jp]);
            let mul_term = d.const_app(p.mul, &[pow_a_succjp, c_succ_m]);
            let body = d.const_app(p.add, &[ih_jp, mul_term]);
            let with_jih = d.lam_fv(jih_fv, carrier, body);
            d.lam_fv(jp_fv, nat, with_jih)
        };

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let s_succ_m_j = d.apply(inner_rec, &[inner_motive, inner_base, inner_step, j]);
        let s_succ_m = d.lam_fv(j_fv, nat, s_succ_m_j);

        let with_ih = d.lam_fv(ih_fv, fn_ty, s_succ_m);
        d.lam_fv(m_fv, nat, with_ih)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let s_m = d.apply(outer_rec, &[outer_motive, outer_base, outer_step, m]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let applied = d.apply(s_m, &[j]);

    let value = {
        let over_j = d.lam_fv(j_fv, nat, applied);
        let over_m = d.lam_fv(m_fv, nat, over_j);
        let over_a = d.lam_fv(a_fv, carrier, over_m);
        d.lam_fv(c_fv, fn_ty, over_a)
    };
    let ty = {
        let over_j = d.arrow(nat, carrier);
        let over_m = d.arrow(nat, over_j);
        let over_a = d.arrow(carrier, over_m);
        d.arrow(fn_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.poly.horner_from_top,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(HORNER_HEIGHT),
    })
}

/// `Complex.hornerFromTop_zero` / `_succ_zero` / `_succ_succ` — the three
/// defining equations of [`declare_horner_from_top`], each closed by
/// `Eq.refl` alone (pure `βδι` reduction — see
/// [`poly::PolyNames::horner_from_top_zero`]/`_succ_zero`/`_succ_succ` for the
/// exact statements).
fn declare_horner_from_top_equations(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    // hornerFromTop_zero : ∀ c a j, Eq Complex (hornerFromTop c a 0 j) (c 0).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let zero_n = d.zero();
        let lhs = d.const_app(p.poly.horner_from_top, &[c, a, zero_n, j]);
        let c0 = d.apply(c, &[zero_n]);
        let stmt_inner = complex_eq(d, p, lhs, c0);
        let proof_inner = complex_eq_refl(d, p, c0);

        let ty = {
            let over_j = d.pi_fv(j_fv, nat, stmt_inner);
            let over_a = d.pi_fv(a_fv, carrier, over_j);
            d.pi_fv(c_fv, fn_ty, over_a)
        };
        let value = {
            let over_j = d.lam_fv(j_fv, nat, proof_inner);
            let over_a = d.lam_fv(a_fv, carrier, over_j);
            d.lam_fv(c_fv, fn_ty, over_a)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.poly.horner_from_top_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // hornerFromTop_succ_zero : ∀ c a m,
    //   Eq Complex (hornerFromTop c a (succ m) 0) (c (succ m)).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let zero_n = d.zero();
        let sm = d.succ(m);
        let lhs = d.const_app(p.poly.horner_from_top, &[c, a, sm, zero_n]);
        let c_sm = d.apply(c, &[sm]);
        let stmt_inner = complex_eq(d, p, lhs, c_sm);
        let proof_inner = complex_eq_refl(d, p, c_sm);

        let ty = {
            let over_m = d.pi_fv(m_fv, nat, stmt_inner);
            let over_a = d.pi_fv(a_fv, carrier, over_m);
            d.pi_fv(c_fv, fn_ty, over_a)
        };
        let value = {
            let over_m = d.lam_fv(m_fv, nat, proof_inner);
            let over_a = d.lam_fv(a_fv, carrier, over_m);
            d.lam_fv(c_fv, fn_ty, over_a)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.poly.horner_from_top_succ_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // hornerFromTop_succ_succ : ∀ c a m j,
    //   Eq Complex (hornerFromTop c a (succ m) (succ j))
    //     (add (hornerFromTop c a m j) (mul (pow a (succ j)) (c (succ m)))).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let sm = d.succ(m);
        let sj = d.succ(j);
        let lhs = d.const_app(p.poly.horner_from_top, &[c, a, sm, sj]);

        let prior = d.const_app(p.poly.horner_from_top, &[c, a, m, j]);
        let c_sm = d.apply(c, &[sm]);
        let pow_a_sj = d.const_app(p.pow, &[a, sj]);
        let mul_term = d.const_app(p.mul, &[pow_a_sj, c_sm]);
        let rhs = d.const_app(p.add, &[prior, mul_term]);

        let stmt_inner = complex_eq(d, p, lhs, rhs);
        let proof_inner = complex_eq_refl(d, p, rhs);

        let ty = {
            let over_j = d.pi_fv(j_fv, nat, stmt_inner);
            let over_m = d.pi_fv(m_fv, nat, over_j);
            let over_a = d.pi_fv(a_fv, carrier, over_m);
            d.pi_fv(c_fv, fn_ty, over_a)
        };
        let value = {
            let over_j = d.lam_fv(j_fv, nat, proof_inner);
            let over_m = d.lam_fv(m_fv, nat, over_j);
            let over_a = d.lam_fv(a_fv, carrier, over_m);
            d.lam_fv(c_fv, fn_ty, over_a)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.poly.horner_from_top_succ_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

/// `Complex.hornerFromTop_diag_eq_polyEval : ∀ c a n, Equiv (hornerFromTop c
/// a n n) (polyEval c (Nat.succ n) a)` — the sum-level bridge between
/// `hornerFromTop`'s nested `Nat.rec` and `polyEval`'s `sumRange` fold. See
/// [`poly::PolyNames::horner_from_top_diag_eq_poly_eval`] for the statement's
/// role and for why the module doc's original "row growth" formula, restated
/// correctly, turns out to already be [`poly::PolyNames::horner_from_top_succ_succ`]
/// (proved by `Eq.refl` before this lemma existed) — the genuinely open part
/// was connecting that recursion to `polyEval` at all, which is what this
/// theorem closes.
///
/// Induction on `n` via [`NatOps::induct`]:
/// - Base (`n = 0`): `hornerFromTop c a 0 0` and `polyEval c 1 a` both reduce
///   — the first by [`poly::PolyNames::horner_from_top_zero`], the second by
///   chaining [`poly::PolyNames::poly_eval_succ`], [`poly::PolyNames::poly_eval_zero`],
///   [`ComplexPrelude::pow_zero`] (each an `Eq` lifted to `Equiv` via
///   `complex_eq_to_equiv`) and a `ring_law_proof` collapse of `add zero (mul
///   c0 one)` — to the same value `c 0`.
/// - Step (`n = succ j`, `ih : Equiv (hornerFromTop c a j j) (polyEval c
///   (succ j) a)`): [`poly::PolyNames::horner_from_top_succ_succ`] unfolds the
///   LHS to `add (hornerFromTop c a j j) (mul (pow a (succ j)) (c (succ
///   j)))`; `ih` rewrites the first summand via `add_congr`;
///   [`poly::PolyNames::poly_eval_succ`] unfolds the RHS to `add (polyEval c
///   (succ j) a) (mul (c (succ j)) (pow a (succ j)))`; the two `add`s then
///   differ only by `mul_comm` inside the second summand, closed by
///   `ring_law_proof`.
fn declare_horner_from_top_diag_eq_poly_eval(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let motive = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let hn = d.const_app(p.poly.horner_from_top, &[c, a, n, n]);
        let sn = d.succ(n);
        let pe = d.const_app(p.poly.poly_eval, &[c, sn, a]);
        zeq(d, p, hn, pe)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // ----- base case: Equiv (hornerFromTop c a 0 0) (polyEval c 1 a) --
            let zero_n = d.zero();
            let c0 = d.apply(c, &[zero_n]);
            let one_c = d.kernel().const_(p.one, vec![]);
            let zero_c = d.kernel().const_(p.zero, vec![]);

            // LHS: Equiv (hornerFromTop c a 0 0) c0.
            let h0_lhs = d.const_app(p.poly.horner_from_top, &[c, a, zero_n, zero_n]);
            let h_lhs_eq = d.lemma(p.poly.horner_from_top_zero, &[c, a, zero_n]);
            let h_lhs = complex_eq_to_equiv(d, p, h0_lhs, c0, h_lhs_eq);

            // RHS, unrolled: Equiv (polyEval c 1 a) c0.
            let pe0 = d.const_app(p.poly.poly_eval, &[c, zero_n, a]);
            let h_pz_eq = d.lemma(p.poly.poly_eval_zero, &[c, a]);
            let h_pz = complex_eq_to_equiv(d, p, pe0, zero_c, h_pz_eq);

            let pow_a0 = d.const_app(p.pow, &[a, zero_n]);
            let h_pow0_eq = d.lemma(p.pow_zero, &[a]);
            let h_pow0 = complex_eq_to_equiv(d, p, pow_a0, one_c, h_pow0_eq);

            let sn0 = d.succ(zero_n);
            let pe1 = d.const_app(p.poly.poly_eval, &[c, sn0, a]);
            let mul_c0_pow0 = d.const_app(p.mul, &[c0, pow_a0]);
            let sum_term = d.const_app(p.add, &[pe0, mul_c0_pow0]);
            let h_ps_eq = d.lemma(p.poly.poly_eval_succ, &[c, zero_n, a]);
            let h_ps = complex_eq_to_equiv(d, p, pe1, sum_term, h_ps_eq);

            let refl_c0 = d.lemma(p.equiv_refl, &[c0]);
            let h_mul_cong = d.lemma(p.mul_congr, &[c0, c0, pow_a0, one_c, refl_c0, h_pow0]);
            // h_mul_cong : Equiv (mul c0 (pow a 0)) (mul c0 one)
            let mul_c0_one = d.const_app(p.mul, &[c0, one_c]);

            let h_add_cong = d.lemma(
                p.add_congr,
                &[pe0, zero_c, mul_c0_pow0, mul_c0_one, h_pz, h_mul_cong],
            );
            // h_add_cong : Equiv sum_term (add zero (mul c0 one))
            let add_zero_mulone = d.const_app(p.add, &[zero_c, mul_c0_one]);

            let c0_v = CExpr::var(d, p, c0);
            let ring_lhs = CExpr::add(CExpr::Zero, CExpr::mul(c0_v.clone(), CExpr::One));
            let h_ring = ring_law_proof(d, p, &ring_lhs, &c0_v);
            // h_ring : Equiv (add zero (mul c0 one)) c0

            let (_e, h_reduce) = zchain(
                d,
                p,
                sum_term,
                &[(add_zero_mulone, h_add_cong), (c0, h_ring)],
            );
            // h_reduce : Equiv sum_term c0

            let h_rhs = d.lemma(p.equiv_trans, &[pe1, sum_term, c0, h_ps, h_reduce]);
            // h_rhs : Equiv pe1 c0
            let h_rhs_symm = d.lemma(p.equiv_symm, &[pe1, c0, h_rhs]);
            // h_rhs_symm : Equiv c0 pe1

            d.lemma(p.equiv_trans, &[h0_lhs, c0, pe1, h_lhs, h_rhs_symm])
        },
        &|d, j, ih| {
            // ----- step: from ih : Equiv (hornerFromTop c a j j) (polyEval c
            // (succ j) a), show Equiv (hornerFromTop c a (succ j) (succ j))
            // (polyEval c (succ (succ j)) a). ----------------------------------
            let sj = d.succ(j);
            let c_sj = d.apply(c, &[sj]);
            let pow_a_sj = d.const_app(p.pow, &[a, sj]);

            let h_lhs_eq = d.lemma(p.poly.horner_from_top_succ_succ, &[c, a, j, j]);
            let hjj = d.const_app(p.poly.horner_from_top, &[c, a, j, j]);
            let mul_pow_c = d.const_app(p.mul, &[pow_a_sj, c_sj]);
            let unrolled_lhs = d.const_app(p.add, &[hjj, mul_pow_c]);
            let h_ssj = d.const_app(p.poly.horner_from_top, &[c, a, sj, sj]);
            let h_lhs = complex_eq_to_equiv(d, p, h_ssj, unrolled_lhs, h_lhs_eq);
            // h_lhs : Equiv h_ssj unrolled_lhs

            let refl_mul = d.lemma(p.equiv_refl, &[mul_pow_c]);
            let pe_sj = d.const_app(p.poly.poly_eval, &[c, sj, a]);
            let h_ih_lift = d.lemma(
                p.add_congr,
                &[hjj, pe_sj, mul_pow_c, mul_pow_c, ih, refl_mul],
            );
            // h_ih_lift : Equiv unrolled_lhs (add pe_sj mul_pow_c)
            let mid = d.const_app(p.add, &[pe_sj, mul_pow_c]);

            let pow_v = CExpr::var(d, p, pow_a_sj);
            let c_sj_v = CExpr::var(d, p, c_sj);
            let comm_lhs = CExpr::mul(pow_v.clone(), c_sj_v.clone());
            let comm_rhs = CExpr::mul(c_sj_v.clone(), pow_v.clone());
            let h_comm = ring_law_proof(d, p, &comm_lhs, &comm_rhs);
            // h_comm : Equiv mul_pow_c (mul c_sj pow_a_sj)
            let mul_c_pow = d.const_app(p.mul, &[c_sj, pow_a_sj]);
            let refl_pe_sj = d.lemma(p.equiv_refl, &[pe_sj]);
            let h_mid_to_rhs_inner = d.lemma(
                p.add_congr,
                &[pe_sj, pe_sj, mul_pow_c, mul_c_pow, refl_pe_sj, h_comm],
            );
            // h_mid_to_rhs_inner : Equiv mid (add pe_sj mul_c_pow)
            let rhs_inner = d.const_app(p.add, &[pe_sj, mul_c_pow]);

            let h_rhs_eq = d.lemma(p.poly.poly_eval_succ, &[c, sj, a]);
            let ssj = d.succ(sj);
            let pe_ssj = d.const_app(p.poly.poly_eval, &[c, ssj, a]);
            let h_rhs = complex_eq_to_equiv(d, p, pe_ssj, rhs_inner, h_rhs_eq);
            // h_rhs : Equiv pe_ssj rhs_inner
            let h_rhs_symm = d.lemma(p.equiv_symm, &[pe_ssj, rhs_inner, h_rhs]);
            // h_rhs_symm : Equiv rhs_inner pe_ssj

            let (_e, chain_proof) = zchain(
                d,
                p,
                h_ssj,
                &[
                    (unrolled_lhs, h_lhs),
                    (mid, h_ih_lift),
                    (rhs_inner, h_mid_to_rhs_inner),
                    (pe_ssj, h_rhs_symm),
                ],
            );
            chain_proof
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(a_fv, carrier, inner);
        d.pi_fv(c_fv, fn_ty, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(a_fv, carrier, inner);
        d.lam_fv(c_fv, fn_ty, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.poly.horner_from_top_diag_eq_poly_eval,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.factorQuotient c a n k := Nat.rec (fun _ => Complex) zero (fun r'
/// _ => hornerFromTop c a n r') (Nat.sub n k)` — see
/// [`poly::PolyNames::factor_quotient`] for why the `zero` base is prepended
/// rather than reindexing `hornerFromTop` directly.
fn declare_factor_quotient(d: &mut IntDev<'_>, p: ComplexPrelude) -> Result<(), KernelError> {
    use crate::BinderInfo;

    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);
    let rec_name = d.prelude().rec;

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one_level]);

    let step = {
        let rp_fv = d.fresh_fvar();
        let rp = d.kernel().fvar(rp_fv);
        let ih_fv = d.fresh_fvar();
        let horner = d.const_app(p.poly.horner_from_top, &[c, a, n, rp]);
        let with_ih = d.lam_fv(ih_fv, carrier, horner);
        d.lam_fv(rp_fv, nat, with_ih)
    };

    let sub_nk = d.sub(n, k);
    let value_body = d.apply(rec, &[motive, zero_c, step, sub_nk]);

    let value = {
        let over_k = d.lam_fv(k_fv, nat, value_body);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        let over_a = d.lam_fv(a_fv, carrier, over_n);
        d.lam_fv(c_fv, fn_ty, over_a)
    };
    let ty = {
        let over_k = d.arrow(nat, carrier);
        let over_n = d.arrow(nat, over_k);
        let over_a = d.arrow(carrier, over_n);
        d.arrow(fn_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.poly.factor_quotient,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FACTOR_QUOTIENT_HEIGHT),
    })
}

/// From `hlt : Lt k n`, derive `j` with `Eq Nat (sub n k) (succ j)` — makes
/// the truncated difference's successor shape explicit once it is known
/// positive.
///
/// Composed from PUBLIC `nat_prelude` facts only
/// (`zero_le`/`lt_of_le_of_lt`/`succ_pred_of_pos`/`le_of_lt_succ`/
/// `succ_sub_of_le`) — **deliberately NOT**
/// `nat_prelude::choose::sub_succ_of_lt`, which proves the identical fact
/// (`Lt k n → sub n k = succ (sub n (succ k))`, a different but equivalent
/// witness) but is `pub(super)` to `nat_prelude::choose`, out of this file's
/// scope. Per the standing rule ("a Nat lemma from a file you do not own is a
/// finding, not something to copy"): `nat_prelude::choose::sub_succ_of_lt`
/// would have made this shorter, and is reported here by exact name rather
/// than duplicated.
fn nat_sub_pos_succ_shape(
    d: &mut IntDev<'_>,
    n: ExprId,
    k: ExprId,
    hlt: ExprId,
) -> (ExprId, ExprId) {
    let nat_p = d.prelude();
    let zero_n = d.zero();

    // Lt zero n, from Le zero k and Lt k n.
    let h_zero_le_k = d.lemma(nat_p.zero_le, &[k]);
    let h_pos_n = d.lemma(nat_p.lt_of_le_of_lt, &[zero_n, k, n, h_zero_le_k, hlt]);

    // n = succ (pred n).
    let pn = d.pred(n);
    let spn = d.succ(pn);
    let h_n_eq = d.lemma(nat_p.succ_pred_of_pos, &[n, h_pos_n]);

    // Lt k (succ (pred n)), transporting hlt along h_n_eq.
    let motive_lt = d.eq_motive(n, &|d, x| d.lt(k, x));
    let hlt2 = d.transport(n, motive_lt, hlt, spn, h_n_eq);

    // Le k (pred n).
    let hle = d.lemma(nat_p.le_of_lt_succ, &[k, pn, hlt2]);

    // sub (succ (pred n)) k = succ (sub (pred n) k).
    let h_ss = d.lemma(nat_p.succ_sub_of_le, &[pn, k, hle]);
    let sub_pn_k = d.sub(pn, k);
    let succ_sub_pn_k = d.succ(sub_pn_k);
    let sub_spn_k = d.sub(spn, k);

    // sub n k = sub (succ (pred n)) k, via h_n_eq, then chain with h_ss.
    let h_n_eq_rev = d.symm(n, spn, h_n_eq);
    let h_sub_congr = d.congr(spn, n, h_n_eq_rev, &|d, x| d.sub(x, k));
    // h_sub_congr : Eq (sub spn k) (sub n k)
    let sub_n_k = d.sub(n, k);
    let h_sub_congr_rev = d.symm(sub_spn_k, sub_n_k, h_sub_congr);
    // h_sub_congr_rev : Eq (sub n k) (sub spn k)

    let h_final = d.trans(sub_n_k, sub_spn_k, succ_sub_pn_k, h_sub_congr_rev, h_ss);
    // h_final : Eq (sub n k) (succ (sub pn k))
    (sub_pn_k, h_final)
}

/// `Complex.factorQuotient_succ_eq : ∀ c a n k, Lt k n → Equiv (factorQuotient
/// c a (Nat.succ n) k) (add (factorQuotient c a n k) (mul (pow a (Nat.sub n
/// k)) (c (Nat.succ n))))` — see
/// [`poly::PolyNames::factor_quotient_succ_eq`] for the derivation and why it
/// needs no fresh induction: once `Nat.sub n k` is known to have a successor
/// shape (`nat_sub_pos_succ_shape`), [`poly::PolyNames::horner_from_top_succ_succ`]
/// — an existing `Eq.refl` fact — IS the correction term, verbatim.
fn declare_factor_quotient_succ_eq(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    use crate::BinderInfo;

    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);
    let rec_name = d.prelude().rec;

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let sn = d.succ(n);
    let lt_kn = d.lt(k, n);

    // ----- Nat-side bookkeeping: sub n k = succ j, for some j. -------------
    let (j, h_final) = nat_sub_pos_succ_shape(d, n, k, hlt);
    let sub_nk = d.sub(n, k);
    let succ_j = d.succ(j);

    // Le k n, from Lt k n (le_succ + le_trans, mirroring `diagonal_pointwise_c`).
    let nat_p = d.prelude();
    let sk = d.succ(k);
    let le_succ_k = d.lemma(nat_p.le_succ, &[k]);
    let le_kn = d.lemma(nat_p.le_trans, &[k, sk, n, le_succ_k, hlt]);

    // sub (succ n) k = succ (sub n k).
    let h_outer = d.lemma(nat_p.succ_sub_of_le, &[n, k, le_kn]);
    let sub_snk = d.sub(sn, k);
    let succ_sub_nk = d.succ(sub_nk);

    // sub (succ n) k = succ (succ j).
    let h_final_succ = d.congr(sub_nk, succ_j, h_final, &|d, x| d.succ(x));
    let succ_succ_j = d.succ(succ_j);
    let h_outer2 = d.trans(sub_snk, succ_sub_nk, succ_succ_j, h_outer, h_final_succ);

    // ----- unfold both `factorQuotient`s to `hornerFromTop`. ---------------
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one_level]);

    let step_sn = {
        let rp_fv = d.fresh_fvar();
        let rp = d.kernel().fvar(rp_fv);
        let ih_fv = d.fresh_fvar();
        let horner = d.const_app(p.poly.horner_from_top, &[c, a, sn, rp]);
        let with_ih = d.lam_fv(ih_fv, carrier, horner);
        d.lam_fv(rp_fv, nat, with_ih)
    };
    let step_n = {
        let rp_fv = d.fresh_fvar();
        let rp = d.kernel().fvar(rp_fv);
        let ih_fv = d.fresh_fvar();
        let horner = d.const_app(p.poly.horner_from_top, &[c, a, n, rp]);
        let with_ih = d.lam_fv(ih_fv, carrier, horner);
        d.lam_fv(rp_fv, nat, with_ih)
    };

    let f_outer = |dd: &mut IntDev<'_>, x: ExprId| dd.apply(rec, &[motive, zero_c, step_sn, x]);
    let h_lift_outer = nat_eq_to_complex_equiv(d, p, sub_snk, succ_succ_j, h_outer2, &f_outer);
    // h_lift_outer : Equiv (factorQuotient c a (succ n) k) (hornerFromTop c a
    // (succ n) (succ j)) -- LHS defeq via factorQuotient's own Definition
    // unfold at sub_snk; RHS defeq via ONE Nat.rec ι-step at succ(succ j).

    let f_inner = |dd: &mut IntDev<'_>, x: ExprId| dd.apply(rec, &[motive, zero_c, step_n, x]);
    let h_lift_inner = nat_eq_to_complex_equiv(d, p, sub_nk, succ_j, h_final, &f_inner);
    // h_lift_inner : Equiv (factorQuotient c a n k) (hornerFromTop c a n j)

    // ----- horner_from_top_succ_succ IS the correction term. ---------------
    let horner_sn_sj = d.const_app(p.poly.horner_from_top, &[c, a, sn, succ_j]);
    let horner_n_j = d.const_app(p.poly.horner_from_top, &[c, a, n, j]);
    let c_sn = d.apply(c, &[sn]);
    let pow_a_sj = d.const_app(p.pow, &[a, succ_j]);
    let mul_pow_sj = d.const_app(p.mul, &[pow_a_sj, c_sn]);
    let rhs_succj = d.const_app(p.add, &[horner_n_j, mul_pow_sj]);

    let h_horner_eq = d.lemma(p.poly.horner_from_top_succ_succ, &[c, a, n, j]);
    let h_horner = complex_eq_to_equiv(d, p, horner_sn_sj, rhs_succj, h_horner_eq);

    // ----- rewrite hornerFromTop c a n j back to factorQuotient c a n k. ---
    let fq_n_k = d.const_app(p.poly.factor_quotient, &[c, a, n, k]);
    let h_inner_symm = d.lemma(p.equiv_symm, &[fq_n_k, horner_n_j, h_lift_inner]);
    let refl_mul = d.lemma(p.equiv_refl, &[mul_pow_sj]);
    let h_rewrite_inner = d.lemma(
        p.add_congr,
        &[
            horner_n_j,
            fq_n_k,
            mul_pow_sj,
            mul_pow_sj,
            h_inner_symm,
            refl_mul,
        ],
    );
    let target_succj = d.const_app(p.add, &[fq_n_k, mul_pow_sj]);

    // ----- rewrite `pow a (succ j)` to `pow a (sub n k)`. -------------------
    let pow_a_subnk = d.const_app(p.pow, &[a, sub_nk]);
    let mul_pow_subnk = d.const_app(p.mul, &[pow_a_subnk, c_sn]);
    let target_final = d.const_app(p.add, &[fq_n_k, mul_pow_subnk]);
    let h_final_rev = d.symm(sub_nk, succ_j, h_final);
    let target_f = |dd: &mut IntDev<'_>, x: ExprId| {
        let pow_x = dd.const_app(p.pow, &[a, x]);
        let mul_x = dd.const_app(p.mul, &[pow_x, c_sn]);
        dd.const_app(p.add, &[fq_n_k, mul_x])
    };
    let h_reindex_pow = nat_eq_to_complex_equiv(d, p, succ_j, sub_nk, h_final_rev, &target_f);

    let fq_sn_k = d.const_app(p.poly.factor_quotient, &[c, a, sn, k]);
    let (_e, chain_proof) = zchain(
        d,
        p,
        fq_sn_k,
        &[
            (horner_sn_sj, h_lift_outer),
            (rhs_succj, h_horner),
            (target_succj, h_rewrite_inner),
            (target_final, h_reindex_pow),
        ],
    );

    let stmt_inner = zeq(d, p, fq_sn_k, target_final);
    let ty = {
        let over_hlt = d.pi_fv(hlt_fv, lt_kn, stmt_inner);
        let over_k = d.pi_fv(k_fv, nat, over_hlt);
        let over_n = d.pi_fv(n_fv, nat, over_k);
        let over_a = d.pi_fv(a_fv, carrier, over_n);
        d.pi_fv(c_fv, fn_ty, over_a)
    };
    let value = {
        let with_hlt = d.lam_fv(hlt_fv, lt_kn, chain_proof);
        let over_k = d.lam_fv(k_fv, nat, with_hlt);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        let over_a = d.lam_fv(a_fv, carrier, over_n);
        d.lam_fv(c_fv, fn_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.poly.factor_quotient_succ_eq,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Complex.factorQuotient_degreeLt : ∀ c a n, polyDegreeLt (factorQuotient c
/// a n) n` — for `k` with `Nat.le n k`,
/// [`crate::nat_prelude::NatPrelude::sub_eq_zero_of_le`] gives `Eq Nat (sub n
/// k) zero`; transported through `factorQuotient`'s own `Nat.rec` shape this
/// lands on the forced `zero` base case.
fn declare_factor_quotient_degree_lt(
    d: &mut IntDev<'_>,
    p: ComplexPrelude,
) -> Result<(), KernelError> {
    use crate::BinderInfo;

    let carrier = complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);
    let nat_p = d.prelude();
    let rec_name = d.prelude().rec;

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let zero_n = d.zero();
    let le_nk = d.le(n, k);

    let h_sub = d.lemma(nat_p.sub_eq_zero_of_le, &[n, k, hk]);
    // h_sub : Eq Nat (sub n k) zero

    // Rebuild factorQuotient's own Nat.rec shape (motive/base/step) so the
    // ascribed Equiv below is defeq to `Equiv (factorQuotient c a n k) zero`
    // once `factor_quotient` is δ-unfolded and β-reduced on the other side.
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let step = {
        let rp_fv = d.fresh_fvar();
        let rp = d.kernel().fvar(rp_fv);
        let ih_fv = d.fresh_fvar();
        let horner = d.const_app(p.poly.horner_from_top, &[c, a, n, rp]);
        let with_ih = d.lam_fv(ih_fv, carrier, horner);
        d.lam_fv(rp_fv, nat, with_ih)
    };

    let sub_nk = d.sub(n, k);
    let f = |dd: &mut IntDev<'_>, x: ExprId| dd.apply(rec, &[motive, zero_c, step, x]);
    let h_equiv = nat_eq_to_complex_equiv(d, p, sub_nk, zero_n, h_sub, &f);
    // h_equiv : Equiv (Nat.rec(...)(sub n k)) (Nat.rec(...)(zero))
    //   -- ascribed below against Equiv (factorQuotient c a n k) zero,
    //   -- defeq since factorQuotient's δ-unfold + β reproduces the same
    //   -- Nat.rec application, and Nat.rec(...)(zero) ι-reduces to zero_c.

    let fq = d.const_app(p.poly.factor_quotient, &[c, a, n]);
    let degree_lt_fq = poly_degree_lt_applied(d, p, fq, n);

    let body_k = d.lam_fv(hk_fv, le_nk, h_equiv);

    let value = {
        let over_k = d.lam_fv(k_fv, nat, body_k);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        let over_a = d.lam_fv(a_fv, carrier, over_n);
        d.lam_fv(c_fv, fn_ty, over_a)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, degree_lt_fq);
        let over_a = d.pi_fv(a_fv, carrier, over_n);
        d.pi_fv(c_fv, fn_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.poly.factor_quotient_degree_lt,
        uparams: vec![],
        ty,
        value,
    })
}
