//! Kernel-checked reconstruction of a **monomial lower-bound** refutation.
//!
//! The certificate ([`crate::nra_monomial_bound_cert`]) says: every variable of
//! a monomial `M = ∏ xᵢ^eᵢ` carries a nonnegative lower bound `loᵢ`, so
//! `M ≥ ∏ loᵢ^eᵢ`, which contradicts an asserted `M < k`. This module turns that
//! into a Lean term of type `False` that the trusted kernel type-checks over the
//! ordered-ring signature the enclosing [`LraReconstructCtx`] carries — the
//! **constructed** reals (`CReal`, trusted surface 0) for the shipped route.
//!
//! # Why this is harder than the two refutations beside it
//!
//! [`zero_product`](super::zero_product) and
//! [`product_positivstellensatz`](super::product_positivstellensatz) both close
//! in a fixed number of steps: one `mul_nonneg`, or one equality chain. Neither
//! has to *propagate* a bound. `mul_nonneg` says `0 ≤ a → 0 ≤ b → 0 ≤ a·b`; it
//! says nothing about `lo ≤ x → lo' ≤ y → lo·lo' ≤ x·y`, which is the actual
//! claim here and is false without `0 ≤ lo` — multiplying bounds is monotone
//! only on the nonnegative orthant.
//!
//! The propagation is `mul_le_mul_of_nonneg_left : ∀ c a b, 0 ≤ c → a ≤ b →
//! c·a ≤ c·b`, applied twice per factor, with the running product `P` of bounds
//! and `M` of variables:
//!
//! ```text
//!   h    : P ≤ M          (the invariant)
//!   hp   : 0 ≤ P
//!   hb   : 0 ≤ b          (a numeral, proved from `zero_lt_one`)
//!   hx   : b ≤ x          (the asserted bound, minted)
//!
//!   hm   := le_trans 0 P M hp h                    : 0 ≤ M
//!   s₁   := mul_le_mul_of_nonneg_left M b x hm hx  : M·b ≤ M·x
//!   s₂   := mul_le_mul_of_nonneg_left b P M hb h   : b·P ≤ b·M
//!   s₂'  := s₂ cast by mul_comm on both sides      : P·b ≤ M·b
//!   h'   := le_trans (P·b) (M·b) (M·x) s₂' s₁      : P·b ≤ M·x
//!   hp'  := mul_nonneg P b hp hb                   : 0 ≤ P·b
//! ```
//!
//! The `mul_comm` cast is not avoidable by reassociating: the signature carries
//! monotonicity only in the LEFT argument, and one of the two steps always
//! needs it on the right, whichever way the product nests.
//!
//! Closing then needs `k ≤ ∏ loᵢ` — a comparison between two *numerals*, which
//! an axiomatic carrier does not compute. There are no numerals in the
//! signature, so `n` is built from `one` by repeated addition and `m ≤ n` is a
//! fold of `add_le_add` with `le_of_lt zero_lt_one`, one step per unit. That is
//! linear in the constant, hence [`MAX_NUMERAL`].
//!
//! # Scope, and why each boundary is a decline rather than an approximation
//!
//! - **`MonomialBound::Exactly`** (`M ≠ k` refuted by `M = k`, the `mult.01`
//!   corpus shape) needs the upper bounds too and an equality transport through
//!   the product; declined.
//! - **A non-strict refuted atom** (`M ≤ k`, refuted only by the strictly
//!   stronger `M > k`) needs `lt` between two numerals rather than `le`;
//!   declined. The certificate distinguishes the two atoms
//!   ([`RefutedAtom`](crate::nra_monomial_bound_cert::RefutedAtom)), so this is
//!   a decision and not an oversight.
//! - **An even-exponent factor with no bound at all** (`d²  ≥ 0` for every real
//!   `d`, the `simple-mono-unsat` shape) needs `sq_nonneg` and collapses the
//!   derived bound to `0`; declined.
//! - **More than one non-unit bound** would need `num a · num b = num (a·b)`
//!   proved in the kernel — a numeral multiplication engine, since the carrier
//!   computes nothing. With at most one, the product of bounds collapses to a
//!   single numeral through `mul_one` alone. Declined.
//! - **A bound the query only *entails*.** `simple-mono-unsat` gets `a ≥ 3` from
//!   `(or (= a 4) (= a 3))`. The certificate is right to carry it and its
//!   checker is right to accept it — but this module *mints each bound as a
//!   kernel hypothesis*, and minting `3 ≤ a` would assume a proposition no
//!   assertion states. Recovering it honestly is `Or.rec` case analysis. So
//!   every bound is re-checked against
//!   [`directly_asserted_lower_bounds`](crate::nra_monomial_bound_cert::directly_asserted_lower_bounds)
//!   and a hull-derived one is declined.
//!
//! # What binds the hypotheses to the query
//!
//! More than in the two modules beside it. `h : lo ≤ x` is minted here, but its
//! constant and its strictness are read off an atom the query literally states,
//! not off the certificate — a strict `x > lo` is minted strict and weakened
//! with `le_of_lt`, exactly as
//! [`product_positivstellensatz`](super::product_positivstellensatz) does. The
//! refuted atom `M < k` is still minted from the certificate, and the monomial
//! is written in the certificate's sorted order rather than the query's, so the
//! term is ring-equal to the assertion rather than syntactically it; binding
//! that remains
//! [`check_monomial_bound_refutation`](crate::nra_monomial_bound_cert::check_monomial_bound_refutation)'s
//! job.

use std::collections::BTreeMap;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::ExprId;

use super::{LraReconstructCtx, ReconstructError};
use crate::nra_monomial_bound_cert::{
    MonomialBound, MonomialBoundRefutationCertificate, RefutedAtom, directly_asserted_lower_bounds,
};

/// Largest numeral built from `one` by repeated addition.
///
/// Both the construction (`n` applications of `add`) and the comparison
/// (`n − m` applications of `add_le_add`) are linear in the constant, so this is
/// a real bound and not a style choice. The corpus shape this covers uses `1`.
const MAX_NUMERAL: i128 = 64;

/// `n` as a ring expression, for `0 ≤ n ≤ MAX_NUMERAL`.
///
/// `numeral 0 = zero`, `numeral 1 = one`, and `numeral (j+1) = add (numeral j)
/// one` for `j ≥ 1`. That last identity is what [`le_step`] relies on, so the
/// shape is load-bearing: it is not merely "some expression of the right value".
fn numeral(ctx: &mut LraReconstructCtx, n: i128) -> ExprId {
    debug_assert!((0..=MAX_NUMERAL).contains(&n));
    if n <= 0 {
        return ctx.mk_zero();
    }
    let one = ctx.mk_one();
    let mut acc = one;
    for _ in 1..n {
        acc = ctx.mk_add(acc, one);
    }
    acc
}

/// `le_of_lt 0 1 zero_lt_one : le zero one`.
fn zero_le_one(ctx: &mut LraReconstructCtx) -> ExprId {
    let zero = ctx.mk_zero();
    let one = ctx.mk_one();
    let zlo = {
        let n = ctx.arith().zero_lt_one;
        ctx.kernel.const_(n, vec![])
    };
    let le_of_lt = ctx.arith().le_of_lt;
    ctx.apply_const(le_of_lt, &[zero, one, zlo])
}

/// `le (numeral j) (numeral (j+1))`.
///
/// For `j = 0` that is `le zero one`, which is `zero_lt_one` weakened. For
/// `j ≥ 1` it is `add_le_add j j 0 1 (le_refl j) (0 ≤ 1) : le (j+0) (j+1)` with
/// the left side rewritten by `add_zero`.
fn le_step(ctx: &mut LraReconstructCtx, j: i128) -> ExprId {
    debug_assert!((0..MAX_NUMERAL).contains(&j));
    if j == 0 {
        return zero_le_one(ctx);
    }
    let nj = numeral(ctx, j);
    let zero = ctx.mk_zero();
    let one = ctx.mk_one();
    let refl = {
        let n = ctx.arith().le_refl;
        ctx.apply_const(n, &[nj])
    };
    let h01 = zero_le_one(ctx);
    // `add_le_add : ∀ a b c d, le a b → le c d → le (add a c) (add b d)`.
    let sum = ctx.add_le_add_app(nj, nj, zero, one, refl, h01);
    let nj_zero = ctx.mk_add(nj, zero);
    let nj_one = ctx.mk_add(nj, one);
    // `add_zero (numeral j) : Eq (add (numeral j) zero) (numeral j)`.
    let eq = ctx.add_zero_eq(nj);
    ctx.le_cast_left(nj_zero, nj, nj_one, sum, eq)
}

/// `le (numeral from) (numeral to)`, or `None` when `from > to`.
///
/// The kernel computes nothing on an abstract carrier, so `1 ≤ 4` is not a
/// reduction — it is three `add_le_add` steps chained with `le_trans`.
fn le_numeral(ctx: &mut LraReconstructCtx, from: i128, to: i128) -> Option<ExprId> {
    if !(0..=MAX_NUMERAL).contains(&from) || !(0..=MAX_NUMERAL).contains(&to) || from > to {
        return None;
    }
    let start = numeral(ctx, from);
    let le_refl = ctx.arith().le_refl;
    let mut acc = ctx.apply_const(le_refl, &[start]);
    for j in from..to {
        let step = le_step(ctx, j);
        let nj = numeral(ctx, j);
        let nj1 = numeral(ctx, j + 1);
        let le_trans = ctx.arith().le_trans;
        acc = ctx.apply_const(le_trans, &[start, nj, nj1, acc, step]);
    }
    Some(acc)
}

/// A wire rational that is a nonnegative integer within [`MAX_NUMERAL`].
fn small_nonneg_integer(w: (i128, i128)) -> Option<i128> {
    let value = Rational::checked_new(w.0, w.1)?;
    if value.denominator() != 1 {
        return None;
    }
    let n = value.numerator();
    (0..=MAX_NUMERAL).contains(&n).then_some(n)
}

/// One factor, validated: its variable, its exponent, and its bound.
struct Factor {
    name: String,
    exponent: u32,
    /// The lower bound, a nonnegative integer within [`MAX_NUMERAL`].
    bound: i128,
    /// Whether the query states that bound as a STRICT atom (`x > lo`).
    strict: bool,
}

/// Validate the certificate against this slice's scope and against the query's
/// own atoms, or say which boundary it crosses.
fn validated_factors(
    certificate: &MonomialBoundRefutationCertificate,
    asserted: &BTreeMap<String, (Rational, bool)>,
) -> Result<Vec<Factor>, ReconstructError> {
    // No `is_empty` guard here: a certificate with no factors expands to no
    // occurrences, which the chain builder already refuses with its own message.
    // Two guards for one case means one of them can be deleted with every test
    // still green, which is how a checker rots.
    let carried = certificate.factors();
    let mut out = Vec::with_capacity(carried.len());
    for (name, exponent, lower) in carried {
        // Not deletable, and deliberately so: an unbounded factor is sound only
        // because `x^even ≥ 0`, which needs `sq_nonneg` and collapses the
        // derived bound to zero. Out of this slice.
        let Some(w) = lower else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "factor `{name}` carries no lower bound; an even-exponent wildcard needs \
                     `sq_nonneg` and a derived bound of zero, which this slice does not build"
                ),
            });
        };
        let Some(bound) = small_nonneg_integer(*w).filter(|_| *exponent >= 1) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "factor `{name}` has exponent {exponent} and bound {}/{}; this slice needs a \
                     positive exponent and an integer bound in 0..={MAX_NUMERAL}, because a \
                     numeral is built from `one` by repeated addition",
                    w.0, w.1
                ),
            });
        };
        // The bound is minted as a kernel hypothesis, so it must be an atom the
        // query STATES, not merely one it entails. A disjunction hull is absent
        // from `asserted` for exactly this reason.
        let Some((value, strict)) = asserted.get(name) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "the query states no lower-bound atom for `{name}`; the certificate's bound \
                     comes from a disjunction hull, and minting it would assume a proposition no \
                     assertion carries (it needs `Or.rec` case analysis)"
                ),
            });
        };
        if *value != Rational::integer(bound) {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "the certificate carries `{name} >= {bound}` but the query's own atom is \
                     {}/{}",
                    value.numerator(),
                    value.denominator()
                ),
            });
        }
        out.push(Factor {
            name: name.clone(),
            exponent: *exponent,
            bound,
            strict: *strict,
        });
    }
    Ok(out)
}

/// The running state of the monotone chain.
#[derive(Clone, Copy)]
struct Chain {
    /// `P`, the left-associated product of the bound numerals.
    bounds: ExprId,
    /// `M`, the left-associated product of the variables.
    monomial: ExprId,
    /// `le P M`.
    le: ExprId,
    /// `le zero P`.
    nonneg: ExprId,
    /// `Eq P (numeral value)` — the collapse of the bound product to a numeral.
    collapse: ExprId,
    /// The value of `P`.
    value: i128,
}

/// Extend the chain by one factor occurrence.
///
/// `b` is the bound numeral (value `bound_value`), `x` the variable, `hx : le b x`
/// and `hb : le zero b`.
fn extend(
    ctx: &mut LraReconstructCtx,
    chain: Chain,
    b: ExprId,
    bound_value: i128,
    x: ExprId,
    hx: ExprId,
    hb: ExprId,
) -> Result<Chain, ReconstructError> {
    let Chain {
        bounds: p,
        monomial: m,
        le: h,
        nonneg: hp,
        collapse,
        value,
    } = chain;
    let zero = ctx.mk_zero();

    // `0 ≤ M`, needed to scale by `M` on the left.
    let le_trans = ctx.arith().le_trans;
    let hm = ctx.apply_const(le_trans, &[zero, p, m, hp, h]);

    // `M·b ≤ M·x`.
    let scale = ctx.arith().mul_le_mul_of_nonneg_left;
    let s1 = ctx.apply_const(scale, &[m, b, x, hm, hx]);
    // `b·P ≤ b·M`.
    let s2 = ctx.apply_const(scale, &[b, p, m, hb, h]);

    // Commute both sides of `s2` into `P·b ≤ M·b`. The signature carries
    // monotonicity only in the left argument, so one of the two scalings always
    // lands on the wrong side and has to be turned around.
    let bp = ctx.mk_mul(b, p);
    let pb = ctx.mk_mul(p, b);
    let bm = ctx.mk_mul(b, m);
    let mb = ctx.mk_mul(m, b);
    let eq_bp_pb = ctx.mul_comm_eq(b, p);
    let s2l = ctx.le_cast_left(bp, pb, bm, s2, eq_bp_pb);
    let eq_bm_mb = ctx.mul_comm_eq(b, m);
    let s2r = ctx.le_cast_right(pb, bm, mb, s2l, eq_bm_mb);

    let mx = ctx.mk_mul(m, x);
    let le_trans = ctx.arith().le_trans;
    let le = ctx.apply_const(le_trans, &[pb, mb, mx, s2r, s1]);

    // `0 ≤ P·b`.
    let mul_nonneg = ctx.arith().mul_nonneg;
    let nonneg = ctx.apply_const(mul_nonneg, &[p, b, hp, hb]);

    let (collapse, value) = collapse_to_numeral(ctx, p, pb, collapse, value, b, bound_value)?;

    Ok(Chain {
        bounds: pb,
        monomial: mx,
        le,
        nonneg,
        collapse,
        value,
    })
}

/// Prove `Eq (P·b) (numeral v)` for the new product value `v`, given
/// `collapse : Eq P (numeral value)`.
///
/// `congr_mul_left` carries the accumulated equality under the multiplication;
/// what remains is `numeral value · b`, and an abstract carrier computes
/// nothing, so that reduces only when one side is `zero` or `one`.
fn collapse_to_numeral(
    ctx: &mut LraReconstructCtx,
    p: ExprId,
    pb: ExprId,
    collapse: ExprId,
    value: i128,
    b: ExprId,
    bound_value: i128,
) -> Result<(ExprId, i128), ReconstructError> {
    let t = numeral(ctx, value);
    let congr = ctx.congr_mul_left(p, t, b, collapse);
    let t_b = ctx.mk_mul(t, b);
    if bound_value == 0 {
        // `t · 0 = 0`. Zero absorbs, so this is checked before the unit cases:
        // a bound of 0 is a perfectly ordinary lower bound (it is what a strict
        // `x > 0` contributes) and must not be mistaken for a second non-unit.
        let mul_zero = ctx.mul_zero_eq(t);
        let zero = ctx.mk_zero();
        let eq = ctx.eq_trans_r(pb, t_b, zero, congr, mul_zero);
        Ok((eq, 0))
    } else if value == 0 {
        // `0 · b = 0`, via `mul_comm` then `mul_zero` (`zero_mul` is not a law
        // of the signature — the same detour `zero_product` takes).
        let zero = ctx.mk_zero();
        let b_zero = ctx.mk_mul(b, zero);
        let comm = ctx.mul_comm_eq(t, b);
        let mul_zero = ctx.mul_zero_eq(b);
        let zero_mul = ctx.eq_trans_r(t_b, b_zero, zero, comm, mul_zero);
        let eq = ctx.eq_trans_r(pb, t_b, zero, congr, zero_mul);
        Ok((eq, 0))
    } else if bound_value == 1 {
        // `t · 1 = t`.
        let mul_one = ctx.mul_one_eq(t);
        let eq = ctx.eq_trans_r(pb, t_b, t, congr, mul_one);
        Ok((eq, value))
    } else if value == 1 {
        // `1 · b = b`, via `mul_comm` then `mul_one` (`one_mul` is not a law of
        // the signature — the same detour `zero_product` takes for `zero_mul`).
        let one = ctx.mk_one();
        let b_one = ctx.mk_mul(b, one);
        let comm = ctx.mul_comm_eq(t, b);
        let mul_one = ctx.mul_one_eq(b);
        let one_mul = ctx.eq_trans_r(t_b, b_one, b, comm, mul_one);
        let eq = ctx.eq_trans_r(pb, t_b, b, congr, one_mul);
        Ok((eq, bound_value))
    } else {
        Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "two non-unit lower bounds ({value} and {bound_value}) would need \
                 `numeral a * numeral b = numeral (a*b)` proved in the kernel — a numeral \
                 multiplication engine, since an abstract carrier computes nothing. This slice \
                 collapses the bound product through `mul_one` alone, so it takes at most one"
            ),
        })
    }
}

/// Fold the validated factors into `P ≤ M` with `P` collapsed to a numeral.
///
/// Each factor's bound is minted once and reused across its occurrences, so a
/// repeated variable assumes its bound once rather than `exponent` times.
fn build_chain(ctx: &mut LraReconstructCtx, factors: &[Factor]) -> Result<Chain, ReconstructError> {
    // A stable opaque `R`-constant per NAME, assigned in the certificate's
    // order, which is sorted — so the emitted module is deterministic.
    let mut index_of: BTreeMap<String, usize> = BTreeMap::new();
    let mut chain: Option<Chain> = None;

    for factor in factors {
        let next = index_of.len();
        let idx = *index_of.entry(factor.name.clone()).or_insert(next);
        let var_name = ctx.var_const(idx);
        let x = ctx.kernel.const_(var_name, vec![]);
        let b = numeral(ctx, factor.bound);

        // The hypothesis, minted at the strictness the QUERY states. A strict
        // `x > lo` is assumed strict and weakened, so the assumed proposition is
        // the asserted one and the weakening is an explicit kernel step.
        let hx = if factor.strict {
            let prop = ctx.mk_lt(b, x);
            let strict = ctx.hyp_axiom(prop)?;
            ctx.le_of_lt_app(b, x, strict)
        } else {
            let prop = ctx.mk_le(b, x);
            ctx.hyp_axiom(prop)?
        };
        let Some(hb) = le_numeral(ctx, 0, factor.bound) else {
            return Err(ReconstructError::UnsupportedTerm {
                term: format!(
                    "cannot prove `0 <= {}` within the numeral bound",
                    factor.bound
                ),
            });
        };

        for _ in 0..factor.exponent {
            chain = Some(match chain.take() {
                None => {
                    let collapse = ctx.eq_refl_r(b);
                    Chain {
                        bounds: b,
                        monomial: x,
                        le: hx,
                        nonneg: hb,
                        collapse,
                        value: factor.bound,
                    }
                }
                Some(previous) => extend(ctx, previous, b, factor.bound, x, hx, hb)?,
            });
        }
    }

    chain.ok_or_else(|| ReconstructError::UnsupportedTerm {
        term: "monomial-bound certificate expands to no factor occurrences".to_owned(),
    })
}

/// Reconstruct the monomial lower-bound refutation to `False`.
///
/// Takes the query as well as the certificate: each bound is minted as a kernel
/// hypothesis, so it has to be checked against an atom the query states rather
/// than taken from the certificate on trust (see the module docs).
///
/// # Errors
///
/// [`ReconstructError::UnsupportedTerm`] at any of this slice's boundaries — an
/// `Exactly` bound, a non-strict refuted atom, an unbounded factor, a bound or
/// constant outside `0..=MAX_NUMERAL`, more than one non-unit bound, or a bound
/// the query only entails; [`ReconstructError::KernelRejected`] if the assembled
/// term does not infer to `False`.
pub(crate) fn reconstruct_monomial_bound(
    ctx: &mut LraReconstructCtx,
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &MonomialBoundRefutationCertificate,
) -> Result<ExprId, ReconstructError> {
    let MonomialBound::AtLeast(claimed_wire) = certificate.bound() else {
        return Err(ReconstructError::UnsupportedTerm {
            term: "an `Exactly` bound refutes `M != k` and needs the upper bounds plus an \
                   equality transport through the product; this slice reconstructs the \
                   lower-bound form only"
                .to_owned(),
        });
    };
    if certificate.refuted_kind() != RefutedAtom::LessThan {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "refuted atom is {:?}; closing a non-strict `M <= k` needs a STRICT numeral \
                 comparison `k < bound` rather than the `le` fold this slice builds",
                certificate.refuted_kind()
            ),
        });
    }
    let Some(k) = small_nonneg_integer(certificate.refuted_against()) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "the refuted constant {}/{} is not an integer in 0..={MAX_NUMERAL}; numerals here \
                 are built from `one` by repeated addition and have no negative form",
                certificate.refuted_against().0,
                certificate.refuted_against().1
            ),
        });
    };

    let asserted = directly_asserted_lower_bounds(arena, assertions);
    let factors = validated_factors(certificate, &asserted)?;

    let chain = build_chain(ctx, &factors)?;

    // Re-derive the claimed bound rather than trusting it: a reconstruction that
    // took the certificate's number on faith would be reconstructing a claim
    // rather than checking one.
    let claimed = small_nonneg_integer(claimed_wire);
    if claimed != Some(chain.value) {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "the certificate claims the factors multiply to {}/{}, but they multiply to {}",
                claimed_wire.0, claimed_wire.1, chain.value
            ),
        });
    }

    // `numeral value ≤ M`, from `P ≤ M` and `Eq P (numeral value)`.
    let bound_numeral = numeral(ctx, chain.value);
    let le_bound_m = ctx.le_cast_left(
        chain.bounds,
        bound_numeral,
        chain.monomial,
        chain.le,
        chain.collapse,
    );

    // `k ≤ numeral value`. A certificate that refutes `M < k` with a bound below
    // `k` refutes nothing.
    let Some(k_le_bound) = le_numeral(ctx, k, chain.value) else {
        return Err(ReconstructError::UnsupportedTerm {
            term: format!(
                "the derived bound {} does not reach the refuted constant {k}, so `M >= {} ` \
                 contradicts nothing about `M < {k}`",
                chain.value, chain.value
            ),
        });
    };

    let k_expr = numeral(ctx, k);
    let le_trans = ctx.arith().le_trans;
    let k_le_m = ctx.apply_const(
        le_trans,
        &[
            k_expr,
            bound_numeral,
            chain.monomial,
            k_le_bound,
            le_bound_m,
        ],
    );

    // The refuted atom, minted: `M < k`.
    let lt_m_k = ctx.mk_lt(chain.monomial, k_expr);
    let h_lt = ctx.hyp_axiom(lt_m_k)?;
    // `lt_of_le_of_lt : ∀ a b c, le a b → lt b c → lt a c`.
    let lt_of_le_of_lt = ctx.arith().lt_of_le_of_lt;
    let absurd = ctx.apply_const(
        lt_of_le_of_lt,
        &[k_expr, chain.monomial, k_expr, k_le_m, h_lt],
    );
    // `lt_irrefl : ∀ a, Not (lt a a)`; `Not P` is `P → False`.
    let lt_irrefl = ctx.arith().lt_irrefl;
    let irrefl = ctx.apply_const(lt_irrefl, &[k_expr]);
    let proof = ctx.kernel.app(irrefl, absurd);

    require_infers_false(ctx, proof)
}

/// The soundness gate: the assembled term must kernel-`infer` to `False`.
///
/// A named function rather than a tail block so it can be aimed at a term that
/// is *not* a refutation. Inline, the gate was unfalsifiable: every fixture that
/// reaches it is correct by construction, so deleting it left every test green —
/// which is exactly the shape of checker this repository keeps finding.
fn require_infers_false(
    ctx: &mut LraReconstructCtx,
    proof: ExprId,
) -> Result<ExprId, ReconstructError> {
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "monomial_bound".to_owned(),
            detail: format!("monomial-bound refutation infer failed: {e:?}"),
        })?;
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    if ctx.kernel_mut().def_eq(inferred, false_) {
        Ok(proof)
    } else {
        Err(ReconstructError::KernelRejected {
            rule: "monomial_bound".to_owned(),
            detail: "monomial-bound refutation did not infer to False".to_owned(),
        })
    }
}

#[cfg(test)]
mod tests {
    //! The only claim that matters is that the trusted kernel infers the
    //! assembled term to `False` over the CONSTRUCTED reals. Everything else is
    //! a boundary, and every boundary below is a decline with a fixture.

    use super::*;
    use crate::nra_monomial_bound_cert::monomial_bound_refutation;
    use axeyum_smtlib::parse_script;

    /// `cli__regress1__nl__ones.smt2`: `a,b,c,d >= 1` and `a*b*c*d < 1`.
    const ONES: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)(declare-fun b () Real)\n\
        (declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (>= a 1))(assert (>= b 1))(assert (>= c 1))(assert (>= d 1))\n\
        (assert (or (= a 1) (= b 1) (= c 1) (= d 1)))\n\
        (assert (< (* a b c d) 1))\n(check-sat)";

    /// One non-unit bound, a repeated variable, and a STRICT bound atom — the
    /// three things `ONES` does not exercise. `a > 0`, `b >= 3`, `a*a*b < 0`.
    const STRICT_AND_REPEATED: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (> a 0))(assert (>= b 3))\n\
        (assert (< (* a a b) 0))\n(check-sat)";

    /// `cli__regress0__arith__mult.01.smt2`: the `Exactly` shape.
    const MULT01: &str = "(set-logic QF_NRA)\n(declare-fun n () Real)(declare-fun x () Real)\n\
        (assert (>= n 1))(assert (<= n 1))(assert (<= x 1))(assert (>= x 1))\n\
        (assert (not (= (* x n) 1)))\n(check-sat)";

    /// `cli__regress1__nl__simple-mono-unsat.smt2`: `d` has an even exponent and
    /// no bound at all.
    const SIMPLE_MONO: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)(declare-fun b () Real)\n\
        (declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (or (= a 4) (= a 3)))(assert (> b 0))(assert (> c 0))\n\
        (assert (< (* a b c d d) 0))\n(check-sat)";

    /// `simple-mono-unsat` with the disjunction replaced by a stated bound, so
    /// the even-exponent wildcard (`d`, unbounded) is the FIRST boundary the
    /// reconstruction meets rather than the second.
    const EVEN_WILDCARD: &str = "(set-logic QF_NRA)\n\
        (declare-fun b () Real)(declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (> b 0))(assert (> c 0))\n\
        (assert (< (* b c d d) 0))\n(check-sat)";

    /// A NON-STRICT refuted atom: `a >= 2`, `b >= 2`, `a*b <= 3`. Genuinely
    /// unsat (`4 > 3`), and the producer certifies it — but closing it needs
    /// `3 < 4` strictly, not `3 <= 4`.
    const AT_MOST: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a 2))(assert (>= b 2))\n\
        (assert (<= (* a b) 3))\n(check-sat)";

    /// A NEGATIVE refuted constant: `a,b >= 1`, `a*b < -1`.
    const NEGATIVE_CONSTANT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a 1))(assert (>= b 1))\n\
        (assert (< (* a b) (- 1)))\n(check-sat)";

    /// A bound past `MAX_NUMERAL`: `a >= 1000`, `b >= 1`, `a*b < 1`.
    const HUGE_BOUND: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a 1000))(assert (>= b 1))\n\
        (assert (< (* a b) 1))\n(check-sat)";

    /// TWO non-unit bounds: `a >= 2`, `b >= 3`, `a*b < 6`.
    const TWO_NON_UNIT: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (>= a 2))(assert (>= b 3))\n\
        (assert (< (* a b) 6))\n(check-sat)";

    /// A bound the query only ENTAILS: `a`'s `>= 3` comes from a disjunction.
    /// `(or (= a 4) (= a 3))`, `b >= 1`, `a*b < 3`.
    const HULL_BOUND: &str = "(set-logic QF_NRA)\n\
        (declare-fun a () Real)(declare-fun b () Real)\n\
        (assert (or (= a 4) (= a 3)))(assert (>= b 1))\n\
        (assert (< (* a b) 3))\n(check-sat)";

    fn query(text: &str) -> (axeyum_ir::TermArena, Vec<TermId>) {
        let p = parse_script(text).expect("parses");
        (p.arena, p.assertions)
    }

    fn certificate(text: &str) -> MonomialBoundRefutationCertificate {
        let (arena, assertions) = query(text);
        monomial_bound_refutation(&arena, &assertions).expect("certificate")
    }

    /// Assert a decline, and assert it is the decline we meant.
    ///
    /// `matches!(.., UnsupportedTerm { .. })` alone was not enough: four of this
    /// module's guards sit behind another guard that rejects the same fixture,
    /// so deleting any one of them left every test green. Naming the reason is
    /// what makes each guard's test die when that guard goes.
    fn declines(result: &Result<ExprId, ReconstructError>, because: &str) {
        match result {
            Err(ReconstructError::UnsupportedTerm { term }) => assert!(
                term.contains(because),
                "declined for the wrong reason: wanted {because:?}, got {term:?}"
            ),
            other => panic!("expected a decline mentioning {because:?}, got {other:?}"),
        }
    }

    fn refutes(text: &str) -> Result<ExprId, ReconstructError> {
        let (arena, assertions) = query(text);
        let cert = monomial_bound_refutation(&arena, &assertions).expect("certificate");
        let mut ctx = LraReconstructCtx::new();
        reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &cert)
    }

    /// **The measurement that decides whether any of this is worth having.**
    ///
    /// `LraReconstructCtx::new()` builds `AxReal` — the legacy AXIOMATIZED
    /// ordered field, 30 assumptions, this repository's only nonzero
    /// trusted-surface row. A refutation checked there rests on all 30.
    /// `CReal` (ADR-0512) is a Bishop setoid over the constructed rationals at
    /// trusted surface **0**, and the shipped route's `lra_ctx()` builds it.
    ///
    /// So this asserts the refutation kernel-checks over the CONSTRUCTED reals
    /// by name. Without it the module would be a 30-axiom proof wearing the same
    /// test name.
    #[test]
    fn the_refutation_kernel_checks_over_the_constructed_reals() {
        for text in [ONES, STRICT_AND_REPEATED] {
            let (arena, assertions) = query(text);
            let cert = monomial_bound_refutation(&arena, &assertions).expect("certificate");
            let (mut ctx, _adoption) =
                LraReconstructCtx::try_new_over_constructed_reals_reporting()
                    .expect("the constructed real development builds");
            let proof = reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &cert)
                .expect("reconstruction succeeds over CReal");
            let inferred = ctx.kernel_mut().infer(proof).expect("infer");
            let false_ = {
                let f = ctx.arith().logic.false_;
                ctx.kernel_mut().const_(f, vec![])
            };
            assert!(
                ctx.kernel_mut().def_eq(inferred, false_),
                "the term must infer to False over CReal, not only over AxReal"
            );
        }
    }

    #[test]
    fn the_kernel_infers_the_refutation_to_false() {
        // `reconstruct_monomial_bound` gates on this internally; assert it again
        // from outside so the gate cannot be deleted silently.
        let (arena, assertions) = query(ONES);
        let cert = monomial_bound_refutation(&arena, &assertions).expect("certificate");
        let mut ctx = LraReconstructCtx::new();
        let proof =
            reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &cert).expect("reconstructs");
        let inferred = ctx.kernel_mut().infer(proof).expect("infer");
        let false_ = {
            let f = ctx.arith().logic.false_;
            ctx.kernel_mut().const_(f, vec![])
        };
        assert!(ctx.kernel_mut().def_eq(inferred, false_));
    }

    #[test]
    fn a_strict_bound_atom_and_a_repeated_variable_also_close() {
        // `a > 0` is minted STRICT and weakened, `a` occurs twice, and `b`'s
        // bound is 3 rather than 1 — none of which `ONES` reaches.
        assert!(refutes(STRICT_AND_REPEATED).is_ok());
    }

    #[test]
    fn the_exactly_shape_is_declined_not_approximated() {
        declines(&refutes(MULT01), "`Exactly` bound");
    }

    #[test]
    fn a_non_strict_refuted_atom_is_declined() {
        assert_eq!(
            certificate(AT_MOST).refuted_kind(),
            RefutedAtom::AtMost,
            "fixture must actually produce the non-strict atom"
        );
        declines(&refutes(AT_MOST), "STRICT numeral comparison");
    }

    #[test]
    fn a_negative_refuted_constant_is_declined() {
        declines(&refutes(NEGATIVE_CONSTANT), "is not an integer in 0..=");
    }

    #[test]
    fn an_unbounded_even_exponent_factor_is_declined() {
        // `simple-mono-unsat` itself declines one guard EARLIER, at `a`'s
        // disjunction hull, so it cannot exercise this one. Same shape with
        // every remaining bound stated directly.
        declines(&refutes(EVEN_WILDCARD), "carries no lower bound");
    }

    #[test]
    fn the_simple_mono_corpus_shape_is_declined() {
        // Two independent reasons, and the module declines on the first it
        // meets: `a >= 3` comes from `(or (= a 4) (= a 3))`, and `d` has no
        // bound at all. Pinned as a SHAPE, not as a guard — deliberately not
        // asserting which of the two fired, since either is a correct decline.
        let result = refutes(SIMPLE_MONO);
        assert!(
            matches!(result, Err(ReconstructError::UnsupportedTerm { .. })),
            "got {result:?}"
        );
    }

    #[test]
    fn a_malformed_or_out_of_range_factor_is_declined() {
        // Three ways past the per-factor validation, all one guard: a bound
        // larger than the numeral fold can build, a zero exponent, and no
        // factors at all.
        // A bound of 1000 is far past the fold.
        declines(
            &refutes(HUGE_BOUND),
            "positive exponent and an integer bound",
        );

        let (arena, assertions) = query(ONES);
        // A zero exponent alongside a real one, so the empty-monomial check
        // cannot be what rejects it.
        let zero_exponent = MonomialBoundRefutationCertificate::testing_from_parts(
            vec![
                ("a".to_owned(), 0, Some((1, 1))),
                ("b".to_owned(), 1, Some((1, 1))),
            ],
            Vec::new(),
            MonomialBound::AtLeast((1, 1)),
            (1, 1),
            RefutedAtom::LessThan,
        );
        let mut ctx = LraReconstructCtx::new();
        declines(
            &reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &zero_exponent),
            "positive exponent and an integer bound",
        );

        let empty = MonomialBoundRefutationCertificate::testing_from_parts(
            Vec::new(),
            Vec::new(),
            MonomialBound::AtLeast((1, 1)),
            (1, 1),
            RefutedAtom::LessThan,
        );
        let mut ctx = LraReconstructCtx::new();
        declines(
            &reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &empty),
            "no factor occurrences",
        );
    }

    #[test]
    fn two_non_unit_bounds_are_declined() {
        // 2 * 3 = 6 is numeral multiplication the kernel cannot compute.
        declines(&refutes(TWO_NON_UNIT), "two non-unit lower bounds");
    }

    #[test]
    fn a_bound_the_query_only_entails_is_declined() {
        // The certificate is genuine and its own checker accepts it: `a >= 3`
        // really does follow from `(or (= a 4) (= a 3))`. But this module MINTS
        // the bound as a hypothesis, and `3 <= a` is not an assertion of this
        // query — recovering it needs `Or.rec`.
        assert!(
            monomial_bound_refutation(&query(HULL_BOUND).0, &query(HULL_BOUND).1).is_some(),
            "fixture must produce a certificate, or this tests nothing"
        );
        declines(&refutes(HULL_BOUND), "disjunction hull");
    }

    #[test]
    fn a_bound_tighter_than_the_query_states_is_declined() {
        // The certificate's carried bound must be the query's own atom, not a
        // tighter one. `ONES` states `a >= 1`; this claims `a >= 2`.
        let (arena, assertions) = query(ONES);
        let forged = MonomialBoundRefutationCertificate::testing_from_parts(
            vec![
                ("a".to_owned(), 1, Some((2, 1))),
                ("b".to_owned(), 1, Some((1, 1))),
                ("c".to_owned(), 1, Some((1, 1))),
                ("d".to_owned(), 1, Some((1, 1))),
            ],
            Vec::new(),
            MonomialBound::AtLeast((2, 1)),
            (1, 1),
            RefutedAtom::LessThan,
        );
        let mut ctx = LraReconstructCtx::new();
        declines(
            &reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &forged),
            "the query's own atom",
        );
    }

    #[test]
    fn a_claimed_bound_the_factors_do_not_multiply_to_is_refused() {
        // Defensive: the certificate's own checker rejects this, so it should
        // never reach here — but a reconstruction that TRUSTED the number would
        // be reconstructing a claim rather than checking one.
        let (arena, assertions) = query(ONES);
        let forged = MonomialBoundRefutationCertificate::testing_from_parts(
            certificate(ONES).factors().to_vec(),
            Vec::new(),
            MonomialBound::AtLeast((7, 1)),
            (1, 1),
            RefutedAtom::LessThan,
        );
        let mut ctx = LraReconstructCtx::new();
        declines(
            &reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &forged),
            "but they multiply to",
        );
    }

    #[test]
    fn a_bound_that_does_not_reach_the_refuted_constant_is_refused() {
        // `1 * 1 * 1 * 1 = 1` does not refute `M < 5`. The certificate's checker
        // rejects it at `claimed >= against`; this is the reconstruction's own
        // re-derivation of the same fact, which is what makes the numeral fold
        // total.
        let (arena, assertions) = query(ONES);
        let forged = MonomialBoundRefutationCertificate::testing_from_parts(
            certificate(ONES).factors().to_vec(),
            Vec::new(),
            MonomialBound::AtLeast((1, 1)),
            (5, 1),
            RefutedAtom::LessThan,
        );
        let mut ctx = LraReconstructCtx::new();
        declines(
            &reconstruct_monomial_bound(&mut ctx, &arena, &assertions, &forged),
            "does not reach the refuted constant",
        );
    }

    #[test]
    fn the_soundness_gate_refuses_a_term_that_is_not_a_proof_of_false() {
        // Without a fixture the gate is unfalsifiable: everything that reaches
        // it is correct by construction. `Eq.refl zero` is a perfectly
        // well-typed term whose type is not `False`, which is precisely the
        // thing a reconstruction must never return as a refutation.
        let mut ctx = LraReconstructCtx::new();
        let zero = ctx.mk_zero();
        let not_a_refutation = ctx.eq_refl_r(zero);
        assert!(matches!(
            require_infers_false(&mut ctx, not_a_refutation),
            Err(ReconstructError::KernelRejected { .. })
        ));
    }

    #[test]
    fn the_numeral_fold_is_total_exactly_where_it_claims_to_be() {
        let mut ctx = LraReconstructCtx::new();
        assert!(le_numeral(&mut ctx, 0, 0).is_some());
        assert!(le_numeral(&mut ctx, 0, 1).is_some());
        assert!(le_numeral(&mut ctx, 3, MAX_NUMERAL).is_some());
        // Downward is not a fold, it is a falsehood.
        assert!(le_numeral(&mut ctx, 2, 1).is_none());
        // Past the bound the term would be proportional to the constant.
        assert!(le_numeral(&mut ctx, 0, MAX_NUMERAL + 1).is_none());
        assert!(le_numeral(&mut ctx, -1, 1).is_none());
    }

    #[test]
    fn the_numeral_ladder_type_checks_at_every_rung() {
        // `le_step`'s shape depends on `numeral (j+1) = add (numeral j) one`,
        // which is an invariant of `numeral` rather than of the kernel. If it
        // ever stops holding the fold silently builds the wrong proposition, so
        // check the inferred type at a spread of rungs.
        let mut ctx = LraReconstructCtx::new();
        for (from, to) in [(0_i128, 1_i128), (0, 5), (1, 2), (2, 7), (7, 7)] {
            let proof = le_numeral(&mut ctx, from, to).expect("in range");
            let inferred = ctx.kernel_mut().infer(proof).expect("infer");
            let a = numeral(&mut ctx, from);
            let b = numeral(&mut ctx, to);
            let expected = ctx.mk_le(a, b);
            assert!(
                ctx.kernel_mut().def_eq(inferred, expected),
                "le_numeral({from}, {to}) did not prove `le {from} {to}`"
            );
        }
    }
}

#[cfg(test)]
mod end_to_end {
    //! The route as a caller sees it: query in, Lean module out.

    use crate::reconstruct::{ProofFragment, scan_proof_fragment};
    use axeyum_smtlib::parse_script;

    const ONES: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)(declare-fun b () Real)\n\
        (declare-fun c () Real)(declare-fun d () Real)\n\
        (assert (>= a 1))(assert (>= b 1))(assert (>= c 1))(assert (>= d 1))\n\
        (assert (or (= a 1) (= b 1) (= c 1) (= d 1)))\n\
        (assert (< (* a b c d) 1))\n(check-sat)";

    #[test]
    fn the_query_classifies_as_a_theory_reconstruction_not_an_attestation() {
        let p = parse_script(ONES).expect("parses");
        assert_eq!(
            scan_proof_fragment(&p.arena, &p.assertions),
            ProofFragment::MonomialBound,
            "must not fall through to the NraEvenPower attestation tier"
        );
    }

    #[test]
    fn the_front_door_emits_a_kernel_checked_lean_module() {
        let mut p = parse_script(ONES).expect("parses");
        let assertions = p.assertions.clone();
        let (fragment, module) =
            crate::reconstruct::prove_unsat_to_lean_module(&mut p.arena, &assertions)
                .expect("a Lean module is produced");
        assert_eq!(fragment, ProofFragment::MonomialBound);
        assert!(!module.is_empty());
        // The module must carry THIS refutation's monotone chaining, not a
        // generic wrapper asserting the conclusion.
        assert!(
            module.contains("mul_le_mul_of_nonneg_left"),
            "the module should contain the bound propagation; got:\n{module}"
        );
    }
}
