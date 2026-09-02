//! **`CReal.hasDerivative_unique`** (Spivak ch. 10): the derivative of a
//! function on `[a,b]` is unique — *given* the interval is genuinely
//! nondegenerate (`CReal.lt a b`).
//!
//! ## The refutation this file's statement is built to survive
//!
//! The naive statement — `HasDerivativeOn F F1 a b → HasDerivativeOn F F2 a
//! b → ∀ z, le a z → le z b → Equiv (F1 z) (F2 z)`, with NO nondegeneracy
//! hypothesis — is **not a theorem**. `hd_spec`'s closeness hypothesis
//! (`within_real (y−x) bound`) is an *upper-bound* requirement, not a
//! tolerance equality, so at a degenerate interval `a = b` it is vacuously
//! satisfiable at `x = y = a`: `F := id`, `a = b = zero`, and BOTH `const
//! zero` and `const one` satisfy `HasDerivativeOn id · zero zero`, yet
//! `Equiv zero one` is false. The fix is exactly the nondegeneracy
//! hypothesis `CReal.lt a b` this file's statement carries — see
//! `derivative.rs`'s own module documentation (the "Uniqueness of the
//! derivative" bullet) for where this was first scouted.
//!
//! ## The route
//!
//! Fix an arbitrary outer accuracy `e' : Nat` and reindex to `e := shift e'
//! = 2·e'+1` (`creal.rs`'s own Bishop shift), so that `natDivSucc 1 e +
//! natDivSucc 1 e = natDivSucc 1 e'` **exactly** (`Rat.natDivSucc_add` then
//! `Rat.natDivSucc_halve`, no weakening step — unlike
//! `archimedean_squeeze.rs`'s own `1/(2j+2)` case, which needs one because
//! *half* of `1/(j+1)` is not a whole multiple of it; here the two summands
//! are *equal*, so `_halve` applies with no slack to spend).
//!
//! [`CRealPrelude::lt_cotrans`] applied to `lt a b` at `z` gives `Or (lt a
//! z) (lt z b)` — a genuine disjunction, usable **without deciding where
//! `z` sits**. Whichever holds hands over an exact rational gap `q0 > 0`
//! (`a + q0 ≤ z`, respectively `z + q0 ≤ b`). Combined with the two moduli
//! `HasDerivativeOn F F1 a b` and `HasDerivativeOn F F2 a b` supply at
//! accuracy `e` (`m1 := mod1 e`, `m2 := mod2 e`, combined exactly as
//! `derivative.rs`'s own sum rule combines two independent moduli: `k :=
//! m1+m2`, `Rat.natDivSucc_antitone` weakens each of `mod1`'s and `mod2`'s
//! own bound down to the shared `natDivSucc 1 k`), a `Rat.le_or_lt` case
//! split (decidable — only `CReal.le` is undecidable, never `Rat.le`) picks
//! `q := min(q0, natDivSucc 1 k)`, and the constructed neighbour `y := z ∓
//! q` (embedded exactly, not merely bounded) stays in `[a,b]` **by
//! construction** and satisfies both `hd_spec` hypotheses at accuracy `e`.
//!
//! Instantiating both specs at `(z, y)`, subtracting, and factoring the
//! shared `(y−z)` out via `right_distrib`/`neg_mul_equiv_left` (the
//! difference of the two error terms is *exactly* `(F2 z − F1 z)·(y−z)`, a
//! pure ring identity independent of which branch produced `y`) gives
//! `|(F1 z − F2 z)·(y−z)| ≤ (2/(e+1))·q`. Since `q` is a **known exact
//! positive rational**, `CReal.le_of_mul_le_mul_left` (fed a `PosBound
//! (ofRat q) k2` obtained from `CReal.pos_bound_of_lt`, eliminated into the
//! same Prop goal every step here targets) cancels it, landing exactly on
//! `le (abs (F1 z − F2 z)) (ofRat (natDivSucc 1 e'))` — the goal
//! `CReal.equiv_zero_of_small` (`archimedean_squeeze.rs`) needs at the
//! OUTER accuracy `e'`, for every `e'` in one uniform construction.
//!
//! ## The nearby-point construction
//!
//! `derivative.rs`'s own module documentation named the missing piece
//! precisely: "a witness `y != x` inside `[a,b]` arbitrarily close to `x`,
//! chosen WITHOUT deciding `x`'s position relative to `a`/`b`". The
//! `lt_cotrans` split above **is** that construction, comparable in scope
//! to `monotone.rs`'s own subdivision construction for
//! `monotone_of_nonneg_deriv`: it is reusable for the IVT, for the
//! integral, and for anything else needing an interior point built without
//! a sign decision.
//!
//! ## Degeneracy is not papered over
//!
//! `lt a b` is a genuine hypothesis, not a restatement of `le a b`: at `a =
//! b` (or any `a ~ b`) it is unprovable (its witness needs an EXACT
//! positive rational gap), matching the refutation exactly — this
//! statement says nothing, and is not expected to say anything, about that
//! case.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::ring_helpers::{add4_comm, right_distrib};
use super::{CRealPrelude, cadd, cle, clt, creal_ty, div_succ, embed, gap_elim, gap_halves, shift};
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_ty, rchain, rle, rlt};

/// Admit `CReal.hasDerivative_unique`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_deriv_unique(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_has_derivative_unique(d, p)
}

// --- shared term builders (private copies; see the sibling modules' own
// identical disclaimers for why these are rebuilt here rather than shared:
// each is private to the module that first needed it) -----------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add x (neg y)` — `x - y`.
fn cdiff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    cadd(d, p, x, ny)
}

fn pos_bound(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h_ab_zero : Equiv (add a b) zero`, derive `Equiv b (neg a)` — `b` is
/// the unique additive inverse of `a`. Purely group-theoretic:
/// `b ~ 0+b ~ (-a+a)+b ~ -a+(a+b) ~ -a+0 ~ -a`. Copied verbatim from
/// `derivative.rs`'s private helper of the same shape.
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (neg (neg x)) x` — double negation, from [`neg_unique`] applied to
/// [`neg_add_self`].
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`. Copied verbatim from
/// `derivative.rs`'s private helper of the same shape.
fn neg_add_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let ab = cadd(d, p, a, b);
    let na_nb = cadd(d, p, na, nb);
    let b_na = cadd(d, p, b, na);
    let na_b = cadd(d, p, na, b);
    let b_nanb = cadd(d, p, b, na_nb);
    let b_na_nb = cadd(d, p, b_na, nb);
    let na_b_nb = cadd(d, p, na_b, nb);
    let b_nb = cadd(d, p, b, nb);
    let na_bnb = cadd(d, p, na, b_nb);
    let na_zero = cadd(d, p, na, zero_c);
    let ab_nanb = cadd(d, p, ab, na_nb);
    let a_bnanb = cadd(d, p, a, b_nanb);
    let a_na = cadd(d, p, a, na);
    let neg_ab = cneg(d, p, ab);

    let step2 = d.lemma(p.add_assoc, &[b, na, nb]);
    let step2_symm = esymm(d, p, b_na_nb, b_nanb, step2);

    let step3 = d.lemma(p.add_comm, &[b, na]);
    let refl_nb = erefl(d, p, nb);
    let step4 = d.lemma(p.add_congr, &[b_na, na_b, nb, nb, step3, refl_nb]);

    let step5 = d.lemma(p.add_assoc, &[na, b, nb]);

    let step6 = d.lemma(p.add_neg, &[b]);
    let refl_na = erefl(d, p, na);
    let step7 = d.lemma(p.add_congr, &[na, na, b_nb, zero_c, refl_na, step6]);

    let step8 = d.lemma(p.add_zero, &[na]);

    let middle_result = echain(
        d,
        p,
        b_nanb,
        &[
            (b_na_nb, step2_symm),
            (na_b_nb, step4),
            (na_bnb, step5),
            (na_zero, step7),
            (na, step8),
        ],
    );

    let refl_a = erefl(d, p, a);
    let step9 = d.lemma(p.add_congr, &[a, a, b_nanb, na, refl_a, middle_result]);
    let step10 = d.lemma(p.add_neg, &[a]);

    let step1 = d.lemma(p.add_assoc, &[a, b, na_nb]);

    let h = echain(
        d,
        p,
        ab_nanb,
        &[(a_bnanb, step1), (a_na, step9), (zero_c, step10)],
    );

    let nu = neg_unique(d, p, ab, na_nb, h);
    esymm(d, p, na_nb, neg_ab, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`. Copied verbatim from
/// `derivative.rs`'s private helper of the same shape.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// `Equiv (mul (neg a) b) (neg (mul a b))` — the mirror of [`mul_neg_equiv`]
/// (which negates the *second* factor). Copied verbatim from
/// `derivative.rs`'s private helper of the same shape.
fn neg_mul_equiv_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let lhs = cmul(d, p, na, b);
    let b_na = cmul(d, p, b, na);
    let c1 = d.lemma(p.mul_comm, &[na, b]);

    let ba = cmul(d, p, b, a);
    let neg_ba = cneg(d, p, ba);
    let c2 = mul_neg_equiv(d, p, b, a);

    let ab = cmul(d, p, a, b);
    let neg_ab = cneg(d, p, ab);
    let c3a = d.lemma(p.mul_comm, &[b, a]);
    let c3 = d.lemma(p.neg_congr, &[ba, ab, c3a]);

    echain(d, p, lhs, &[(b_na, c1), (neg_ba, c2), (neg_ab, c3)])
}

/// From `h : le (abs x) bound`, derive `le (abs (neg x)) bound`. Copied
/// verbatim from `derivative.rs`'s private helper of the same shape.
fn le_abs_neg_of_le_abs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);

    let nle = d.lemma(p.neg_le_abs, &[x]);
    let upper = d.lemma(p.le_trans, &[nx, abs_x, bound, nle, h]);

    let le_x_bound = {
        let sle = d.lemma(p.le_abs_self, &[x]);
        d.lemma(p.le_trans, &[x, abs_x, bound, sle, h])
    };
    let nn = double_neg(d, p, x);
    let nn_symm = esymm(d, p, nnx, x, nn);
    let refl_bound = erefl(d, p, bound);
    let lower = d.lemma(
        p.le_congr,
        &[x, nnx, bound, bound, nn_symm, refl_bound, le_x_bound],
    );

    d.lemma(p.abs_le, &[nx, bound, upper, lower])
}

/// `Equiv (abs (neg x)) (abs x)` — from [`le_abs_neg_of_le_abs`] applied
/// twice (once at `bound := abs x` via `le_refl`, once at `bound := abs (neg
/// x)` via `le_refl` transported back through [`double_neg`]) and
/// `equiv_of_le_le`. `creal/fermat.rs` had a byte-identical (modulo
/// comments) private copy; it now imports this one instead.
pub(super) fn abs_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let abs_nx = cabs(d, p, nx);

    let refl_absx = d.lemma(p.le_refl, &[abs_x]);
    let le1 = le_abs_neg_of_le_abs(d, p, x, abs_x, refl_absx); // le abs_nx abs_x

    let refl_absnx = d.lemma(p.le_refl, &[abs_nx]);
    let le2_pre = le_abs_neg_of_le_abs(d, p, nx, abs_nx, refl_absnx);
    // le2_pre : le (abs (neg nx)) abs_nx, i.e. le (abs (neg (neg x))) abs_nx
    let nnx = cneg(d, p, nx);
    let abs_nnx = cabs(d, p, nnx);
    let dn = double_neg(d, p, x); // Equiv nnx x
    let abs_congr_dn = d.lemma(p.abs_congr, &[nnx, x, dn]); // Equiv abs_nnx abs_x
    let refl_absnx2 = erefl(d, p, abs_nx);
    let le2 = d.lemma(
        p.le_congr,
        &[
            abs_nnx,
            abs_x,
            abs_nx,
            abs_nx,
            abs_congr_dn,
            refl_absnx2,
            le2_pre,
        ],
    );
    // le2 : le abs_x abs_nx

    d.lemma(p.equiv_of_le_le, &[abs_nx, abs_x, le1, le2])
}

/// From `h : Equiv (add a (neg b)) zero`, derive `Equiv a b`. Also built
/// (independently, before this one was widened to `pub(super)`) as
/// private helpers of the same shape in `creal/monotone.rs` and
/// `creal/trig_fn.rs` — both out of scope for this refactor (live lanes),
/// so those two copies remain. `creal/exp_fn.rs` imports this one instead
/// of keeping its own third copy.
pub(super) fn equiv_of_sub_equiv_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let nb = cneg(d, p, b);
    let diff = cadd(d, p, a, nb);
    let lhs = cadd(d, p, diff, b);
    let zero_c = czero(d, p);

    let a_from_lhs = {
        let assoc = d.lemma(p.add_assoc, &[a, nb, b]);
        let nb_b = cadd(d, p, nb, b);
        let a_nbb = cadd(d, p, a, nb_b);
        let nas = neg_add_self(d, p, b);
        let refl_a = erefl(d, p, a);
        let cong = d.lemma(p.add_congr, &[a, a, nb_b, zero_c, refl_a, nas]);
        let a_zero = cadd(d, p, a, zero_c);
        let trim = d.lemma(p.add_zero, &[a]);
        echain(d, p, lhs, &[(a_nbb, assoc), (a_zero, cong), (a, trim)])
    };
    let b_from_lhs = {
        let refl_b = erefl(d, p, b);
        let cong = d.lemma(p.add_congr, &[diff, zero_c, b, b, h, refl_b]);
        let zero_b = cadd(d, p, zero_c, b);
        let comm = d.lemma(p.add_comm, &[zero_c, b]);
        let b_zero = cadd(d, p, b, zero_c);
        let trim = d.lemma(p.add_zero, &[b]);
        echain(d, p, lhs, &[(zero_b, cong), (b_zero, comm), (b, trim)])
    };
    let a_from_lhs_symm = esymm(d, p, lhs, a, a_from_lhs);
    d.lemma(p.equiv_trans, &[a, lhs, b, a_from_lhs_symm, b_from_lhs])
}

/// `Equiv (abs (ofRat q)) (ofRat q)` for `q_nonneg : Rat.le Rat.zero q` —
/// `abs_le` (upper via `Rat.neg_nonpos_of_nonneg` + `Rat.le_trans`, lower via
/// `le_abs_self`) sandwiches the embedding between itself. `creal/fermat.rs`
/// had a byte-identical (modulo comments) private copy; it now imports this
/// one instead.
pub(super) fn abs_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    q: ExprId,
    q_nonneg: ExprId,
) -> ExprId {
    let rat = p.rat;
    let q_emb = embed(d, p, q);
    let abs_q = cabs(d, p, q_emb);

    let refl_q = d.lemma(p.le_refl, &[q_emb]);

    let neg_q = crate::rat_prelude::ops::rneg(d, q);
    let neg_le_zero = d.lemma(rat.neg_nonpos_of_nonneg, &[q, q_nonneg]); // Rat.le (neg q) 0
    let rzero_expr = crate::rat_prelude::ops::rzero(d, rat);
    let neg_q_le_q = d.lemma(rat.le_trans, &[neg_q, rzero_expr, q, neg_le_zero, q_nonneg]);
    let creal_neg_q_le_q = d.lemma(p.of_rat_le, &[neg_q, q, neg_q_le_q]);
    // creal_neg_q_le_q : le (ofRat (neg q)) (ofRat q)

    let neg_q_emb = cneg(d, p, q_emb);
    let of_rat_neg_q = embed(d, p, neg_q);
    let on_eq = d.lemma(p.of_rat_neg, &[q]); // Equiv (neg q_emb) (ofRat (neg q))
    let on_eq_symm = esymm(d, p, of_rat_neg_q, neg_q_emb, on_eq);
    // on_eq_symm : Equiv (ofRat (neg q)) (neg q_emb)

    let refl_qemb = erefl(d, p, q_emb);
    let upper = d.lemma(
        p.le_congr,
        &[
            of_rat_neg_q,
            neg_q_emb,
            q_emb,
            q_emb,
            on_eq_symm,
            refl_qemb,
            creal_neg_q_le_q,
        ],
    );
    // upper : le (neg q_emb) q_emb

    let abs_le_result = d.lemma(p.abs_le, &[q_emb, q_emb, refl_q, upper]);
    // abs_le_result : le (abs q_emb) q_emb

    let le_abs_self_q = d.lemma(p.le_abs_self, &[q_emb]); // le q_emb (abs q_emb)

    d.lemma(
        p.equiv_of_le_le,
        &[abs_q, q_emb, abs_le_result, le_abs_self_q],
    )
}

// --- range/order algebra for the nearby-point construction ------------------

/// `Equiv (add (add v u) (neg v)) u` — `(v+u)-v ~ u`, for ANY `u`. Used at
/// `v := z` with `u := embed q` (the upper branch) or `u := neg (embed q)`
/// (the lower branch) to identify `y - z` with the exact signed gap.
/// `creal/fermat.rs` had a byte-identical private copy; it now imports this
/// one instead. `creal/add_sub_cancel`'s name collides with two OTHER,
/// genuinely different helpers of the same name (`creal/convergence.rs`'s
/// is over `Rat`, not `CReal`, and returns a pair; `creal/uniform_continuity.rs`'s
/// takes its arguments in the other order and proves `Equiv (add a (add b
/// (neg a))) b`, not this statement) — do not treat those as more copies
/// of this one.
pub(super) fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, u: ExprId) -> ExprId {
    let nv = cneg(d, p, v);
    let vu = cadd(d, p, v, u);
    let start = cadd(d, p, vu, nv);

    let uv = cadd(d, p, u, v);
    let comm1 = d.lemma(p.add_comm, &[v, u]); // v+u ~ u+v
    let refl_nv = erefl(d, p, nv);
    let step1 = d.lemma(p.add_congr, &[vu, uv, nv, nv, comm1, refl_nv]);
    let uv_nv = cadd(d, p, uv, nv);

    let assoc = d.lemma(p.add_assoc, &[u, v, nv]); // (u+v)+(-v) ~ u+(v+-v)
    let vnv = cadd(d, p, v, nv);
    let u_vnv = cadd(d, p, u, vnv);

    let an = d.lemma(p.add_neg, &[v]); // v+-v ~ 0
    let refl_u = erefl(d, p, u);
    let zero_c = czero(d, p);
    let step2 = d.lemma(p.add_congr, &[u, u, vnv, zero_c, refl_u, an]);
    let u_zero = cadd(d, p, u, zero_c);

    let trim = d.lemma(p.add_zero, &[u]);

    echain(
        d,
        p,
        start,
        &[(uv_nv, step1), (u_vnv, assoc), (u_zero, step2), (u, trim)],
    )
}

/// From `h : le (add x q) y`, derive `le x (add y (neg q))` — the CReal-level
/// "subtract `q` from a `le`" step. `creal/fermat.rs` had a byte-identical
/// (modulo comments) private copy; it now imports this one instead.
pub(super) fn le_sub_of_add_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    q: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let nq = cneg(d, p, q);
    let refl_nq = d.lemma(p.le_refl, &[nq]);
    let xq = cadd(d, p, x, q);
    let step = d.lemma(p.add_le_add, &[xq, y, nq, nq, h, refl_nq]);
    // step : le (add (add x q) (neg q)) (add y (neg q))

    let lhs_equiv_x = {
        let assoc = d.lemma(p.add_assoc, &[x, q, nq]); // (x+q)+(-q) ~ x+(q+-q)
        let qnq = cadd(d, p, q, nq);
        let x_qnq = cadd(d, p, x, qnq);
        let an = d.lemma(p.add_neg, &[q]); // q+-q ~ 0
        let refl_x = erefl(d, p, x);
        let zero_c = czero(d, p);
        let cong = d.lemma(p.add_congr, &[x, x, qnq, zero_c, refl_x, an]);
        let x_zero = cadd(d, p, x, zero_c);
        let trim = d.lemma(p.add_zero, &[x]);
        let start = cadd(d, p, xq, nq);
        echain(d, p, start, &[(x_qnq, assoc), (x_zero, cong), (x, trim)])
    };
    let y_nq = cadd(d, p, y, nq);
    let refl_target = erefl(d, p, y_nq);
    let start = cadd(d, p, xq, nq);
    d.lemma(
        p.le_congr,
        &[start, x, y_nq, y_nq, lhs_equiv_x, refl_target, step],
    )
}

// --- the ring identity: the two error terms differ by exactly `-v*(y-z)` ---

/// Given `a_term = F y - F z`, `p1 = mul (F1 z) diff`, `p2 = mul (F2 z)
/// diff`, `v = F1 z - F2 z`, `diff = y - z`, return `(mvd, proof)` where
/// `mvd := mul v diff` and `proof : Equiv D (neg mvd)`, `D := (a_term - p1) -
/// (a_term - p2)` — the error terms' difference. Pure ring algebra,
/// independent of the sign of `diff`.
fn error_diff_ring_identity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a_term: ExprId,
    p1: ExprId,
    p2: ExprId,
    v: ExprId,
    diff: ExprId,
    f1z: ExprId,
    f2z: ExprId,
) -> (ExprId, ExprId) {
    let np1 = cneg(d, p, p1);
    let np2 = cneg(d, p, p2);
    let error1 = cadd(d, p, a_term, np1);
    let error2 = cadd(d, p, a_term, np2);
    let neg_error2 = cneg(d, p, error2);
    let dd = cadd(d, p, error1, neg_error2);

    // Step (i): neg error2 ~ add (neg a_term) p2.
    let na_term = cneg(d, p, a_term);
    let nnp2 = cneg(d, p, np2);
    let na_nnp2 = cadd(d, p, na_term, nnp2);
    let nad = neg_add_distrib(d, p, a_term, np2); // neg error2 ~ na_nnp2
    let dn_p2 = double_neg(d, p, p2); // Equiv nnp2 p2
    let refl_na_term = erefl(d, p, na_term);
    let cong1 = d.lemma(
        p.add_congr,
        &[na_term, na_term, nnp2, p2, refl_na_term, dn_p2],
    );
    let na_p2 = cadd(d, p, na_term, p2);
    let step_i = echain(d, p, neg_error2, &[(na_nnp2, nad), (na_p2, cong1)]);

    // D ~ add error1 (add (neg a_term) p2) =: d1
    let refl_error1 = erefl(d, p, error1);
    let cong2 = d.lemma(
        p.add_congr,
        &[error1, error1, neg_error2, na_p2, refl_error1, step_i],
    );
    let d1 = cadd(d, p, error1, na_p2);

    // add4_comm(a_term, np1, na_term, p2) : d1 ~ (a_term+na_term)+(np1+p2)
    let (target5, proof5) = add4_comm(d, p, a_term, np1, na_term, p2);
    let np1_p2 = cadd(d, p, np1, p2);

    let an = d.lemma(p.add_neg, &[a_term]); // a_term + na_term ~ zero
    let zero_c = czero(d, p);
    let refl_np1p2 = erefl(d, p, np1_p2);
    let a_term_na_term = cadd(d, p, a_term, na_term);
    let cong3 = d.lemma(
        p.add_congr,
        &[a_term_na_term, zero_c, np1_p2, np1_p2, an, refl_np1p2],
    );
    let zero_np1p2 = cadd(d, p, zero_c, np1_p2);
    let comm_z = d.lemma(p.add_comm, &[zero_c, np1_p2]);
    let np1p2_zero = cadd(d, p, np1_p2, zero_c);
    let trim_z = d.lemma(p.add_zero, &[np1_p2]);

    let q1 = np1_p2; // Q1 = add (neg p1) p2
    let step_ii = echain(
        d,
        p,
        target5,
        &[(zero_np1p2, cong3), (np1p2_zero, comm_z), (q1, trim_z)],
    );

    let d_to_q1 = echain(d, p, dd, &[(d1, cong2), (target5, proof5), (q1, step_ii)]);

    // mvd := mul v diff ~ add p1 (neg p2), via right_distrib + neg_mul_equiv_left.
    let mvd = cmul(d, p, v, diff);
    let neg_f2z = cneg(d, p, f2z);
    let rd = right_distrib(d, p, f1z, neg_f2z, diff);
    // rd : Equiv mvd (add (mul f1z diff) (mul (neg f2z) diff))
    let mul_negf2z_diff = cmul(d, p, neg_f2z, diff);
    let nmel = neg_mul_equiv_left(d, p, f2z, diff); // Equiv mul_negf2z_diff (neg p2)
    let refl_p1 = erefl(d, p, p1);
    let cong4 = d.lemma(p.add_congr, &[p1, p1, mul_negf2z_diff, np2, refl_p1, nmel]);
    let p1_np2 = cadd(d, p, p1, np2);
    let p1_mul_negf2z_diff = cadd(d, p, p1, mul_negf2z_diff);
    let mvd_eq = echain(d, p, mvd, &[(p1_mul_negf2z_diff, rd), (p1_np2, cong4)]);
    // mvd_eq : Equiv mvd p1_np2

    // neg mvd ~ neg p1_np2 ~ (neg_add_distrib) add (neg p1) (neg (neg p2)) ~ (double_neg) add (neg p1) p2 = Q1
    let neg_mvd = cneg(d, p, mvd);
    let neg_p1_np2 = cneg(d, p, p1_np2);
    let nc = d.lemma(p.neg_congr, &[mvd, p1_np2, mvd_eq]); // Equiv neg_mvd neg_p1_np2
    let nad2 = neg_add_distrib(d, p, p1, np2); // Equiv neg_p1_np2 (add (neg p1) (neg np2))
    let nnp2b = cneg(d, p, np2);
    let np1_nnp2 = cadd(d, p, np1, nnp2b);
    let dn_p2b = double_neg(d, p, p2); // Equiv nnp2b p2
    let refl_np1 = erefl(d, p, np1);
    let cong5 = d.lemma(p.add_congr, &[np1, np1, nnp2b, p2, refl_np1, dn_p2b]);
    let neg_mvd_to_q1 = echain(
        d,
        p,
        neg_mvd,
        &[(neg_p1_np2, nc), (np1_nnp2, nad2), (q1, cong5)],
    );
    // neg_mvd_to_q1 : Equiv neg_mvd q1

    let q1_to_neg_mvd = esymm(d, p, neg_mvd, q1, neg_mvd_to_q1);
    let full = d.lemma(p.equiv_trans, &[dd, q1, neg_mvd, d_to_q1, q1_to_neg_mvd]);
    (mvd, full)
}

/// `Equiv (abs mvd) (abs (mul q_emb v))`, where `mvd = mul v diff` and
/// `diff_equiv_signed : Equiv diff signed_q` with `signed_q = q_emb` (`flip
/// = false`, the upper branch) or `signed_q = neg q_emb` (`flip = true`,
/// the lower branch). Exposes the scalar `q_emb` on the LEFT (via
/// `mul_comm`) so [`CRealPrelude::le_of_mul_le_mul_left`] can cancel it
/// later; the sign flip (when present) is absorbed by [`abs_neg_equiv`],
/// since `|-t| = |t|` regardless of sign.
fn mvd_to_mul_qv_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    diff: ExprId,
    diff_equiv_signed: ExprId,
    q_emb: ExprId,
    flip: bool,
) -> ExprId {
    let mvd = cmul(d, p, v, diff);
    let mul_qv = cmul(d, p, q_emb, v);
    let mul_v_q = cmul(d, p, v, q_emb);
    let refl_v = erefl(d, p, v);

    if flip {
        let neg_q_emb = cneg(d, p, q_emb);
        let step1 = d.lemma(
            p.mul_congr,
            &[v, v, diff, neg_q_emb, refl_v, diff_equiv_signed],
        );
        // step1 : Equiv mvd (mul v (neg q_emb))
        let mul_v_negq = cmul(d, p, v, neg_q_emb);
        let mne = mul_neg_equiv(d, p, v, q_emb); // Equiv mul_v_negq (neg mul_v_q)
        let neg_mul_v_q = cneg(d, p, mul_v_q);
        let comm = d.lemma(p.mul_comm, &[v, q_emb]); // Equiv mul_v_q mul_qv
        let ncomm = d.lemma(p.neg_congr, &[mul_v_q, mul_qv, comm]); // Equiv neg_mul_v_q (neg mul_qv)
        let neg_mul_qv = cneg(d, p, mul_qv);
        let full = echain(
            d,
            p,
            mvd,
            &[(mul_v_negq, step1), (neg_mul_v_q, mne), (neg_mul_qv, ncomm)],
        );
        // full : Equiv mvd (neg mul_qv)
        let abs_cong = d.lemma(p.abs_congr, &[mvd, neg_mul_qv, full]); // Equiv (abs mvd) (abs neg_mul_qv)
        let ane = abs_neg_equiv(d, p, mul_qv); // Equiv (abs neg_mul_qv) (abs mul_qv)
        let abs_mvd = cabs(d, p, mvd);
        let abs_neg_mul_qv = cabs(d, p, neg_mul_qv);
        let abs_mul_qv = cabs(d, p, mul_qv);
        d.lemma(
            p.equiv_trans,
            &[abs_mvd, abs_neg_mul_qv, abs_mul_qv, abs_cong, ane],
        )
    } else {
        let step1 = d.lemma(p.mul_congr, &[v, v, diff, q_emb, refl_v, diff_equiv_signed]);
        // step1 : Equiv mvd mul_v_q
        let comm = d.lemma(p.mul_comm, &[v, q_emb]); // Equiv mul_v_q mul_qv
        let full = echain(d, p, mvd, &[(mul_v_q, step1), (mul_qv, comm)]);
        d.lemma(p.abs_congr, &[mvd, mul_qv, full])
    }
}

/// `Equiv (add (mul c q) (mul c q)) (mul q r_emb)`, where `c = ofRat c_rat`,
/// `q = ofRat q_rat` (an arbitrary rational embedding, kept symbolic here),
/// and `rat_halve_eq : Eq Rat (add c_rat c_rat) r_rat` — reshapes the
/// doubled `hd_spec` bound into a form with the SAME scalar `q_emb`
/// [`CRealPrelude::le_of_mul_le_mul_left`] will cancel, via `mul_comm` +
/// `left_distrib` + `of_rat_add` + a rewrite along the `Rat`-level halving
/// identity.
fn bound2_to_scaled(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c_emb: ExprId,
    q_emb: ExprId,
    c_rat: ExprId,
    r_rat: ExprId,
    rat_halve_eq: ExprId,
) -> ExprId {
    let cq = cmul(d, p, c_emb, q_emb);
    let bound2 = cadd(d, p, cq, cq);

    let qc = cmul(d, p, q_emb, c_emb);
    let mc = d.lemma(p.mul_comm, &[c_emb, q_emb]); // Equiv cq qc
    let step1 = d.lemma(p.add_congr, &[cq, qc, cq, qc, mc, mc]);
    let qc_qc = cadd(d, p, qc, qc);

    let c_emb_c_emb = cadd(d, p, c_emb, c_emb);
    let q_cc = cmul(d, p, q_emb, c_emb_c_emb);
    let ld = d.lemma(p.left_distrib, &[q_emb, c_emb, c_emb]); // Equiv q_cc qc_qc
    let step2 = esymm(d, p, q_cc, qc_qc, ld);

    let add_c_rat_c_rat = radd(d, c_rat, c_rat);
    let embedded_sum = embed(d, p, add_c_rat_c_rat);
    let ora = d.lemma(p.of_rat_add, &[c_rat, c_rat]); // Equiv c_emb_c_emb embedded_sum
    let refl_q = erefl(d, p, q_emb);
    let step3 = d.lemma(
        p.mul_congr,
        &[q_emb, q_emb, c_emb_c_emb, embedded_sum, refl_q, ora],
    );
    let q_embedded_sum = cmul(d, p, q_emb, embedded_sum);

    let chain1 = echain(
        d,
        p,
        bound2,
        &[(qc_qc, step1), (q_cc, step2), (q_embedded_sum, step3)],
    );
    // chain1 : Equiv bound2 (mul q_emb (embed (add c_rat c_rat)))

    crate::rat_prelude::ops::rat_eq_rewrite(
        d,
        add_c_rat_c_rat,
        r_rat,
        rat_halve_eq,
        chain1,
        &|d, t| {
            let embedded_t = embed(d, p, t);
            let scaled = cmul(d, p, q_emb, embedded_t);
            cequiv(d, p, bound2, scaled)
        },
    )
}

/// `CReal.Equiv a b`.
fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.equiv, &[a, b])
}

// --- the shared "finish" step: two hd_spec instances at the SAME accuracy,
// combined and cancelled by the exact rational gap `q` ----------------------

#[allow(clippy::too_many_arguments)]
fn finish_common(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    y: ExprId,
    haz: ExprId,
    hzb: ExprId,
    le_a_y: ExprId,
    le_y_b: ExprId,
    e: ExprId,
    k: ExprId,
    m1: ExprId,
    m2: ExprId,
    v: ExprId,
    q: ExprId,
    q_pos: ExprId,
    q_le_bound_k: ExprId,
    diff_equiv_signed: ExprId,
    abs_diff_eq_q: ExprId,
    flip: bool,
    target: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;

    let q_emb = embed(d, p, q);
    let diff_yx = cdiff(d, p, y, z);

    // --- moduli antitone bounds: q <= rm1, q <= rm2 -----------------------
    let m1_le_k = d.lemma(nat_p.le_add_right, &[m1, m2]); // Nat.le m1 k
    let raw2 = d.lemma(nat_p.le_add_right, &[m2, m1]); // Nat.le m2 (add m2 m1)
    let comm_eq = d.lemma(nat_p.add_comm, &[m2, m1]); // Eq (add m2 m1) k
    let m2_plus_m1 = d.add(m2, m1);
    let m2_le_k = nat_rewrite_prop(d, m2_plus_m1, k, comm_eq, raw2, &|d, t| d.le(m2, t));

    let rm1 = div_succ(d, p, 1, m1);
    let rm2 = div_succ(d, p, 1, m2);
    let bound_k_rat = div_succ(d, p, 1, k);

    let anti1 = d.lemma(rat.nat_div_succ_antitone, &[m1, k, m1_le_k]); // Rat.le bound_k_rat rm1
    let anti2 = d.lemma(rat.nat_div_succ_antitone, &[m2, k, m2_le_k]);

    let q_le_rm1 = d.lemma(rat.le_trans, &[q, bound_k_rat, rm1, q_le_bound_k, anti1]);
    let q_le_rm2 = d.lemma(rat.le_trans, &[q, bound_k_rat, rm2, q_le_bound_k, anti2]);

    // --- hd_spec hypotheses ------------------------------------------------
    let abs_diff = cabs(d, p, diff_yx);
    let build_hyp = |d: &mut IntDev<'_>, rmi: ExprId, q_le_rmi: ExprId| -> ExprId {
        let ofr_rmi = d.const_app(p.of_rat, &[rmi]);
        let q_le_ofr = d.lemma(p.of_rat_le, &[q, rmi, q_le_rmi]); // le q_emb ofr_rmi
        let abs_diff_eq_q_symm = esymm(d, p, abs_diff, q_emb, abs_diff_eq_q);
        let refl_ofr = erefl(d, p, ofr_rmi);
        d.lemma(
            p.le_congr,
            &[
                q_emb,
                abs_diff,
                ofr_rmi,
                ofr_rmi,
                abs_diff_eq_q_symm,
                refl_ofr,
                q_le_ofr,
            ],
        )
    };
    let hyp1 = build_hyp(d, rm1, q_le_rm1);
    let hyp2 = build_hyp(d, rm2, q_le_rm2);

    // --- hd_spec calls -------------------------------------------------
    let error1_bound = d.lemma(
        p.hd_spec,
        &[f, f1, a, b, hf1, e, z, y, haz, hzb, le_a_y, le_y_b, hyp1],
    );
    let error2_bound = d.lemma(
        p.hd_spec,
        &[f, f2, a, b, hf2, e, z, y, haz, hzb, le_a_y, le_y_b, hyp2],
    );

    let c_rat = div_succ(d, p, 1, e);
    let c_emb = d.const_app(p.of_rat, &[c_rat]);
    let orig_bound = cmul(d, p, c_emb, abs_diff);
    let common_bound_q = cmul(d, p, c_emb, q_emb);

    let bound_transport = {
        let refl_c = erefl(d, p, c_emb);
        d.lemma(
            p.mul_congr,
            &[c_emb, c_emb, abs_diff, q_emb, refl_c, abs_diff_eq_q],
        )
    };

    let f1z = d.apply(f1, &[z]);
    let f2z = d.apply(f2, &[z]);
    let fx = d.apply(f, &[z]);
    let fy = d.apply(f, &[y]);
    let a_term = cdiff(d, p, fy, fx);
    let p1 = cmul(d, p, f1z, diff_yx);
    let p2 = cmul(d, p, f2z, diff_yx);
    let neg_p1 = cneg(d, p, p1);
    let neg_p2 = cneg(d, p, p2);
    let error1 = cadd(d, p, a_term, neg_p1);
    let error2 = cadd(d, p, a_term, neg_p2);

    let error1_bound_q = {
        let abs_e1 = cabs(d, p, error1);
        let refl_abs_e1 = erefl(d, p, abs_e1);
        d.lemma(
            p.le_congr,
            &[
                abs_e1,
                abs_e1,
                orig_bound,
                common_bound_q,
                refl_abs_e1,
                bound_transport,
                error1_bound,
            ],
        )
    };
    let error2_bound_q = {
        let abs_e2 = cabs(d, p, error2);
        let refl_abs_e2 = erefl(d, p, abs_e2);
        d.lemma(
            p.le_congr,
            &[
                abs_e2,
                abs_e2,
                orig_bound,
                common_bound_q,
                refl_abs_e2,
                bound_transport,
                error2_bound,
            ],
        )
    };

    // --- triangle inequality ---------------------------------------------
    let neg_error2 = cneg(d, p, error2);
    let dd_expr = cadd(d, p, error1, neg_error2);
    let triangle = d.lemma(p.abs_add_le, &[error1, neg_error2]);
    let abs_neg_error2_le = le_abs_neg_of_le_abs(d, p, error2, common_bound_q, error2_bound_q);
    let abs_error1 = cabs(d, p, error1);
    let abs_neg_error2 = cabs(d, p, neg_error2);
    let sum_bounds = d.lemma(
        p.add_le_add,
        &[
            abs_error1,
            common_bound_q,
            abs_neg_error2,
            common_bound_q,
            error1_bound_q,
            abs_neg_error2_le,
        ],
    );
    let bound2 = cadd(d, p, common_bound_q, common_bound_q);
    let sum_of_abs = cadd(d, p, abs_error1, abs_neg_error2);
    let abs_dd_expr = cabs(d, p, dd_expr);
    let bound_dd = d.lemma(
        p.le_trans,
        &[abs_dd_expr, sum_of_abs, bound2, triangle, sum_bounds],
    );

    // --- ring identity: D ~ neg (mul v diff_yx) ---------------------------
    let (mvd, identity) = error_diff_ring_identity(d, p, a_term, p1, p2, v, diff_yx, f1z, f2z);
    let neg_mvd = cneg(d, p, mvd);

    let bound_neg_mvd = {
        let refl_bound2 = erefl(d, p, bound2);
        let abs_cong = d.lemma(p.abs_congr, &[dd_expr, neg_mvd, identity]);
        let abs_neg_mvd = cabs(d, p, neg_mvd);
        d.lemma(
            p.le_congr,
            &[
                abs_dd_expr,
                abs_neg_mvd,
                bound2,
                bound2,
                abs_cong,
                refl_bound2,
                bound_dd,
            ],
        )
    };
    let abs_mvd = cabs(d, p, mvd);
    let bound_mvd = {
        let an_eq = abs_neg_equiv(d, p, mvd);
        let refl_bound2 = erefl(d, p, bound2);
        let abs_neg_mvd = cabs(d, p, neg_mvd);
        d.lemma(
            p.le_congr,
            &[
                abs_neg_mvd,
                abs_mvd,
                bound2,
                bound2,
                an_eq,
                refl_bound2,
                bound_neg_mvd,
            ],
        )
    };

    // --- reshape mvd's magnitude to (abs (mul q_emb v)) -------------------
    let mul_qv = cmul(d, p, q_emb, v);
    let mvd_eq_abs_target = mvd_to_mul_qv_equiv(d, p, v, diff_yx, diff_equiv_signed, q_emb, flip);
    let abs_mul_qv = cabs(d, p, mul_qv);
    let bound_mul_qv = {
        let refl_bound2 = erefl(d, p, bound2);
        d.lemma(
            p.le_congr,
            &[
                abs_mvd,
                abs_mul_qv,
                bound2,
                bound2,
                mvd_eq_abs_target,
                refl_bound2,
                bound_mvd,
            ],
        )
    };

    // --- reshape bound2 ~ mul q_emb r_emb ----------------------------------
    let bound2_eq = bound2_to_scaled(d, p, c_emb, q_emb, c_rat, r_final, rat_halve_eq);
    let r_emb = d.const_app(p.of_rat, &[r_final]);
    let scaled_bound = cmul(d, p, q_emb, r_emb);
    let bound_scaled = {
        let refl_abs = erefl(d, p, abs_mul_qv);
        d.lemma(
            p.le_congr,
            &[
                abs_mul_qv,
                abs_mul_qv,
                bound2,
                scaled_bound,
                refl_abs,
                bound2_eq,
                bound_mul_qv,
            ],
        )
    };

    // --- extract le (mul q_emb v) scaled_bound and le (mul q_emb (neg v)) scaled_bound
    let upper_qv = {
        let sle = d.lemma(p.le_abs_self, &[mul_qv]);
        d.lemma(
            p.le_trans,
            &[mul_qv, abs_mul_qv, scaled_bound, sle, bound_scaled],
        )
    };
    let neg_mul_qv = cneg(d, p, mul_qv);
    let lower_qv = {
        let nle = d.lemma(p.neg_le_abs, &[mul_qv]);
        d.lemma(
            p.le_trans,
            &[neg_mul_qv, abs_mul_qv, scaled_bound, nle, bound_scaled],
        )
    };
    let neg_v = cneg(d, p, v);
    let mul_q_negv = cmul(d, p, q_emb, neg_v);
    let mne = mul_neg_equiv(d, p, q_emb, v); // Equiv mul_q_negv neg_mul_qv
    let mne_symm = esymm(d, p, mul_q_negv, neg_mul_qv, mne);
    let lower_qv2 = {
        let refl_scaled = erefl(d, p, scaled_bound);
        d.lemma(
            p.le_congr,
            &[
                neg_mul_qv,
                mul_q_negv,
                scaled_bound,
                scaled_bound,
                mne_symm,
                refl_scaled,
                lower_qv,
            ],
        )
    };

    // --- cancellation, via an existential PosBound witness for q_emb -----
    let predicate_k = {
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let body = pos_bound(d, p, q_emb, k2);
        d.lam_fv(k2_fv, nat, body)
    };
    let lt_zero_qemb = d.lemma(p.of_rat_pos, &[q, q_pos]);
    let ex_witness = d.lemma(p.pos_bound_of_lt, &[q_emb, lt_zero_qemb]);
    let minor_k = {
        let k2_fv = d.fresh_fvar();
        let k2 = d.kernel().fvar(k2_fv);
        let pb_ty = pos_bound(d, p, q_emb, k2);
        let pb_fv = d.fresh_fvar();
        let pb = d.kernel().fvar(pb_fv);

        let le_v_r = d.lemma(
            p.le_of_mul_le_mul_left,
            &[q_emb, v, r_emb, k2, pb, upper_qv],
        );
        let le_negv_r = d.lemma(
            p.le_of_mul_le_mul_left,
            &[q_emb, neg_v, r_emb, k2, pb, lower_qv2],
        );
        let body = d.lemma(p.abs_le, &[v, r_emb, le_v_r, le_negv_r]);

        let with_pb = d.lam_fv(pb_fv, pb_ty, body);
        d.lam_fv(k2_fv, nat, with_pb)
    };
    exists_elim(d, predicate_k, target, ex_witness, minor_k)
}

// --- the two `lt_cotrans` branches: build a nearby point `y` off `z` by an
// exact rational gap `q`, small enough for BOTH `hd_spec` moduli AND to stay
// inside `[a,b]` -- the "nearby-point-in-bounds off a known gap" lemma the
// module documentation names, specialised inline to what `finish_common`
// consumes. -------------------------------------------------------------

/// The lower branch: `h_az : lt a z`. Builds `y := z - q` for `q :=
/// min(q0, bound_k)`, `q0` the exact gap `lt a z` carries.
#[allow(clippy::too_many_arguments)]
fn branch_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    h_az: ExprId,
) -> ExprId {
    let rat = p.rat;
    let rat_carrier = rat_ty(d);

    let mod1_fn = d.const_app(p.hd_modulus, &[f, f1, a, b, hf1]);
    let m1 = d.apply(mod1_fn, &[e]);
    let mod2_fn = d.const_app(p.hd_modulus, &[f, f2, a, b, hf2]);
    let m2 = d.apply(mod2_fn, &[e]);
    let k = d.add(m1, m2);
    let bound_k = div_succ(d, p, 1, k);

    let minor = {
        let q0_fv = d.fresh_fvar();
        let q0 = d.kernel().fvar(q0_fv);
        let zero_rat = crate::rat_prelude::ops::rzero(d, rat);
        let positive = rlt(d, rat, zero_rat, q0);
        let embedded_q0 = embed(d, p, q0);
        let shifted = cadd(d, p, a, embedded_q0);
        let bounded = cle(d, p, shifted, z);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (q0_pos, a_q0_le_z) = gap_halves(d, p, a, z, q0, w);

        let body = branch_lower_body(
            d,
            p,
            f,
            f1,
            f2,
            a,
            b,
            hf1,
            hf2,
            z,
            haz,
            hzb,
            e,
            v,
            r_final,
            rat_halve_eq,
            target,
            k,
            m1,
            m2,
            bound_k,
            q0,
            q0_pos,
            a_q0_le_z,
        );
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q0_fv, rat_carrier, with_w)
    };
    gap_elim(d, p, a, z, target, h_az, minor)
}

#[allow(clippy::too_many_arguments)]
fn branch_lower_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    k: ExprId,
    m1: ExprId,
    m2: ExprId,
    bound_k: ExprId,
    q0: ExprId,
    q0_pos: ExprId,
    a_q0_le_z: ExprId,
) -> ExprId {
    let rat = p.rat;
    let case = d.lemma(rat.le_or_lt, &[q0, bound_k]); // Or (Rat.le q0 bound_k) (Rat.lt bound_k q0)
    let left_ty = rle(d, rat, q0, bound_k);
    let right_ty = rlt(d, rat, bound_k, q0);

    d.or_elim(
        left_ty,
        right_ty,
        target,
        case,
        &|d, h_le| {
            let q_le_q0 = d.lemma(rat.le_refl, &[q0]);
            finish_lower_with_q(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                k,
                m1,
                m2,
                q0,
                q0_pos,
                a_q0_le_z,
                q0,
                q0_pos,
                q_le_q0,
                h_le,
            )
        },
        &|d, h_lt| {
            let q_pos = {
                let one_nat = d.num(1);
                let unit_le = d.lemma(p.rat.int.nat.le_refl, &[one_nat]);
                d.lemma(rat.nat_div_succ_pos, &[one_nat, k, unit_le])
            };
            let q_le_q0 = d.lemma(rat.le_of_lt, &[bound_k, q0, h_lt]);
            let q_le_bound_k = d.lemma(rat.le_refl, &[bound_k]);
            finish_lower_with_q(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                k,
                m1,
                m2,
                q0,
                q0_pos,
                a_q0_le_z,
                bound_k,
                q_pos,
                q_le_q0,
                q_le_bound_k,
            )
        },
    )
}

/// Shared tail of both `Rat.le_or_lt` cases: given the chosen `q`
/// (`q_pos : Rat.lt 0 q`, `q_le_q0 : Rat.le q q0`, `q_le_bound_k : Rat.le q
/// bound_k`), build `y := z - q` and hand off to [`finish_common`].
#[allow(clippy::too_many_arguments)]
fn finish_lower_with_q(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    k: ExprId,
    m1: ExprId,
    m2: ExprId,
    q0: ExprId,
    _q0_pos: ExprId,
    a_q0_le_z: ExprId,
    q: ExprId,
    q_pos: ExprId,
    q_le_q0: ExprId,
    q_le_bound_k: ExprId,
) -> ExprId {
    let q_emb = embed(d, p, q);
    let q0_emb = embed(d, p, q0);
    let neg_q_emb = cneg(d, p, q_emb);
    let y = cadd(d, p, z, neg_q_emb);

    // le a y : from a_q0_le_z (le (add a q0_emb) z), cancel to `le a (z -
    // q0_emb)`, then weaken q0 -> q.
    let a_le_z_minus_q0 = le_sub_of_add_le(d, p, a, q0_emb, z, a_q0_le_z);
    let q_emb_le_q0_emb = d.lemma(p.of_rat_le, &[q, q0, q_le_q0]);
    let neg_q0_emb = cneg(d, p, q0_emb);
    let neg_q0_le_neg_q = d.lemma(p.neg_le_neg, &[q_emb, q0_emb, q_emb_le_q0_emb]);
    let refl_z = d.lemma(p.le_refl, &[z]);
    let z_minus_q0_le_y = d.lemma(
        p.add_le_add,
        &[z, z, neg_q0_emb, neg_q_emb, refl_z, neg_q0_le_neg_q],
    );
    let z_minus_q0 = cadd(d, p, z, neg_q0_emb);
    let le_a_y = d.lemma(
        p.le_trans,
        &[a, z_minus_q0, y, a_le_z_minus_q0, z_minus_q0_le_y],
    );

    // le y b : from hzb (le z b) and q >= 0.
    let rat_zero = crate::rat_prelude::ops::rzero(d, p.rat);
    let zero_le_q = d.lemma(p.rat.le_of_lt, &[rat_zero, q, q_pos]);
    let zero_le_q_emb = d.lemma(p.of_rat_le, &[rat_zero, q, zero_le_q]);
    let zero_c = czero(d, p);
    let neg_zero_c = cneg(d, p, zero_c);
    let neg_q_le_neg_zero_c = d.lemma(p.neg_le_neg, &[zero_c, q_emb, zero_le_q_emb]);
    // neg_q_le_neg_zero_c : le neg_q_emb neg_zero_c
    let nz_eq = neg_zero_equiv_local(d, p);
    let neg_q_le_zero = {
        let refl_negq = erefl(d, p, neg_q_emb);
        d.lemma(
            p.le_congr,
            &[
                neg_q_emb,
                neg_q_emb,
                neg_zero_c,
                zero_c,
                refl_negq,
                nz_eq,
                neg_q_le_neg_zero_c,
            ],
        )
    };
    let y_le_z_plus_zero = d.lemma(
        p.add_le_add,
        &[z, z, neg_q_emb, zero_c, refl_z, neg_q_le_zero],
    );
    let z_plus_zero = cadd(d, p, z, zero_c);
    let az = d.lemma(p.add_zero, &[z]);
    let y_le_z = {
        let refl_y = erefl(d, p, y);
        d.lemma(
            p.le_congr,
            &[y, y, z_plus_zero, z, refl_y, az, y_le_z_plus_zero],
        )
    };
    let le_y_b = d.lemma(p.le_trans, &[y, z, b, y_le_z, hzb]);

    // diff_equiv_signed : Equiv (add y (neg z)) (neg q_emb).
    let diff_equiv_signed = add_sub_cancel(d, p, z, neg_q_emb);

    // abs_diff_eq_q : Equiv (abs (add y (neg z))) q_emb.
    let diff_yx = cdiff(d, p, y, z);
    let abs_diff_congr = d.lemma(p.abs_congr, &[diff_yx, neg_q_emb, diff_equiv_signed]);
    // abs_neg_equiv(q_emb) : Equiv (abs neg_q_emb) (abs q_emb) -- NOT q_emb itself;
    // abs_of_nonneg supplies the missing (abs q_emb) ~ q_emb step.
    let abs_neg_q = abs_neg_equiv(d, p, q_emb);
    let abs_q_eq_q = abs_of_nonneg(d, p, q, zero_le_q);
    let abs_diff_yx = cabs(d, p, diff_yx);
    let abs_neg_q_emb = cabs(d, p, neg_q_emb);
    let abs_q_emb = cabs(d, p, q_emb);
    let abs_diff_eq_q = {
        let step1 = d.lemma(
            p.equiv_trans,
            &[
                abs_diff_yx,
                abs_neg_q_emb,
                abs_q_emb,
                abs_diff_congr,
                abs_neg_q,
            ],
        );
        d.lemma(
            p.equiv_trans,
            &[abs_diff_yx, abs_q_emb, q_emb, step1, abs_q_eq_q],
        )
    };

    finish_common(
        d,
        p,
        f,
        f1,
        f2,
        a,
        b,
        hf1,
        hf2,
        z,
        y,
        haz,
        hzb,
        le_a_y,
        le_y_b,
        e,
        k,
        m1,
        m2,
        v,
        q,
        q_pos,
        q_le_bound_k,
        diff_equiv_signed,
        abs_diff_eq_q,
        true,
        target,
        r_final,
        rat_halve_eq,
    )
}

/// `Equiv (neg zero) zero`.
fn neg_zero_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = esymm(d, p, padded, nz, h1);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// The upper branch: `h_zb : lt z b`. Builds `y := z + q` for `q :=
/// min(q0, bound_k)`, `q0` the exact gap `lt z b` carries.
#[allow(clippy::too_many_arguments)]
fn branch_upper(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    h_zb: ExprId,
) -> ExprId {
    let rat = p.rat;
    let rat_carrier = rat_ty(d);

    let mod1_fn = d.const_app(p.hd_modulus, &[f, f1, a, b, hf1]);
    let m1 = d.apply(mod1_fn, &[e]);
    let mod2_fn = d.const_app(p.hd_modulus, &[f, f2, a, b, hf2]);
    let m2 = d.apply(mod2_fn, &[e]);
    let k = d.add(m1, m2);
    let bound_k = div_succ(d, p, 1, k);

    let minor = {
        let q0_fv = d.fresh_fvar();
        let q0 = d.kernel().fvar(q0_fv);
        let zero_rat = crate::rat_prelude::ops::rzero(d, rat);
        let positive = rlt(d, rat, zero_rat, q0);
        let embedded_q0 = embed(d, p, q0);
        let shifted = cadd(d, p, z, embedded_q0);
        let bounded = cle(d, p, shifted, b);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (q0_pos, z_q0_le_b) = gap_halves(d, p, z, b, q0, w);

        let body = branch_upper_body(
            d,
            p,
            f,
            f1,
            f2,
            a,
            b,
            hf1,
            hf2,
            z,
            haz,
            hzb,
            e,
            v,
            r_final,
            rat_halve_eq,
            target,
            k,
            m1,
            m2,
            bound_k,
            q0,
            q0_pos,
            z_q0_le_b,
        );
        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q0_fv, rat_carrier, with_w)
    };
    gap_elim(d, p, z, b, target, h_zb, minor)
}

#[allow(clippy::too_many_arguments)]
fn branch_upper_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    k: ExprId,
    m1: ExprId,
    m2: ExprId,
    bound_k: ExprId,
    q0: ExprId,
    q0_pos: ExprId,
    z_q0_le_b: ExprId,
) -> ExprId {
    let rat = p.rat;
    let case = d.lemma(rat.le_or_lt, &[q0, bound_k]);
    let left_ty = rle(d, rat, q0, bound_k);
    let right_ty = rlt(d, rat, bound_k, q0);

    d.or_elim(
        left_ty,
        right_ty,
        target,
        case,
        &|d, h_le| {
            let q_le_q0 = d.lemma(rat.le_refl, &[q0]);
            finish_upper_with_q(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                k,
                m1,
                m2,
                q0,
                q0_pos,
                z_q0_le_b,
                q0,
                q0_pos,
                q_le_q0,
                h_le,
            )
        },
        &|d, h_lt| {
            let q_pos = {
                let one_nat = d.num(1);
                let unit_le = d.lemma(p.rat.int.nat.le_refl, &[one_nat]);
                d.lemma(rat.nat_div_succ_pos, &[one_nat, k, unit_le])
            };
            let q_le_q0 = d.lemma(rat.le_of_lt, &[bound_k, q0, h_lt]);
            let q_le_bound_k = d.lemma(rat.le_refl, &[bound_k]);
            finish_upper_with_q(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                k,
                m1,
                m2,
                q0,
                q0_pos,
                z_q0_le_b,
                bound_k,
                q_pos,
                q_le_q0,
                q_le_bound_k,
            )
        },
    )
}

/// Shared tail of both `Rat.le_or_lt` cases for the upper branch: build `y
/// := z + q` and hand off to [`finish_common`].
#[allow(clippy::too_many_arguments)]
fn finish_upper_with_q(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    e: ExprId,
    v: ExprId,
    r_final: ExprId,
    rat_halve_eq: ExprId,
    target: ExprId,
    k: ExprId,
    m1: ExprId,
    m2: ExprId,
    q0: ExprId,
    _q0_pos: ExprId,
    z_q0_le_b: ExprId,
    q: ExprId,
    q_pos: ExprId,
    q_le_q0: ExprId,
    q_le_bound_k: ExprId,
) -> ExprId {
    let q_emb = embed(d, p, q);
    let q0_emb = embed(d, p, q0);
    let y = cadd(d, p, z, q_emb);

    // le a y : le z (add z q_emb) [le_add_of_nonneg] then le_trans with haz.
    let rat_zero = crate::rat_prelude::ops::rzero(d, p.rat);
    let zero_le_q = d.lemma(p.rat.le_of_lt, &[rat_zero, q, q_pos]);
    let z_le_y = d.lemma(p.le_add_of_nonneg, &[z, q, zero_le_q]);
    let le_a_y = d.lemma(p.le_trans, &[a, z, y, haz, z_le_y]);

    // le y b : from z_q0_le_b (le (add z q0_emb) b) and q <= q0.
    let q_emb_le_q0_emb = d.lemma(p.of_rat_le, &[q, q0, q_le_q0]);
    let refl_z = d.lemma(p.le_refl, &[z]);
    let z_q_le_z_q0 = d.lemma(
        p.add_le_add,
        &[z, z, q_emb, q0_emb, refl_z, q_emb_le_q0_emb],
    );
    let z_plus_q0 = cadd(d, p, z, q0_emb);
    let le_y_b = d.lemma(p.le_trans, &[y, z_plus_q0, b, z_q_le_z_q0, z_q0_le_b]);

    // diff_equiv_signed : Equiv (add y (neg z)) q_emb.
    let diff_equiv_signed = add_sub_cancel(d, p, z, q_emb);

    // abs_diff_eq_q : Equiv (abs (add y (neg z))) q_emb.
    let diff_yx = cdiff(d, p, y, z);
    let abs_diff_congr = d.lemma(p.abs_congr, &[diff_yx, q_emb, diff_equiv_signed]);
    let abs_q_eq_q = abs_of_nonneg(d, p, q, zero_le_q);
    let abs_diff_yx = cabs(d, p, diff_yx);
    let abs_q_emb = cabs(d, p, q_emb);
    let abs_diff_eq_q = d.lemma(
        p.equiv_trans,
        &[abs_diff_yx, abs_q_emb, q_emb, abs_diff_congr, abs_q_eq_q],
    );

    finish_common(
        d,
        p,
        f,
        f1,
        f2,
        a,
        b,
        hf1,
        hf2,
        z,
        y,
        haz,
        hzb,
        le_a_y,
        le_y_b,
        e,
        k,
        m1,
        m2,
        v,
        q,
        q_pos,
        q_le_bound_k,
        diff_equiv_signed,
        abs_diff_eq_q,
        false,
        target,
        r_final,
        rat_halve_eq,
    )
}

// --- the top-level theorem ---------------------------------------------

/// `CReal.hasDerivative_unique : ∀ F F1 F2 a b, HasDerivativeOn F F1 a b →
/// HasDerivativeOn F F2 a b → lt a b → ∀ z, le a z → le z b → Equiv (F1 z)
/// (F2 z)`. See the module documentation for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_has_derivative_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let f1_fv = d.fresh_fvar();
    let f1 = d.kernel().fvar(f1_fv);
    let f2_fv = d.fresh_fvar();
    let f2 = d.kernel().fvar(f2_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hf1_ty = d.const_app(p.has_derivative_on, &[f, f1, a, b]);
    let hf1_fv = d.fresh_fvar();
    let hf1 = d.kernel().fvar(hf1_fv);
    let hf2_ty = d.const_app(p.has_derivative_on, &[f, f2, a, b]);
    let hf2_fv = d.fresh_fvar();
    let hf2 = d.kernel().fvar(hf2_fv);

    let hab_ty = clt(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_ty = cle(d, p, a, z);
    let haz_fv = d.fresh_fvar();
    let haz = d.kernel().fvar(haz_fv);
    let hzb_ty = cle(d, p, z, b);
    let hzb_fv = d.fresh_fvar();
    let hzb = d.kernel().fvar(hzb_fv);

    let f1z = d.apply(f1, &[z]);
    let f2z = d.apply(f2, &[z]);
    let v = cdiff(d, p, f1z, f2z);

    let e_fv = d.fresh_fvar();
    let e_prime = d.kernel().fvar(e_fv);
    let body = build_bound_proof(
        d, p, f, f1, f2, a, b, hf1, hf2, hab, z, haz, hzb, v, e_prime,
    );
    let hyp_small = d.lam_fv(e_fv, nat, body);

    let v_equiv_zero = d.lemma(p.equiv_zero_of_small, &[v, hyp_small]);
    let conclusion = equiv_of_sub_equiv_zero(d, p, f1z, f2z, v_equiv_zero);

    let value = {
        let with_hzb = d.lam_fv(hzb_fv, hzb_ty, conclusion);
        let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
        let with_z = d.lam_fv(z_fv, carrier, with_haz);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_z);
        let with_hf2 = d.lam_fv(hf2_fv, hf2_ty, with_hab);
        let with_hf1 = d.lam_fv(hf1_fv, hf1_ty, with_hf2);
        let with_b = d.lam_fv(b_fv, carrier, with_hf1);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_f2 = d.lam_fv(f2_fv, func_ty, with_a);
        let with_f1 = d.lam_fv(f1_fv, func_ty, with_f2);
        d.lam_fv(f_fv, func_ty, with_f1)
    };
    let ty = {
        let concl = cequiv(d, p, f1z, f2z);
        let after_hzb = d.arrow(hzb_ty, concl);
        let after_haz = d.arrow(haz_ty, after_hzb);
        let over_z = d.pi_fv(z_fv, carrier, after_haz);
        let after_hab = d.arrow(hab_ty, over_z);
        let after_hf2 = d.arrow(hf2_ty, after_hab);
        let after_hf1 = d.arrow(hf1_ty, after_hf2);
        let over_b = d.pi_fv(b_fv, carrier, after_hf1);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_f2 = d.pi_fv(f2_fv, func_ty, over_a);
        let over_f1 = d.pi_fv(f1_fv, func_ty, over_f2);
        d.pi_fv(f_fv, func_ty, over_f1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.deriv_unique.has_derivative_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// Build the proof of `le (abs v) (ofRat (natDivSucc 1 e'))` for the fixed
/// outer accuracy `e_prime`, by reindexing to `e := shift e_prime` and
/// case-splitting `lt_cotrans a b hab z`. See the module documentation.
#[allow(clippy::too_many_arguments)]
fn build_bound_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    f1: ExprId,
    f2: ExprId,
    a: ExprId,
    b: ExprId,
    hf1: ExprId,
    hf2: ExprId,
    hab: ExprId,
    z: ExprId,
    haz: ExprId,
    hzb: ExprId,
    v: ExprId,
    e_prime: ExprId,
) -> ExprId {
    let rat = p.rat;
    let e = shift(d, e_prime);

    let r_final = div_succ(d, p, 1, e_prime);
    let r_emb = d.const_app(p.of_rat, &[r_final]);
    let abs_v = cabs(d, p, v);
    let target = cle(d, p, abs_v, r_emb);

    let c_rat = div_succ(d, p, 1, e);
    let two_e_rat = div_succ(d, p, 2, e);
    let one_nat = d.num(1);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, e]);
    let halve = d.lemma(rat.nat_div_succ_halve, &[e_prime]);
    let add_c_rat_c_rat = radd(d, c_rat, c_rat);
    let (_, rat_halve_eq) = rchain(d, add_c_rat_c_rat, &[(two_e_rat, fuse), (r_final, halve)]);

    let cot = d.lemma(p.lt_cotrans, &[a, b, hab, z]);
    let lt_az_ty = clt(d, p, a, z);
    let lt_zb_ty = clt(d, p, z, b);

    d.or_elim(
        lt_az_ty,
        lt_zb_ty,
        target,
        cot,
        &|d, h_az| {
            branch_lower(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                h_az,
            )
        },
        &|d, h_zb| {
            branch_upper(
                d,
                p,
                f,
                f1,
                f2,
                a,
                b,
                hf1,
                hf2,
                z,
                haz,
                hzb,
                e,
                v,
                r_final,
                rat_halve_eq,
                target,
                h_zb,
            )
        },
    )
}

/// The kernel names `creal/deriv_unique.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivUniqueNames {
    /// `CReal.hasDerivative_unique : ∀ F F1 F2 a b, HasDerivativeOn F F1 a b
    /// → HasDerivativeOn F F2 a b → lt a b → ∀ z, le a z → le z b → Equiv
    /// (F1 z) (F2 z)` (`creal/deriv_unique.rs`) — the derivative of a
    /// function on `[a,b]` is unique, GIVEN the interval is genuinely
    /// nondegenerate (`lt a b`, not merely `le a b`). The naive statement
    /// without that hypothesis is refuted at a degenerate interval `a = b`
    /// (`id`'s derivative is simultaneously `const zero` and `const one`
    /// there); see that module's own documentation for the refutation and
    /// the `lt_cotrans`-based nearby-point construction that replaces it.
    pub has_derivative_unique: NameId,
}

impl DerivUniqueNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            has_derivative_unique: kernel.name_str(creal, "hasDerivative_unique"),
        }
    }
}
