//! **`CReal.pow` and the geometric series over ℝ.**
//!
//! ## The convention, matched to `Nat`/`Int`/`Complex`
//!
//! `CReal.pow` is structural `Nat.rec` on the exponent, matching
//! `Int.pow`'s and `Complex.pow`'s own convention exactly
//! (`int_prelude/defs.rs::declare_pow`, `complex.rs::declare_pow`): `pow x
//! Nat.zero ≡ one`, `pow x (Nat.succ j) ≡ mul (pow x j) x` — recursion on
//! the exponent, the recursive factor `mul (pow x j) x` with the fresh copy
//! on the **right** and the inductive value on the **left**. This is the
//! eighth carrier to match this convention; nothing here invents a ninth.
//!
//! `pow_zero`/`pow_succ` close by `Eq.refl` alone, exactly `Complex.pow_zero`/
//! `_succ` do: `pow`'s `Nat.rec` application ι-reduces to the literal term
//! (`one`, or `mul (pow x j) x`) directly, with no `CReal.mul` internals ever
//! unfolded to get there. Every other law here **does** need `Equiv`, never
//! `Eq`: `CReal.Equiv` is a defined `Prop` relation and nothing rewrites
//! under `pow` for free, and `funext` is unavailable.
//!
//! ## The missing distributivity direction
//!
//! `CReal.left_distrib` is `mul x (add y z) ~ add (mul x y) (mul x z)` — the
//! sum has to sit in the multiplicand's **right** slot. [`mul_sub_one_geom`]
//! needs to expand `mul (add one (neg x)) xⁿ`, where the sum is on the
//! **left**, so this file uses the missing direction
//! ([`right_distrib`](super::ring_helpers::right_distrib), shared with
//! `creal/derivative.rs` in `creal/ring_helpers.rs` since both built it
//! independently and identically) from `mul_comm` plus `left_distrib`, and
//! the companion `neg (mul x y) ~ mul (neg x) y` ([`neg_mul_left`]) by the
//! same "any right-additive-inverse partner of `mul x y` under `add` **is**
//! `neg (mul x y)`" argument `creal/series.rs::neg_add` uses for `neg(add a
//! b)` — reused here as the general uniqueness step ([`neg_unique`]) rather
//! than re-derived, since `series.rs`'s copy is private to that module.
//!
//! ## `mul_sub_one_geom`: multiplied through, and why
//!
//! [`declare_mul_sub_one_geom`] states `(1 − x) · Σ_{k<n} xᵏ ~ 1 − xⁿ` —
//! multiplied through, **not** `Σ xᵏ ~ (1−xⁿ)/(1−x)`. The quotient form needs
//! `inv (1 − x)` with a *witnessed* `PosBound`, which no theorem can supply
//! for an arbitrary `x` (nothing here knows `1 − x` is apart from zero), and
//! reaching it from `x ≁ 1` would need Markov's principle, which this kernel
//! neither proves nor assumes. The multiplied form holds for **every** `x`,
//! including `x ~ 1`, where the quotient form is meaningless. This mirrors
//! `Complex.mul_sub_one_geom`'s own decision exactly
//! (`complex.rs::declare_mul_sub_one_geom`) — the only difference is that
//! `Complex` closes its final ring identity with the `ring` decision
//! procedure (`complex.rs::ring_law_proof`), which `CReal` has no analogue
//! of, so the identity is closed by hand here instead
//! ([`right_distrib`]/[`neg_mul_left`] plus one 4-term telescoping
//! cancellation, [`telescope_cancel`]).
//!
//! ## `geom_sum_bounded`: named for what it proves
//!
//! [`declare_geom_sum_bounded`] is `(1 − x) · Σ_{k<n} xᵏ ≤ 1`, from
//! [`mul_sub_one_geom`] plus [`declare_pow_nonneg`] — **not** a bound on the
//! partial sum `Σ xᵏ` itself, which would need `inv` and a witnessed modulus
//! exactly as the quotient form of `mul_sub_one_geom` would. It needs only
//! `0 ≤ x` (to get `0 ≤ xⁿ`, hence `1 − xⁿ ≤ 1`) — **not** `x ≤ 1`, which a
//! reader might expect from "the geometric series is bounded on `[0,1]`": for
//! `x > 1` the multiplier `1 − x` is negative and the product is bounded by
//! `1` even more trivially. The hypothesis that would be needed for a bound
//! on `Σ xᵏ` alone (rather than on `(1−x)·Σ xᵏ`) does not appear in this
//! statement because this statement does not reach that claim.

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, DERIVED_HEIGHT, clt, creal_ty, equiv};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit `CReal.pow`, its defining equations, additivity, `Equiv`-congruence,
/// the two monotonicity facts every convergence-rate argument needs, the
/// geometric series identity, and its boundedness corollary.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_power(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_pow(d, p)?;
    declare_pow_equations(d, p)?;
    declare_pow_add(d, p)?;
    declare_pow_congr(d, p)?;
    declare_pow_nonneg(d, p)?;
    declare_pow_le_one(d, p)?;
    declare_mul_sub_one_geom(d, p)?;
    declare_geom_sum_bounded(d, p)?;
    declare_pow_le_pow_of_le_one(d, p)?;
    declare_mul_sub_one_geom_tail(d, p)?;
    declare_geom_tail_bounded(d, p)?;
    declare_one_le_pow_of_one_le(d, p)?;
    declare_pow_le_pow_of_one_le(d, p)?;
    declare_pow_pos(d, p)?;
    declare_pow_succ_lt_one(d, p)?;
    declare_pow_succ_gt_one(d, p)?;
    declare_not_apart_one_of_pow_succ_eq_one(d, p)
}

// --- small local term builders ----------------------------------------------

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

/// `Eq.{1} CReal a b`.
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// Chain `Equiv start …` through `(next, step)` pairs, rebuilt here (private
/// to every module that needs it, `series.rs::echain` included) rather than
/// imported.
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

/// `Equiv (neg zero) zero`, as a proof term — rebuilt from `add_zero`/
/// `add_comm`/`add_neg`, exactly `series.rs::neg_zero_equiv` (private there).
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // add nz zero ~ nz
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// Given `f_proof : Equiv (add s t) zero`, produce `Equiv (neg s) t` — "any
/// right-additive-inverse partner of `s` is `neg s`". This is the general
/// uniqueness step `series.rs::neg_add`'s second half already performs for
/// the specific witness `t := (neg a)+(neg b)`; lifted here to take `t` as a
/// parameter since that copy is private to `series.rs`.
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    s: ExprId,
    t: ExprId,
    f_proof: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let ns = cneg(d, p, s);

    // neg s ~ add(neg s) zero
    let step_a_target = cadd(d, p, ns, zero_c);
    let step_a = {
        let h = d.lemma(p.add_zero, &[ns]); // step_a_target ~ ns
        d.lemma(p.equiv_symm, &[step_a_target, ns, h]) // ns ~ step_a_target
    };

    // add(neg s) zero ~ add(neg s)(add s t)
    let st = cadd(d, p, s, t);
    let step_b_target = cadd(d, p, ns, st);
    let step_b = {
        let f_symm = d.lemma(p.equiv_symm, &[st, zero_c, f_proof]); // zero ~ add s t
        let refl_ns = d.lemma(p.equiv_refl, &[ns]);
        d.lemma(p.add_congr, &[ns, ns, zero_c, st, refl_ns, f_symm])
    };

    // add(neg s)(add s t) ~ add(add(neg s) s) t
    let ns_s = cadd(d, p, ns, s);
    let step_c_target = cadd(d, p, ns_s, t);
    let step_c = {
        let assoc = d.lemma(p.add_assoc, &[ns, s, t]); // step_c_target ~ step_b_target
        d.lemma(p.equiv_symm, &[step_c_target, step_b_target, assoc])
    };

    // add(add(neg s) s) t ~ add zero t
    let step_d_target = cadd(d, p, zero_c, t);
    let step_d = {
        let x = {
            let comm = d.lemma(p.add_comm, &[ns, s]); // ns_s ~ add s ns
            let s_ns = cadd(d, p, s, ns);
            let negl = d.lemma(p.add_neg, &[s]); // add s ns ~ zero
            d.lemma(p.equiv_trans, &[ns_s, s_ns, zero_c, comm, negl])
        };
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(p.add_congr, &[ns_s, zero_c, t, t, x, refl_t])
    };

    // add zero t ~ t
    let t_zero = cadd(d, p, t, zero_c);
    let step_e = {
        let comm = d.lemma(p.add_comm, &[zero_c, t]); // step_d_target ~ t_zero
        let collapse = d.lemma(p.add_zero, &[t]); // t_zero ~ t
        d.lemma(p.equiv_trans, &[step_d_target, t_zero, t, comm, collapse])
    };

    echain(
        d,
        p,
        ns,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (t, step_e),
        ],
    )
}

/// `Equiv (mul zero b) zero` — `mul_zero` reversed through `mul_comm`
/// (`mul_zero` itself has `zero` on the **right**).
fn mul_zero_left(d: &mut IntDev<'_>, p: CRealPrelude, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let zb = cmul(d, p, zero_c, b);
    let bz = cmul(d, p, b, zero_c);
    let h1 = d.lemma(p.mul_comm, &[zero_c, b]); // zb ~ bz
    let h2 = d.lemma(p.mul_zero, &[b]); // bz ~ zero
    echain(d, p, zb, &[(bz, h1), (zero_c, h2)])
}

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))` — the missing
/// distributivity direction, the sum on the **left** of the product.
/// `CReal.left_distrib` only distributes a sum on the right; this is built
/// from it plus `mul_comm` on all three products, exactly the way
/// `series.rs`'s local helpers are built from the declared laws rather than
/// declared themselves.
/// `Equiv (neg (mul a b)) (mul (neg a) b)` — additive inverse on the left of
/// a product, via [`right_distrib`] and [`neg_unique`]: `mul a b` and
/// `mul (neg a) b` sum to `mul zero b ~ zero` (`right_distrib` at `add a (neg
/// a) ~ zero`, then [`mul_zero_left`]), so `mul (neg a) b` is *a*
/// right-additive-inverse partner of `mul a b`, hence — by [`neg_unique`] —
/// *the* one.
fn neg_mul_left(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cmul(d, p, a, b);
    let nab = cmul(d, p, na, b);
    let zero_c = czero(d, p);

    // right_distrib(a, na, b) : Equiv (mul (add a na) b) (add ab nab)
    let s1 = right_distrib(d, p, a, na, b);
    let add_a_na = cadd(d, p, a, na);
    let sum_expr = cmul(d, p, add_a_na, b);

    let h_add_neg = d.lemma(p.add_neg, &[a]); // add a na ~ zero
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let h_congr = d.lemma(p.mul_congr, &[add_a_na, zero_c, b, b, h_add_neg, refl_b]);
    // h_congr : sum_expr ~ mul zero b
    let mzb = cmul(d, p, zero_c, b);
    let h_mzb_zero = mul_zero_left(d, p, b); // mzb ~ zero

    // sum_expr ~ zero
    let sum_zero = echain(d, p, sum_expr, &[(mzb, h_congr), (zero_c, h_mzb_zero)]);

    // f_proof : Equiv (add ab nab) zero, from sum_target ~ sum_expr ~ zero.
    let sum_target = cadd(d, p, ab, nab);
    let s1_symm = d.lemma(p.equiv_symm, &[sum_expr, sum_target, s1]); // sum_target ~ sum_expr
    let f_proof = d.lemma(
        p.equiv_trans,
        &[sum_target, sum_expr, zero_c, s1_symm, sum_zero],
    );

    // neg_unique(ab, nab, f_proof) : Equiv (neg ab) nab
    neg_unique(d, p, ab, nab, f_proof)
}

/// `Equiv (add (add a (neg z)) (add z (neg b))) (add a (neg b))` — the
/// 4-term telescoping cancellation `(A−Z)+(Z−B) ~ A−B`, the algebraic core
/// of [`declare_mul_sub_one_geom`]'s successor step (the `Z`'s cancel).
fn telescope_cancel(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    z: ExprId,
    b: ExprId,
) -> ExprId {
    let nz = cneg(d, p, z);
    let nb = cneg(d, p, b);
    let a_nz = cadd(d, p, a, nz);
    let z_nb = cadd(d, p, z, nb);
    let start = cadd(d, p, a_nz, z_nb);

    // start ~ a + (nz + (z + nb))   [add_assoc a nz (z+nb)]
    let nz_znb = cadd(d, p, nz, z_nb);
    let s1 = cadd(d, p, a, nz_znb);
    let h1 = d.lemma(p.add_assoc, &[a, nz, z_nb]);

    // nz + (z + nb) ~ (nz + z) + nb   [add_assoc nz z nb, reversed]
    let nz_z = cadd(d, p, nz, z);
    let nz_z_nb = cadd(d, p, nz_z, nb);
    let s2 = cadd(d, p, a, nz_z_nb);
    let h2_inner = {
        let assoc = d.lemma(p.add_assoc, &[nz, z, nb]); // nz_z_nb ~ nz_znb
        d.lemma(p.equiv_symm, &[nz_z_nb, nz_znb, assoc]) // nz_znb ~ nz_z_nb
    };
    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let h2 = d.lemma(p.add_congr, &[a, a, nz_znb, nz_z_nb, refl_a, h2_inner]);

    // (nz + z) ~ zero
    let zero_c = czero(d, p);
    let h_cancel = {
        let comm = d.lemma(p.add_comm, &[nz, z]); // nz_z ~ (z + nz)
        let z_nz = cadd(d, p, z, nz);
        let negr = d.lemma(p.add_neg, &[z]); // z + nz ~ zero
        d.lemma(p.equiv_trans, &[nz_z, z_nz, zero_c, comm, negr])
    };

    // (nz+z) + nb ~ zero + nb
    let zero_nb = cadd(d, p, zero_c, nb);
    let s3 = cadd(d, p, a, zero_nb);
    let refl_nb = d.lemma(p.equiv_refl, &[nb]);
    let h3_inner = d.lemma(p.add_congr, &[nz_z, zero_c, nb, nb, h_cancel, refl_nb]);
    let h3 = d.lemma(p.add_congr, &[a, a, nz_z_nb, zero_nb, refl_a, h3_inner]);

    // zero + nb ~ nb
    let h4_inner = {
        let comm = d.lemma(p.add_comm, &[zero_c, nb]); // zero_nb ~ (nb + zero)
        let nb_zero = cadd(d, p, nb, zero_c);
        let collapse = d.lemma(p.add_zero, &[nb]); // nb_zero ~ nb
        d.lemma(p.equiv_trans, &[zero_nb, nb_zero, nb, comm, collapse])
    };
    let target = cadd(d, p, a, nb);
    let h4 = d.lemma(p.add_congr, &[a, a, zero_nb, nb, refl_a, h4_inner]);

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (target, h4)])
}

// --- `CReal.pow` -------------------------------------------------------------

/// `CReal.pow : CReal → Nat → CReal`, by structural `Nat.rec` on the
/// exponent — see the module documentation for the convention.
fn declare_pow(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = d.kernel().const_(p.one, vec![]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = d.const_app(p.mul, &[ih, x]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pow,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 42),
    })
}

/// `CReal.pow_zero`/`CReal.pow_succ`: the defining equations of
/// [`declare_pow`], each closed by `Eq.refl` alone since `pow`'s `Nat.rec`
/// application ι-reduces on both minor premises — exactly `Complex.pow_zero`/
/// `_succ`'s own shape.
fn declare_pow_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    // pow_zero : ∀ x, Eq CReal (pow x Nat.zero) one.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.pow, &[x, zero_n]);
        let one = d.kernel().const_(p.one, vec![]);
        let stmt = creal_eq(d, p, lhs, one);
        let proof = creal_eq_refl(d, p, one);
        let value = d.lam_fv(x_fv, carrier, proof);
        let ty = d.pi_fv(x_fv, carrier, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // pow_succ : ∀ x (m : Nat), Eq CReal (pow x (Nat.succ m)) (mul (pow x m) x).
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let sm = d.succ(m);
        let lhs = d.const_app(p.pow, &[x, sm]);
        let pm = d.const_app(p.pow, &[x, m]);
        let rhs = d.const_app(p.mul, &[pm, x]);
        let stmt_inner = creal_eq(d, p, lhs, rhs);
        let proof_inner = creal_eq_refl(d, p, rhs);

        let ty = {
            let inner = d.pi_fv(m_fv, nat, stmt_inner);
            d.pi_fv(x_fv, carrier, inner)
        };
        let value = {
            let inner = d.lam_fv(m_fv, nat, proof_inner);
            d.lam_fv(x_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.pow_add : ∀ x (m n : Nat), Equiv (pow x (Nat.add m n)) (mul (pow x
/// m) (pow x n))`. Induction on `n`, mirroring `Complex.pow_add`'s own proof
/// shape (`complex.rs::declare_pow_add`) verbatim, over `CReal.Equiv`.
fn declare_pow_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let sum = NatOps::add(d, m, v);
        let lhs = d.const_app(p.pow, &[x, sum]);
        let pow_m = d.const_app(p.pow, &[x, m]);
        let pow_v = d.const_app(p.pow, &[x, v]);
        let rhs = d.const_app(p.mul, &[pow_m, pow_v]);
        equiv(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let pow_m = d.const_app(p.pow, &[x, m]);
            let one = d.kernel().const_(p.one, vec![]);
            let product = d.const_app(p.mul, &[pow_m, one]);
            let h = d.lemma(p.mul_one, &[pow_m]); // Equiv (mul pow_m one) pow_m
            d.lemma(p.equiv_symm, &[product, pow_m, h])
        },
        &|d, j, ih| {
            let pow_m = d.const_app(p.pow, &[x, m]);
            let pow_j = d.const_app(p.pow, &[x, j]);
            let sum_mj = NatOps::add(d, m, j);
            let pow_sum = d.const_app(p.pow, &[x, sum_mj]);
            let start = d.const_app(p.mul, &[pow_sum, x]);

            let ih_applied = d.const_app(p.mul, &[pow_m, pow_j]);
            let refl_x = d.lemma(p.equiv_refl, &[x]);
            let h_ih = d.lemma(p.mul_congr, &[pow_sum, ih_applied, x, x, ih, refl_x]);
            let after_ih = d.const_app(p.mul, &[ih_applied, x]);

            let h_assoc = d.lemma(p.mul_assoc, &[pow_m, pow_j, x]);
            let inner = d.const_app(p.mul, &[pow_j, x]);
            let end = d.const_app(p.mul, &[pow_m, inner]);

            d.lemma(p.equiv_trans, &[start, after_ih, end, h_ih, h_assoc])
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, carrier, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_congr : ∀ x y (n : Nat), Equiv x y → Equiv (pow x n) (pow y
/// n)`. Induction on `n`: the base case is `Equiv one one` up to `pow`'s own
/// ι-reduction at `Nat.zero` (both sides), the step is [`CRealPrelude::mul_congr`]
/// against the outer hypothesis and the inductive hypothesis.
fn declare_pow_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        let py = d.const_app(p.pow, &[y, v]);
        equiv(d, p, px, py)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.kernel().const_(p.one, vec![]);
            d.lemma(p.equiv_refl, &[one])
        },
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            let py_j = d.const_app(p.pow, &[y, j]);
            d.lemma(p.mul_congr, &[px_j, py_j, x, y, ih, h])
        },
        n,
    );

    let hyp = equiv(d, p, x, y);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h = d.arrow(hyp, inner);
        let with_y = d.pi_fv(y_fv, carrier, with_h);
        d.pi_fv(x_fv, carrier, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h = d.lam_fv(h_fv, hyp, inner);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_congr,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.powerSeriesTerm` -- the power series term family, its
// `Equiv`-congruence, and the coefficient-boundedness domination package.
// ---------------------------------------------------------------------------

fn cpow(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.pow, &[x, n])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

/// `CReal.powerSeriesTerm : (Nat → CReal) → Nat → CReal → CReal :=
/// fun c j x => mul (c j) (pow x j)` — the `j`-th term of the power series
/// with coefficients `c`, evaluated at `x`. A bare `Definition`, asserting
/// nothing. `pow`'s own height is `DERIVED_HEIGHT + 42`
/// ([`declare_pow`]); this sits one above it, matching this development's
/// own convention of giving a thin wrapper a height just past what it
/// unfolds to.
pub(super) fn declare_power_series_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let cj = d.apply(c, &[j]);
    let pow_x_j = cpow(d, p, x, j);
    let body = cmul(d, p, cj, pow_x_j);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        let with_j = d.lam_fv(j_fv, nat, with_x);
        d.lam_fv(c_fv, coeff_ty, with_j)
    };
    let ty = {
        let with_x = d.arrow(carrier, carrier);
        let with_j = d.arrow(nat, with_x);
        d.arrow(coeff_ty, with_j)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.power_series_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 43),
    })
}

/// `CReal.powerSeriesTerm_congr : ∀ c j p q, Equiv p q → Equiv
/// (powerSeriesTerm c j p) (powerSeriesTerm c j q)` — from
/// [`CRealPrelude::pow_congr`] (`Equiv p q → Equiv (pow p j) (pow q j)`) and
/// [`CRealPrelude::mul_congr`] against `Equiv (c j) (c j)` reflexivity on
/// the left factor. No induction: `pow_congr` already did the induction on
/// the exponent.
pub(super) fn declare_power_series_term_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let heq_ty = equiv(d, p, pp, qq);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    let cj = d.apply(c, &[j]);
    let refl_cj = d.lemma(p.equiv_refl, &[cj]);
    let pow_congr_proof = d.lemma(p.pow_congr, &[pp, qq, heq, j]);
    let proof = d.lemma(p.mul_congr, &[cj, cj, pp, qq, refl_cj, pow_congr_proof]);

    let value = {
        let with_heq = d.lam_fv(heq_fv, heq_ty, proof);
        let with_qq = d.lam_fv(qq_fv, carrier, with_heq);
        let with_pp = d.lam_fv(pp_fv, carrier, with_qq);
        let with_j = d.lam_fv(j_fv, nat, with_pp);
        d.lam_fv(c_fv, coeff_ty, with_j)
    };
    let ty = {
        let pst_c_j_p = d.const_app(p.power_series_term, &[c, j, pp]);
        let pst_c_j_q = d.const_app(p.power_series_term, &[c, j, qq]);
        let concl = equiv(d, p, pst_c_j_p, pst_c_j_q);
        let inner = d.arrow(heq_ty, concl);
        let with_qq = d.pi_fv(qq_fv, carrier, inner);
        let with_pp = d.pi_fv(pp_fv, carrier, with_qq);
        let with_j = d.pi_fv(j_fv, nat, with_pp);
        d.pi_fv(c_fv, coeff_ty, with_j)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series_term_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.powerSeriesTerm_abs_le : ∀ c M, (∀ j, le (abs (c j)) M) → ∀ x r,
/// le zero x → le x r → ∀ j, le (abs (powerSeriesTerm c j x)) (mul M (pow r
/// j))`. See the field documentation on
/// [`CRealPrelude::power_series_term_abs_le`] for the route: base
/// monotonicity of `pow` plus a two-sided `abs_le` (mirroring
/// `creal/monotone.rs`'s own private `abs_le_of_nonneg_le`, reproduced here
/// since that helper is not `pub(super)`) plus `abs_mul_le_of_bounds`. No
/// induction on `j` is needed — everything is a direct combination for an
/// arbitrary `j`.
pub(super) fn declare_power_series_term_abs_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let coeff_ty = d.arrow(nat, carrier);
    let zero_c = czero(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hbound_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let cj = d.apply(c, &[j]);
        let abs_cj = cabs(d, p, cj);
        let body = cle(d, p, abs_cj, m);
        d.pi_fv(j_fv, nat, body)
    };
    let hbound_fv = d.fresh_fvar();
    let hbound = d.kernel().fvar(hbound_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hx0_ty = cle(d, p, zero_c, x);
    let hx0_fv = d.fresh_fvar();
    let hx0 = d.kernel().fvar(hx0_fv);
    let hxr_ty = cle(d, p, x, r);
    let hxr_fv = d.fresh_fvar();
    let hxr = d.kernel().fvar(hxr_fv);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let cj = d.apply(c, &[j]);
    let hcj_le_m = d.apply(hbound, &[j]);

    let pow_x_j = cpow(d, p, x, j);
    let pow_r_j = cpow(d, p, r, j);

    // h_le : le pow_x_j pow_r_j.
    let h_le = d.lemma(p.pow_le_pow_of_base_le, &[x, r, hx0, hxr, j]);

    // hv_nonneg : le zero pow_x_j; h_bound_nonneg : le zero pow_r_j (via
    // le zero r, from le_trans on hx0/hxr).
    let hv_nonneg = d.lemma(p.pow_nonneg, &[x, hx0, j]);
    let hr0 = d.lemma(p.le_trans, &[zero_c, x, r, hx0, hxr]);
    let h_bound_nonneg = d.lemma(p.pow_nonneg, &[r, hr0, j]);

    // abs_le_of_nonneg_le route: le (neg pow_x_j) pow_r_j, from
    // neg_le_neg + neg_zero_equiv + le_trans.
    let neg_pow_x_j = cneg(d, p, pow_x_j);
    let neg_zero_c = cneg(d, p, zero_c);
    let step1 = d.lemma(p.neg_le_neg, &[zero_c, pow_x_j, hv_nonneg]);
    let nz_eq = neg_zero_equiv(d, p);
    let refl_npxj = d.lemma(p.equiv_refl, &[neg_pow_x_j]);
    let npxj_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow_x_j,
            neg_pow_x_j,
            neg_zero_c,
            zero_c,
            refl_npxj,
            nz_eq,
            step1,
        ],
    );
    let npxj_le_pow_r_j = d.lemma(p.le_trans, &[neg_pow_x_j, zero_c, pow_r_j, npxj_le_zero, h_bound_nonneg]);
    let abs_pow_x_j_le_pow_r_j = d.lemma(p.abs_le, &[pow_x_j, pow_r_j, h_le, npxj_le_pow_r_j]);

    let concl_proof = d.lemma(
        p.abs_mul_le_of_bounds,
        &[cj, pow_x_j, m, pow_r_j, hcj_le_m, abs_pow_x_j_le_pow_r_j],
    );

    let value = {
        let with_j = d.lam_fv(j_fv, nat, concl_proof);
        let with_hxr = d.lam_fv(hxr_fv, hxr_ty, with_j);
        let with_hx0 = d.lam_fv(hx0_fv, hx0_ty, with_hxr);
        let with_r = d.lam_fv(r_fv, carrier, with_hx0);
        let with_x = d.lam_fv(x_fv, carrier, with_r);
        let with_hbound = d.lam_fv(hbound_fv, hbound_ty, with_x);
        let with_m = d.lam_fv(m_fv, carrier, with_hbound);
        d.lam_fv(c_fv, coeff_ty, with_m)
    };
    let ty = {
        let pst = d.const_app(p.power_series_term, &[c, j, x]);
        let mul_m_pow_r_j = cmul(d, p, m, pow_r_j);
        let abs_pst = cabs(d, p, pst);
        let concl_j = cle(d, p, abs_pst, mul_m_pow_r_j);
        let with_j = d.pi_fv(j_fv, nat, concl_j);
        let with_hxr = d.arrow(hxr_ty, with_j);
        let with_hx0 = d.arrow(hx0_ty, with_hxr);
        let with_r = d.pi_fv(r_fv, carrier, with_hx0);
        let with_x = d.pi_fv(x_fv, carrier, with_r);
        let with_hbound = d.arrow(hbound_ty, with_x);
        let with_m = d.pi_fv(m_fv, carrier, with_hbound);
        d.pi_fv(c_fv, coeff_ty, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series_term_abs_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_nonneg : ∀ x n, le zero x → le zero (pow x n)`. Induction on
/// `n`: the base case is `le_of_lt zero_lt_one` up to `pow`'s ι-reduction,
/// the step is [`CRealPrelude::mul_nonneg`] against the inductive hypothesis
/// and the outer `le zero x` hypothesis.
fn declare_pow_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        let zero_c = czero(d, p);
        cle(d, p, zero_c, px)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let one = d.kernel().const_(p.one, vec![]);
            let lt_witness = d.lemma(p.zero_lt_one, &[]);
            d.lemma(p.le_of_lt, &[zero_c, one, lt_witness])
        },
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            d.lemma(p.mul_nonneg, &[px_j, x, ih, h])
        },
        n,
    );

    let hyp = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h = d.arrow(hyp, inner);
        d.pi_fv(x_fv, carrier, with_h)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h = d.lam_fv(h_fv, hyp, inner);
        d.lam_fv(x_fv, carrier, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_le_one : ∀ x n, le zero x → le x one → le (pow x n) one`.
/// Induction on `n`: the base case is `le_refl one` up to `pow`'s
/// ι-reduction. The step multiplies the inductive hypothesis `pow x j ≤ one`
/// by the nonnegative `x` on the **left**
/// ([`CRealPrelude::mul_le_mul_of_nonneg_left`], giving `x·(pow x j) ≤ x·one
/// ~ x`), chains through `x ≤ one` ([`CRealPrelude::le_trans`]), and commutes
/// the product back into `pow`'s own right-recursive shape
/// (`mul_comm`+`le_congr`).
fn declare_pow_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        let one = d.kernel().const_(p.one, vec![]);
        cle(d, p, px, one)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let one = d.kernel().const_(p.one, vec![]);
            d.lemma(p.le_refl, &[one])
        },
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            let one = d.kernel().const_(p.one, vec![]);

            // h1_prod : le (mul x px_j) (mul x one)
            let h1_prod = d.lemma(p.mul_le_mul_of_nonneg_left, &[x, px_j, one, h0, ih]);
            let x_pxj = d.const_app(p.mul, &[x, px_j]);
            let x_one = d.const_app(p.mul, &[x, one]);

            // fold (mul x one) down to x
            let mul_one_x = d.lemma(p.mul_one, &[x]); // Equiv (mul x one) x
            let refl_x_pxj = d.lemma(p.equiv_refl, &[x_pxj]);
            let h_folded = d.lemma(
                p.le_congr,
                &[x_pxj, x_pxj, x_one, x, refl_x_pxj, mul_one_x, h1_prod],
            );
            // h_folded : le x_pxj x

            // chain with x ≤ one
            let h2 = d.lemma(p.le_trans, &[x_pxj, x, one, h_folded, h1]);
            // h2 : le x_pxj one

            // commute x_pxj into pxj_x = mul px_j x (pow's own shape)
            let pxj_x = d.const_app(p.mul, &[px_j, x]);
            let comm = d.lemma(p.mul_comm, &[px_j, x]); // Equiv pxj_x x_pxj
            let comm_symm = d.lemma(p.equiv_symm, &[pxj_x, x_pxj, comm]); // Equiv x_pxj pxj_x
            let refl_one = d.lemma(p.equiv_refl, &[one]);
            d.lemma(
                p.le_congr,
                &[x_pxj, pxj_x, one, one, comm_symm, refl_one, h2],
            )
        },
        n,
    );

    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let hyp1 = {
        let one = d.kernel().const_(p.one, vec![]);
        cle(d, p, x, one)
    };
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h1 = d.arrow(hyp1, inner);
        let with_h0 = d.arrow(hyp0, with_h1);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, inner);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_h1);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the geometric series identity over ℝ -----------------------------------

/// `λ k, pow x k`, shared between [`declare_mul_sub_one_geom`] and
/// [`declare_geom_sum_bounded`] so the two never drift into structurally
/// distinct (merely defeq) closures.
fn pow_fn(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.const_app(p.pow, &[x, i]);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `CReal.mul_sub_one_geom : ∀ x (n : Nat), Equiv (mul (add one (neg x))
/// (sumRange (fun k => pow x k) n)) (add one (neg (pow x n)))` — **the
/// geometric series identity**, `(1 − x) · Σ_{k<n} xᵏ = 1 − xⁿ`. See the
/// module documentation for why this is stated multiplied through rather
/// than as a quotient.
///
/// Induction on `n`, telescoping — mirroring `Complex.mul_sub_one_geom`'s own
/// proof shape (`complex.rs::declare_mul_sub_one_geom`), with the closing
/// ring identity built by hand ([`right_distrib`], [`neg_mul_left`],
/// [`telescope_cancel`]) in place of `Complex`'s `ring_law_proof`, which
/// `CReal` has no analogue of.
fn declare_mul_sub_one_geom(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = d.const_app(p.neg, &[x]);
    let a = d.const_app(p.add, &[one, neg_x]); // a = 1 - x

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let f = pow_fn(d, p, x);
        let sum = d.const_app(p.sum_range, &[f, v]);
        let lhs = d.const_app(p.mul, &[a, sum]);
        let pow_v = d.const_app(p.pow, &[x, v]);
        let neg_pow_v = d.const_app(p.neg, &[pow_v]);
        let rhs = d.const_app(p.add, &[one, neg_pow_v]);
        equiv(d, p, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // Goal, after ι on both `sumRange f zero` and `pow x zero`:
            // Equiv (mul a zero) (add one (neg one)).
            let zero_c = czero(d, p);
            let neg_one = d.const_app(p.neg, &[one]);
            let add_one_neg_one = d.const_app(p.add, &[one, neg_one]);
            let mul_a_zero = d.const_app(p.mul, &[a, zero_c]);

            let mul_zero_h = d.lemma(p.mul_zero, &[a]); // Equiv mul_a_zero zero_c
            let add_neg_h = d.lemma(p.add_neg, &[one]); // Equiv add_one_neg_one zero_c
            let sym = d.lemma(p.equiv_symm, &[add_one_neg_one, zero_c, add_neg_h]);
            d.lemma(
                p.equiv_trans,
                &[mul_a_zero, zero_c, add_one_neg_one, mul_zero_h, sym],
            )
        },
        &|d, j, ih| {
            // ih : Equiv (mul a (sumRange f j)) (add one (neg (pow x j)))
            let xn = d.const_app(p.pow, &[x, j]);
            let s_j = {
                let f = pow_fn(d, p, x);
                d.const_app(p.sum_range, &[f, j])
            };
            let extended = d.const_app(p.add, &[s_j, xn]);
            let start = d.const_app(p.mul, &[a, extended]);

            // start ~ distributed = add (mul a s_j) (mul a xn)  [left_distrib]
            let a_s_j = d.const_app(p.mul, &[a, s_j]);
            let a_xn = d.const_app(p.mul, &[a, xn]);
            let distributed = d.const_app(p.add, &[a_s_j, a_xn]);
            let h1 = d.lemma(p.left_distrib, &[a, s_j, xn]);

            // distributed ~ after_ih = add (add one (neg xn)) (mul a xn)
            //   [substitute ih into the first summand]
            let neg_xn = d.const_app(p.neg, &[xn]);
            let one_minus_xn = d.const_app(p.add, &[one, neg_xn]);
            let after_ih = d.const_app(p.add, &[one_minus_xn, a_xn]);
            let refl_a_xn = d.lemma(p.equiv_refl, &[a_xn]);
            let h2 = d.lemma(
                p.add_congr,
                &[a_s_j, one_minus_xn, a_xn, a_xn, ih, refl_a_xn],
            );

            // a_xn = mul (add one (neg x)) xn ~ add (mul one xn) (mul (neg x) xn)
            //      ~ add xn (neg (mul x xn))                    [right_distrib, then simplify]
            let x_xn = d.const_app(p.mul, &[x, xn]);
            let neg_x_xn = d.const_app(p.neg, &[x_xn]);
            let mul_one_xn = d.const_app(p.mul, &[one, xn]);
            let mul_negx_xn = d.const_app(p.mul, &[neg_x, xn]);
            let expanded = d.const_app(p.add, &[mul_one_xn, mul_negx_xn]);
            let h_rd = right_distrib(d, p, one, neg_x, xn);
            // h_rd : Equiv a_xn expanded

            // mul one xn ~ xn
            let h_one_xn = {
                let xn_one = d.const_app(p.mul, &[xn, one]);
                let comm = d.lemma(p.mul_comm, &[one, xn]); // mul_one_xn ~ xn_one
                let mo = d.lemma(p.mul_one, &[xn]); // xn_one ~ xn
                echain(d, p, mul_one_xn, &[(xn_one, comm), (xn, mo)])
            };

            // mul (neg x) xn ~ neg (mul x xn), from neg_mul_left's reverse direction
            let h_negx_xn = {
                let raw = neg_mul_left(d, p, x, xn); // Equiv (neg x_xn) mul_negx_xn
                d.lemma(p.equiv_symm, &[neg_x_xn, mul_negx_xn, raw])
                // Equiv mul_negx_xn neg_x_xn
            };

            let simplified = d.const_app(p.add, &[xn, neg_x_xn]);
            let h_simplify = d.lemma(
                p.add_congr,
                &[mul_one_xn, xn, mul_negx_xn, neg_x_xn, h_one_xn, h_negx_xn],
            );
            // h_simplify : expanded ~ simplified

            let h_a_xn = echain(d, p, a_xn, &[(expanded, h_rd), (simplified, h_simplify)]);
            // h_a_xn : Equiv a_xn simplified

            // after_ih ~ mid = add one_minus_xn simplified
            let mid = d.const_app(p.add, &[one_minus_xn, simplified]);
            let refl_omx = d.lemma(p.equiv_refl, &[one_minus_xn]);
            let h_mid = d.lemma(
                p.add_congr,
                &[
                    one_minus_xn,
                    one_minus_xn,
                    a_xn,
                    simplified,
                    refl_omx,
                    h_a_xn,
                ],
            );
            // h_mid : Equiv after_ih mid

            // mid ~ end = add one (neg (mul xn x))  [telescope_cancel, then commute
            // mul x xn -> mul xn x to match pow's own right-recursive shape]
            let xn_x = d.const_app(p.mul, &[xn, x]);
            let neg_xn_x = d.const_app(p.neg, &[xn_x]);
            let end = d.const_app(p.add, &[one, neg_xn_x]);
            let end_x_xn = d.const_app(p.add, &[one, neg_x_xn]);
            let h_telescope = telescope_cancel(d, p, one, xn, x_xn);
            // h_telescope : Equiv mid end_x_xn

            let x_xn_comm = d.lemma(p.mul_comm, &[x, xn]); // Equiv x_xn xn_x
            let neg_comm = d.lemma(p.neg_congr, &[x_xn, xn_x, x_xn_comm]); // Equiv neg_x_xn neg_xn_x
            let refl_one2 = d.lemma(p.equiv_refl, &[one]);
            let h_fix = d.lemma(
                p.add_congr,
                &[one, one, neg_x_xn, neg_xn_x, refl_one2, neg_comm],
            );
            // h_fix : Equiv end_x_xn end

            let h_end = d.lemma(p.equiv_trans, &[mid, end_x_xn, end, h_telescope, h_fix]);
            // h_end : Equiv mid end

            let h_final_mid = d.lemma(p.equiv_trans, &[after_ih, mid, end, h_mid, h_end]);
            // h_final_mid : Equiv after_ih end

            let h_start_distributed =
                d.lemma(p.equiv_trans, &[start, distributed, after_ih, h1, h2]);
            // h_start_distributed : Equiv start after_ih

            d.lemma(
                p.equiv_trans,
                &[start, after_ih, end, h_start_distributed, h_final_mid],
            )
            // Equiv start end
        },
        n,
    );

    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        d.pi_fv(x_fv, carrier, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        d.lam_fv(x_fv, carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sub_one_geom,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geom_sum_bounded : ∀ x n, le zero x → le (mul (add one (neg x))
/// (sumRange (fun k => pow x k) n)) one`. See the module documentation for
/// why `x ≤ one` is not a hypothesis here.
fn declare_geom_sum_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = d.const_app(p.neg, &[x]);
    let a = d.const_app(p.add, &[one, neg_x]);
    let f = pow_fn(d, p, x);
    let sum_n = d.const_app(p.sum_range, &[f, n]);
    let lhs = d.const_app(p.mul, &[a, sum_n]);
    let pow_n = d.const_app(p.pow, &[x, n]);

    // pow_nonneg's constructed type is `∀ x, le zero x → ∀ n, le zero (pow x
    // n)` (the hypothesis is bound BEFORE `n`, not after) — apply in that
    // order.
    // pow_nonneg x h n : le zero pow_n
    let h_nonneg = d.lemma(p.pow_nonneg, &[x, h, n]);

    // neg_le_neg zero pow_n h_nonneg : le (neg pow_n) (neg zero)
    let zero_c = czero(d, p);
    let h_negle = d.lemma(p.neg_le_neg, &[zero_c, pow_n, h_nonneg]);
    let neg_pow_n = d.const_app(p.neg, &[pow_n]);
    let neg_zero = d.const_app(p.neg, &[zero_c]);

    // le (neg pow_n) zero, via neg_zero ~ zero
    let h_negzero = neg_zero_equiv(d, p);
    let refl_negpn = d.lemma(p.equiv_refl, &[neg_pow_n]);
    let h_negle_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow_n, neg_pow_n, neg_zero, zero_c, refl_negpn, h_negzero, h_negle,
        ],
    );
    // h_negle_zero : le neg_pow_n zero

    // add_le_add one one neg_pow_n zero (le_refl one) h_negle_zero
    //   : le (add one neg_pow_n) (add one zero)
    let h_refl_one = d.lemma(p.le_refl, &[one]);
    let h_add = d.lemma(
        p.add_le_add,
        &[one, one, neg_pow_n, zero_c, h_refl_one, h_negle_zero],
    );
    let one_minus_pn = d.const_app(p.add, &[one, neg_pow_n]);
    let one_plus_zero = d.const_app(p.add, &[one, zero_c]);

    // fold (add one zero) down to one
    let h_addzero = d.lemma(p.add_zero, &[one]);
    let refl_ompn = d.lemma(p.equiv_refl, &[one_minus_pn]);
    let h_bound = d.lemma(
        p.le_congr,
        &[
            one_minus_pn,
            one_minus_pn,
            one_plus_zero,
            one,
            refl_ompn,
            h_addzero,
            h_add,
        ],
    );
    // h_bound : le one_minus_pn one

    // transport across mul_sub_one_geom : Equiv lhs one_minus_pn
    let h_geom = d.lemma(p.mul_sub_one_geom, &[x, n]);
    let h_geom_symm = d.lemma(p.equiv_symm, &[lhs, one_minus_pn, h_geom]);
    // h_geom_symm : Equiv one_minus_pn lhs
    let refl_one = d.lemma(p.equiv_refl, &[one]);
    let proof_inner = d.lemma(
        p.le_congr,
        &[one_minus_pn, lhs, one, one, h_geom_symm, refl_one, h_bound],
    );

    let hyp = cle(d, p, zero_c, x);
    let stmt_inner = cle(d, p, lhs, one);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h = d.arrow(hyp, inner);
        d.pi_fv(x_fv, carrier, with_h)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h = d.lam_fv(h_fv, hyp, inner);
        d.lam_fv(x_fv, carrier, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_sum_bounded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- monotonicity of the powers on `[0,1]`, and the geometric tail ---------

/// `CReal.pow_le_pow_of_le_one : ∀ x, le zero x → le x one → ∀ n, le (pow x
/// (Nat.succ n)) (pow x n)`. Not an induction: for a fixed `n`, `pow`'s own
/// ι-reduction identifies `pow x (succ n)` with `mul (pow x n) x`
/// definitionally, so [`CRealPrelude::mul_le_mul_of_nonneg_left`] at `a := pow
/// x n` (nonnegative via [`declare_pow_nonneg`]) against the outer `x ≤ one`
/// gives `mul (pow x n) x ≤ mul (pow x n) one`, and
/// [`CRealPrelude::mul_one`] folds the right side back to `pow x n`.
fn declare_pow_le_pow_of_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pow_n = d.const_app(p.pow, &[x, n]);
    let one = d.kernel().const_(p.one, vec![]);

    let h_nonneg = d.lemma(p.pow_nonneg, &[x, h0, n]);
    let base_le = d.lemma(p.mul_le_mul_of_nonneg_left, &[pow_n, x, one, h_nonneg, h1]);
    // base_le : le (mul pow_n x) (mul pow_n one)
    let mul_pn_x = d.const_app(p.mul, &[pow_n, x]);
    let mul_pn_one = d.const_app(p.mul, &[pow_n, one]);
    let mul_one_h = d.lemma(p.mul_one, &[pow_n]); // Equiv mul_pn_one pow_n
    let refl_lhs = d.lemma(p.equiv_refl, &[mul_pn_x]);
    let proof_inner = d.lemma(
        p.le_congr,
        &[
            mul_pn_x, mul_pn_x, mul_pn_one, pow_n, refl_lhs, mul_one_h, base_le,
        ],
    );
    // proof_inner : le mul_pn_x pow_n, defeq to le (pow x (succ n)) pow_n

    let sn = d.succ(n);
    let pow_sn = d.const_app(p.pow, &[x, sn]);
    let hyp0 = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let hyp1 = cle(d, p, x, one);
    let stmt_inner = cle(d, p, pow_sn, pow_n);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h1 = d.arrow(hyp1, inner);
        let with_h0 = d.arrow(hyp0, with_h1);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, inner);
        let with_h0 = d.lam_fv(h0_fv, hyp0, with_h1);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_pow_of_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (add (add a b) (neg a)) b` — group cancellation, rebuilt here since
/// `series.rs::cancel_right` is private to that module.
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, na);

    let ba = cadd(d, p, b, a);
    let comm1 = d.lemma(p.add_comm, &[a, b]); // ab ~ ba
    let refl_na = d.lemma(p.equiv_refl, &[na]);
    let s1 = cadd(d, p, ba, na);
    let h1 = d.lemma(p.add_congr, &[ab, ba, na, na, comm1, refl_na]);

    let a_na = cadd(d, p, a, na);
    let s2 = cadd(d, p, b, a_na);
    let h2 = d.lemma(p.add_assoc, &[b, a, na]); // s1 ~ s2

    let zero_c = czero(d, p);
    let h_an = d.lemma(p.add_neg, &[a]); // a_na ~ zero
    let refl_b = d.lemma(p.equiv_refl, &[b]);
    let s3 = cadd(d, p, b, zero_c);
    let h3 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, h_an]); // s2 ~ s3

    let h4 = d.lemma(p.add_zero, &[b]); // s3 ~ b

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (b, h4)])
}

/// `λ k, pow x (add m k)` — the shifted power sequence
/// [`declare_mul_sub_one_geom_tail`] needs, matching `sumRange_split`'s own
/// internal construction (`series.rs::shifted_fn`) up to beta, which is all
/// the kernel's own defeq check needs when the two are combined.
fn shifted_pow_fn(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId, x: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.const_app(p.pow, &[x, mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Equiv (mul a_ (sumRange (shifted_pow_fn m x) n)) (add base (neg (pow x
/// (add m n))))`, for fixed `x`, `m`, `a_ := add one (neg x)` and `base :=
/// pow x m` — the shifted-partial-sum shape [`declare_mul_sub_one_geom_tail`]
/// proves by induction on `n`, then converts.
///
/// This is [`declare_mul_sub_one_geom`]'s own successor-step algebra,
/// verbatim, with the accumulator generalised from the constant `one` to the
/// caller-supplied `base` and `pow x j` generalised to `pow x (add m j)` —
/// every step below that manipulates the *ring identity* `mul (add one (neg
/// x)) xn ~ add xn (neg (mul x xn))` ([`right_distrib`], [`neg_mul_left`],
/// [`telescope_cancel`]) is unchanged, because that identity never mentions
/// the accumulator.
fn mul_a_shifted_sum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    m: ExprId,
    a_: ExprId,
    base: ExprId,
    n: ExprId,
) -> ExprId {
    let nat_add = d.prelude().add;

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let f = shifted_pow_fn(d, p, m, x);
        let sum = d.const_app(p.sum_range, &[f, v]);
        let lhs = d.const_app(p.mul, &[a_, sum]);
        let mv = d.const_app(nat_add, &[m, v]);
        let pow_mv = d.const_app(p.pow, &[x, mv]);
        let neg_pow_mv = d.const_app(p.neg, &[pow_mv]);
        let rhs = d.const_app(p.add, &[base, neg_pow_mv]);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            let zero_c = czero(d, p);
            let neg_base = cneg(d, p, base);
            let add_base_neg_base = cadd(d, p, base, neg_base);
            let mul_a_zero = d.const_app(p.mul, &[a_, zero_c]);
            let mul_zero_h = d.lemma(p.mul_zero, &[a_]); // mul_a_zero ~ zero
            let add_neg_h = d.lemma(p.add_neg, &[base]); // add_base_neg_base ~ zero
            let sym = d.lemma(p.equiv_symm, &[add_base_neg_base, zero_c, add_neg_h]);
            d.lemma(
                p.equiv_trans,
                &[mul_a_zero, zero_c, add_base_neg_base, mul_zero_h, sym],
            )
        },
        &|d, j, ih| {
            // ih : Equiv (mul a_ (sumRange shifted j)) (add base (neg (pow x (add m j))))
            let mj = d.const_app(nat_add, &[m, j]);
            let xn = d.const_app(p.pow, &[x, mj]);
            let s_j = {
                let f = shifted_pow_fn(d, p, m, x);
                d.const_app(p.sum_range, &[f, j])
            };
            let extended = d.const_app(p.add, &[s_j, xn]);
            let start = d.const_app(p.mul, &[a_, extended]);

            let a_s_j = d.const_app(p.mul, &[a_, s_j]);
            let a_xn = d.const_app(p.mul, &[a_, xn]);
            let distributed = d.const_app(p.add, &[a_s_j, a_xn]);
            let h1 = d.lemma(p.left_distrib, &[a_, s_j, xn]);

            let neg_xn = d.const_app(p.neg, &[xn]);
            let base_minus_xn = d.const_app(p.add, &[base, neg_xn]);
            let after_ih = d.const_app(p.add, &[base_minus_xn, a_xn]);
            let refl_a_xn = d.lemma(p.equiv_refl, &[a_xn]);
            let h2 = d.lemma(
                p.add_congr,
                &[a_s_j, base_minus_xn, a_xn, a_xn, ih, refl_a_xn],
            );

            let neg_x = cneg(d, p, x);
            let one = d.kernel().const_(p.one, vec![]);
            let x_xn = d.const_app(p.mul, &[x, xn]);
            let neg_x_xn = d.const_app(p.neg, &[x_xn]);
            let mul_one_xn = d.const_app(p.mul, &[one, xn]);
            let mul_negx_xn = d.const_app(p.mul, &[neg_x, xn]);
            let expanded = d.const_app(p.add, &[mul_one_xn, mul_negx_xn]);
            let h_rd = right_distrib(d, p, one, neg_x, xn);

            let h_one_xn = {
                let xn_one = d.const_app(p.mul, &[xn, one]);
                let comm = d.lemma(p.mul_comm, &[one, xn]); // mul_one_xn ~ xn_one
                let mo = d.lemma(p.mul_one, &[xn]); // xn_one ~ xn
                echain(d, p, mul_one_xn, &[(xn_one, comm), (xn, mo)])
            };
            let h_negx_xn = {
                let raw = neg_mul_left(d, p, x, xn); // Equiv neg_x_xn mul_negx_xn
                d.lemma(p.equiv_symm, &[neg_x_xn, mul_negx_xn, raw])
                // Equiv mul_negx_xn neg_x_xn
            };

            let simplified = d.const_app(p.add, &[xn, neg_x_xn]);
            let h_simplify = d.lemma(
                p.add_congr,
                &[mul_one_xn, xn, mul_negx_xn, neg_x_xn, h_one_xn, h_negx_xn],
            );
            let h_a_xn = echain(d, p, a_xn, &[(expanded, h_rd), (simplified, h_simplify)]);

            let mid = d.const_app(p.add, &[base_minus_xn, simplified]);
            let refl_bmx = d.lemma(p.equiv_refl, &[base_minus_xn]);
            let h_mid = d.lemma(
                p.add_congr,
                &[
                    base_minus_xn,
                    base_minus_xn,
                    a_xn,
                    simplified,
                    refl_bmx,
                    h_a_xn,
                ],
            );

            let xn_x = d.const_app(p.mul, &[xn, x]);
            let neg_xn_x = d.const_app(p.neg, &[xn_x]);
            let end = d.const_app(p.add, &[base, neg_xn_x]);
            let end_x_xn = d.const_app(p.add, &[base, neg_x_xn]);
            let h_telescope = telescope_cancel(d, p, base, xn, x_xn);

            let x_xn_comm = d.lemma(p.mul_comm, &[x, xn]); // Equiv x_xn xn_x
            let neg_comm = d.lemma(p.neg_congr, &[x_xn, xn_x, x_xn_comm]);
            let refl_base2 = d.lemma(p.equiv_refl, &[base]);
            let h_fix = d.lemma(
                p.add_congr,
                &[base, base, neg_x_xn, neg_xn_x, refl_base2, neg_comm],
            );

            let h_end = d.lemma(p.equiv_trans, &[mid, end_x_xn, end, h_telescope, h_fix]);
            let h_final_mid = d.lemma(p.equiv_trans, &[after_ih, mid, end, h_mid, h_end]);
            let h_start_distributed =
                d.lemma(p.equiv_trans, &[start, distributed, after_ih, h1, h2]);
            d.lemma(
                p.equiv_trans,
                &[start, after_ih, end, h_start_distributed, h_final_mid],
            )
        },
        n,
    )
}

/// `CReal.mul_sub_one_geom_tail : ∀ x m n, Equiv (mul (add one (neg x)) (add
/// (sumRange (fun k => pow x k) (add m n)) (neg (sumRange (fun k => pow x k)
/// m)))) (add (pow x m) (neg (pow x (add m n))))`. See the module
/// documentation for the derivation: [`mul_a_shifted_sum`] proves the
/// shifted-partial-sum form by induction, and [`CRealPrelude::sum_range_split`]
/// plus [`cancel_right`] convert it into the direct tail above — the same
/// conversion `series.rs::declare_sum_range_tail_le` performs.
fn declare_mul_sub_one_geom_tail(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a_ = cadd(d, p, one, neg_x);
    let base = d.const_app(p.pow, &[x, m]);

    let shifted_proof = mul_a_shifted_sum(d, p, x, m, a_, base, n);
    // shifted_proof : Equiv (mul a_ (sumRange (shifted_pow_fn m x) n))
    //                       (add base (neg (pow x (add m n))))

    let f = pow_fn(d, p, x);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let mn = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_direct = cadd(d, p, sum_f_mn, neg_sum_f_m);

    let shifted_f = shifted_pow_fn(d, p, m, x);
    let sum_shifted_n = d.const_app(p.sum_range, &[shifted_f, n]);

    let split = d.lemma(p.sum_range_split, &[f, m, n]);
    // split : Equiv sum_f_mn (add sum_f_m sum_shifted_n)
    let sum_f_m_plus_shifted = cadd(d, p, sum_f_m, sum_shifted_n);
    let refl_neg = d.lemma(p.equiv_refl, &[neg_sum_f_m]);
    let step_a = d.lemma(
        p.add_congr,
        &[
            sum_f_mn,
            sum_f_m_plus_shifted,
            neg_sum_f_m,
            neg_sum_f_m,
            split,
            refl_neg,
        ],
    );
    // step_a : Equiv tail_direct (add sum_f_m_plus_shifted neg_sum_f_m)
    let middle = cadd(d, p, sum_f_m_plus_shifted, neg_sum_f_m);
    let cancel = cancel_right(d, p, sum_f_m, sum_shifted_n); // Equiv middle sum_shifted_n
    let tail_equiv = d.lemma(
        p.equiv_trans,
        &[tail_direct, middle, sum_shifted_n, step_a, cancel],
    );
    // tail_equiv : Equiv tail_direct sum_shifted_n

    let refl_a = d.lemma(p.equiv_refl, &[a_]);
    let mul_congr_h = d.lemma(
        p.mul_congr,
        &[a_, a_, tail_direct, sum_shifted_n, refl_a, tail_equiv],
    );
    let lhs_direct = d.const_app(p.mul, &[a_, tail_direct]);
    let lhs_shifted = d.const_app(p.mul, &[a_, sum_shifted_n]);
    // mul_congr_h : Equiv lhs_direct lhs_shifted

    let pow_mn = d.const_app(p.pow, &[x, mn]);
    let neg_pow_mn = cneg(d, p, pow_mn);
    let rhs = cadd(d, p, base, neg_pow_mn);

    let proof_inner = d.lemma(
        p.equiv_trans,
        &[lhs_direct, lhs_shifted, rhs, mul_congr_h, shifted_proof],
    );

    let stmt_inner = equiv(d, p, lhs_direct, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let inner2 = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, carrier, inner2)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let inner2 = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, carrier, inner2)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_sub_one_geom_tail,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.geom_tail_bounded : ∀ x, le zero x → ∀ m n, le (mul (add one (neg
/// x)) (add (sumRange (fun k => pow x k) (add m n)) (neg (sumRange (fun k =>
/// pow x k) m)))) (pow x m)`. Mirrors [`declare_geom_sum_bounded`]'s own proof
/// shape verbatim: [`declare_pow_nonneg`] bounds the dropped `−(pow x (add m
/// n))` term below by `zero`, and [`declare_mul_sub_one_geom_tail`] transports
/// the resulting `le` back across the ring identity. See the module
/// documentation for why `0 ≤ x` alone suffices (no `x ≤ one`).
fn declare_geom_tail_bounded(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.kernel().const_(p.one, vec![]);
    let neg_x = cneg(d, p, x);
    let a_ = cadd(d, p, one, neg_x);
    let f = pow_fn(d, p, x);
    let sum_f_m = d.const_app(p.sum_range, &[f, m]);
    let mn = d.const_app(nat_add, &[m, n]);
    let sum_f_mn = d.const_app(p.sum_range, &[f, mn]);
    let neg_sum_f_m = cneg(d, p, sum_f_m);
    let tail_direct = cadd(d, p, sum_f_mn, neg_sum_f_m);
    let lhs = d.const_app(p.mul, &[a_, tail_direct]);
    let pow_m = d.const_app(p.pow, &[x, m]);
    let pow_mn = d.const_app(p.pow, &[x, mn]);

    // pow_nonneg x h (add m n) : le zero pow_mn
    let h_nonneg = d.lemma(p.pow_nonneg, &[x, h, mn]);
    let zero_c = czero(d, p);
    let neg_pow_mn = cneg(d, p, pow_mn);
    let neg_zero = cneg(d, p, zero_c);
    let h_negle = d.lemma(p.neg_le_neg, &[zero_c, pow_mn, h_nonneg]);
    // h_negle : le neg_pow_mn neg_zero
    let h_negzero = neg_zero_equiv(d, p); // Equiv neg_zero zero_c
    let refl_negpmn = d.lemma(p.equiv_refl, &[neg_pow_mn]);
    let h_negle_zero = d.lemma(
        p.le_congr,
        &[
            neg_pow_mn,
            neg_pow_mn,
            neg_zero,
            zero_c,
            refl_negpmn,
            h_negzero,
            h_negle,
        ],
    );
    // h_negle_zero : le neg_pow_mn zero

    let h_refl_pow_m = d.lemma(p.le_refl, &[pow_m]);
    let h_add = d.lemma(
        p.add_le_add,
        &[pow_m, pow_m, neg_pow_mn, zero_c, h_refl_pow_m, h_negle_zero],
    );
    // h_add : le (add pow_m neg_pow_mn) (add pow_m zero)
    let pow_m_minus_pmn = cadd(d, p, pow_m, neg_pow_mn);
    let pow_m_plus_zero = cadd(d, p, pow_m, zero_c);
    let h_addzero = d.lemma(p.add_zero, &[pow_m]); // pow_m_plus_zero ~ pow_m
    let refl_pmmp = d.lemma(p.equiv_refl, &[pow_m_minus_pmn]);
    let h_bound = d.lemma(
        p.le_congr,
        &[
            pow_m_minus_pmn,
            pow_m_minus_pmn,
            pow_m_plus_zero,
            pow_m,
            refl_pmmp,
            h_addzero,
            h_add,
        ],
    );
    // h_bound : le pow_m_minus_pmn pow_m

    let h_geom = d.lemma(p.mul_sub_one_geom_tail, &[x, m, n]);
    // h_geom : Equiv lhs pow_m_minus_pmn
    let h_geom_symm = d.lemma(p.equiv_symm, &[lhs, pow_m_minus_pmn, h_geom]);
    let refl_pow_m = d.lemma(p.equiv_refl, &[pow_m]);
    let proof_inner = d.lemma(
        p.le_congr,
        &[
            pow_m_minus_pmn,
            lhs,
            pow_m,
            pow_m,
            h_geom_symm,
            refl_pow_m,
            h_bound,
        ],
    );

    let hyp = cle(d, p, zero_c, x);
    let stmt_inner = cle(d, p, lhs, pow_m);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_m = d.pi_fv(m_fv, nat, inner);
        let with_h = d.arrow(hyp, with_m);
        d.pi_fv(x_fv, carrier, with_h)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_m = d.lam_fv(m_fv, nat, inner);
        let with_h = d.lam_fv(h_fv, hyp, with_m);
        d.lam_fv(x_fv, carrier, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.geom_tail_bounded,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the reverse-direction monotonicity lemmas -------------------------------
//
// `declare_pow_le_one`/`declare_pow_le_pow_of_le_one` above take the base's
// relation to `one` as a *hypothesis*; every growth argument (this includes
// the strict lemmas and the headline below) needs the mirror direction, which
// this file did not have.

/// `CReal.one_le_pow_of_one_le : ∀ x, le one x → ∀ n, le one (pow x n)`.
/// Mirror of [`declare_pow_le_one`]: induction on `n`, base case `le_refl
/// one` up to `pow`'s ι-reduction. The step rewrites the inductive
/// hypothesis `one ≤ pow x j` across `mul_one` (symm) to `one ≤ mul (pow x j)
/// one`, then chains with [`CRealPrelude::mul_le_mul_of_nonneg_left`] at `c
/// := pow x j` against the outer `one ≤ x`. Unlike [`declare_pow_le_one`],
/// `pow x j` already sits in `mul_le_mul_of_nonneg_left`'s **left** (`c`)
/// slot, matching `pow`'s own right-recursive shape `mul (pow x j) x`
/// directly, so no closing `mul_comm` is needed.
fn declare_one_le_pow_of_one_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let one = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_c, one, lt01]);
    let h0 = d.lemma(p.le_trans, &[zero_c, one, x, le01, h1]);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        cle(d, p, one, px)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| d.lemma(p.le_refl, &[one]),
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            let mul_pxj_one = d.const_app(p.mul, &[px_j, one]);
            let mul_pxj_x = d.const_app(p.mul, &[px_j, x]);

            let mul_one_h = d.lemma(p.mul_one, &[px_j]); // Equiv mul_pxj_one px_j
            let mul_one_symm = d.lemma(p.equiv_symm, &[mul_pxj_one, px_j, mul_one_h]); // Equiv px_j mul_pxj_one
            let refl_one = d.lemma(p.equiv_refl, &[one]);
            let step_a = d.lemma(
                p.le_congr,
                &[one, one, px_j, mul_pxj_one, refl_one, mul_one_symm, ih],
            );
            // step_a : le one mul_pxj_one

            let h_nonneg = d.lemma(p.pow_nonneg, &[x, h0, j]);
            let step_b = d.lemma(p.mul_le_mul_of_nonneg_left, &[px_j, one, x, h_nonneg, h1]);
            // step_b : le mul_pxj_one mul_pxj_x

            d.lemma(p.le_trans, &[one, mul_pxj_one, mul_pxj_x, step_a, step_b])
            // : le one mul_pxj_x, defeq to le one (pow x (succ j))
        },
        n,
    );

    let hyp1 = cle(d, p, one, x);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h1 = d.arrow(hyp1, inner);
        d.pi_fv(x_fv, carrier, with_h1)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, inner);
        d.lam_fv(x_fv, carrier, with_h1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.one_le_pow_of_one_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_le_pow_of_one_le : ∀ x, le one x → ∀ n, le (pow x n) (pow x
/// (Nat.succ n))`. Mirror of [`declare_pow_le_pow_of_le_one`], not an
/// induction: [`CRealPrelude::mul_le_mul_of_nonneg_left`] at `c := pow x n`
/// against `one ≤ x` gives `mul (pow x n) one ≤ mul (pow x n) x`, and
/// [`CRealPrelude::mul_one`] folds the left side back to `pow x n`. Needs
/// only the one hypothesis `one ≤ x` — `zero ≤ x`
/// ([`CRealPrelude::pow_nonneg`]'s own hypothesis) is derived from it via
/// [`CRealPrelude::zero_lt_one`] and [`CRealPrelude::le_trans`] rather than
/// taken as a separate parameter.
fn declare_pow_le_pow_of_one_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pow_n = d.const_app(p.pow, &[x, n]);
    let one = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_c, one, lt01]);
    let h0 = d.lemma(p.le_trans, &[zero_c, one, x, le01, h1]);

    let h_nonneg = d.lemma(p.pow_nonneg, &[x, h0, n]);
    let base_le = d.lemma(p.mul_le_mul_of_nonneg_left, &[pow_n, one, x, h_nonneg, h1]);
    // base_le : le (mul pow_n one) (mul pow_n x)
    let mul_pn_one = d.const_app(p.mul, &[pow_n, one]);
    let mul_pn_x = d.const_app(p.mul, &[pow_n, x]);
    let mul_one_h = d.lemma(p.mul_one, &[pow_n]); // Equiv mul_pn_one pow_n
    let refl_rhs = d.lemma(p.equiv_refl, &[mul_pn_x]);
    let proof_inner = d.lemma(
        p.le_congr,
        &[
            mul_pn_one, pow_n, mul_pn_x, mul_pn_x, mul_one_h, refl_rhs, base_le,
        ],
    );
    // proof_inner : le pow_n mul_pn_x, defeq to le (pow x n) (pow x (succ n))

    let sn = d.succ(n);
    let pow_sn = d.const_app(p.pow, &[x, sn]);
    let hyp1 = cle(d, p, one, x);
    let stmt_inner = cle(d, p, pow_n, pow_sn);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h1 = d.arrow(hyp1, inner);
        d.pi_fv(x_fv, carrier, with_h1)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, inner);
        d.lam_fv(x_fv, carrier, with_h1)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_le_pow_of_one_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_pos : ∀ x, lt zero x → ∀ n, lt zero (pow x n)`. Mirror of
/// [`declare_pow_nonneg`], strict: induction on `n`, base case
/// [`CRealPrelude::zero_lt_one`] up to `pow`'s ι-reduction, step
/// [`CRealPrelude::mul_pos`] applied to the inductive hypothesis and the
/// outer `0 < x`.
fn declare_pow_pos(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let px = d.const_app(p.pow, &[x, v]);
        let zero_c = czero(d, p);
        clt(d, p, zero_c, px)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| d.lemma(p.zero_lt_one, &[]),
        &|d, j, ih| {
            let px_j = d.const_app(p.pow, &[x, j]);
            d.lemma(p.mul_pos, &[px_j, x, ih, h])
        },
        n,
    );

    let hyp = {
        let zero_c = czero(d, p);
        clt(d, p, zero_c, x)
    };
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt_inner);
        let with_h = d.arrow(hyp, inner);
        d.pi_fv(x_fv, carrier, with_h)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_inner);
        let with_h = d.lam_fv(h_fv, hyp, inner);
        d.lam_fv(x_fv, carrier, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_pos,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the strict halves, and the honest shape of the headline ---------------
//
// `eq_one_of_pow_eq_one` as originally framed (`x^n ~ 1 → x ~ 1`) needs
// tightness of `Apart` (`Not (Apart x y) → Equiv x y`), which is Markov's
// principle and is exactly the wall `CRealPrelude::apart`'s own doc block
// names as neither proved nor assumed anywhere in this development. What
// **is** reachable constructively is `Not (Apart x one)`: assume `Apart x
// one` (a *given* disjunction, not one manufactured from nothing — `Or`-
// elimination needs no excluded middle), derive a strict pow bound in
// whichever branch the disjunction handed over, and contradict it against
// the hypothesis `pow x (succ m) ~ one` via `lt_irrefl`. The two branches
// need a STRICT pow bound in each direction, which is what
// `pow_succ_lt_one`/`pow_succ_gt_one` below supply — and, contrary to the
// route this file's earlier sketch assumed, neither needs `mul_pos`,
// `right_distrib`/`neg_mul_left`, or any rational-gap algebra: both are
// [`declare_pow_le_one`]'s own induction with the closing step swapped from
// `le_trans` to `lt_of_le_of_lt`/`lt_of_lt_of_le` against a *strict*
// inductive hypothesis.

/// `CReal.pow_succ_lt_one : ∀ x, le zero x → lt x one → ∀ m, lt (pow x
/// (Nat.succ m)) one`. See [`CRealPrelude::pow_succ_lt_one`] for the shape
/// and the proof sketch.
fn declare_pow_succ_lt_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let one = d.kernel().const_(p.one, vec![]);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let sv = d.succ(v);
        let pxsv = d.const_app(p.pow, &[x, sv]);
        clt(d, p, pxsv, one)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt_inner = motive(d, m);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // Base: lt (pow x (succ zero)) one, i.e. lt (mul one x) one.
            let mul_one_x = d.const_app(p.mul, &[one, x]);
            let mul_x_one = d.const_app(p.mul, &[x, one]);
            let step1 = d.lemma(p.mul_comm, &[one, x]); // Equiv mul_one_x mul_x_one
            let step2 = d.lemma(p.mul_one, &[x]); // Equiv mul_x_one x
            let chain = d.lemma(p.equiv_trans, &[mul_one_x, mul_x_one, x, step1, step2]);
            // chain : Equiv mul_one_x x
            let eq_ab = d.lemma(p.equiv_symm, &[mul_one_x, x, chain]); // Equiv x mul_one_x
            let refl_one = d.lemma(p.equiv_refl, &[one]);
            d.lemma(p.lt_congr, &[x, mul_one_x, one, one, eq_ab, refl_one, hlt])
        },
        &|d, j, ih| {
            // Step: ih : lt (pow x (succ j)) one =: lt a one.
            // Want: lt (mul a x) one = lt (pow x (succ (succ j))) one.
            let sj = d.succ(j);
            let a = d.const_app(p.pow, &[x, sj]);
            let mul_a_x = d.const_app(p.mul, &[a, x]);
            let mul_a_one = d.const_app(p.mul, &[a, one]);

            let h_nonneg_a = d.lemma(p.pow_nonneg, &[x, h0, sj]);
            let hle = d.lemma(p.le_of_lt, &[x, one, hlt]); // le x one
            let mul_le = d.lemma(p.mul_le_mul_of_nonneg_left, &[a, x, one, h_nonneg_a, hle]);
            // mul_le : le mul_a_x mul_a_one
            let mul_one_h = d.lemma(p.mul_one, &[a]); // Equiv mul_a_one a
            let refl_max = d.lemma(p.equiv_refl, &[mul_a_x]);
            let le_a = d.lemma(
                p.le_congr,
                &[mul_a_x, mul_a_x, mul_a_one, a, refl_max, mul_one_h, mul_le],
            );
            // le_a : le mul_a_x a
            d.lemma(p.lt_of_le_of_lt, &[mul_a_x, a, one, le_a, ih])
            // : lt mul_a_x one
        },
        m,
    );

    let h0_ty = {
        let zero_c = czero(d, p);
        cle(d, p, zero_c, x)
    };
    let hlt_ty = clt(d, p, x, one);
    let ty = {
        let inner = d.pi_fv(m_fv, nat, stmt_inner);
        let with_hlt = d.arrow(hlt_ty, inner);
        let with_h0 = d.arrow(h0_ty, with_hlt);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let inner = d.lam_fv(m_fv, nat, proof_inner);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, inner);
        let with_h0 = d.lam_fv(h0_fv, h0_ty, with_hlt);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_succ_lt_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pow_succ_gt_one : ∀ x, lt one x → ∀ m, lt one (pow x (Nat.succ
/// m))`. Mirror of [`declare_pow_succ_lt_one`]; `zero ≤ x` is derived from
/// `one < x` rather than taken as a hypothesis, exactly as in
/// [`declare_pow_le_pow_of_one_le`].
fn declare_pow_succ_gt_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let one = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let lt01 = d.lemma(p.zero_lt_one, &[]);
    let le01 = d.lemma(p.le_of_lt, &[zero_c, one, lt01]);
    let hle_one_x = d.lemma(p.le_of_lt, &[one, x, hlt]); // le one x
    let h0 = d.lemma(p.le_trans, &[zero_c, one, x, le01, hle_one_x]);

    let motive = |d: &mut IntDev<'_>, v: ExprId| -> ExprId {
        let sv = d.succ(v);
        let pxsv = d.const_app(p.pow, &[x, sv]);
        clt(d, p, one, pxsv)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt_inner = motive(d, m);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            // Base: lt one (pow x (succ zero)) = lt one (mul one x).
            let mul_one_x = d.const_app(p.mul, &[one, x]);
            let mul_x_one = d.const_app(p.mul, &[x, one]);
            let step1 = d.lemma(p.mul_comm, &[one, x]);
            let step2 = d.lemma(p.mul_one, &[x]);
            let chain = d.lemma(p.equiv_trans, &[mul_one_x, mul_x_one, x, step1, step2]);
            // chain : Equiv mul_one_x x
            let eq_ce = d.lemma(p.equiv_symm, &[mul_one_x, x, chain]); // Equiv x mul_one_x
            let refl_one = d.lemma(p.equiv_refl, &[one]);
            d.lemma(p.lt_congr, &[one, one, x, mul_one_x, refl_one, eq_ce, hlt])
        },
        &|d, j, ih| {
            // Step: ih : lt one (pow x (succ j)) =: lt one a.
            // Want: lt one (mul a x) = lt one (pow x (succ (succ j))).
            let sj = d.succ(j);
            let a = d.const_app(p.pow, &[x, sj]);
            let mul_a_one = d.const_app(p.mul, &[a, one]);
            let mul_a_x = d.const_app(p.mul, &[a, x]);

            let h_nonneg_a = d.lemma(p.pow_nonneg, &[x, h0, sj]);
            let hle = d.lemma(p.le_of_lt, &[one, x, hlt]); // le one x
            let mul_le = d.lemma(p.mul_le_mul_of_nonneg_left, &[a, one, x, h_nonneg_a, hle]);
            // mul_le : le mul_a_one mul_a_x
            let mul_one_h = d.lemma(p.mul_one, &[a]); // Equiv mul_a_one a
            let refl_max = d.lemma(p.equiv_refl, &[mul_a_x]);
            let le_a = d.lemma(
                p.le_congr,
                &[mul_a_one, a, mul_a_x, mul_a_x, mul_one_h, refl_max, mul_le],
            );
            // le_a : le a mul_a_x
            d.lemma(p.lt_of_lt_of_le, &[one, a, mul_a_x, ih, le_a])
            // : lt one mul_a_x
        },
        m,
    );

    let hlt_ty = clt(d, p, one, x);
    let ty = {
        let inner = d.pi_fv(m_fv, nat, stmt_inner);
        let with_hlt = d.arrow(hlt_ty, inner);
        d.pi_fv(x_fv, carrier, with_hlt)
    };
    let value = {
        let inner = d.lam_fv(m_fv, nat, proof_inner);
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, inner);
        d.lam_fv(x_fv, carrier, with_hlt)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pow_succ_gt_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.Apart x y`, rebuilt privately exactly as every other file in this
/// directory does (`field.rs::apart`, `cotransitivity.rs::apart`) rather
/// than sharing one helper.
fn apart(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.apart, &[x, y])
}

/// `CReal.not_apart_one_of_pow_succ_eq_one : ∀ x, le zero x → ∀ m, Equiv (pow
/// x (Nat.succ m)) one → Not (Apart x one)`. See
/// [`CRealPrelude::not_apart_one_of_pow_succ_eq_one`] for the proof sketch
/// and for exactly why `Equiv x one` is out of reach here.
fn declare_not_apart_one_of_pow_succ_eq_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let one = d.kernel().const_(p.one, vec![]);
    let zero_c = czero(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let sm = d.succ(m);
    let pow_sm = d.const_app(p.pow, &[x, sm]);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);
    let hn_ty = equiv(d, p, pow_sm, one);

    let lt_x_one = clt(d, p, x, one);
    let lt_one_x = clt(d, p, one, x);
    let apart_ty = apart(d, p, x, one);
    let false_ty = d.false_ty();

    let apart_fv = d.fresh_fvar();
    let apart_h = d.kernel().fvar(apart_fv);

    let contradiction = d.or_elim(
        lt_x_one,
        lt_one_x,
        false_ty,
        apart_h,
        &|d, hlt| {
            // hlt : lt x one.
            let strict = d.lemma(p.pow_succ_lt_one, &[x, h0, hlt, m]);
            // strict : lt pow_sm one
            let hn_symm = d.lemma(p.equiv_symm, &[pow_sm, one, hn]); // Equiv one pow_sm
            let ge = d.lemma(p.le_of_equiv, &[one, pow_sm, hn_symm]); // le one pow_sm
            let lt_one_one = d.lemma(p.lt_of_le_of_lt, &[one, pow_sm, one, ge, strict]);
            d.lemma(p.lt_irrefl, &[one, lt_one_one])
        },
        &|d, hlt| {
            // hlt : lt one x.
            let strict = d.lemma(p.pow_succ_gt_one, &[x, hlt, m]);
            // strict : lt one pow_sm
            let le_eq = d.lemma(p.le_of_equiv, &[pow_sm, one, hn]); // le pow_sm one
            let lt_one_one = d.lemma(p.lt_of_lt_of_le, &[one, pow_sm, one, strict, le_eq]);
            d.lemma(p.lt_irrefl, &[one, lt_one_one])
        },
    );

    let h0_ty = cle(d, p, zero_c, x);
    let not_apart_ty = d.not(apart_ty);
    let ty = {
        let after_hn = d.arrow(hn_ty, not_apart_ty);
        let with_m = d.pi_fv(m_fv, nat, after_hn);
        let with_h0 = d.arrow(h0_ty, with_m);
        d.pi_fv(x_fv, carrier, with_h0)
    };
    let value = {
        let with_apart = d.lam_fv(apart_fv, apart_ty, contradiction);
        let with_hn = d.lam_fv(hn_fv, hn_ty, with_apart);
        let with_m = d.lam_fv(m_fv, nat, with_hn);
        let with_h0 = d.lam_fv(h0_fv, h0_ty, with_m);
        d.lam_fv(x_fv, carrier, with_h0)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.not_apart_one_of_pow_succ_eq_one,
        uparams: vec![],
        ty,
        value,
    })
}
