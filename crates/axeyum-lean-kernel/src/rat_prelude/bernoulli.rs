//! **Bernoulli's inequality** and the harmonic power bound it yields, over
//! `ℚ`.
//!
//! ## Why `ℚ` and not `CReal`
//!
//! The consumer that motivated this file —
//! [`crate::CRealPrelude::geom_pair_within`]'s own module documentation
//! (`creal/geometric.rs`) — names its undischarged leaf as `seq Yₐ b`: a
//! **rational** sample of a real sequence, not a real number itself. Nothing
//! downstream of that leaf needs a `CReal.pow`-vs-`natDivSucc` comparison
//! stated over `CReal`; it needs one stated over `ℚ`, at a rational obtained
//! by evaluating the real construction at one index. Building Bernoulli and
//! the harmonic bound here, over the decidable-order carrier that has no
//! `Apart`/`PosBound` bookkeeping at all, is strictly less work than
//! building the same statement over `CReal` and gets the geometric lane
//! everything it can consume from a rational fact. Bridging this rational
//! bound back across a `CReal.pow` sample (closing `CReal.geom_cauchy`
//! itself) is **not** attempted here — see the module note at the bottom of
//! this file for exactly what that bridge would need, and why it is out of
//! this slice's reach without editing `creal/geometric.rs`, which this
//! slice's constraints forbid touching.
//!
//! ## The statement, and why the accumulator is an inline `Nat.rec`, not a cast
//!
//! `ℚ` has `Nat`-indexed `pow` ([`super::polynomial`]) but no `Nat → ℚ`
//! cast/embedding declared anywhere in this prelude. Bernoulli's usual
//! statement, `1 + n·t ≤ (1+t)ⁿ`, needs `n·t` — a natural number's-worth of
//! copies of a rational `t` — and introducing a new named cast purely to
//! write one side of one theorem would be more public surface than the
//! statement needs. Instead [`l_term`] builds `n·t`'s companion quantity
//! `L t n := 1 + n·t` directly as an **inline** `Nat.rec` term (`L t 0 := 1`,
//! `L t (succ j) := L t j + t`), the same admission shape
//! `polynomial.rs::declare_pow` already uses for `Rat.pow` itself — a
//! `Nat.rec` application built by hand rather than through a named
//! `Definition`, since nothing else in this prelude needs to refer to `L` by
//! name.
//!
//! `Rat.bernoulli : ∀ t, Rat.le Rat.zero t → ∀ n, Rat.le (L t n) (Rat.pow (Rat.add Rat.one t) n)`
//!
//! `t ≥ 0`, not `t ≥ -1`: the `t ≥ -1` form is the textbook-general
//! statement, but every use this repository has for it (`geom_pair_within`'s
//! leaf, and Bernoulli's own standard corollary below) instantiates `t` as
//! a nonnegative quantity (`1 − x` bounded below, or a `PosBound` modulus),
//! and the `t ≥ 0` proof is materially simpler: it needs no sign case split
//! on `1+t` (`0 ≤ t` alone gives `0 ≤ 1+t` via [`RatPrelude::add_nonneg`]),
//! where the general form needs one. Extending to `t ≥ -1` is future work if
//! a caller ever needs it; nothing here forecloses it.
//!
//! ## The proof
//!
//! By induction on `n`, following the textbook step exactly
//! (`(1+t)ⁿ⁺¹ = (1+t)ⁿ(1+t) ≥ (1+nt)(1+t) = 1+(n+1)t+nt² ≥ 1+(n+1)t`,
//! discarding `nt² ≥ 0`), but phrased without ever forming `nt²` as its own
//! term (this development has no `sq` for `ℚ` outside `dotN`'s diagonal, and
//! summoning one would be more machinery than the two inequalities below):
//!
//! - [`declare_bernoulli`]'s step multiplies the induction hypothesis
//!   `L t j ≤ (1+t)ʲ` on the right by the constant `0 ≤ 1+t`
//!   ([`RatPrelude::mul_le_mul_of_nonneg_right`]), giving
//!   `(L t j)·(1+t) ≤ (1+t)ʲ⁺¹` (the right side defeq by `Rat.pow`'s own
//!   `ι`-reduction, no lemma needed).
//! - It bridges `L t (j+1) = L t j + t` up to `(L t j)·(1+t)` by expanding
//!   the right side (`(L t j)·(1+t) = L t j + (L t j)·t` via
//!   [`RatPrelude::left_distrib`] + [`RatPrelude::mul_one`]) and bounding the
//!   discarded term: `t ≤ (L t j)·t` follows from `1 ≤ L t j` (proved by
//!   [`one_le_l`], a **second, nested** induction — reused verbatim by
//!   [`declare_bernoulli_harmonic_bound`] below) and `0 ≤ t`, via
//!   [`RatPrelude::mul_le_mul_of_nonneg_right`] again.
//! - [`RatPrelude::le_trans`] composes the two bounds.
//!
//! ## The harmonic bound
//!
//! [`declare_bernoulli_harmonic_bound`] is the corollary
//! `geom_pair_within`'s own diagnosis actually asked for, stated to avoid
//! `Rat.inv` and division reasoning entirely (this prelude's inverse needs a
//! **positive** hypothesis and this bound's natural use site — a `pow` at
//! `x = 0` — is exactly the case a division-shaped statement would need to
//! special-case):
//!
//! `Rat.bernoulli_harmonic_bound : ∀ x t, 0 ≤ x → 0 ≤ t →`
//! `Rat.mul x (Rat.add Rat.one t) ≤ Rat.one → ∀ m,`
//! `Rat.mul (Rat.pow x m) (L t m) ≤ Rat.one`
//!
//! i.e. `xᵐ · (1 + m·t) ≤ 1` — the cross-multiplied form of `xᵐ ≤
//! 1/(1+m·t)`, avoiding `Rat.inv` on either side. The hypothesis
//! `x·(1+t) ≤ 1` is exactly `x ≤ 1/(1+t)` cross-multiplied, i.e. exactly
//! what a caller holding `1/x = 1+t` (this file's own module doc quotes the
//! task this way) or a `PosBound`-style bound has on hand already; `x = 0`
//! satisfies it for any `t ≥ 0` with no special case.
//!
//! **Derivation.** By induction on `m`, with invariant `(L t m)·(pow x m) ≤
//! 1` (`L` on the left throughout, so every expansion below is
//! [`RatPrelude::right_distrib`], never [`RatPrelude::left_distrib`], and no
//! commutativity rewrite is needed to align terms): writing `P := pow x m`,
//! the step needs `pow x m ≤ 1` at the *current* `m` (proved by
//! [`pow_le_one`], a third nested induction, using the derived fact `x ≤ 1`
//! — itself one non-inductive computation from the hypothesis, `x = x·1 ≤
//! x·(1+t) ≤ 1`) and `pow x m ≥ 0` implicitly through
//! [`RatPrelude::mul_le_mul_of_nonneg_left`]/`_right`'s own nonnegativity
//! side conditions. The hypothesis is converted **once**, before the
//! induction starts, from `x·(1+t) ≤ 1` to the already-expanded `x + t·x ≤
//! 1` (via [`RatPrelude::left_distrib`] + [`RatPrelude::mul_one`] +
//! [`RatPrelude::mul_comm`]) — an expansion the per-step algebra would
//! otherwise repeat at every `m`.
//!
//! ## What this does **not** close
//!
//! `geom_pair_within`'s own leaf is `seq Yₐ b` where `Yₐ := xᵃ · inv(1−x)`
//! is a **`CReal`**, and `seq` is `CReal`'s Cauchy-sequence projection — not
//! a plain rational `pow`. Consuming this file's
//! [`RatPrelude::bernoulli_harmonic_bound`] there needs a bridge this slice
//! does not build: a lemma relating `seq (CReal.pow x a) b` (a **sampled**
//! real power) to `Rat.pow (sample of x) b`-style rational arithmetic, plus
//! discharging `CReal.inv`'s own regularity/bound machinery in
//! `power.rs`/`cancellation.rs` (both off-limits to this slice) against the
//! rational bound proved here. That bridge is real-analysis content in its
//! own right (essentially: relating a `CReal.pow`'s *defining sequence* to
//! the rational `pow` this file proves things about), not index bookkeeping,
//! and is exactly the kind of `CReal`-level work `geometric.rs`'s own module
//! doc says is still missing. This file supplies the **rational** half of
//! that bridge — Bernoulli and the harmonic bound proper — so that whichever
//! future slice builds the `CReal`-side connection has a ready-made
//! rational lemma to land on, rather than needing to invent one under time
//! pressure alongside the real-analysis bridge itself.

use super::RatPrelude;
use super::ops::{
    radd, rat_eq_rewrite, rat_ty, rcongr, rle, rmul, rone, rpow, rsymm, rtrans, rzero,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Declare `Rat.bernoulli` and `Rat.bernoulli_harmonic_bound`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_bernoulli(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_bernoulli_inequality(d, p)?;
    declare_bernoulli_harmonic_bound(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The companion sequence `L t n := 1 + n·t`, and small reusable facts about
// it — none of these are named kernel declarations, only reusable Rust term
// builders, exactly as `creal/geometric.rs`'s own module doc describes for
// its reproduced-verbatim private helpers.
// ---------------------------------------------------------------------------

/// `L t n`, built as `Nat.rec (fun _ => Rat) Rat.one (fun _ ih => Rat.add ih t) n`
/// — `L t 0 ≡ 1`, `L t (succ j) ≡ L t j + t` by `ι`-reduction, mirroring
/// `polynomial.rs::declare_pow`'s own admission shape exactly (a `Type`-valued
/// motive, so the recursor's universe parameter is [`NatOps::level_one`], not
/// the `Prop`-motive `level_zero` [`NatOps::induct`] hardcodes).
fn l_term(d: &mut IntDev<'_>, p: RatPrelude, t: ExprId, n: ExprId) -> ExprId {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rone(d, p);
    let minor_succ = {
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = radd(d, ih, t);
        let inner = d.lam_fv(ih_fv, carrier, body);
        let j_fv = d.fresh_fvar();
        d.lam_fv(j_fv, nat, inner)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    d.apply(rec, &[motive, minor_zero, minor_succ, n])
}

/// `Eq Rat (Rat.mul Rat.one x) x` — the `1·x = x` this prelude has no
/// standalone `one_mul` field for (only [`RatPrelude::mul_one`], `a·1 = a`).
/// Built once via [`RatPrelude::mul_comm`] then [`RatPrelude::mul_one`],
/// reused everywhere a `one * _` needs collapsing.
fn one_mul_eq(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one = rone(d, p);
    let comm = d.lemma(p.mul_comm, &[one, x]); // Eq (one*x) (x*one)
    let one_x = rmul(d, one, x);
    let x_one = rmul(d, x, one);
    let collapse = d.lemma(p.mul_one, &[x]); // Eq (x*one) x
    rtrans(d, one_x, x_one, x, comm, collapse)
}

/// `one_le_l t h n : Rat.le Rat.one (L t n)`, given `h : Rat.le Rat.zero t`.
///
/// A **nested** induction on `n`, not a declared theorem: `L t n = 1 + n·t
/// ≥ 1` since every added `t` is nonnegative. Reused both by
/// [`declare_bernoulli_inequality`]'s own step (to discard the squared
/// term, see this file's module doc) and available to
/// [`declare_bernoulli_harmonic_bound`] should a future extension need it,
/// though the harmonic bound as built here does not.
fn one_le_l(d: &mut IntDev<'_>, p: RatPrelude, t: ExprId, h: ExprId, n: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let one = rone(d, p);
        let lx = l_term(d, p, t, x);
        rle(d, p, one, lx)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one = rone(d, p);
        d.lemma(p.le_refl, &[one])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let one = rone(d, p);
        let zero = rzero(d, p);
        let lj = l_term(d, p, t, j);
        // add_le_add(one, lj, zero, t, ih, h) : le (one+zero) (lj+t).
        let sum_le = d.lemma(p.add_le_add, &[one, lj, zero, t, ih, h]);
        let one_plus_zero = radd(d, one, zero);
        let add_zero_eq = d.lemma(p.add_zero, &[one]); // Eq (one+zero) one
        let target_rhs = radd(d, lj, t);
        rat_eq_rewrite(d, one_plus_zero, one, add_zero_eq, sum_le, &|d, x| {
            rle(d, p, x, target_rhs)
        })
    };
    d.induct(&motive, &base, &step, n)
}

/// `pow_nonneg x hx n : Rat.le Rat.zero (Rat.pow x n)`, given `hx : Rat.le
/// Rat.zero x`. A nested induction, used only by [`pow_le_one`]'s own
/// derivation is NOT needed for it (that proof only needs `x ≤ 1`, never a
/// separate nonnegativity fact about `pow`) — kept here because
/// [`declare_bernoulli_harmonic_bound`]'s own base case needs `0 ≤ 1`, not
/// `0 ≤ pow x n`, so this helper is currently unused; retained as the
/// natural counterpart to [`pow_le_one`] and dropped if a linter objects.
#[allow(dead_code)]
fn pow_nonneg(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, hx: ExprId, n: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
        let zero = rzero(d, p);
        let py = rpow(d, p, x, y);
        rle(d, p, zero, py)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero = rzero(d, p);
        let one = rone(d, p);
        let zlo = d.lemma(p.zero_lt_one, &[]);
        d.lemma(p.le_of_lt, &[zero, one, zlo])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let pj = rpow(d, p, x, j);
        d.lemma(p.mul_nonneg, &[pj, x, ih, hx])
    };
    d.induct(&motive, &base, &step, n)
}

/// `pow_le_one x hx0 hx1 n : Rat.le (Rat.pow x n) Rat.one`, given `hx0 : 0 ≤
/// x` and `hx1 : x ≤ 1`. A nested induction:
/// `pow x (j+1) = (pow x j)·x ≤ 1·x = x ≤ 1`.
fn pow_le_one(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    x: ExprId,
    hx0: ExprId,
    hx1: ExprId,
    n: ExprId,
) -> ExprId {
    let motive = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
        let one = rone(d, p);
        let py = rpow(d, p, x, y);
        rle(d, p, py, one)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one = rone(d, p);
        d.lemma(p.le_refl, &[one])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let pj = rpow(d, p, x, j);
        let one = rone(d, p);
        // mul_le_mul_of_nonneg_right(pj, one, x, hx0, ih) : le (pj*x) (one*x).
        let raw = d.lemma(p.mul_le_mul_of_nonneg_right, &[pj, one, x, hx0, ih]);
        let one_x = rmul(d, one, x);
        let one_x_eq_x = one_mul_eq(d, p, x);
        let pjx = rmul(d, pj, x);
        let step1 = rat_eq_rewrite(d, one_x, x, one_x_eq_x, raw, &|d, y| rle(d, p, pjx, y));
        // step1 : le (pj*x) x; chain with hx1 : le x one.
        d.lemma(p.le_trans, &[pjx, x, one, step1, hx1])
    };
    d.induct(&motive, &base, &step, n)
}

// ---------------------------------------------------------------------------
// `Rat.bernoulli`.
// ---------------------------------------------------------------------------

/// `Rat.bernoulli : ∀ t, Rat.le Rat.zero t →`
/// `∀ n, Rat.le (L t n) (Rat.pow (Rat.add Rat.one t) n)`.
///
/// See the module doc for the full derivation.
fn declare_bernoulli_inequality(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let h_ty = {
        let zero = rzero(d, p);
        rle(d, p, zero, t)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let one_plus_t = {
        let one = rone(d, p);
        radd(d, one, t)
    };
    // Constant across the whole induction: 0 ≤ 1+t.
    let h_one_plus_t_nonneg = {
        let zero = rzero(d, p);
        let one = rone(d, p);
        let zlo = d.lemma(p.zero_lt_one, &[]);
        let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zlo]);
        d.lemma(p.add_nonneg, &[one, t, zero_le_one, h])
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lx = l_term(d, p, t, x);
        let px = rpow(d, p, one_plus_t, x);
        rle(d, p, lx, px)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        // L t 0 ≡ one, pow (1+t) 0 ≡ one (both by iota) — le_refl closes it.
        let one = rone(d, p);
        d.lemma(p.le_refl, &[one])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        // ih : Rat.le (L t j) (pow (1+t) j).
        let lj = l_term(d, p, t, j);
        let pj = rpow(d, p, one_plus_t, j);

        // step1 : le (lj*(1+t)) (pj*(1+t)).
        let step1 = d.lemma(
            p.mul_le_mul_of_nonneg_right,
            &[lj, pj, one_plus_t, h_one_plus_t_nonneg, ih],
        );

        // key : le t (lj*t), from 1 ≤ lj (nested induction) and 0 ≤ t.
        let one = rone(d, p);
        let one_le_lj = one_le_l(d, p, t, h, j);
        let raw_key = d.lemma(p.mul_le_mul_of_nonneg_right, &[one, lj, t, h, one_le_lj]);
        let one_t = rmul(d, one, t);
        let one_t_eq_t = one_mul_eq(d, p, t);
        let lj_t = rmul(d, lj, t);
        let key = rat_eq_rewrite(d, one_t, t, one_t_eq_t, raw_key, &|d, y| rle(d, p, y, lj_t));

        // mono : le (lj+t) (lj+lj*t).
        let lj_le_lj = d.lemma(p.le_refl, &[lj]);
        let mono = d.lemma(p.add_le_add, &[lj, lj, t, lj_t, lj_le_lj, key]);

        // Expand lj*(1+t) = lj*1 + lj*t = lj + lj*t.
        let lj_one_plus_t = rmul(d, lj, one_plus_t);
        let dist = d.lemma(p.left_distrib, &[lj, one, t]); // Eq (lj*(1+t)) (lj*1+lj*t)
        let lj_one = rmul(d, lj, one);
        let fix = d.lemma(p.mul_one, &[lj]); // Eq (lj*1) lj
        let congr = rcongr(d, lj_one, lj, fix, &|d, y| radd(d, y, lj_t));
        let lj_one_plus_lj_t = radd(d, lj_one, lj_t);
        let lj_plus_lj_t = radd(d, lj, lj_t);
        let combined = rtrans(
            d,
            lj_one_plus_t,
            lj_one_plus_lj_t,
            lj_plus_lj_t,
            dist,
            congr,
        );
        let h_sym = rsymm(d, lj_one_plus_t, lj_plus_lj_t, combined);

        let lj_plus_t = radd(d, lj, t);
        let mono2 = rat_eq_rewrite(d, lj_plus_lj_t, lj_one_plus_t, h_sym, mono, &|d, y| {
            rle(d, p, lj_plus_t, y)
        });

        // final : le (lj+t) (pj*(1+t)).
        let pj_one_plus_t = rmul(d, pj, one_plus_t);
        d.lemma(
            p.le_trans,
            &[lj_plus_t, lj_one_plus_t, pj_one_plus_t, mono2, step1],
        )
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof_n = d.induct(&motive, &base, &step, n);
    let stmt_n = motive(d, n);

    let ty_n = d.pi_fv(n_fv, nat, stmt_n);
    let value_n = d.lam_fv(n_fv, nat, proof_n);
    let ty_h = d.pi_fv(h_fv, h_ty, ty_n);
    let value_h = d.lam_fv(h_fv, h_ty, value_n);
    let ty = d.pi_fv(t_fv, carrier, ty_h);
    let value = d.lam_fv(t_fv, carrier, value_h);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bernoulli,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `Rat.bernoulli_harmonic_bound`.
// ---------------------------------------------------------------------------

/// `Rat.bernoulli_harmonic_bound : ∀ x t, Rat.le Rat.zero x → Rat.le Rat.zero t →`
/// `Rat.le (Rat.mul x (Rat.add Rat.one t)) Rat.one →`
/// `∀ m, Rat.le (Rat.mul (L t m) (Rat.pow x m)) Rat.one`.
///
/// See the module doc for the full derivation.
fn declare_bernoulli_harmonic_bound(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hx_ty = {
        let zero = rzero(d, p);
        rle(d, p, zero, x)
    };
    let hx_fv = d.fresh_fvar();
    let hx = d.kernel().fvar(hx_fv);

    let ht_ty = {
        let zero = rzero(d, p);
        rle(d, p, zero, t)
    };
    let ht_fv = d.fresh_fvar();
    let ht = d.kernel().fvar(ht_fv);

    let hxt_ty = {
        let one = rone(d, p);
        let one_plus_t = radd(d, one, t);
        let prod = rmul(d, x, one_plus_t);
        rle(d, p, prod, one)
    };
    let hxt_fv = d.fresh_fvar();
    let hxt = d.kernel().fvar(hxt_fv);

    // One-time hypothesis conversion: x*(1+t) ≤ 1  ~>  x + t*x ≤ 1.
    let h_xt = {
        let one = rone(d, p);
        let one_plus_t = radd(d, one, t);
        let x_one_plus_t = rmul(d, x, one_plus_t);
        let dist = d.lemma(p.left_distrib, &[x, one, t]); // Eq (x*(1+t)) (x*1+x*t)
        let x_one = rmul(d, x, one);
        let x_t = rmul(d, x, t);
        let fix1 = d.lemma(p.mul_one, &[x]); // Eq (x*1) x
        let congr1 = rcongr(d, x_one, x, fix1, &|d, y| radd(d, y, x_t));
        let x_one_plus_xt = radd(d, x_one, x_t);
        let x_plus_xt = radd(d, x, x_t);
        let step1 = rtrans(d, x_one_plus_t, x_one_plus_xt, x_plus_xt, dist, congr1);
        let fix2 = d.lemma(p.mul_comm, &[x, t]); // Eq (x*t) (t*x)
        let t_x = rmul(d, t, x);
        let congr2 = rcongr(d, x_t, t_x, fix2, &|d, y| radd(d, x, y));
        let x_plus_tx = radd(d, x, t_x);
        let step2 = rtrans(d, x_one_plus_t, x_plus_xt, x_plus_tx, step1, congr2);
        rat_eq_rewrite(d, x_one_plus_t, x_plus_tx, step2, hxt, &|d, y| {
            rle(d, p, y, one)
        })
    };

    // Global, non-inductive: x ≤ 1, from x = x*1 ≤ x*(1+t) ≤ 1.
    let hx1 = {
        let one = rone(d, p);
        let one_plus_t = radd(d, one, t);
        let one_le_one_plus_t = {
            let zero = rzero(d, p);
            let one_le_one = d.lemma(p.le_refl, &[one]);
            let sum_le = d.lemma(p.add_le_add, &[one, one, zero, t, one_le_one, ht]);
            let one_plus_zero = radd(d, one, zero);
            let add_zero_eq = d.lemma(p.add_zero, &[one]);
            rat_eq_rewrite(d, one_plus_zero, one, add_zero_eq, sum_le, &|d, y| {
                rle(d, p, y, one_plus_t)
            })
        };
        // x*1 ≤ x*(1+t), from 1 ≤ 1+t and 0 ≤ x.
        let raw = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[x, one, one_plus_t, hx, one_le_one_plus_t],
        );
        let x_one = rmul(d, x, one);
        let fix = d.lemma(p.mul_one, &[x]); // Eq (x*1) x
        let x_one_plus_t = rmul(d, x, one_plus_t);
        let step_a = rat_eq_rewrite(d, x_one, x, fix, raw, &|d, y| rle(d, p, y, x_one_plus_t));
        let one_const = rone(d, p);
        d.lemma(p.le_trans, &[x, x_one_plus_t, one_const, step_a, hxt])
    };

    let motive = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
        let ly = l_term(d, p, t, y);
        let py = rpow(d, p, x, y);
        let prod = rmul(d, ly, py);
        let one = rone(d, p);
        rle(d, p, prod, one)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        // L t 0 ≡ one, pow x 0 ≡ one; target: le (one*one) one.
        let one = rone(d, p);
        let one_one = rmul(d, one, one);
        let mul_one_eq = d.lemma(p.mul_one, &[one]); // Eq (one*one) one
        let sym = rsymm(d, one_one, one, mul_one_eq);
        let base_at_one = d.lemma(p.le_refl, &[one]);
        rat_eq_rewrite(d, one, one_one, sym, base_at_one, &|d, y| rle(d, p, y, one))
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        // ih : le (lj*pj) one.
        let lj = l_term(d, p, t, j);
        let pj = rpow(d, p, x, j);
        let one = rone(d, p);

        // hpx : le (pj*x) x, from pow_le_one at j and 0 ≤ x, x ≤ 1.
        let pow_le_one_j = pow_le_one(d, p, x, hx, hx1, j);
        let raw_hpx = d.lemma(
            p.mul_le_mul_of_nonneg_right,
            &[pj, one, x, hx, pow_le_one_j],
        );
        let one_x = rmul(d, one, x);
        let one_x_eq_x = one_mul_eq(d, p, x);
        let pjx = rmul(d, pj, x);
        let hpx = rat_eq_rewrite(d, one_x, x, one_x_eq_x, raw_hpx, &|d, y| rle(d, p, pjx, y));

        // term1 : le (lj*(pj*x)) x, via mul_assoc then ih scaled by x on the right.
        let lj_pj = rmul(d, lj, pj);
        let assoc = d.lemma(p.mul_assoc, &[lj, pj, x]); // Eq ((lj*pj)*x) (lj*(pj*x))
        let raw_term1 = d.lemma(p.mul_le_mul_of_nonneg_right, &[lj_pj, one, x, hx, ih]);
        // raw_term1 : le ((lj*pj)*x) (one*x)
        let lj_pj_x = rmul(d, lj_pj, x);
        let lj_pjx = rmul(d, lj, pjx);
        let step_assoc = rat_eq_rewrite(d, lj_pj_x, lj_pjx, assoc, raw_term1, &|d, y| {
            rle(d, p, y, one_x)
        });
        let term1 = rat_eq_rewrite(d, one_x, x, one_x_eq_x, step_assoc, &|d, y| {
            rle(d, p, lj_pjx, y)
        });

        // term2 : le (t*(pj*x)) (t*x), from 0 ≤ t and hpx.
        let t_pjx = rmul(d, t, pjx);
        let t_x = rmul(d, t, x);
        let term2 = d.lemma(p.mul_le_mul_of_nonneg_left, &[t, pjx, x, ht, hpx]);

        // sum_bound : le (lj*(pj*x) + t*(pj*x)) (x + t*x).
        let sum_bound = d.lemma(p.add_le_add, &[lj_pjx, x, t_pjx, t_x, term1, term2]);

        // final_le : le (lj*(pj*x) + t*(pj*x)) one.
        let lhs_sum = radd(d, lj_pjx, t_pjx);
        let rhs_sum = radd(d, x, t_x);
        let final_le = d.lemma(p.le_trans, &[lhs_sum, rhs_sum, one, sum_bound, h_xt]);

        // Rewrite lhs_sum into (lj+t)*(pj*x) via right_distrib, symm'd.
        let rd = d.lemma(p.right_distrib, &[lj, t, pjx]); // Eq ((lj+t)*(pj*x)) (lj*(pj*x)+t*(pj*x))
        let lj_plus_t = radd(d, lj, t);
        let target_lhs = rmul(d, lj_plus_t, pjx);
        let rd_sym = rsymm(d, target_lhs, lhs_sum, rd);
        rat_eq_rewrite(d, lhs_sum, target_lhs, rd_sym, final_le, &|d, y| {
            rle(d, p, y, one)
        })
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let proof_m = d.induct(&motive, &base, &step, m);
    let stmt_m = motive(d, m);

    let ty_m = d.pi_fv(m_fv, nat, stmt_m);
    let value_m = d.lam_fv(m_fv, nat, proof_m);
    let ty_hxt = d.pi_fv(hxt_fv, hxt_ty, ty_m);
    let value_hxt = d.lam_fv(hxt_fv, hxt_ty, value_m);
    let ty_ht = d.pi_fv(ht_fv, ht_ty, ty_hxt);
    let value_ht = d.lam_fv(ht_fv, ht_ty, value_hxt);
    let ty_hx = d.pi_fv(hx_fv, hx_ty, ty_ht);
    let value_hx = d.lam_fv(hx_fv, hx_ty, value_ht);
    let ty_t = d.pi_fv(t_fv, carrier, ty_hx);
    let value_t = d.lam_fv(t_fv, carrier, value_hx);
    let ty = d.pi_fv(x_fv, carrier, ty_t);
    let value = d.lam_fv(x_fv, carrier, value_t);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bernoulli_harmonic_bound,
        uparams: vec![],
        ty,
        value,
    })
}
