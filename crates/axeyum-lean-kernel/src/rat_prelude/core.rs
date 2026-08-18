//! The **structural core**: what makes `Eq Rat` usable.
//!
//! `Rat` is a normalised structure, so two rationals are equal exactly when
//! their projections are — but the projections are only reachable through
//! `Rat.rec`, and the two proof fields are dependently typed. Everything in
//! this module exists to turn that into three usable facts:
//!
//! - [`declare_structural`] — `mk_congr`, `eta`, `ext`. Equal numerator and
//!   equal denominator give equal rationals, *whatever* the proof fields hold,
//!   because the kernel has definitional **proof irrelevance**.
//! - [`declare_uniqueness`] — `eq_of_cross`: a reduced representative is
//!   unique, so cross-multiplication decides equality. This is the keystone,
//!   and the only genuinely number-theoretic step: it needs Gauss's lemma over
//!   `ℕ` (coprime cancellation, from Bézout) and cancellation over `ℤ`.
//! - [`declare_normalize_laws`] — `normalize` preserves the value it is given
//!   (`normalize_cross`) and therefore respects cross-equality
//!   (`normalize_congr`) and is the identity on an already-reduced pair
//!   (`self_normalize`).
//!
//! With those, a ring law over `ℚ` becomes a cross-multiplication identity over
//! the constructed `ℤ`, which is ordinary algebra.

use super::RatPrelude;
use super::ops::{
    bezout_elim, den, int_eq_to_nat, iprod, iprod_head_rewrite, iprod_perm, mk, normalize, num,
    one_le_succ, pos_cases, positive_ty, rat_theorem, rat_ty, rchain, reduced_ty, req, rrefl,
    rsymm,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, Shape, case_split};
use crate::nat_prelude::NatOps;

/// Admit `Rat.mk_congr`, `Rat.eta` and `Rat.ext`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_structural(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    // --- mk_congr ----------------------------------------------------------
    // ∀ n1 n2 d1 d2, n1 = n2 → d1 = d2 →
    //   ∀ p1 r1 p2 r2, mk n1 d1 p1 r1 = mk n2 d2 p2 r2
    //
    // The two proof fields are never inspected: at `n1 = n1`, `d1 = d1` the two
    // sides differ only in them, and definitional proof irrelevance makes
    // `Eq.refl` check against the stated type.
    {
        let n1_fv = d.fresh_fvar();
        let n1 = d.kernel().fvar(n1_fv);
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        let d1_fv = d.fresh_fvar();
        let d1 = d.kernel().fvar(d1_fv);
        let d2_fv = d.fresh_fvar();
        let d2 = d.kernel().fvar(d2_fv);
        let hn_ty = d.ieq(n1, n2);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hd_ty = d.eq(d1, d2);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);
        let p1_ty = positive_ty(d, d1);
        let p1_fv = d.fresh_fvar();
        let p1 = d.kernel().fvar(p1_fv);
        let r1_ty = reduced_ty(d, n1, d1);
        let r1_fv = d.fresh_fvar();
        let r1 = d.kernel().fvar(r1_fv);
        let source = mk(d, n1, d1, p1, r1);

        // `∀ p2 r2, source = mk numerator denominator p2 r2`, the shape both
        // transports move through.
        let goal = |d: &mut IntDev<'_>, numerator: ExprId, denominator: ExprId| -> ExprId {
            let p2_ty = positive_ty(d, denominator);
            let p2_fv = d.fresh_fvar();
            let p2 = d.kernel().fvar(p2_fv);
            let r2_ty = reduced_ty(d, numerator, denominator);
            let r2_fv = d.fresh_fvar();
            let r2 = d.kernel().fvar(r2_fv);
            let target = mk(d, numerator, denominator, p2, r2);
            let equation = req(d, source, target);
            let with_r2 = d.pi_fv(r2_fv, r2_ty, equation);
            d.pi_fv(p2_fv, p2_ty, with_r2)
        };

        // Base: numerator `n1`, denominator `d1` — reflexivity, up to proof
        // irrelevance in `p2`/`r2`.
        let base = {
            let p2_ty = positive_ty(d, d1);
            let p2_fv = d.fresh_fvar();
            let r2_ty = reduced_ty(d, n1, d1);
            let r2_fv = d.fresh_fvar();
            let body = rrefl(d, source);
            let with_r2 = d.lam_fv(r2_fv, r2_ty, body);
            d.lam_fv(p2_fv, p2_ty, with_r2)
        };
        // Move the numerator n1 ↦ n2 at fixed denominator d1.
        let at_n2 = {
            let motive = d.ieq_motive(n1, &|d, y| goal(d, y, d1));
            d.itransport(n1, motive, base, n2, hn)
        };
        // Then the denominator d1 ↦ d2.
        let body = {
            let motive = d.eq_motive(d1, &|d, x| goal(d, n2, x));
            d.transport(d1, motive, at_n2, d2, hd)
        };

        let ty = {
            let inner = goal(d, n2, d2);
            let with_r1 = d.pi_fv(r1_fv, r1_ty, inner);
            let with_p1 = d.pi_fv(p1_fv, p1_ty, with_r1);
            let with_hd = d.pi_fv(hd_fv, hd_ty, with_p1);
            let with_hn = d.pi_fv(hn_fv, hn_ty, with_hd);
            let with_d2 = d.pi_fv(d2_fv, nat_ty, with_hn);
            let with_d1 = d.pi_fv(d1_fv, nat_ty, with_d2);
            let with_n2 = d.pi_fv(n2_fv, int_ty, with_d1);
            d.pi_fv(n1_fv, int_ty, with_n2)
        };
        let value = {
            let with_r1 = d.lam_fv(r1_fv, r1_ty, body);
            let with_p1 = d.lam_fv(p1_fv, p1_ty, with_r1);
            let with_hd = d.lam_fv(hd_fv, hd_ty, with_p1);
            let with_hn = d.lam_fv(hn_fv, hn_ty, with_hd);
            let with_d2 = d.lam_fv(d2_fv, nat_ty, with_hn);
            let with_d1 = d.lam_fv(d1_fv, nat_ty, with_d2);
            let with_n2 = d.lam_fv(n2_fv, int_ty, with_d1);
            d.lam_fv(n1_fv, int_ty, with_n2)
        };
        d.declare_theorem(p.mk_congr, ty, value)?;
    }

    // --- eta ---------------------------------------------------------------
    // ∀ q, q = mk (num q) (den q) (den_pos q) (reduced q).
    // By `Rat.rec`: on `mk n dn pp rr` the right-hand side ι-reduces to itself.
    rat_theorem(d, p.eta, 1, &|d, v| {
        let q = v[0];
        let claim = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let rebuilt = {
                let numerator = num(d, x);
                let denominator = den(d, x);
                let positive = super::ops::den_pos(d, x);
                let reduced = super::ops::reduced(d, x);
                mk(d, numerator, denominator, positive, reduced)
            };
            req(d, x, rebuilt)
        };
        let stmt = claim(d, q);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = claim(d, x);
            d.lam_fv(x_fv, carrier, body)
        };
        let minor = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let dn_fv = d.fresh_fvar();
            let dn = d.kernel().fvar(dn_fv);
            let pp_ty = positive_ty(d, dn);
            let pp_fv = d.fresh_fvar();
            let pp = d.kernel().fvar(pp_fv);
            let rr_ty = reduced_ty(d, n, dn);
            let rr_fv = d.fresh_fvar();
            let rr = d.kernel().fvar(rr_fv);
            let built = mk(d, n, dn, pp, rr);
            let body = rrefl(d, built);
            let with_rr = d.lam_fv(rr_fv, rr_ty, body);
            let with_pp = d.lam_fv(pp_fv, pp_ty, with_rr);
            let with_dn = d.lam_fv(dn_fv, nat_ty, with_pp);
            d.lam_fv(n_fv, int_ty, with_dn)
        };
        let level_zero = d.kernel().level_zero();
        let rec = d.kernel().const_(p.int.rat_rec, vec![level_zero]);
        let proof = d.apply(rec, &[motive, minor, q]);
        (stmt, proof)
    })?;

    // --- ext ---------------------------------------------------------------
    // ∀ q r, num q = num r → den q = den r → q = r.
    rat_theorem(d, p.ext, 2, &|d, v| {
        let (q, r) = (v[0], v[1]);
        let hn_ty = {
            let left = num(d, q);
            let right = num(d, r);
            d.ieq(left, right)
        };
        let hd_ty = {
            let left = den(d, q);
            let right = den(d, r);
            d.eq(left, right)
        };
        let conclusion = req(d, q, r);
        let stmt = {
            let inner = d.arrow(hd_ty, conclusion);
            d.arrow(hn_ty, inner)
        };
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let expand = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let numerator = num(d, x);
            let denominator = den(d, x);
            let positive = super::ops::den_pos(d, x);
            let reduced = super::ops::reduced(d, x);
            mk(d, numerator, denominator, positive, reduced)
        };
        let left_expanded = expand(d, q);
        let right_expanded = expand(d, r);
        let step_left = d.const_app(p.eta, &[q]);
        let step_middle = {
            let nq = num(d, q);
            let nr = num(d, r);
            let dq = den(d, q);
            let dr = den(d, r);
            let pq = super::ops::den_pos(d, q);
            let rq = super::ops::reduced(d, q);
            let pr = super::ops::den_pos(d, r);
            let rr = super::ops::reduced(d, r);
            d.const_app(p.mk_congr, &[nq, nr, dq, dr, hn, hd, pq, rq, pr, rr])
        };
        let step_right = {
            let forward = d.const_app(p.eta, &[r]);
            rsymm(d, r, right_expanded, forward)
        };
        let (_, chained) = rchain(
            d,
            q,
            &[
                (left_expanded, step_left),
                (right_expanded, step_middle),
                (r, step_right),
            ],
        );
        let proof = {
            let with_hd = d.lam_fv(hd_fv, hd_ty, chained);
            d.lam_fv(hn_fv, hn_ty, with_hd)
        };
        (stmt, proof)
    })
}

/// Admit the `ℕ` and `ℤ` facts uniqueness rests on.
///
/// Two of them are the real content:
///
/// - **Gauss's lemma** `nat_gauss : 1 ≤ k → gcd k a = 1 → k ∣ a·b → k ∣ b`.
///   This is the coprime-cancellation step, and it comes straight out of a
///   Bézout certificate scaled by `b`: the balanced all-naturals identity
///   `(1 + k·mn) + a·nn = k·mp + a·np` becomes `b + X = Y` with `k` dividing
///   both `X` and `Y`, so `dvd_add_right_cancel_of_pos` yields `k ∣ b` without
///   ever forming a difference. `Nat.euclid_lemma` runs the same argument for a
///   *prime* `k`; this is that argument with primality replaced by the
///   coprimality it was only ever used to produce.
/// - **`int_mul_right_cancel`** — cancelling a positive natural factor in `ℤ`.
///   The only four-way constructor split in this module. Two of the four
///   branches are sign contradictions, and both close through
///   `not_zero_le_neg_of_nat`.
///
/// Everything else about the order is then *derived* rather than split on:
/// `int_mul_lt_mul_right` is `le` monotonicity plus cancellation
/// (`a·c = b·c` would give `a = b`, contradicting `a < b`), and the two
/// reverse-direction lemmas fall out of `Int.le_total`, `Int.eq_em` and
/// `Int.lt_irrefl`. That is why there is one case split here and not five.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_arithmetic_support(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let int = p.int;

    // nat_mul_right_cancel : ∀ c a b, 1 ≤ c → a*c = b*c → a = b.
    // `Nat.mul_left_cancel_of_pos` cancels on the LEFT; two `mul_comm` steps
    // put the equation in that shape.
    d.theorem(p.nat_mul_right_cancel, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let unit = d.num(1);
        let positive = NatOps::le(d, unit, c);
        let left = NatOps::mul(d, a, c);
        let right = NatOps::mul(d, b, c);
        let hypothesis = d.eq(left, right);
        let conclusion = d.eq(a, b);
        let stmt = {
            let inner = d.arrow(hypothesis, conclusion);
            d.arrow(positive, inner)
        };
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hh_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(hh_fv);
        let start = NatOps::mul(d, c, a);
        let target = NatOps::mul(d, c, b);
        let first = d.lemma(nat.mul_comm, &[c, a]);
        let last = d.lemma(nat.mul_comm, &[b, c]);
        let (_, chained) = d.chain(start, &[(left, first), (right, hh), (target, last)]);
        let body = d.lemma(nat.mul_left_cancel_of_pos, &[c, a, b, hp, chained]);
        let proof = {
            let with_h = d.lam_fv(hh_fv, hypothesis, body);
            d.lam_fv(hp_fv, positive, with_h)
        };
        (stmt, proof)
    })?;

    // nat_dvd_antisymm_pos : ∀ a b, 1 ≤ a → 1 ≤ b → a ∣ b → b ∣ a → a = b.
    // Positivity is load-bearing in `le_of_dvd` (2 ∣ 0 but 2 ≰ 0).
    d.theorem(p.nat_dvd_antisymm_pos, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let unit = d.num(1);
        let a_pos = NatOps::le(d, unit, a);
        let b_pos = NatOps::le(d, unit, b);
        let forward = d.dvd(a, b);
        let backward = d.dvd(b, a);
        let conclusion = d.eq(a, b);
        let stmt = {
            let after_backward = d.arrow(backward, conclusion);
            let after_forward = d.arrow(forward, after_backward);
            let after_b = d.arrow(b_pos, after_forward);
            d.arrow(a_pos, after_b)
        };
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);
        let a_le_b = d.lemma(nat.le_of_dvd, &[a, b, hb, hf]);
        let b_le_a = d.lemma(nat.le_of_dvd, &[b, a, ha, hg]);
        let body = d.lemma(nat.le_antisymm, &[a, b, a_le_b, b_le_a]);
        let proof = {
            let with_g = d.lam_fv(hg_fv, backward, body);
            let with_f = d.lam_fv(hf_fv, forward, with_g);
            let with_b = d.lam_fv(hb_fv, b_pos, with_f);
            d.lam_fv(ha_fv, a_pos, with_b)
        };
        (stmt, proof)
    })?;

    declare_gauss(d, p)?;

    // of_nat_inj : ∀ a b, ofNat a = ofNat b → a = b.
    // `natAbs (ofNat a)` ι-reduces to `a`, so the congruence IS the statement.
    d.theorem(p.of_nat_inj, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let left = d.of_nat(a);
        let right = d.of_nat(b);
        let hypothesis = d.ieq(left, right);
        let conclusion = d.eq(a, b);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = int_eq_to_nat(d, left, right, h, &|d, x| d.const_app(int.nat_abs, &[x]));
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // not_zero_le_neg_of_nat : ∀ k, 1 ≤ k → Int.le Int.zero (Int.negOfNat k) → False.
    // At `k = succ j` the hypothesis is `Int.le (ofNat 0) (negSucc j)`, which
    // UNFOLDS to `False` — the branch is the identity.
    d.theorem(p.not_zero_le_neg_of_nat, 1, &|d, v| {
        let k = v[0];
        let unit = d.num(1);
        let positive = NatOps::le(d, unit, k);
        let claim = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let negated = d.neg_of_nat(x);
            let zero = d.izero();
            let bound = d.ile(zero, negated);
            let false_ty = d.false_ty();
            d.arrow(bound, false_ty)
        };
        let stmt = {
            let inner = claim(d, k);
            d.arrow(positive, inner)
        };
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let body = pos_cases(d, k, hp, &claim, &|d, j| {
            let successor = d.succ(j);
            let negated = d.neg_of_nat(successor);
            let zero = d.izero();
            let bound = d.ile(zero, negated);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            d.lam_fv(h_fv, bound, h)
        });
        let proof = d.lam_fv(hp_fv, positive, body);
        (stmt, proof)
    })?;

    // nat_div_cross : ∀ g x y, 1 ≤ g → g ∣ x → g ∣ y → (x/g)*y = x*(y/g).
    // Dividing EITHER side of a product by a common divisor gives the same
    // answer — which is exactly the sense in which `Rat.normalize` keeps the
    // value it was handed.
    d.theorem(p.nat_div_cross, 3, &|d, v| {
        let (g, x, y) = (v[0], v[1], v[2]);
        let unit = d.num(1);
        let positive = NatOps::le(d, unit, g);
        let divides_x = d.dvd(g, x);
        let divides_y = d.dvd(g, y);
        let reduced_x = NatOps::div(d, x, g);
        let reduced_y = NatOps::div(d, y, g);
        let left = NatOps::mul(d, reduced_x, y);
        let right = NatOps::mul(d, x, reduced_y);
        let conclusion = d.eq(left, right);
        let stmt = {
            let after_y = d.arrow(divides_y, conclusion);
            let after_x = d.arrow(divides_x, after_y);
            d.arrow(positive, after_x)
        };
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv);
        let cancel_x = d.lemma(nat.div_mul_cancel_of_dvd, &[g, x, hp, hx]);
        let cancel_y = d.lemma(nat.div_mul_cancel_of_dvd, &[g, y, hp, hy]);
        let scaled_y = NatOps::mul(d, g, reduced_y);
        let scaled_x = NatOps::mul(d, g, reduced_x);
        let expanded = {
            let back = d.symm(scaled_y, y, cancel_y);
            d.congr(y, scaled_y, back, &|d, t| NatOps::mul(d, reduced_x, t))
        };
        let nested = NatOps::mul(d, reduced_x, scaled_y);
        let flat_head = NatOps::mul(d, reduced_x, g);
        let flat = NatOps::mul(d, flat_head, reduced_y);
        let regroup = {
            let forward = d.lemma(nat.mul_assoc, &[reduced_x, g, reduced_y]);
            d.symm(flat, nested, forward)
        };
        let commuted_head = NatOps::mul(d, g, reduced_x);
        let commute = d.lemma(nat.mul_comm, &[reduced_x, g]);
        let swapped = d.congr(flat_head, commuted_head, commute, &|d, t| {
            NatOps::mul(d, t, reduced_y)
        });
        let commuted = NatOps::mul(d, commuted_head, reduced_y);
        let closed = d.congr(scaled_x, x, cancel_x, &|d, t| NatOps::mul(d, t, reduced_y));
        let (_, chained) = d.chain(
            left,
            &[
                (nested, expanded),
                (flat, regroup),
                (commuted, swapped),
                (right, closed),
            ],
        );
        let proof = {
            let with_y = d.lam_fv(hy_fv, divides_y, chained);
            let with_x = d.lam_fv(hx_fv, divides_x, with_y);
            d.lam_fv(hp_fv, positive, with_x)
        };
        (stmt, proof)
    })?;

    declare_nat_abs_mul(d, p)?;
    declare_int_cancellation(d, p)?;
    declare_int_order(d, p)
}

/// `nat_abs_mul_of_nat : ∀ (x : Int) (k : Nat), natAbs (x * ofNat k) = natAbs x * k`.
///
/// A two-branch split that is `rfl` on the left and `nat_abs_neg_of_nat` on the
/// right: `ofNat m * ofNat k` ι-reduces to `ofNat (m·k)` and `negSucc m * ofNat k`
/// to `negOfNat (succ m · k)`.
fn declare_nat_abs_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
        let scale = d.of_nat(k);
        let product = d.imul(args[0], scale);
        let left = d.const_app(int.nat_abs, &[product]);
        let magnitude = d.const_app(int.nat_abs, &[args[0]]);
        let right = NatOps::mul(d, magnitude, k);
        d.eq(left, right)
    };
    let body = case_split(d, &[x], &statement, &|d, branches| match branches[0].0 {
        Shape::OfNat => {
            let m = branches[0].1;
            let product = NatOps::mul(d, m, k);
            d.refl(product)
        }
        Shape::NegSucc => {
            let m = branches[0].1;
            let successor = d.succ(m);
            let product = NatOps::mul(d, successor, k);
            d.lemma(int.nat_abs_neg_of_nat, &[product])
        }
    });
    let ty = {
        let inner = statement(d, &[x]);
        let with_k = d.pi_fv(k_fv, nat_ty, inner);
        d.pi_fv(x_fv, int_ty, with_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat_ty, body);
        d.lam_fv(x_fv, int_ty, with_k)
    };
    d.declare_theorem(p.nat_abs_mul_of_nat, ty, value)
}

/// Gauss's lemma over `ℕ`, from a Bézout certificate scaled by `b`.
fn declare_gauss(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    d.theorem(p.nat_gauss, 3, &|d, v| {
        let (k, a, b) = (v[0], v[1], v[2]);
        let unit = d.num(1);
        let positive = NatOps::le(d, unit, k);
        let common = NatOps::gcd(d, a, k);
        let coprime = d.eq(common, unit);
        let product = NatOps::mul(d, a, b);
        let divides_product = d.dvd(k, product);
        let conclusion = d.dvd(k, b);
        let stmt = {
            let after_product = d.arrow(divides_product, conclusion);
            let after_coprime = d.arrow(coprime, after_product);
            d.arrow(positive, after_coprime)
        };

        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        // `bezout k a (gcd k a)`, moved along `gcd k a = 1`.
        let certificate = {
            let base = d.lemma(nat.gcd_bezout, &[a, k]);
            let motive = d.eq_motive(common, &|d, x| d.bezout(a, k, x));
            d.transport(common, motive, base, unit, hg)
        };

        let body = bezout_elim(
            d,
            a,
            k,
            unit,
            conclusion,
            certificate,
            &|d, mp, mn, np, nn, equation| {
                let a_mn = NatOps::mul(d, a, mn);
                let k_nn = NatOps::mul(d, k, nn);
                let a_mp = NatOps::mul(d, a, mp);
                let k_np = NatOps::mul(d, k, np);
                let left_head = NatOps::add(d, unit, a_mn);
                let left = NatOps::add(d, left_head, k_nn);
                let right = NatOps::add(d, a_mp, k_np);

                // Scale the identity by `b`.
                let scaled = d.congr(left, right, equation, &|d, t| NatOps::mul(d, t, b));
                let left_b = NatOps::mul(d, left, b);
                let right_b = NatOps::mul(d, right, b);
                let a_mn_b = NatOps::mul(d, a_mn, b);
                let k_nn_b = NatOps::mul(d, k_nn, b);
                let a_mp_b = NatOps::mul(d, a_mp, b);
                let k_np_b = NatOps::mul(d, k_np, b);

                // `(k·x)·b = k·(x·b)`, so `dvd_mul` applies after reassociating.
                let divides_k_multiple = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                    let inner = NatOps::mul(d, x, b);
                    let base = d.lemma(nat.dvd_mul, &[k, inner]);
                    let assoc = d.lemma(nat.mul_assoc, &[k, x, b]);
                    let head = NatOps::mul(d, k, x);
                    let flat = NatOps::mul(d, head, b);
                    let nested = NatOps::mul(d, k, inner);
                    let back = d.symm(flat, nested, assoc);
                    let motive = d.eq_motive(nested, &|d, y| d.dvd(k, y));
                    d.transport(nested, motive, base, flat, back)
                };
                // `(a·b)·x = a·(b·x) = a·(x·b) = (a·x)·b`, so `k ∣ a·b` carries.
                let divides_a_multiple = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                    let base = d.lemma(nat.dvd_mul_right_of_dvd, &[k, product, x, hd]);
                    let product_x = NatOps::mul(d, product, x);
                    let a_x = NatOps::mul(d, a, x);
                    let flat = NatOps::mul(d, a_x, b);
                    let b_x = NatOps::mul(d, b, x);
                    let x_b = NatOps::mul(d, x, b);
                    let first = d.lemma(nat.mul_assoc, &[a, b, x]);
                    let nested_bx = NatOps::mul(d, a, b_x);
                    let commute = d.lemma(nat.mul_comm, &[b, x]);
                    let second = d.congr(b_x, x_b, commute, &|d, t| NatOps::mul(d, a, t));
                    let nested_xb = NatOps::mul(d, a, x_b);
                    let assoc_back = d.lemma(nat.mul_assoc, &[a, x, b]);
                    let third = d.symm(flat, nested_xb, assoc_back);
                    let (_, chained) = d.chain(
                        product_x,
                        &[(nested_bx, first), (nested_xb, second), (flat, third)],
                    );
                    let motive = d.eq_motive(product_x, &|d, y| d.dvd(k, y));
                    d.transport(product_x, motive, base, flat, chained)
                };

                let d_a_mn_b = divides_a_multiple(d, mn);
                let d_k_nn_b = divides_k_multiple(d, nn);
                let d_a_mp_b = divides_a_multiple(d, mp);
                let d_k_np_b = divides_k_multiple(d, np);

                let excess = NatOps::add(d, a_mn_b, k_nn_b);
                let divides_excess = d.lemma(nat.dvd_add, &[k, a_mn_b, k_nn_b, d_a_mn_b, d_k_nn_b]);
                let total = NatOps::add(d, a_mp_b, k_np_b);
                let divides_total = d.lemma(nat.dvd_add, &[k, a_mp_b, k_np_b, d_a_mp_b, d_k_np_b]);
                let right_expand = d.lemma(nat.right_distrib, &[a_mp, k_np, b]);
                let divides_right_b = {
                    let back = d.symm(right_b, total, right_expand);
                    let motive = d.eq_motive(total, &|d, y| d.dvd(k, y));
                    d.transport(total, motive, divides_total, right_b, back)
                };

                // `left·b = (b + k·mn·b) + a·nn·b = b + X`.
                let outer = d.lemma(nat.right_distrib, &[left_head, k_nn, b]);
                let head_b = NatOps::mul(d, left_head, b);
                let split_outer = NatOps::add(d, head_b, k_nn_b);
                let inner_expand = d.lemma(nat.right_distrib, &[unit, a_mn, b]);
                let unit_b = NatOps::mul(d, unit, b);
                let split_inner = NatOps::add(d, unit_b, a_mn_b);
                let step_inner = d.congr(head_b, split_inner, inner_expand, &|d, t| {
                    NatOps::add(d, t, k_nn_b)
                });
                let with_unit = NatOps::add(d, split_inner, k_nn_b);
                let one_mul = d.lemma(nat.one_mul, &[b]);
                let b_plus = NatOps::add(d, b, a_mn_b);
                let step_one = d.congr(unit_b, b, one_mul, &|d, t| {
                    let head = NatOps::add(d, t, a_mn_b);
                    NatOps::add(d, head, k_nn_b)
                });
                let flattened = NatOps::add(d, b_plus, k_nn_b);
                let assoc = d.lemma(nat.add_assoc, &[b, a_mn_b, k_nn_b]);
                let b_plus_excess = NatOps::add(d, b, excess);
                let (_, left_normalised) = d.chain(
                    left_b,
                    &[
                        (split_outer, outer),
                        (with_unit, step_inner),
                        (flattened, step_one),
                        (b_plus_excess, assoc),
                    ],
                );

                let bridge = {
                    let back = d.symm(left_b, b_plus_excess, left_normalised);
                    let (_, joined) = d.chain(b_plus_excess, &[(left_b, back), (right_b, scaled)]);
                    joined
                };
                let divides_b_plus = {
                    let back = d.symm(b_plus_excess, right_b, bridge);
                    let motive = d.eq_motive(right_b, &|d, y| d.dvd(k, y));
                    d.transport(right_b, motive, divides_right_b, b_plus_excess, back)
                };
                let excess_plus_b = NatOps::add(d, excess, b);
                let commute = d.lemma(nat.add_comm, &[b, excess]);
                let divides_excess_plus = {
                    let motive = d.eq_motive(b_plus_excess, &|d, y| d.dvd(k, y));
                    d.transport(
                        b_plus_excess,
                        motive,
                        divides_b_plus,
                        excess_plus_b,
                        commute,
                    )
                };
                d.lemma(
                    nat.dvd_add_right_cancel_of_pos,
                    &[k, excess, b, hp, divides_excess, divides_excess_plus],
                )
            },
        );

        let proof = {
            let with_d = d.lam_fv(hd_fv, divides_product, body);
            let with_g = d.lam_fv(hg_fv, coprime, with_d);
            d.lam_fv(hp_fv, positive, with_g)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// `int_mul_right_cancel : ∀ (a b : Int) (c : Nat), 1 ≤ c →
/// a * ofNat c = b * ofNat c → a = b`.
///
/// The four-way split. `ofNat m * ofNat c` ι-reduces to `ofNat (m·c)` and
/// `negSucc m * ofNat c` to `negOfNat (succ m · c)`, so each branch is a
/// statement about naturals that the `Int` constructors merely wrap.
fn declare_int_cancellation(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let int = p.int;
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let positive_ty_c = {
        let unit = d.num(1);
        NatOps::le(d, unit, c)
    };
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let scale = d.of_nat(c);

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
        let left = d.imul(args[0], scale);
        let right = d.imul(args[1], scale);
        let hypothesis = d.ieq(left, right);
        let conclusion = d.ieq(args[0], args[1]);
        d.arrow(hypothesis, conclusion)
    };

    let body = case_split(d, &[a, b], &statement, &|d, branches| {
        let left_term = d.branch_term(branches[0]);
        let right_term = d.branch_term(branches[1]);
        let hypothesis = {
            let left = d.imul(left_term, scale);
            let right = d.imul(right_term, scale);
            d.ieq(left, right)
        };
        let conclusion = d.ieq(left_term, right_term);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // The impossible mixed-sign branches: a non-negative integer cannot
        // equal a negated positive natural.
        let clash =
            |d: &mut IntDev<'_>, magnitude: ExprId, negated_of: ExprId, equation: ExprId| {
                let positive = {
                    let successor = d.succ(negated_of);
                    let head = one_le_succ(d, negated_of);
                    let scaled = NatOps::mul(d, successor, c);
                    let _ = scaled;
                    d.lemma(nat.one_le_mul, &[successor, c, head, hc])
                };
                let lifted = d.of_nat(magnitude);
                let nonneg = d.lemma(p.int_zero_le_of_nat, &[magnitude]);
                let successor = d.succ(negated_of);
                let product = NatOps::mul(d, successor, c);
                let negated = d.neg_of_nat(product);
                let moved = d.int_eq_rewrite(lifted, negated, equation, nonneg, &|d, y| {
                    let zero = d.izero();
                    d.ile(zero, y)
                });
                let impossible = d.lemma(p.not_zero_le_neg_of_nat, &[product, positive, moved]);
                d.absurd(conclusion, impossible)
            };

        let body = match (branches[0].0, branches[1].0) {
            (Shape::OfNat, Shape::OfNat) => {
                let (m, n) = (branches[0].1, branches[1].1);
                let left = NatOps::mul(d, m, c);
                let right = NatOps::mul(d, n, c);
                let lifted = d.lemma(p.of_nat_inj, &[left, right, h]);
                let cancelled = d.lemma(p.nat_mul_right_cancel, &[c, m, n, hc, lifted]);
                d.nat_eq_to_int(m, n, cancelled, &|d, x| d.of_nat(x))
            }
            (Shape::OfNat, Shape::NegSucc) => {
                let (m, n) = (branches[0].1, branches[1].1);
                let magnitude = NatOps::mul(d, m, c);
                clash(d, magnitude, n, h)
            }
            (Shape::NegSucc, Shape::OfNat) => {
                let (m, n) = (branches[0].1, branches[1].1);
                let magnitude = NatOps::mul(d, n, c);
                let flipped = {
                    let left = d.imul(left_term, scale);
                    let right = d.imul(right_term, scale);
                    d.isymm(left, right, h)
                };
                clash(d, magnitude, m, flipped)
            }
            (Shape::NegSucc, Shape::NegSucc) => {
                let (m, n) = (branches[0].1, branches[1].1);
                let ma = d.succ(m);
                let na = d.succ(n);
                let ka = NatOps::mul(d, ma, c);
                let kb = NatOps::mul(d, na, c);
                let left = d.neg_of_nat(ka);
                let right = d.neg_of_nat(kb);
                let lifted =
                    int_eq_to_nat(d, left, right, h, &|d, y| d.const_app(int.nat_abs, &[y]));
                let magnitude_left = d.const_app(int.nat_abs, &[left]);
                let magnitude_right = d.const_app(int.nat_abs, &[right]);
                let recover_left = d.lemma(int.nat_abs_neg_of_nat, &[ka]);
                let recover_right = d.lemma(int.nat_abs_neg_of_nat, &[kb]);
                let back = d.symm(magnitude_left, ka, recover_left);
                let (_, chained) = d.chain(
                    ka,
                    &[
                        (magnitude_left, back),
                        (magnitude_right, lifted),
                        (kb, recover_right),
                    ],
                );
                let cancelled = d.lemma(p.nat_mul_right_cancel, &[c, ma, na, hc, chained]);
                d.nat_eq_to_int(ma, na, cancelled, &|d, x| d.neg_of_nat(x))
            }
        };
        d.lam_fv(h_fv, hypothesis, body)
    });

    let ty = {
        let inner = statement(d, &[a, b]);
        let with_hc = d.pi_fv(hc_fv, positive_ty_c, inner);
        let with_c = d.pi_fv(c_fv, nat_ty, with_hc);
        let with_b = d.pi_fv(b_fv, int_ty, with_c);
        d.pi_fv(a_fv, int_ty, with_b)
    };
    let value = {
        let with_hc = d.lam_fv(hc_fv, positive_ty_c, body);
        let with_c = d.lam_fv(c_fv, nat_ty, with_hc);
        let with_b = d.lam_fv(b_fv, int_ty, with_c);
        d.lam_fv(a_fv, int_ty, with_b)
    };
    d.declare_theorem(p.int_mul_right_cancel, ty, value)
}

/// The four `ℤ` order lemmas the rational order needs, all derived: no case
/// split, only `Int.le_total`, `Int.eq_em`, `Int.lt_of_le_of_ne` and
/// `Int.lt_irrefl` over the two primitives above.
fn declare_int_order(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    // A `∀ (a b : Int) (c : Nat), [1 ≤ c →] hypothesis → conclusion` telescope.
    let mixed = |d: &mut IntDev<'_>,
                 name,
                 needs_positive: bool,
                 build: &dyn Fn(
        &mut IntDev<'_>,
        ExprId,
        ExprId,
        ExprId,
        ExprId,
        ExprId,
    ) -> (ExprId, ExprId, ExprId)|
     -> Result<(), KernelError> {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let positive = {
            let unit = d.num(1);
            NatOps::le(d, unit, c)
        };
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let scale = d.of_nat(c);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let (hypothesis, conclusion, proof) = build(d, a, b, c, hc, h);
        let _ = scale;
        let mut ty = d.arrow(hypothesis, conclusion);
        let mut value = d.lam_fv(h_fv, hypothesis, proof);
        if needs_positive {
            ty = d.pi_fv(hc_fv, positive, ty);
            value = d.lam_fv(hc_fv, positive, value);
        }
        ty = d.pi_fv(c_fv, nat_ty, ty);
        value = d.lam_fv(c_fv, nat_ty, value);
        ty = d.pi_fv(b_fv, int_ty, ty);
        value = d.lam_fv(b_fv, int_ty, value);
        ty = d.pi_fv(a_fv, int_ty, ty);
        value = d.lam_fv(a_fv, int_ty, value);
        d.declare_theorem(name, ty, value)
    };

    // int_mul_le_mul_right : le a b → le (a·ofNat c) (b·ofNat c).
    mixed(d, p.int_mul_le_mul_right, false, &|d, a, b, c, _hc, h| {
        let scale = d.of_nat(c);
        let hypothesis = d.ile(a, b);
        let scaled_a = d.imul(a, scale);
        let scaled_b = d.imul(b, scale);
        let conclusion = d.ile(scaled_a, scaled_b);
        let nonneg = d.lemma(p.int_zero_le_of_nat, &[c]);
        let base = d.lemma(int.mul_le_mul_of_nonneg_left, &[scale, a, b, nonneg, h]);
        let left_scaled = d.imul(scale, a);
        let right_scaled = d.imul(scale, b);
        let commute_a = d.lemma(int.mul_comm, &[scale, a]);
        let commute_b = d.lemma(int.mul_comm, &[scale, b]);
        let first = d.int_eq_rewrite(left_scaled, scaled_a, commute_a, base, &|d, x| {
            d.ile(x, right_scaled)
        });
        let proof = d.int_eq_rewrite(right_scaled, scaled_b, commute_b, first, &|d, x| {
            d.ile(scaled_a, x)
        });
        (hypothesis, conclusion, proof)
    })?;

    // int_mul_lt_mul_right : 1 ≤ c → lt a b → lt (a·ofNat c) (b·ofNat c).
    // Monotone for `le`, and the two sides cannot be EQUAL, because
    // cancellation would then give `a = b` against `lt a b`.
    mixed(d, p.int_mul_lt_mul_right, true, &|d, a, b, c, hc, h| {
        let scale = d.of_nat(c);
        let hypothesis = d.ilt(a, b);
        let scaled_a = d.imul(a, scale);
        let scaled_b = d.imul(b, scale);
        let conclusion = d.ilt(scaled_a, scaled_b);
        let weak = d.lemma(int.le_of_lt, &[a, b, h]);
        let monotone = d.lemma(p.int_mul_le_mul_right, &[a, b, c, weak]);
        let distinct = {
            let equal = d.ieq(scaled_a, scaled_b);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let same = d.lemma(p.int_mul_right_cancel, &[a, b, c, hc, e]);
            let back = d.isymm(a, b, same);
            let reflexive = d.int_eq_rewrite(b, a, back, h, &|d, y| d.ilt(a, y));
            let impossible = d.lemma(int.lt_irrefl, &[a, reflexive]);
            d.lam_fv(e_fv, equal, impossible)
        };
        let proof = d.lemma(
            int.lt_of_le_of_ne,
            &[scaled_a, scaled_b, monotone, distinct],
        );
        (hypothesis, conclusion, proof)
    })?;

    // int_le_of_mul_le_mul_right : 1 ≤ c → le (a·C) (b·C) → le a b.
    mixed(
        d,
        p.int_le_of_mul_le_mul_right,
        true,
        &|d, a, b, c, hc, h| {
            let scale = d.of_nat(c);
            let scaled_a = d.imul(a, scale);
            let scaled_b = d.imul(b, scale);
            let hypothesis = d.ile(scaled_a, scaled_b);
            let conclusion = d.ile(a, b);
            let forward = d.ile(a, b);
            let backward = d.ile(b, a);
            let total = d.lemma(int.le_total, &[a, b]);
            let proof = d.or_elim(
                forward,
                backward,
                conclusion,
                total,
                &|_d, ordered| ordered,
                &|d, reversed| {
                    let equal = d.ieq(a, b);
                    let distinct = d.not(equal);
                    let decided = d.lemma(int.eq_em, &[a, b]);
                    d.or_elim(
                        equal,
                        distinct,
                        conclusion,
                        decided,
                        &|d, same| {
                            let reflexive = d.lemma(int.le_refl, &[a]);
                            d.int_eq_rewrite(a, b, same, reflexive, &|d, y| d.ile(a, y))
                        },
                        &|d, different| {
                            let flipped = {
                                let reversed_equal = d.ieq(b, a);
                                let e_fv = d.fresh_fvar();
                                let e = d.kernel().fvar(e_fv);
                                let straight = d.isymm(b, a, e);
                                let impossible = d.apply(different, &[straight]);
                                d.lam_fv(e_fv, reversed_equal, impossible)
                            };
                            let strict = d.lemma(int.lt_of_le_of_ne, &[b, a, reversed, flipped]);
                            let scaled = d.lemma(p.int_mul_lt_mul_right, &[b, a, c, hc, strict]);
                            let cycle = d.lemma(
                                int.lt_of_lt_of_le,
                                &[scaled_b, scaled_a, scaled_b, scaled, h],
                            );
                            let impossible = d.lemma(int.lt_irrefl, &[scaled_b, cycle]);
                            d.absurd(conclusion, impossible)
                        },
                    )
                },
            );
            (hypothesis, conclusion, proof)
        },
    )?;

    // int_lt_of_mul_lt_mul_right : 1 ≤ c → lt (a·C) (b·C) → lt a b.
    mixed(
        d,
        p.int_lt_of_mul_lt_mul_right,
        true,
        &|d, a, b, c, _hc, h| {
            let scale = d.of_nat(c);
            let scaled_a = d.imul(a, scale);
            let scaled_b = d.imul(b, scale);
            let hypothesis = d.ilt(scaled_a, scaled_b);
            let conclusion = d.ilt(a, b);
            let equal = d.ieq(a, b);
            let distinct = d.not(equal);
            let decided = d.lemma(int.eq_em, &[a, b]);
            let proof = d.or_elim(
                equal,
                distinct,
                conclusion,
                decided,
                &|d, same| {
                    let congruent = d.icongr(a, b, same, &|d, x| d.imul(x, scale));
                    let back = d.isymm(scaled_a, scaled_b, congruent);
                    let reflexive =
                        d.int_eq_rewrite(scaled_b, scaled_a, back, h, &|d, y| d.ilt(scaled_a, y));
                    let impossible = d.lemma(int.lt_irrefl, &[scaled_a, reflexive]);
                    d.absurd(conclusion, impossible)
                },
                &|d, different| {
                    let forward = d.ile(a, b);
                    let backward = d.ile(b, a);
                    let total = d.lemma(int.le_total, &[a, b]);
                    d.or_elim(
                        forward,
                        backward,
                        conclusion,
                        total,
                        &|d, ordered| d.lemma(int.lt_of_le_of_ne, &[a, b, ordered, different]),
                        &|d, reversed| {
                            let monotone = d.lemma(p.int_mul_le_mul_right, &[b, a, c, reversed]);
                            let cycle = d.lemma(
                                int.lt_of_lt_of_le,
                                &[scaled_a, scaled_b, scaled_a, h, monotone],
                            );
                            let impossible = d.lemma(int.lt_irrefl, &[scaled_a, cycle]);
                            d.absurd(conclusion, impossible)
                        },
                    )
                },
            );
            (hypothesis, conclusion, proof)
        },
    )
}

/// **Uniqueness of the reduced representative**, in both directions.
///
/// `eq_of_cross : num q * ofNat (den r) = num r * ofNat (den q) → q = r`.
///
/// This is the one step that makes a normalised structure behave like a
/// quotient, and the whole reason `Rat` can carry ordinary `Eq` at all. The
/// argument, over `ℕ` after taking magnitudes:
///
/// ```text
/// |n_q|·d_r = |n_r|·d_q                 the hypothesis, via natAbs
/// d_q ∣ |n_q|·d_r   and  gcd |n_q| d_q = 1   ⟹  d_q ∣ d_r      (Gauss)
/// d_r ∣ |n_r|·d_q   and  gcd |n_r| d_r = 1   ⟹  d_r ∣ d_q      (Gauss)
/// d_q = d_r                                   (antisymmetry, both positive)
/// n_q = n_r                                   (cancel ofNat d_r, positive)
/// ```
///
/// Both `Rat.reduced` fields are load-bearing and both positivity fields are
/// load-bearing: drop reducedness and `1/2 = 2/4` is a counterexample to the
/// conclusion; drop positivity and `d ∣ 0` makes the antisymmetry step false.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniqueness(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let int = p.int;

    rat_theorem(d, p.eq_of_cross, 2, &|d, v| {
        let (q, r) = (v[0], v[1]);
        let nq = num(d, q);
        let nr = num(d, r);
        let dq = den(d, q);
        let dr = den(d, r);
        let scale_q = d.of_nat(dq);
        let scale_r = d.of_nat(dr);
        let cross_left = d.imul(nq, scale_r);
        let cross_right = d.imul(nr, scale_q);
        let hypothesis = d.ieq(cross_left, cross_right);
        let conclusion = req(d, q, r);
        let stmt = d.arrow(hypothesis, conclusion);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // The hypothesis, taken to ℕ: |n_q|·d_r = |n_r|·d_q.
        let magnitude_q = d.const_app(int.nat_abs, &[nq]);
        let magnitude_r = d.const_app(int.nat_abs, &[nr]);
        let lifted = int_eq_to_nat(d, cross_left, cross_right, h, &|d, y| {
            d.const_app(int.nat_abs, &[y])
        });
        let left_abs = d.const_app(int.nat_abs, &[cross_left]);
        let right_abs = d.const_app(int.nat_abs, &[cross_right]);
        let left_split = d.lemma(p.nat_abs_mul_of_nat, &[nq, dr]);
        let right_split = d.lemma(p.nat_abs_mul_of_nat, &[nr, dq]);
        let left_product = NatOps::mul(d, magnitude_q, dr);
        let right_product = NatOps::mul(d, magnitude_r, dq);
        let back = d.symm(left_abs, left_product, left_split);
        let (_, equation) = d.chain(
            left_product,
            &[
                (left_abs, back),
                (right_abs, lifted),
                (right_product, right_split),
            ],
        );

        let positive_q = super::ops::den_pos(d, q);
        let positive_r = super::ops::den_pos(d, r);
        let coprime_q = super::ops::reduced(d, q);
        let coprime_r = super::ops::reduced(d, r);

        // d_q ∣ |n_q|·d_r, from `d_q ∣ d_q·|n_r|` moved along the equation.
        let divides_forward = {
            let seed = d.lemma(nat.dvd_mul, &[dq, magnitude_r]);
            let staged = NatOps::mul(d, dq, magnitude_r);
            let commute = d.lemma(nat.mul_comm, &[dq, magnitude_r]);
            let motive = d.eq_motive(staged, &|d, y| d.dvd(dq, y));
            let at_right = d.transport(staged, motive, seed, right_product, commute);
            let reversed = d.symm(left_product, right_product, equation);
            let motive = d.eq_motive(right_product, &|d, y| d.dvd(dq, y));
            d.transport(right_product, motive, at_right, left_product, reversed)
        };
        let dq_divides_dr = d.lemma(
            p.nat_gauss,
            &[dq, magnitude_q, dr, positive_q, coprime_q, divides_forward],
        );
        // d_r ∣ |n_r|·d_q, symmetrically.
        let divides_backward = {
            let seed = d.lemma(nat.dvd_mul, &[dr, magnitude_q]);
            let staged = NatOps::mul(d, dr, magnitude_q);
            let commute = d.lemma(nat.mul_comm, &[dr, magnitude_q]);
            let motive = d.eq_motive(staged, &|d, y| d.dvd(dr, y));
            let at_left = d.transport(staged, motive, seed, left_product, commute);
            let motive = d.eq_motive(left_product, &|d, y| d.dvd(dr, y));
            d.transport(left_product, motive, at_left, right_product, equation)
        };
        let dr_divides_dq = d.lemma(
            p.nat_gauss,
            &[dr, magnitude_r, dq, positive_r, coprime_r, divides_backward],
        );
        let denominators = d.lemma(
            p.nat_dvd_antisymm_pos,
            &[dq, dr, positive_q, positive_r, dq_divides_dr, dr_divides_dq],
        );

        // With the denominators equal, cancel the (positive) common factor.
        let aligned = d.nat_rewrite(dq, dr, denominators, h, &|d, x| {
            let lifted = d.of_nat(x);
            let right = d.imul(nr, lifted);
            d.ieq(cross_left, right)
        });
        let numerators = d.lemma(p.int_mul_right_cancel, &[nq, nr, dr, positive_r, aligned]);
        let body = d.const_app(p.ext, &[q, r, numerators, denominators]);
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // cross_of_eq : the converse, one transport.
    rat_theorem(d, p.cross_of_eq, 2, &|d, v| {
        let (q, r) = (v[0], v[1]);
        let claim = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let nq = num(d, q);
            let nx = num(d, x);
            let dq = den(d, q);
            let dx = den(d, x);
            let scale_x = d.of_nat(dx);
            let scale_q = d.of_nat(dq);
            let left = d.imul(nq, scale_x);
            let right = d.imul(nx, scale_q);
            d.ieq(left, right)
        };
        let hypothesis = req(d, q, r);
        let conclusion = claim(d, r);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let base = {
            let start = claim(d, q);
            let _ = start;
            let nq = num(d, q);
            let dq = den(d, q);
            let scale = d.of_nat(dq);
            let side = d.imul(nq, scale);
            d.irefl(side)
        };
        let body = super::ops::rat_eq_rewrite(d, q, r, h, base, &claim);
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// `Rat.normalize` keeps the value it was handed, and therefore respects
/// cross-equality.
///
/// - `normalize_cross` — `num (normalize n d h) · d = n · den (normalize n d h)`.
///   Both branches are `nat_div_cross` (dividing either side of a product by a
///   common divisor gives the same answer) wrapped in the constructor the
///   numerator's sign selects.
/// - `normalize_congr` — the workhorse. Two `normalize` calls agree whenever
///   their inputs cross-multiply equal. Everything downstream is an instance:
///   a ring law over `ℚ` is `normalize_congr` applied to an identity in `ℤ`.
/// - `self_normalize` — normalising an already-reduced pair changes nothing.
/// - `add_cross` / `mul_cross` — `normalize_cross` read at the pair `Rat.add`
///   and `Rat.mul` actually build, which is how a law reaches the projections
///   of a sum or a product without unfolding `normalize` again.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_normalize_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let int = p.int;
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();

    // --- normalize_cross ---------------------------------------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let dd_fv = d.fresh_fvar();
        let dd = d.kernel().fvar(dd_fv);
        let positive = positive_ty(d, dd);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| -> ExprId {
            let reduced = normalize(d, args[0], dd, h);
            let numerator = num(d, reduced);
            let denominator = den(d, reduced);
            let scale = d.of_nat(dd);
            let left = d.imul(numerator, scale);
            let lifted = d.of_nat(denominator);
            let right = d.imul(args[0], lifted);
            d.ieq(left, right)
        };
        // Both branches share the ℕ identity; only the wrapper differs.
        let divided = |d: &mut IntDev<'_>, magnitude: ExprId| -> (ExprId, ExprId, ExprId) {
            let common = NatOps::gcd(d, magnitude, dd);
            let divides_magnitude = d.lemma(nat.gcd_dvd_left, &[magnitude, dd]);
            let divides_den = d.lemma(nat.gcd_dvd_right, &[magnitude, dd]);
            let common_positive = d.lemma(nat.one_le_of_dvd_pos, &[common, dd, h, divides_den]);
            let identity = d.lemma(
                p.nat_div_cross,
                &[
                    common,
                    magnitude,
                    dd,
                    common_positive,
                    divides_magnitude,
                    divides_den,
                ],
            );
            let reduced_magnitude = NatOps::div(d, magnitude, common);
            let reduced_den = NatOps::div(d, dd, common);
            let left = NatOps::mul(d, reduced_magnitude, dd);
            let right = NatOps::mul(d, magnitude, reduced_den);
            let _ = (left, right);
            (identity, reduced_magnitude, reduced_den)
        };
        let body = case_split(d, &[n], &statement, &|d, branches| match branches[0].0 {
            Shape::OfNat => {
                let m = branches[0].1;
                let (identity, reduced_magnitude, reduced_den) = divided(d, m);
                let left = NatOps::mul(d, reduced_magnitude, dd);
                let right = NatOps::mul(d, m, reduced_den);
                d.nat_eq_to_int(left, right, identity, &|d, x| d.of_nat(x))
            }
            Shape::NegSucc => {
                let m = branches[0].1;
                let magnitude = d.succ(m);
                let (identity, reduced_magnitude, reduced_den) = divided(d, magnitude);
                let left = NatOps::mul(d, reduced_magnitude, dd);
                let right = NatOps::mul(d, magnitude, reduced_den);
                let negated = d.neg_of_nat(reduced_magnitude);
                let scale = d.of_nat(dd);
                let start = d.imul(negated, scale);
                let folded = d.lemma(int.mul_neg_of_nat_of_nat, &[reduced_magnitude, dd]);
                let middle = d.neg_of_nat(left);
                let rewritten = d.nat_eq_to_int(left, right, identity, &|d, x| d.neg_of_nat(x));
                let target = d.neg_of_nat(right);
                let (_, chained) = d.ichain(start, &[(middle, folded), (target, rewritten)]);
                chained
            }
        });
        let ty = {
            let inner = statement(d, &[n]);
            let with_h = d.pi_fv(h_fv, positive, inner);
            let with_dd = d.pi_fv(dd_fv, nat_ty, with_h);
            d.pi_fv(n_fv, int_ty, with_dd)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, positive, body);
            let with_dd = d.lam_fv(dd_fv, nat_ty, with_h);
            d.lam_fv(n_fv, int_ty, with_dd)
        };
        d.declare_theorem(p.normalize_cross, ty, value)?;
    }

    // --- normalize_congr ---------------------------------------------------
    {
        let n1_fv = d.fresh_fvar();
        let n1 = d.kernel().fvar(n1_fv);
        let e1_fv = d.fresh_fvar();
        let e1 = d.kernel().fvar(e1_fv);
        let positive_1 = positive_ty(d, e1);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        let e2_fv = d.fresh_fvar();
        let e2 = d.kernel().fvar(e2_fv);
        let positive_2 = positive_ty(d, e2);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let scale_1 = d.of_nat(e1);
        let scale_2 = d.of_nat(e2);
        let hypothesis = {
            let left = d.imul(n1, scale_2);
            let right = d.imul(n2, scale_1);
            d.ieq(left, right)
        };
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let x = normalize(d, n1, e1, h1);
        let y = normalize(d, n2, e2, h2);
        let conclusion = req(d, x, y);
        let num_x = num(d, x);
        let num_y = num(d, y);
        let den_x = {
            let raw = den(d, x);
            d.of_nat(raw)
        };
        let den_y = {
            let raw = den(d, y);
            d.of_nat(raw)
        };
        let keeps_x = d.lemma(p.normalize_cross, &[n1, e1, h1]);
        let keeps_y = d.lemma(p.normalize_cross, &[n2, e2, h2]);

        let product = d.imul(scale_1, scale_2);
        let left_head = d.imul(num_x, den_y);
        let right_head = d.imul(num_y, den_x);
        let left_scaled = d.imul(left_head, product);
        let right_scaled = d.imul(right_head, product);

        // Left: (n_X·d_Y)·(e1·e2) → … → n2·(e1·(d_X·d_Y)).
        let l1 = iprod(d, &[num_x, den_y, scale_1, scale_2]);
        let s1 = d.lemma(int.mul_assoc, &[num_x, den_y, product]);
        let l2 = iprod(d, &[num_x, scale_1, den_y, scale_2]);
        let s2 = iprod_perm(
            d,
            &[num_x, den_y, scale_1, scale_2],
            &[num_x, scale_1, den_y, scale_2],
        );
        let l3 = iprod(d, &[n1, den_x, den_y, scale_2]);
        let s3 = iprod_head_rewrite(d, num_x, scale_1, &[den_y, scale_2], n1, den_x, keeps_x);
        let l4 = iprod(d, &[n1, scale_2, den_x, den_y]);
        let s4 = iprod_perm(
            d,
            &[n1, den_x, den_y, scale_2],
            &[n1, scale_2, den_x, den_y],
        );
        let l5 = iprod(d, &[n2, scale_1, den_x, den_y]);
        let s5 = iprod_head_rewrite(d, n1, scale_2, &[den_x, den_y], n2, scale_1, hyp);
        let (_, left_chain) = d.ichain(
            left_scaled,
            &[(l1, s1), (l2, s2), (l3, s3), (l4, s4), (l5, s5)],
        );

        // Right: (n_Y·d_X)·(e1·e2) → … → the same normal form.
        let r1 = iprod(d, &[num_y, den_x, scale_1, scale_2]);
        let t1 = d.lemma(int.mul_assoc, &[num_y, den_x, product]);
        let r2 = iprod(d, &[num_y, scale_2, den_x, scale_1]);
        let t2 = iprod_perm(
            d,
            &[num_y, den_x, scale_1, scale_2],
            &[num_y, scale_2, den_x, scale_1],
        );
        let r3 = iprod(d, &[n2, den_y, den_x, scale_1]);
        let t3 = iprod_head_rewrite(d, num_y, scale_2, &[den_x, scale_1], n2, den_y, keeps_y);
        let r4 = iprod(d, &[n2, scale_1, den_x, den_y]);
        let t4 = iprod_perm(
            d,
            &[n2, den_y, den_x, scale_1],
            &[n2, scale_1, den_x, den_y],
        );
        let (_, right_chain) = d.ichain(right_scaled, &[(r1, t1), (r2, t2), (r3, t3), (r4, t4)]);

        let joined = {
            let back = d.isymm(right_scaled, r4, right_chain);
            d.itrans(left_scaled, l5, right_scaled, left_chain, back)
        };
        let common = NatOps::mul(d, e1, e2);
        let common_positive = d.lemma(nat.one_le_mul, &[e1, e2, h1, h2]);
        let cross = d.lemma(
            p.int_mul_right_cancel,
            &[left_head, right_head, common, common_positive, joined],
        );
        let body = d.const_app(p.eq_of_cross, &[x, y, cross]);

        let ty = {
            let with_hyp = d.pi_fv(hyp_fv, hypothesis, conclusion);
            let with_h2 = d.pi_fv(h2_fv, positive_2, with_hyp);
            let with_e2 = d.pi_fv(e2_fv, nat_ty, with_h2);
            let with_n2 = d.pi_fv(n2_fv, int_ty, with_e2);
            let with_h1 = d.pi_fv(h1_fv, positive_1, with_n2);
            let with_e1 = d.pi_fv(e1_fv, nat_ty, with_h1);
            d.pi_fv(n1_fv, int_ty, with_e1)
        };
        let value = {
            let with_hyp = d.lam_fv(hyp_fv, hypothesis, body);
            let with_h2 = d.lam_fv(h2_fv, positive_2, with_hyp);
            let with_e2 = d.lam_fv(e2_fv, nat_ty, with_h2);
            let with_n2 = d.lam_fv(n2_fv, int_ty, with_e2);
            let with_h1 = d.lam_fv(h1_fv, positive_1, with_n2);
            let with_e1 = d.lam_fv(e1_fv, nat_ty, with_h1);
            d.lam_fv(n1_fv, int_ty, with_e1)
        };
        d.declare_theorem(p.normalize_congr, ty, value)?;
    }

    // --- self_normalize ----------------------------------------------------
    rat_theorem(d, p.self_normalize, 1, &|d, v| {
        let q = v[0];
        let numerator = num(d, q);
        let denominator = den(d, q);
        let positive = super::ops::den_pos(d, q);
        let renormalised = normalize(d, numerator, denominator, positive);
        let stmt = req(d, renormalised, q);
        let keeps = d.lemma(p.normalize_cross, &[numerator, denominator, positive]);
        let proof = d.const_app(p.eq_of_cross, &[renormalised, q, keeps]);
        (stmt, proof)
    })?;

    // --- add_cross / mul_cross ---------------------------------------------
    let over_pair = |d: &mut IntDev<'_>,
                     name,
                     numerator: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
                     combine: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId|
     -> Result<(), KernelError> {
        rat_theorem(d, name, 2, &|d, v| {
            let (a, b) = (v[0], v[1]);
            let den_a = den(d, a);
            let den_b = den(d, b);
            let combined_num = numerator(d, a, b);
            let combined_den = NatOps::mul(d, den_a, den_b);
            let positive_a = super::ops::den_pos(d, a);
            let positive_b = super::ops::den_pos(d, b);
            let positive = d.lemma(nat.one_le_mul, &[den_a, den_b, positive_a, positive_b]);
            let result = combine(d, a, b);
            let result_num = num(d, result);
            let result_den = den(d, result);
            let scale = d.of_nat(combined_den);
            let left = d.imul(result_num, scale);
            let lifted = d.of_nat(result_den);
            let right = d.imul(combined_num, lifted);
            let stmt = d.ieq(left, right);
            let proof = d.lemma(p.normalize_cross, &[combined_num, combined_den, positive]);
            (stmt, proof)
        })
    };
    over_pair(
        d,
        p.add_cross,
        &|d, a, b| {
            let num_a = num(d, a);
            let num_b = num(d, b);
            let den_a = den(d, a);
            let den_b = den(d, b);
            let scale_b = d.of_nat(den_b);
            let scale_a = d.of_nat(den_a);
            let first = d.imul(num_a, scale_b);
            let second = d.imul(num_b, scale_a);
            d.iadd(first, second)
        },
        &|d, a, b| super::ops::radd(d, a, b),
    )?;
    over_pair(
        d,
        p.mul_cross,
        &|d, a, b| {
            let num_a = num(d, a);
            let num_b = num(d, b);
            d.imul(num_a, num_b)
        },
        &|d, a, b| super::ops::rmul(d, a, b),
    )
}
