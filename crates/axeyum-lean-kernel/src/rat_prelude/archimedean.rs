//! The **Archimedean property of ℚ**, and the one definition it is stated
//! against.
//!
//! ## Why this is here and not in the real construction
//!
//! ADR-0512 (`docs/research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md`)
//! builds `ℝ` as a Bishop setoid of *regular* sequences of rationals, and the
//! one step of that construction which is not routine is transitivity of the
//! setoid relation. Chaining two closeness hypotheses directly gives
//! `|x_n − z_n| ≤ 4/n`, which is not the `≤ 2/n` the relation asks for; Bishop's
//! argument instead compares at an arbitrary third index `j`,
//!
//! ```text
//! |x_n − z_n| ≤ |x_n − x_j| + |x_j − y_j| + |y_j − z_j| + |z_j − z_n|
//!             ≤ (1/n + 1/j) + 2/j + 2/j + (1/j + 1/n)  =  2/n + 6/j
//! ```
//!
//! and then discharges the `6/j` with a statement **about ℚ, not about ℝ**: if
//! `a ≤ b + 6/j` for every `j`, then `a ≤ b`. That is the Archimedean property,
//! it is the only genuinely new rational lemma the whole real construction
//! needs, and it belongs to the rational development.
//!
//! ## `k/(j+1)`, not `k · (1/(j+1))`
//!
//! The bound is written as a single [`Rat.normalize`](super) —
//! `Rat.natDivSucc k j := normalize (ofNat k) (j+1)` — rather than as a product
//! of a rational `k` with `1/(j+1)`. Three reasons, and the third is the one
//! that saves the most work:
//!
//! 1. `Rat.mul` renormalises, so `k · (1/(j+1))`'s projections are opaque and
//!    every use would have to go through `mul_cross`; `normalize`'s are reached
//!    by [`normalize_cross`](super::RatPrelude::normalize_cross) in one step.
//! 2. the successor denominator is positive **by construction**, so the
//!    positivity proof is `one_le_succ` and never a hypothesis; and
//! 3. it makes `2/n` and `6/j` the *same* construction at different `k`, so the
//!    regularity bound, the closeness bound and the Archimedean bound are one
//!    definition instead of three. `Rat.abs` is likewise never needed, because
//!    `|a| ≤ b` is stated as the pair `−b ≤ a ∧ a ≤ b`.
//!
//! ## The witness is computed, not asserted to exist
//!
//! [`declare_archimedean`] does not quantify existentially over the index. For
//! `0 < c` the index is `k · den c` outright: `c = p/q` with `p ≥ 1`, so
//!
//! ```text
//! k/(k·q + 1) < p/q   ⟸   k·q < p·(k·q + 1)   ⟸   p ≥ 1
//! ```
//!
//! and no search, no `Exists`, and no elimination is involved on the way in.
//! The `Exists` that does appear is `Int.lt_dest`'s, one level down, and it is
//! the *only* one.

use super::RatPrelude;
use super::ops::{
    den, den_pos, den_z, iregroup3, iregroup4, normalize, num, one_le_succ, radd, rat_eq_rewrite,
    rchain, rcongr, rle, rlt, rneg, rsymm, rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.natDivSucc`: above every `Rat` definition so it
/// outranks everything it unfolds to.
const NAT_DIV_SUCC_HEIGHT: u16 = 33;

/// Declare `theorem name : ∀ (x_0 : t_0) … (x_{n-1} : t_{n-1}), stmt := …`,
/// where the binder types are **not** all the same carrier.
///
/// `rat_theorem`/`int_theorem`/`NatOps::theorem` each fix one carrier; the
/// Archimedean statements mix `Rat` and `Nat` binders, so they need this.
pub(super) fn mixed_theorem(
    d: &mut IntDev<'_>,
    name: NameId,
    binders: &[ExprId],
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<(), KernelError> {
    let fvs: Vec<u64> = (0..binders.len()).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (stmt, proof) = build(d, &vars);
    let mut ty = stmt;
    let mut value = proof;
    for (index, &fv) in fvs.iter().enumerate().rev() {
        ty = d.pi_fv(fv, binders[index], ty);
        value = d.lam_fv(fv, binders[index], value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.natDivSucc k j` — the rational `k/(j+1)`.
fn nat_div_succ(d: &mut IntDev<'_>, p: RatPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.nat_div_succ, &[k, j])
}

/// Admit `Rat.natDivSucc`, the three bridges, the witness lemma and the
/// Archimedean property itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof.
pub(super) fn declare_archimedean(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_nat_div_succ(d, p)?;
    declare_decidable_order(d, p)?;
    declare_positive_bridges(d, p)?;
    declare_witness(d, p)?;
    declare_nat_div_succ_antitone(d, p)?;
    declare_archimedean_property(d, p)
}

/// `Rat.natDivSucc (k j : Nat) : Rat := normalize (ofNat k) (succ j) _`.
fn declare_nat_div_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = super::ops::rat_ty(d);
    let nat_ty = d.nat_ty();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let numerator = d.of_nat(k);
    let denominator = d.succ(j);
    let positive = one_le_succ(d, j);
    let body = normalize(d, numerator, denominator, positive);
    let value = {
        let with_j = d.lam_fv(j_fv, nat_ty, body);
        d.lam_fv(k_fv, nat_ty, with_j)
    };
    let ty = {
        let inner = d.arrow(nat_ty, carrier);
        d.arrow(nat_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nat_div_succ,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(NAT_DIV_SUCC_HEIGHT),
    })
}

/// `Int.le x y ∨ Int.lt y x`, and the same read through the cross-multiplication
/// definition of `Rat.le`/`Rat.lt`.
///
/// This is what replaces proof by contradiction. The Archimedean argument
/// naturally runs "suppose `¬(a ≤ b)`", but `¬¬P → P` is not available in this
/// intuitionistic logic prelude and never will be. It does not have to be:
/// `Int.le` is **decidable** here — `Int.le_total` and `Int.eq_em` are both
/// proved — so the disjunction can be produced outright and the argument
/// becomes a case split rather than a refutation.
fn declare_decidable_order(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let int_ty = d.int_ty();

    // int_le_or_lt : ∀ (x y : Int), Or (Int.le x y) (Int.lt y x).
    mixed_theorem(d, p.int_le_or_lt, &[int_ty, int_ty], &|d, v| {
        let (x, y) = (v[0], v[1]);
        let ordered = d.ile(x, y);
        let strict = d.ilt(y, x);
        let stmt = d.or(ordered, strict);

        let forward = d.ile(x, y);
        let backward = d.ile(y, x);
        let total = d.lemma(int.le_total, &[x, y]);
        let proof = d.or_elim(
            forward,
            backward,
            stmt,
            total,
            &|d, h| d.or_inl(ordered, strict, h),
            &|d, reversed| {
                // `y ≤ x`: either `y = x`, and then `x ≤ y` by reflexivity
                // transported along the equation, or `y ≠ x`, and then `y < x`.
                let decided = d.lemma(int.eq_em, &[y, x]);
                let equal = d.ieq(y, x);
                let distinct = d.not(equal);
                d.or_elim(
                    equal,
                    distinct,
                    stmt,
                    decided,
                    &|d, e| {
                        let reflexive = d.lemma(int.le_refl, &[y]);
                        let recovered = d.int_eq_rewrite(y, x, e, reflexive, &|d, z| d.ile(z, y));
                        d.or_inl(ordered, strict, recovered)
                    },
                    &|d, ne| {
                        let sharp = d.lemma(int.lt_of_le_of_ne, &[y, x, reversed, ne]);
                        d.or_inr(ordered, strict, sharp)
                    },
                )
            },
        );
        (stmt, proof)
    })?;

    // le_or_lt : ∀ (a b : Rat), Or (Rat.le a b) (Rat.lt b a).
    //
    // `Rat.le a b` IS `Int.le (num a · den b) (num b · den a)` and `Rat.lt b a`
    // IS `Int.lt (num b · den a) (num a · den b)`, so the integer disjunction at
    // the two cross-products is already the statement.
    let carrier = super::ops::rat_ty(d);
    mixed_theorem(d, p.le_or_lt, &[carrier, carrier], &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ordered = rle(d, p, a, b);
        let strict = rlt(d, p, b, a);
        let stmt = d.or(ordered, strict);
        let left = {
            let numerator = num(d, a);
            let scale = den_z(d, b);
            d.imul(numerator, scale)
        };
        let right = {
            let numerator = num(d, b);
            let scale = den_z(d, a);
            d.imul(numerator, scale)
        };
        let proof = d.lemma(p.int_le_or_lt, &[left, right]);
        (stmt, proof)
    })
}

/// The two positivity bridges: `0 < q` in `ℚ` gives `0 < num q` in `ℤ`, and a
/// positive integer is at least one.
///
/// The second is where the *discreteness* of `ℤ` enters, and it is the reason
/// an Archimedean argument works at all: the search below needs `p ≥ 1` from
/// `p > 0`, which is false in `ℚ` and true in `ℤ`.
fn declare_positive_bridges(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    let int_ty = d.int_ty();
    let carrier = super::ops::rat_ty(d);

    // int_pos_of_pos : ∀ q, Rat.lt Rat.zero q → Int.lt Int.zero (Rat.num q).
    //
    // `Rat.lt 0 q` unfolds to `Int.lt (0 · den q) (num q · 1)`; both sides
    // collapse, exactly as they do for the non-strict bridge in `super::laws`.
    mixed_theorem(d, p.int_pos_of_pos, &[carrier], &|d, v| {
        let q = v[0];
        let numerator = num(d, q);
        let zero = d.izero();
        let unit = d.ione();
        let denominator = den_z(d, q);
        let rational = {
            let target = rzero(d, p);
            rlt(d, p, target, q)
        };
        let integral = d.ilt(zero, numerator);
        let stmt = d.arrow(rational, integral);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let left_collapse = d.lemma(p.int_zero_mul, &[denominator]);
        let right_collapse = d.lemma(int.mul_one, &[numerator]);
        let left_scaled = d.imul(zero, denominator);
        let right_scaled = d.imul(numerator, unit);
        let at_left = d.int_eq_rewrite(left_scaled, zero, left_collapse, h, &|d, x| {
            d.ilt(x, right_scaled)
        });
        let body = d.int_eq_rewrite(right_scaled, numerator, right_collapse, at_left, &|d, x| {
            d.ilt(zero, x)
        });
        let proof = d.lam_fv(h_fv, rational, body);
        (stmt, proof)
    })?;

    // int_one_le_of_pos : ∀ (x : Int), Int.lt Int.zero x → Int.le (Int.ofNat 1) x.
    //
    // `Int.lt_dest` turns `0 < x` into `∃ i, x = 0 + ofNat (i+1)`; `Int.add_comm`
    // and `Int.add_zero` normalise that to `x = ofNat (i+1)`, and
    // `Int.le (ofNat 1) (ofNat (i+1))` IS `Nat.le 1 (i+1)`.
    mixed_theorem(d, p.int_one_le_of_pos, &[int_ty], &|d, v| {
        let x = v[0];
        let zero = d.izero();
        let one_nat = d.num(1);
        let one_z = d.of_nat(one_nat);
        let hypothesis = d.ilt(zero, x);
        let conclusion = d.ile(one_z, x);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dest = d.lemma(int.lt_dest, &[zero, x, h]);
        let shift_body = |d: &mut IntDev<'_>, i: ExprId| {
            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);
            d.ieq(x, shifted)
        };
        let nat_ty = d.nat_ty();
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = shift_body(d, i);
            d.lam_fv(i_fv, nat_ty, body)
        };
        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = shift_body(d, i);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);

            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);
            let flipped = d.iadd(value, zero);
            let commute = d.lemma(int.add_comm, &[zero, value]);
            let collapse = d.lemma(int.add_zero, &[value]);
            let (_, normalise) = d.ichain(shifted, &[(flipped, commute), (value, collapse)]);
            let normalised = d.itrans(x, shifted, value, hi, normalise);
            // `Int.le (ofNat 1) (ofNat (succ i))` reduces to `Nat.le 1 (succ i)`.
            let base = {
                let zero_nat = d.zero();
                let ground = d.lemma(nat.zero_le, &[i]);
                d.lemma(nat.le_succ_succ, &[zero_nat, i, ground])
            };
            let back = d.isymm(x, value, normalised);
            let transported = d.int_eq_rewrite(value, x, back, base, &|d, z| d.ile(one_z, z));
            let with_h = d.lam_fv(hi_fv, hi_ty, transported);
            d.lam_fv(i_fv, nat_ty, with_h)
        };
        let body = exists_elim(d, predicate, conclusion, dest, minor);
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// `0 < c → k/(k·den c + 1) < c` — the Archimedean **witness**, computed.
///
/// Unfolding both sides, the goal is
/// `num r · den c < num c · den r` with `r = normalize (ofNat k) (k·q + 1)`.
/// Scale by `k·q + 1`, substitute `normalize_cross` on the left, cancel the
/// (positive) `den r` on both sides, and what is left is
/// `k·q < num c · (k·q + 1)`, which follows from `1 ≤ num c` because
/// `k·q < k·q + 1`.
fn declare_witness(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    let nat_ty = d.nat_ty();
    let carrier = super::ops::rat_ty(d);

    mixed_theorem(d, p.nat_div_succ_lt_of_pos, &[nat_ty, carrier], &|d, v| {
        let (k, c) = (v[0], v[1]);
        let scale = den(d, c);
        let index = NatOps::mul(d, k, scale);
        let bound = nat_div_succ(d, p, k, index);
        let hypothesis = {
            let target = rzero(d, p);
            rlt(d, p, target, c)
        };
        let conclusion = rlt(d, p, bound, c);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // The bound, in the shape its projections are reachable through.
        let numerator = d.of_nat(k);
        let denominator = d.succ(index);
        let positive = one_le_succ(d, index);
        let representative = normalize(d, numerator, denominator, positive);
        let bound_num = num(d, representative);
        let bound_den = den(d, representative);
        let bound_den_z = den_z(d, representative);
        let bound_den_pos = den_pos(d, representative);
        let denominator_z = d.of_nat(denominator);
        let scale_z = den_z(d, c);
        let c_num = num(d, c);

        // `1 ≤ num c`, the discreteness step.
        let c_positive = d.lemma(p.int_pos_of_pos, &[c, h]);
        let one_le = d.lemma(p.int_one_le_of_pos, &[c_num, c_positive]);

        // `k·q + 1 ≤ num c · (k·q + 1)`: scale `1 ≤ num c` and normalise `1 · s`.
        let scaled_bound = d.imul(c_num, denominator_z);
        let lifted_one = {
            let one_nat = d.num(1);
            d.of_nat(one_nat)
        };
        let scaled = d.lemma(
            p.int_mul_le_mul_right,
            &[lifted_one, c_num, denominator, one_le],
        );
        let unit_product = {
            let one_nat = d.num(1);
            NatOps::mul(d, one_nat, denominator)
        };
        let unit_collapse = {
            let one_mul = d.lemma(nat.one_mul, &[denominator]);
            d.nat_eq_to_int(unit_product, denominator, one_mul, &|d, x| d.of_nat(x))
        };
        let lifted_unit_product = d.of_nat(unit_product);
        let dominates = d.int_eq_rewrite(
            lifted_unit_product,
            denominator_z,
            unit_collapse,
            scaled,
            &|d, z| d.ile(z, scaled_bound),
        );

        // `k·q < k·q + 1` IS `Nat.le (succ (k·q)) (succ (k·q))`.
        let index_z = d.of_nat(index);
        let successor = d.lemma(nat.le_refl, &[denominator]);
        let core = d.lemma(
            int.lt_of_lt_of_le,
            &[index_z, denominator_z, scaled_bound, successor, dominates],
        );

        // Scale both sides by `den r`, which is positive.
        let index_product = d.imul(numerator, scale_z);
        let scaled_strict = d.lemma(
            p.int_mul_lt_mul_right,
            &[index_product, scaled_bound, bound_den, bound_den_pos, core],
        );

        // Left side: `(num r · q) · s = (num r · s) · q = (k · den r) · q
        //           = (k · q) · den r`, the last of which is what we have.
        let goal_left = {
            let head = d.imul(bound_num, scale_z);
            d.imul(head, denominator_z)
        };
        let regrouped_left = iregroup3(
            d,
            [bound_num, scale_z, denominator_z],
            [bound_num, denominator_z, scale_z],
        );
        let cross = d.lemma(p.normalize_cross, &[numerator, denominator, positive]);
        let from_head = d.imul(bound_num, denominator_z);
        let to_head = d.imul(numerator, bound_den_z);
        let substituted = d.icongr(from_head, to_head, cross, &|d, t| d.imul(t, scale_z));
        let after_substitution = d.imul(to_head, scale_z);
        let regrouped_again = iregroup3(
            d,
            [numerator, bound_den_z, scale_z],
            [numerator, scale_z, bound_den_z],
        );
        let source_left = d.imul(index_product, bound_den_z);
        let middle_left = d.imul(from_head, scale_z);
        let (_, left_chain) = d.ichain(
            goal_left,
            &[
                (middle_left, regrouped_left),
                (after_substitution, substituted),
                (source_left, regrouped_again),
            ],
        );

        // Right side: `(num c · den r) · s = (num c · s) · den r`.
        let goal_right = {
            let head = d.imul(c_num, bound_den_z);
            d.imul(head, denominator_z)
        };
        let source_right = d.imul(scaled_bound, bound_den_z);
        let right_chain = iregroup3(
            d,
            [c_num, bound_den_z, denominator_z],
            [c_num, denominator_z, bound_den_z],
        );

        // Move the scaled inequality back onto the goal's two sides.
        let back_left = d.isymm(goal_left, source_left, left_chain);
        let at_left =
            d.int_eq_rewrite(source_left, goal_left, back_left, scaled_strict, &|d, z| {
                d.ilt(z, source_right)
            });
        let back_right = d.isymm(goal_right, source_right, right_chain);
        let at_right = d.int_eq_rewrite(source_right, goal_right, back_right, at_left, &|d, z| {
            d.ilt(goal_left, z)
        });

        // Cancel the common positive factor `k·q + 1`.
        let left_side = d.imul(bound_num, scale_z);
        let right_side = d.imul(c_num, bound_den_z);
        let body = d.lemma(
            p.int_lt_of_mul_lt_mul_right,
            &[left_side, right_side, denominator, positive, at_right],
        );
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// `Rat.natDivSucc_antitone : ∀ j j', Nat.le j j' →
/// Rat.le (natDivSucc 1 j') (natDivSucc 1 j)`.
///
/// **Antitonicity, at last.** The direct route, not the reciprocal one:
/// `natDivSucc 1 m` is `normalize (ofNat 1) (succ m) _`, so
/// [`RatPrelude::normalize_cross`] at each side gives `num · (succ m) = den`
/// (after cancelling the `ofNat 1` factor with `Nat.one_mul`). Scaling the
/// goal `num_a · den_b ≤ num_b · den_a` by `(succ j') · (succ j)` and
/// regrouping with [`iregroup4`] turns each side into `den_a · den_b` times
/// one successor denominator — exactly `Nat.succ_le_succ` on the hypothesis,
/// scaled by the (positive) `den_a · den_b` and read back through
/// [`RatPrelude::int_le_of_mul_le_mul_right`].
///
/// No `Rat.inv` is touched, so this needs neither an `inv_inv` law (this
/// prelude still has none) nor a dedicated `Nat → Rat` order-transport lemma:
/// `Int.le (ofNat m) (ofNat n)` already unfolds to `Nat.le m n` definitionally
/// (the four-case table `int_prelude`'s definitions module builds `Int.le`
/// from), so `Nat.succ_le_succ` applied to the hypothesis serves directly
/// wherever an `Int.le` between the two successor denominators is needed.
#[allow(clippy::too_many_lines)]
fn declare_nat_div_succ_antitone(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    let nat_ty = d.nat_ty();

    mixed_theorem(d, p.nat_div_succ_antitone, &[nat_ty, nat_ty], &|d, v| {
        let (j, jp) = (v[0], v[1]);
        let hyp_ty = NatOps::le(d, j, jp);

        let one_nat = d.num(1);
        let one_z = d.of_nat(one_nat);
        let a = d.const_app(p.nat_div_succ, &[one_nat, jp]);
        let b = d.const_app(p.nat_div_succ, &[one_nat, j]);
        let concl = rle(d, p, a, b);
        let stmt = d.arrow(hyp_ty, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let ea = d.succ(jp);
        let eb = d.succ(j);
        let eaz = d.of_nat(ea);
        let ebz = d.of_nat(eb);
        let pos_a = one_le_succ(d, jp);
        let pos_b = one_le_succ(d, j);

        // The two representatives, built directly rather than through
        // `Rat.natDivSucc` so `normalize_cross` applies to them without a
        // detour through `a`/`b`'s unfolding (proof irrelevance + delta
        // bridges the two back together at the very end, where `body`'s
        // inferred type is checked against `concl`).
        let rep_a = normalize(d, one_z, ea, pos_a);
        let rep_b = normalize(d, one_z, eb, pos_b);
        let na = num(d, rep_a);
        let da = den(d, rep_a);
        let daz = den_z(d, rep_a);
        let nb = num(d, rep_b);
        let db = den(d, rep_b);
        let dbz = den_z(d, rep_b);

        // Eq-A : na * eaz = daz.
        let cross_a = d.lemma(p.normalize_cross, &[one_z, ea, pos_a]);
        let one_z_daz = d.imul(one_z, daz);
        let one_mul_da_nat = d.lemma(nat.one_mul, &[da]);
        let one_mul_da_product = NatOps::mul(d, one_nat, da);
        let one_mul_da =
            d.nat_eq_to_int(one_mul_da_product, da, one_mul_da_nat, &|d, t| d.of_nat(t));
        let na_eaz = d.imul(na, eaz);
        let (_, eqa) = d.ichain(na_eaz, &[(one_z_daz, cross_a), (daz, one_mul_da)]);

        // Eq-B : nb * ebz = dbz.
        let cross_b = d.lemma(p.normalize_cross, &[one_z, eb, pos_b]);
        let one_z_dbz = d.imul(one_z, dbz);
        let one_mul_db_nat = d.lemma(nat.one_mul, &[db]);
        let one_mul_db_product = NatOps::mul(d, one_nat, db);
        let one_mul_db =
            d.nat_eq_to_int(one_mul_db_product, db, one_mul_db_nat, &|d, t| d.of_nat(t));
        let nb_ebz = d.imul(nb, ebz);
        let (_, eqb) = d.ichain(nb_ebz, &[(one_z_dbz, cross_b), (dbz, one_mul_db)]);

        // `Nat.le eb ea`, which IS `Int.le ebz eaz` (both `ofNat`s).
        let hyp_e = d.lemma(nat.succ_le_succ, &[j, jp, h]);

        // Scale by the (positive) product of the two denominators.
        let da_db = NatOps::mul(d, da, db);
        let scaled_hyp = d.lemma(p.int_mul_le_mul_right, &[ebz, eaz, da_db, hyp_e]);

        let dadbz = d.imul(daz, dbz);
        let source_lhs = d.imul(ebz, dadbz);
        let source_rhs = d.imul(eaz, dadbz);

        let ea_eb = d.imul(eaz, ebz);
        let na_dbz = d.imul(na, dbz);
        let nb_daz = d.imul(nb, daz);
        let goal_lhs = d.imul(na_dbz, ea_eb);
        let goal_rhs = d.imul(nb_daz, ea_eb);

        // --- LHS: (na*dbz)*(eaz*ebz) = ebz*(daz*dbz) ---
        let goal_lhs_left_head = d.imul(na_dbz, eaz);
        let goal_lhs_left = d.imul(goal_lhs_left_head, ebz);
        let bridge_lhs_forward = d.lemma(int.mul_assoc, &[na_dbz, eaz, ebz]);
        let bridge_lhs = d.isymm(goal_lhs_left, goal_lhs, bridge_lhs_forward);

        let regroup_lhs = iregroup4(d, [na, dbz, eaz, ebz], [na, eaz, dbz, ebz]);
        let regrouped_lhs_head = d.imul(na_eaz, dbz);
        let regrouped_lhs = d.imul(regrouped_lhs_head, ebz);

        let subst_lhs = d.icongr(na_eaz, daz, eqa, &|d, t| {
            let head = d.imul(t, dbz);
            d.imul(head, ebz)
        });
        let subst_lhs_result = d.imul(dadbz, ebz);

        let commute_lhs = d.lemma(int.mul_comm, &[dadbz, ebz]);

        let (_, lhs_chain) = d.ichain(
            goal_lhs,
            &[
                (goal_lhs_left, bridge_lhs),
                (regrouped_lhs, regroup_lhs),
                (subst_lhs_result, subst_lhs),
                (source_lhs, commute_lhs),
            ],
        );

        // --- RHS: (nb*daz)*(eaz*ebz) = eaz*(daz*dbz) ---
        let goal_rhs_left_head = d.imul(nb_daz, eaz);
        let goal_rhs_left = d.imul(goal_rhs_left_head, ebz);
        let bridge_rhs_forward = d.lemma(int.mul_assoc, &[nb_daz, eaz, ebz]);
        let bridge_rhs = d.isymm(goal_rhs_left, goal_rhs, bridge_rhs_forward);

        let regroup_rhs = iregroup4(d, [nb, daz, eaz, ebz], [nb, ebz, daz, eaz]);
        let regrouped_rhs_head = d.imul(nb_ebz, daz);
        let regrouped_rhs = d.imul(regrouped_rhs_head, eaz);

        let subst_rhs = d.icongr(nb_ebz, dbz, eqb, &|d, t| {
            let head = d.imul(t, daz);
            d.imul(head, eaz)
        });
        let dbz_daz = d.imul(dbz, daz);
        let subst_rhs_mid = d.imul(dbz_daz, eaz);

        let swap_db_da = d.lemma(int.mul_comm, &[dbz, daz]);
        let commute_inner_rhs = d.icongr(dbz_daz, dadbz, swap_db_da, &|d, t| d.imul(t, eaz));
        let subst_rhs_final = d.imul(dadbz, eaz);

        let commute_rhs = d.lemma(int.mul_comm, &[dadbz, eaz]);

        let (_, rhs_chain) = d.ichain(
            goal_rhs,
            &[
                (goal_rhs_left, bridge_rhs),
                (regrouped_rhs, regroup_rhs),
                (subst_rhs_mid, subst_rhs),
                (subst_rhs_final, commute_inner_rhs),
                (source_rhs, commute_rhs),
            ],
        );

        // Transport `scaled_hyp` along both chains onto the scaled goal.
        let back_lhs = d.isymm(goal_lhs, source_lhs, lhs_chain);
        let at_lhs = d.int_eq_rewrite(source_lhs, goal_lhs, back_lhs, scaled_hyp, &|d, z| {
            d.ile(z, source_rhs)
        });
        let back_rhs = d.isymm(goal_rhs, source_rhs, rhs_chain);
        let scaled_goal = d.int_eq_rewrite(source_rhs, goal_rhs, back_rhs, at_lhs, &|d, z| {
            d.ile(goal_lhs, z)
        });

        // Cancel the common (positive) factor `(succ j') * (succ j)`.
        let ea_eb_nat = NatOps::mul(d, ea, eb);
        let one_le_ea_eb = d.lemma(nat.one_le_mul, &[ea, eb, pos_a, pos_b]);
        let body = d.lemma(
            p.int_le_of_mul_le_mul_right,
            &[na_dbz, nb_daz, ea_eb_nat, one_le_ea_eb, scaled_goal],
        );

        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })
}

/// `(∀ j, a ≤ b + k/(j+1)) → a ≤ b`.
///
/// The case split is on [`RatPrelude::le_or_lt`], not on a double negation.
/// In the `b < a` branch, `c := (−b) + a` is positive, the witness lemma
/// produces an index whose bound is strictly below `c`, and `b + bound < b + c
/// = a` contradicts the hypothesis at that index.
fn declare_archimedean_property(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat_ty = d.nat_ty();
    let carrier = super::ops::rat_ty(d);

    mixed_theorem(
        d,
        p.le_of_le_add_nat_div_succ,
        &[carrier, carrier, nat_ty],
        &|d, v| {
            let (a, b, k) = (v[0], v[1], v[2]);
            let conclusion = rle(d, p, a, b);
            let hypothesis = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let bound = nat_div_succ(d, p, k, j);
                let shifted = radd(d, b, bound);
                let body = rle(d, p, a, shifted);
                d.pi_fv(j_fv, nat_ty, body)
            };
            let stmt = d.arrow(hypothesis, conclusion);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let ordered = rle(d, p, a, b);
            let strict = rlt(d, p, b, a);
            let decided = d.lemma(p.le_or_lt, &[a, b]);
            let body = d.or_elim(
                ordered,
                strict,
                conclusion,
                decided,
                &|_d, settled| settled,
                &|d, below| {
                    let zero = rzero(d, p);
                    let opposite = rneg(d, b);
                    let gap = radd(d, opposite, a);

                    // `0 < (−b) + a`, from `b < a` translated by `−b`.
                    let reflexive = d.lemma(p.le_refl, &[opposite]);
                    let translated = d.lemma(
                        p.add_lt_add_of_le_of_lt,
                        &[opposite, opposite, b, a, reflexive, below],
                    );
                    let cancelled = radd(d, opposite, b);
                    let commuted = radd(d, b, opposite);
                    let commute = d.lemma(p.add_comm, &[opposite, b]);
                    let vanish = d.lemma(p.add_neg, &[b]);
                    let (_, to_zero) = rchain(d, cancelled, &[(commuted, commute), (zero, vanish)]);
                    let positive =
                        rat_eq_rewrite(d, cancelled, zero, to_zero, translated, &|d, x| {
                            rlt(d, p, x, gap)
                        });

                    // The witness index, and the hypothesis read at it.
                    let scale = den(d, gap);
                    let index = NatOps::mul(d, k, scale);
                    let bound = nat_div_succ(d, p, k, index);
                    let below_gap = d.lemma(p.nat_div_succ_lt_of_pos, &[k, gap, positive]);
                    let shifted = radd(d, b, bound);
                    let instance = d.apply(h, &[index]);

                    // `b + bound < b + gap`, and `b + gap = a`.
                    let reflexive_b = d.lemma(p.le_refl, &[b]);
                    let step = d.lemma(
                        p.add_lt_add_of_le_of_lt,
                        &[b, b, bound, gap, reflexive_b, below_gap],
                    );
                    let restored = radd(d, b, gap);
                    let regrouped = radd(d, commuted, a);
                    let associate = d.lemma(p.add_assoc, &[b, opposite, a]);
                    let opened = rsymm(d, regrouped, restored, associate);
                    let zeroed = radd(d, zero, a);
                    let collapse = rcongr(d, commuted, zero, vanish, &|d, t| radd(d, t, a));
                    let flipped = radd(d, a, zero);
                    let commute_zero = d.lemma(p.add_comm, &[zero, a]);
                    let drop_zero = d.lemma(p.add_zero, &[a]);
                    let (_, to_a) = rchain(
                        d,
                        restored,
                        &[
                            (regrouped, opened),
                            (zeroed, collapse),
                            (flipped, commute_zero),
                            (a, drop_zero),
                        ],
                    );
                    let under =
                        rat_eq_rewrite(d, restored, a, to_a, step, &|d, x| rlt(d, p, shifted, x));

                    // `a ≤ b + bound < a`.
                    let irreflexive = d.lemma(p.lt_of_le_of_lt, &[a, shifted, a, instance, under]);
                    let refutation = d.lemma(p.lt_irrefl, &[a]);
                    let impossible = d.apply(refutation, &[irreflexive]);
                    d.absurd(conclusion, impossible)
                },
            );
            let proof = d.lam_fv(h_fv, hypothesis, body);
            (stmt, proof)
        },
    )
}
