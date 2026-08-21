//! The six laws whose two sides do **not** share a denominator: associativity,
//! distributivity, and the three monotonicity laws.
//!
//! ## The move
//!
//! `Rat.add` and `Rat.mul` renormalise, so in `(a+b)+c` the projections of
//! `a+b` are opaque — there is no equation for `num (a+b)`, only the
//! cross-relation [`super::core`] proves. Two lemmas fix that once:
//!
//! ```text
//! normalize n₁ e₁ _ + normalize n₂ e₂ _ = normalize (n₁·e₂ + n₂·e₁) (e₁·e₂) _
//! normalize n₁ e₁ _ · normalize n₂ e₂ _ = normalize (n₁·n₂)         (e₁·e₂) _
//! ```
//!
//! `Rat.add a b` **is** `normalize (…) (…) _` definitionally, and
//! `Rat.self_normalize` turns any *other* rational into a `normalize` too. So a
//! nested expression collapses into a single `Rat.normalize` and the law becomes
//! one identity in the constructed `ℤ`, which `normalize_congr` consumes.
//!
//! The monotonicity laws cannot collapse — they are inequalities, and
//! `normalize` is value-preserving, not order-preserving as a function. They
//! take the other route: prove the inequality between the *unnormalised*
//! cross-products, then move it onto the compound rationals' own projections
//! with `add_cross`/`mul_cross` and cancel the positive scaling.
//!
//! ## Why every scaling factor is written right-nested
//!
//! `ofNat (x · (y · z))` is **definitionally** `ofNat x · (ofNat y · ofNat z)`,
//! because `Int.mul (ofNat a) (ofNat b)` ι-reduces to `ofNat (Nat.mul a b)`.
//! The left-nested spelling is not: `Nat.mul` associativity is a theorem, not a
//! reduction. Denominators that arrive left-nested are re-associated explicitly
//! by [`regroup_denominator`] — that single step is the entire cost of the
//! distinction, and skipping it produces a kernel rejection with no location.
//!
//! Factor bookkeeping is [`Flat`]'s job: it carries the multiset explicitly and
//! panics on a reordering that is not a permutation, so a mis-derived law fails
//! with a Rust message naming the two lists rather than as an opaque
//! `TypeMismatch`.

use super::RatPrelude;
use super::ops::{
    Flat, den, den_pos, den_z, normalize, num, positive_ty, radd, rat_theorem, rchain, rcongr, req,
    rle, rmul, rsymm,
};
use super::statements;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit the two `normalize`-combination lemmas and the six laws.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_scaling_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_normalize_mul(d, p)?;
    declare_normalize_add(d, p)?;
    declare_mul_assoc(d, p)?;
    declare_add_assoc(d, p)?;
    declare_left_distrib(d, p)?;
    declare_additive_monotone(d, p)?;
    declare_multiplicative_monotone(d, p)
}

// --- shared plumbing --------------------------------------------------------

/// Two products with the same factor multiset are equal.
fn agree(d: &mut IntDev<'_>, canonical: &[ExprId], mut left: Flat, mut right: Flat) -> ExprId {
    left.perm(d, canonical);
    right.perm(d, canonical);
    let (left_start, canon, left_proof) = left.finish(d);
    let (right_start, _, right_proof) = right.finish(d);
    let back = d.isymm(right_start, canon, right_proof);
    d.itrans(left_start, canon, right_start, left_proof, back)
}

/// `Eq Int (ofNat from) (ofNat to)` from a `Nat` equation — used only to move a
/// denominator from the left-nested spelling to the right-nested one.
fn regroup_denominator(d: &mut IntDev<'_>, from: ExprId, to: ExprId, equation: ExprId) -> ExprId {
    d.nat_eq_to_int(from, to, equation, &|d, x| d.of_nat(x))
}

/// The six binders `∀ (n₁ : Int) (e₁ : Nat) (h₁ : 1 ≤ e₁) (n₂ e₂ h₂), …` that
/// both `normalize`-combination lemmas quantify over.
struct Pair {
    n1: ExprId,
    e1: ExprId,
    h1: ExprId,
    n2: ExprId,
    e2: ExprId,
    h2: ExprId,
    binders: [(u64, ExprId); 6],
}

fn open_pair(d: &mut IntDev<'_>) -> Pair {
    let int_ty = d.int_ty();
    let nat_ty = d.nat_ty();
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
    Pair {
        n1,
        e1,
        h1,
        n2,
        e2,
        h2,
        binders: [
            (n1_fv, int_ty),
            (e1_fv, nat_ty),
            (h1_fv, positive_1),
            (n2_fv, int_ty),
            (e2_fv, nat_ty),
            (h2_fv, positive_2),
        ],
    }
}

fn close_pair(
    d: &mut IntDev<'_>,
    pair: &Pair,
    name: crate::name::NameId,
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, kind) in pair.binders.iter().rev() {
        ty = d.pi_fv(fv, kind, ty);
        value = d.lam_fv(fv, kind, value);
    }
    d.declare_theorem(name, ty, value)
}

// --- the two normalize-combination lemmas -----------------------------------

/// `normalize n₁ e₁ _ · normalize n₂ e₂ _ = normalize (n₁·n₂) (e₁·e₂) _`.
fn declare_normalize_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let pair = open_pair(d);
    let Pair {
        n1,
        e1,
        h1,
        n2,
        e2,
        h2,
        ..
    } = pair;

    let x = normalize(d, n1, e1, h1);
    let y = normalize(d, n2, e2, h2);
    let num_x = num(d, x);
    let num_y = num(d, y);
    let den_x = den(d, x);
    let den_y = den(d, y);
    let scale_x = den_z(d, x);
    let scale_y = den_z(d, y);
    let positive_x = den_pos(d, x);
    let positive_y = den_pos(d, y);
    let lifted_1 = d.of_nat(e1);
    let lifted_2 = d.of_nat(e2);

    let source_num = d.imul(num_x, num_y);
    let source_den = NatOps::mul(d, den_x, den_y);
    let source_pos = d.lemma(nat.one_le_mul, &[den_x, den_y, positive_x, positive_y]);
    let target_num = d.imul(n1, n2);
    let target_den = NatOps::mul(d, e1, e2);
    let target_pos = d.lemma(nat.one_le_mul, &[e1, e2, h1, h2]);

    let keeps_x = d.lemma(p.normalize_cross, &[n1, e1, h1]);
    let keeps_y = d.lemma(p.normalize_cross, &[n2, e2, h2]);

    let identity = {
        let lifted_target_den = d.of_nat(target_den);
        let lifted_source_den = d.of_nat(source_den);
        let mut left = Flat::begin_product(
            d,
            source_num,
            &[num_x, num_y],
            lifted_target_den,
            &[lifted_1, lifted_2],
        );
        left.perm(d, &[num_x, lifted_1, num_y, lifted_2]);
        left.rewrite_prefix(d, 2, &[n1, scale_x], keeps_x);
        left.perm(d, &[num_y, lifted_2, n1, scale_x]);
        left.rewrite_prefix(d, 2, &[n2, scale_y], keeps_y);
        let right = Flat::begin_product(
            d,
            target_num,
            &[n1, n2],
            lifted_source_den,
            &[scale_x, scale_y],
        );
        agree(d, &[n1, n2, scale_x, scale_y], left, right)
    };
    let proof = d.const_app(
        p.normalize_congr,
        &[
            source_num, source_den, source_pos, target_num, target_den, target_pos, identity,
        ],
    );
    let combined = rmul(d, x, y);
    let rebuilt = normalize(d, target_num, target_den, target_pos);
    let stmt = req(d, combined, rebuilt);
    close_pair(d, &pair, p.normalize_mul_normalize, stmt, proof)
}

/// `normalize n₁ e₁ _ + normalize n₂ e₂ _ = normalize (n₁·e₂ + n₂·e₁) (e₁·e₂) _`.
fn declare_normalize_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let pair = open_pair(d);
    let Pair {
        n1,
        e1,
        h1,
        n2,
        e2,
        h2,
        ..
    } = pair;

    let x = normalize(d, n1, e1, h1);
    let y = normalize(d, n2, e2, h2);
    let num_x = num(d, x);
    let num_y = num(d, y);
    let den_x = den(d, x);
    let den_y = den(d, y);
    let scale_x = den_z(d, x);
    let scale_y = den_z(d, y);
    let positive_x = den_pos(d, x);
    let positive_y = den_pos(d, y);
    let lifted_1 = d.of_nat(e1);
    let lifted_2 = d.of_nat(e2);

    let source_head = d.imul(num_x, scale_y);
    let source_tail = d.imul(num_y, scale_x);
    let source_num = d.iadd(source_head, source_tail);
    let source_den = NatOps::mul(d, den_x, den_y);
    let source_pos = d.lemma(nat.one_le_mul, &[den_x, den_y, positive_x, positive_y]);
    let target_head = d.imul(n1, lifted_2);
    let target_tail = d.imul(n2, lifted_1);
    let target_num = d.iadd(target_head, target_tail);
    let target_den = NatOps::mul(d, e1, e2);
    let target_pos = d.lemma(nat.one_le_mul, &[e1, e2, h1, h2]);

    let keeps_x = d.lemma(p.normalize_cross, &[n1, e1, h1]);
    let keeps_y = d.lemma(p.normalize_cross, &[n2, e2, h2]);

    let identity = {
        let scale_target = d.of_nat(target_den);
        let scale_source = d.of_nat(source_den);
        let whole_left = d.imul(source_num, scale_target);
        let whole_right = d.imul(target_num, scale_source);

        // Distribute both sides.
        let open_left = d.lemma(
            p.int_right_distrib,
            &[source_head, source_tail, scale_target],
        );
        let open_right = d.lemma(
            p.int_right_distrib,
            &[target_head, target_tail, scale_source],
        );
        let left_first = d.imul(source_head, scale_target);
        let left_second = d.imul(source_tail, scale_target);
        let right_first = d.imul(target_head, scale_source);
        let right_second = d.imul(target_tail, scale_source);
        let split_left = d.iadd(left_first, left_second);
        let split_right = d.iadd(right_first, right_second);

        // n₁'s summand.
        let first = {
            let mut flat = Flat::begin_product(
                d,
                source_head,
                &[num_x, scale_y],
                scale_target,
                &[lifted_1, lifted_2],
            );
            flat.perm(d, &[num_x, lifted_1, scale_y, lifted_2]);
            flat.rewrite_prefix(d, 2, &[n1, scale_x], keeps_x);
            let target = Flat::begin_product(
                d,
                target_head,
                &[n1, lifted_2],
                scale_source,
                &[scale_x, scale_y],
            );
            agree(d, &[n1, lifted_2, scale_x, scale_y], flat, target)
        };
        // n₂'s summand.
        let second = {
            let mut flat = Flat::begin_product(
                d,
                source_tail,
                &[num_y, scale_x],
                scale_target,
                &[lifted_1, lifted_2],
            );
            flat.perm(d, &[num_y, lifted_2, scale_x, lifted_1]);
            flat.rewrite_prefix(d, 2, &[n2, scale_y], keeps_y);
            let target = Flat::begin_product(
                d,
                target_tail,
                &[n2, lifted_1],
                scale_source,
                &[scale_x, scale_y],
            );
            agree(d, &[n2, lifted_1, scale_x, scale_y], flat, target)
        };

        let staged = d.iadd(right_first, left_second);
        let step_first = d.icongr(left_first, right_first, first, &|d, t| {
            d.iadd(t, left_second)
        });
        let step_second = d.icongr(left_second, right_second, second, &|d, t| {
            d.iadd(right_first, t)
        });
        let close_right = d.isymm(whole_right, split_right, open_right);
        let (_, chained) = d.ichain(
            whole_left,
            &[
                (split_left, open_left),
                (staged, step_first),
                (split_right, step_second),
                (whole_right, close_right),
            ],
        );
        chained
    };
    let proof = d.const_app(
        p.normalize_congr,
        &[
            source_num, source_den, source_pos, target_num, target_den, target_pos, identity,
        ],
    );
    let combined = radd(d, x, y);
    let rebuilt = normalize(d, target_num, target_den, target_pos);
    let stmt = req(d, combined, rebuilt);
    close_pair(d, &pair, p.normalize_add_normalize, stmt, proof)
}

// --- the three equational laws ----------------------------------------------

/// The `Rat.mul`/`Rat.add` shape of a rational: numerator, denominator, its
/// positivity, and the three `ofNat` views the identities use.
struct Parts {
    num: ExprId,
    den: ExprId,
    scale: ExprId,
    positive: ExprId,
}

fn parts(d: &mut IntDev<'_>, q: ExprId) -> Parts {
    Parts {
        num: num(d, q),
        den: den(d, q),
        scale: den_z(d, q),
        positive: den_pos(d, q),
    }
}

/// `(a·b)·c = a·(b·c)`.
fn declare_mul_assoc(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    rat_theorem(d, p.mul_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let stmt = statements::mul_assoc(d, p, v);
        let pa = parts(d, a);
        let pb = parts(d, b);
        let pc = parts(d, c);

        let ab_num = d.imul(pa.num, pb.num);
        let ab_den = NatOps::mul(d, pa.den, pb.den);
        let ab_pos = d.lemma(nat.one_le_mul, &[pa.den, pb.den, pa.positive, pb.positive]);
        let bc_num = d.imul(pb.num, pc.num);
        let bc_den = NatOps::mul(d, pb.den, pc.den);
        let bc_pos = d.lemma(nat.one_le_mul, &[pb.den, pc.den, pb.positive, pc.positive]);

        // c and a, rewritten as the `normalize`s they are equal to.
        let renormalised_c = normalize(d, pc.num, pc.den, pc.positive);
        let renormalised_a = normalize(d, pa.num, pa.den, pa.positive);
        let to_c = {
            let forward = d.const_app(p.self_normalize, &[c]);
            super::ops::rsymm(d, renormalised_c, c, forward)
        };
        let to_a = {
            let forward = d.const_app(p.self_normalize, &[a]);
            rsymm(d, renormalised_a, a, forward)
        };
        let left_source = rmul(d, a, b);
        let right_source = rmul(d, b, c);
        let step_left = rcongr(d, c, renormalised_c, to_c, &|d, t| rmul(d, left_source, t));
        let step_right = rcongr(d, a, renormalised_a, to_a, &|d, t| rmul(d, t, right_source));

        let collapse_left = d.const_app(
            p.normalize_mul_normalize,
            &[ab_num, ab_den, ab_pos, pc.num, pc.den, pc.positive],
        );
        let collapse_right = d.const_app(
            p.normalize_mul_normalize,
            &[pa.num, pa.den, pa.positive, bc_num, bc_den, bc_pos],
        );

        let left_num = d.imul(ab_num, pc.num);
        let left_den = NatOps::mul(d, ab_den, pc.den);
        let left_pos = d.lemma(nat.one_le_mul, &[ab_den, pc.den, ab_pos, pc.positive]);
        let right_num = d.imul(pa.num, bc_num);
        let right_den = NatOps::mul(d, pa.den, bc_den);
        let right_pos = d.lemma(nat.one_le_mul, &[pa.den, bc_den, pa.positive, bc_pos]);

        let identity = {
            let scale_right = d.of_nat(right_den);
            let scale_left = d.of_nat(left_den);
            let start_left = d.imul(left_num, scale_right);
            let start_right = d.imul(right_num, scale_left);
            // The right-hand denominator arrives left-nested; re-associate it.
            let regroup = {
                let equation = d.lemma(nat.mul_assoc, &[pa.den, pb.den, pc.den]);
                regroup_denominator(d, left_den, right_den, equation)
            };
            let middle_right = d.imul(right_num, scale_right);
            let step = d.icongr(scale_left, scale_right, regroup, &|d, t| {
                d.imul(right_num, t)
            });

            let mut left = Flat::begin_product(d, pa.num, &[pa.num], pb.num, &[pb.num]);
            left.scale(d, pc.num, &[pc.num]);
            left.scale(d, scale_right, &[pa.scale, pb.scale, pc.scale]);
            let right = Flat::begin_product(
                d,
                right_num,
                &[pa.num, pb.num, pc.num],
                scale_right,
                &[pa.scale, pb.scale, pc.scale],
            );
            let canonical = [pa.num, pb.num, pc.num, pa.scale, pb.scale, pc.scale];
            let aligned = agree(d, &canonical, left, right);
            // start_right = middle_right = start_left, so flip the last step.
            let back = d.isymm(start_left, middle_right, aligned);
            d.itrans(start_right, middle_right, start_left, step, back)
        };
        let identity = {
            let scale_right = d.of_nat(right_den);
            let scale_left = d.of_nat(left_den);
            let start_left = d.imul(left_num, scale_right);
            let start_right = d.imul(right_num, scale_left);
            d.isymm(start_right, start_left, identity)
        };
        let bridge = d.const_app(
            p.normalize_congr,
            &[
                left_num, left_den, left_pos, right_num, right_den, right_pos, identity,
            ],
        );

        let left_collapsed = normalize(d, left_num, left_den, left_pos);
        let right_collapsed = normalize(d, right_num, right_den, right_pos);
        let mid_left = rmul(d, left_source, renormalised_c);
        let mid_right = rmul(d, renormalised_a, right_source);
        let goal_right = rmul(d, a, right_source);
        let undo_right = rsymm(d, mid_right, right_collapsed, collapse_right);
        let undo_a = {
            let forward = rcongr(d, a, renormalised_a, to_a, &|d, t| rmul(d, t, right_source));
            rsymm(d, goal_right, mid_right, forward)
        };
        let _ = step_right;
        let start = rmul(d, left_source, c);
        let (_, proof) = rchain(
            d,
            start,
            &[
                (mid_left, step_left),
                (left_collapsed, collapse_left),
                (right_collapsed, bridge),
                (mid_right, undo_right),
                (goal_right, undo_a),
            ],
        );
        (stmt, proof)
    })
}

/// `(a+b)+c = a+(b+c)`.
fn declare_add_assoc(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    rat_theorem(d, p.add_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let stmt = statements::add_assoc(d, p, v);
        let pa = parts(d, a);
        let pb = parts(d, b);
        let pc = parts(d, c);

        let ab_head = d.imul(pa.num, pb.scale);
        let ab_tail = d.imul(pb.num, pa.scale);
        let ab_num = d.iadd(ab_head, ab_tail);
        let ab_den = NatOps::mul(d, pa.den, pb.den);
        let ab_pos = d.lemma(nat.one_le_mul, &[pa.den, pb.den, pa.positive, pb.positive]);
        let bc_head = d.imul(pb.num, pc.scale);
        let bc_tail = d.imul(pc.num, pb.scale);
        let bc_num = d.iadd(bc_head, bc_tail);
        let bc_den = NatOps::mul(d, pb.den, pc.den);
        let bc_pos = d.lemma(nat.one_le_mul, &[pb.den, pc.den, pb.positive, pc.positive]);

        let renormalised_c = normalize(d, pc.num, pc.den, pc.positive);
        let renormalised_a = normalize(d, pa.num, pa.den, pa.positive);
        let to_c = {
            let forward = d.const_app(p.self_normalize, &[c]);
            rsymm(d, renormalised_c, c, forward)
        };
        let to_a = {
            let forward = d.const_app(p.self_normalize, &[a]);
            rsymm(d, renormalised_a, a, forward)
        };
        let left_source = radd(d, a, b);
        let right_source = radd(d, b, c);
        let step_left = rcongr(d, c, renormalised_c, to_c, &|d, t| radd(d, left_source, t));

        let collapse_left = d.const_app(
            p.normalize_add_normalize,
            &[ab_num, ab_den, ab_pos, pc.num, pc.den, pc.positive],
        );
        let collapse_right = d.const_app(
            p.normalize_add_normalize,
            &[pa.num, pa.den, pa.positive, bc_num, bc_den, bc_pos],
        );

        let lifted_ab = d.of_nat(ab_den);
        let lifted_bc = d.of_nat(bc_den);
        let left_head = d.imul(ab_num, pc.scale);
        let left_tail = d.imul(pc.num, lifted_ab);
        let left_num = d.iadd(left_head, left_tail);
        let left_den = NatOps::mul(d, ab_den, pc.den);
        let left_pos = d.lemma(nat.one_le_mul, &[ab_den, pc.den, ab_pos, pc.positive]);
        let right_head = d.imul(pa.num, lifted_bc);
        let right_tail = d.imul(bc_num, pa.scale);
        let right_num = d.iadd(right_head, right_tail);
        let right_den = NatOps::mul(d, pa.den, bc_den);
        let right_pos = d.lemma(nat.one_le_mul, &[pa.den, bc_den, pa.positive, bc_pos]);

        let identity = {
            let scale = d.of_nat(right_den);
            let scale_left = d.of_nat(left_den);
            let atoms = [pa.scale, pb.scale, pc.scale];
            let start_left = d.imul(left_num, scale);
            let start_right_raw = d.imul(right_num, scale_left);
            let regroup = {
                let equation = d.lemma(nat.mul_assoc, &[pa.den, pb.den, pc.den]);
                regroup_denominator(d, left_den, right_den, equation)
            };
            let start_right = d.imul(right_num, scale);
            let regroup_step = d.icongr(scale_left, scale, regroup, &|d, t| d.imul(right_num, t));

            // Left: ((n_a·d_b + n_b·d_a)·d_c + n_c·(d_a·d_b))·K.
            let left_first = d.imul(left_head, scale);
            let left_second = d.imul(left_tail, scale);
            let open_left = d.lemma(p.int_right_distrib, &[left_head, left_tail, scale]);
            let split_left = d.iadd(left_first, left_second);
            let inner_open = d.lemma(p.int_right_distrib, &[ab_head, ab_tail, pc.scale]);
            let inner_first = d.imul(ab_head, pc.scale);
            let inner_second = d.imul(ab_tail, pc.scale);
            let inner_split = d.iadd(inner_first, inner_second);
            let lifted_inner =
                d.icongr(left_head, inner_split, inner_open, &|d, t| d.imul(t, scale));
            let inner_scaled = d.imul(inner_split, scale);
            let expand_inner = d.lemma(p.int_right_distrib, &[inner_first, inner_second, scale]);
            let term_a = d.imul(inner_first, scale);
            let term_b = d.imul(inner_second, scale);
            let sum_ab = d.iadd(term_a, term_b);
            let staged_left = d.iadd(inner_scaled, left_second);
            let step_expand = d.icongr(left_first, inner_scaled, lifted_inner, &|d, t| {
                d.iadd(t, left_second)
            });
            let step_split = d.icongr(inner_scaled, sum_ab, expand_inner, &|d, t| {
                d.iadd(t, left_second)
            });
            let grouped_left = d.iadd(sum_ab, left_second);

            // Right: (n_a·(d_b·d_c) + (n_b·d_c + n_c·d_b)·d_a)·K.
            let right_first = d.imul(right_head, scale);
            let right_second = d.imul(right_tail, scale);
            let open_right = d.lemma(p.int_right_distrib, &[right_head, right_tail, scale]);
            let split_right = d.iadd(right_first, right_second);
            let inner_open_right = d.lemma(p.int_right_distrib, &[bc_head, bc_tail, pa.scale]);
            let inner_first_right = d.imul(bc_head, pa.scale);
            let inner_second_right = d.imul(bc_tail, pa.scale);
            let inner_split_right = d.iadd(inner_first_right, inner_second_right);
            let lifted_inner_right =
                d.icongr(right_tail, inner_split_right, inner_open_right, &|d, t| {
                    d.imul(t, scale)
                });
            let inner_scaled_right = d.imul(inner_split_right, scale);
            let expand_inner_right = d.lemma(
                p.int_right_distrib,
                &[inner_first_right, inner_second_right, scale],
            );
            let term_b_right = d.imul(inner_first_right, scale);
            let term_c_right = d.imul(inner_second_right, scale);
            let sum_bc = d.iadd(term_b_right, term_c_right);
            let staged_right = d.iadd(right_first, inner_scaled_right);
            let step_expand_right = d.icongr(
                right_second,
                inner_scaled_right,
                lifted_inner_right,
                &|d, t| d.iadd(right_first, t),
            );
            let step_split_right =
                d.icongr(inner_scaled_right, sum_bc, expand_inner_right, &|d, t| {
                    d.iadd(right_first, t)
                });
            let grouped_right = d.iadd(right_first, sum_bc);

            // The three monomials, matched.
            let match_a = {
                let mut left = Flat::begin_product(d, pa.num, &[pa.num], pb.scale, &[pb.scale]);
                left.scale(d, pc.scale, &[pc.scale]);
                left.scale(d, scale, &atoms);
                let right = {
                    let mut flat =
                        Flat::begin_product(d, pa.num, &[pa.num], lifted_bc, &[pb.scale, pc.scale]);
                    flat.scale(d, scale, &atoms);
                    flat
                };
                let canonical = [pa.num, pb.scale, pc.scale, pa.scale, pb.scale, pc.scale];
                agree(d, &canonical, left, right)
            };
            let match_b = {
                let mut left = Flat::begin_product(d, pb.num, &[pb.num], pa.scale, &[pa.scale]);
                left.scale(d, pc.scale, &[pc.scale]);
                left.scale(d, scale, &atoms);
                let mut right = Flat::begin_product(d, pb.num, &[pb.num], pc.scale, &[pc.scale]);
                right.scale(d, pa.scale, &[pa.scale]);
                right.scale(d, scale, &atoms);
                let canonical = [pb.num, pa.scale, pc.scale, pa.scale, pb.scale, pc.scale];
                agree(d, &canonical, left, right)
            };
            let match_c = {
                let mut left =
                    Flat::begin_product(d, pc.num, &[pc.num], lifted_ab, &[pa.scale, pb.scale]);
                left.scale(d, scale, &atoms);
                let mut right = Flat::begin_product(d, pc.num, &[pc.num], pb.scale, &[pb.scale]);
                right.scale(d, pa.scale, &[pa.scale]);
                right.scale(d, scale, &atoms);
                let canonical = [pc.num, pa.scale, pb.scale, pa.scale, pb.scale, pc.scale];
                agree(d, &canonical, left, right)
            };

            let goal_a = d.imul(right_head, scale);
            let goal_b = d.imul(inner_first_right, scale);
            let goal_c = d.imul(inner_second_right, scale);
            let after_a = d.iadd(goal_a, term_b);
            let step_a = d.icongr(term_a, goal_a, match_a, &|d, t| d.iadd(t, term_b));
            let after_b = d.iadd(goal_a, goal_b);
            let step_b = d.icongr(term_b, goal_b, match_b, &|d, t| d.iadd(goal_a, t));
            let sum_head = d.iadd(goal_a, goal_b);
            let with_c = d.iadd(sum_head, goal_c);
            let step_c = d.icongr(left_second, goal_c, match_c, &|d, t| d.iadd(sum_head, t));
            let grouped_flat = d.iadd(after_b, left_second);
            let step_pair = d.icongr(sum_ab, after_a, step_a, &|d, t| d.iadd(t, left_second));
            let step_pair2 = d.icongr(after_a, after_b, step_b, &|d, t| d.iadd(t, left_second));
            let regroup_sum = d.lemma(int.add_assoc, &[goal_a, goal_b, goal_c]);
            let nested = d.iadd(goal_b, goal_c);
            let final_right = d.iadd(goal_a, nested);

            let close_inner_right = d.isymm(staged_right, grouped_right, step_split_right);
            let close_outer_right = d.isymm(split_right, staged_right, step_expand_right);
            let close_right = d.isymm(start_right, split_right, open_right);
            let back_regroup = d.isymm(start_right_raw, start_right, regroup_step);
            let staged_after_a = d.iadd(after_a, left_second);

            let (_, chained) = d.ichain(
                start_left,
                &[
                    (split_left, open_left),
                    (staged_left, step_expand),
                    (grouped_left, step_split),
                    (staged_after_a, step_pair),
                    (grouped_flat, step_pair2),
                    (with_c, step_c),
                    (final_right, regroup_sum),
                    (staged_right, close_inner_right),
                    (split_right, close_outer_right),
                    (start_right, close_right),
                    (start_right_raw, back_regroup),
                ],
            );
            chained
        };

        let bridge = d.const_app(
            p.normalize_congr,
            &[
                left_num, left_den, left_pos, right_num, right_den, right_pos, identity,
            ],
        );

        let left_collapsed = normalize(d, left_num, left_den, left_pos);
        let right_collapsed = normalize(d, right_num, right_den, right_pos);
        let mid_left = radd(d, left_source, renormalised_c);
        let mid_right = radd(d, renormalised_a, right_source);
        let goal_right = radd(d, a, right_source);
        let undo_right = rsymm(d, mid_right, right_collapsed, collapse_right);
        let undo_a = {
            let forward = rcongr(d, a, renormalised_a, to_a, &|d, t| radd(d, t, right_source));
            rsymm(d, goal_right, mid_right, forward)
        };
        let start = radd(d, left_source, c);
        let (_, proof) = rchain(
            d,
            start,
            &[
                (mid_left, step_left),
                (left_collapsed, collapse_left),
                (right_collapsed, bridge),
                (mid_right, undo_right),
                (goal_right, undo_a),
            ],
        );
        (stmt, proof)
    })
}

/// `a·(b+c) = a·b + a·c`.
fn declare_left_distrib(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    rat_theorem(d, p.left_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let stmt = statements::left_distrib(d, p, v);
        let pa = parts(d, a);
        let pb = parts(d, b);
        let pc = parts(d, c);

        let bc_head = d.imul(pb.num, pc.scale);
        let bc_tail = d.imul(pc.num, pb.scale);
        let bc_num = d.iadd(bc_head, bc_tail);
        let bc_den = NatOps::mul(d, pb.den, pc.den);
        let bc_pos = d.lemma(nat.one_le_mul, &[pb.den, pc.den, pb.positive, pc.positive]);
        let ab_num = d.imul(pa.num, pb.num);
        let ab_den = NatOps::mul(d, pa.den, pb.den);
        let ab_pos = d.lemma(nat.one_le_mul, &[pa.den, pb.den, pa.positive, pb.positive]);
        let ac_num = d.imul(pa.num, pc.num);
        let ac_den = NatOps::mul(d, pa.den, pc.den);
        let ac_pos = d.lemma(nat.one_le_mul, &[pa.den, pc.den, pa.positive, pc.positive]);

        let renormalised_a = normalize(d, pa.num, pa.den, pa.positive);
        let to_a = {
            let forward = d.const_app(p.self_normalize, &[a]);
            rsymm(d, renormalised_a, a, forward)
        };
        let sum = radd(d, b, c);
        let step_left = rcongr(d, a, renormalised_a, to_a, &|d, t| rmul(d, t, sum));
        let collapse_left = d.const_app(
            p.normalize_mul_normalize,
            &[pa.num, pa.den, pa.positive, bc_num, bc_den, bc_pos],
        );
        let collapse_right = d.const_app(
            p.normalize_add_normalize,
            &[ab_num, ab_den, ab_pos, ac_num, ac_den, ac_pos],
        );

        let left_num = d.imul(pa.num, bc_num);
        let left_den = NatOps::mul(d, pa.den, bc_den);
        let left_pos = d.lemma(nat.one_le_mul, &[pa.den, bc_den, pa.positive, bc_pos]);
        let lifted_ac = d.of_nat(ac_den);
        let lifted_ab = d.of_nat(ab_den);
        let right_head = d.imul(ab_num, lifted_ac);
        let right_tail = d.imul(ac_num, lifted_ab);
        let right_num = d.iadd(right_head, right_tail);
        let right_den = NatOps::mul(d, ab_den, ac_den);
        let right_pos = d.lemma(nat.one_le_mul, &[ab_den, ac_den, ab_pos, ac_pos]);

        let identity = {
            let scale_left = d.of_nat(left_den);
            let scale_right_raw = d.of_nat(right_den);
            let regrouped_den = {
                let inner = NatOps::mul(d, pb.den, ac_den);
                NatOps::mul(d, pa.den, inner)
            };
            let scale_right = d.of_nat(regrouped_den);
            let regroup = {
                let equation = d.lemma(nat.mul_assoc, &[pa.den, pb.den, ac_den]);
                regroup_denominator(d, right_den, regrouped_den, equation)
            };
            let start_left = d.imul(left_num, scale_right_raw);
            let mid_left = d.imul(left_num, scale_right);
            let step_regroup = d.icongr(scale_right_raw, scale_right, regroup, &|d, t| {
                d.imul(left_num, t)
            });
            let right_atoms = [pa.scale, pb.scale, pa.scale, pc.scale];
            let left_atoms = [pa.scale, pb.scale, pc.scale];

            // Distribute the left side.
            let split_head = d.imul(pa.num, bc_head);
            let split_tail = d.imul(pa.num, bc_tail);
            let split_num = d.iadd(split_head, split_tail);
            let open_inner = d.lemma(int.left_distrib, &[pa.num, bc_head, bc_tail]);
            let lifted_inner = d.icongr(left_num, split_num, open_inner, &|d, t| {
                d.imul(t, scale_right)
            });
            let split_scaled = d.imul(split_num, scale_right);
            let open_left = d.lemma(p.int_right_distrib, &[split_head, split_tail, scale_right]);
            let term_a = d.imul(split_head, scale_right);
            let term_b = d.imul(split_tail, scale_right);
            let split_left = d.iadd(term_a, term_b);

            // Distribute the right side.
            let goal_a = d.imul(right_head, scale_left);
            let goal_b = d.imul(right_tail, scale_left);
            let split_right = d.iadd(goal_a, goal_b);
            let open_right = d.lemma(p.int_right_distrib, &[right_head, right_tail, scale_left]);
            let start_right = d.imul(right_num, scale_left);

            let match_a = {
                let mut left =
                    Flat::begin_product(d, pa.num, &[pa.num], bc_head, &[pb.num, pc.scale]);
                left.scale(d, scale_right, &right_atoms);
                let mut right = Flat::begin_product(d, pa.num, &[pa.num], pb.num, &[pb.num]);
                right.scale(d, lifted_ac, &[pa.scale, pc.scale]);
                right.scale(d, scale_left, &left_atoms);
                let canonical = [
                    pa.num, pb.num, pa.scale, pa.scale, pb.scale, pc.scale, pc.scale,
                ];
                agree(d, &canonical, left, right)
            };
            let match_b = {
                let mut left =
                    Flat::begin_product(d, pa.num, &[pa.num], bc_tail, &[pc.num, pb.scale]);
                left.scale(d, scale_right, &right_atoms);
                let mut right = Flat::begin_product(d, pa.num, &[pa.num], pc.num, &[pc.num]);
                right.scale(d, lifted_ab, &[pa.scale, pb.scale]);
                right.scale(d, scale_left, &left_atoms);
                let canonical = [
                    pa.num, pc.num, pa.scale, pa.scale, pb.scale, pb.scale, pc.scale,
                ];
                agree(d, &canonical, left, right)
            };

            let staged = d.iadd(goal_a, term_b);
            let step_a = d.icongr(term_a, goal_a, match_a, &|d, t| d.iadd(t, term_b));
            let step_b = d.icongr(term_b, goal_b, match_b, &|d, t| d.iadd(goal_a, t));
            let close_right = d.isymm(start_right, split_right, open_right);
            let (_, chained) = d.ichain(
                start_left,
                &[
                    (mid_left, step_regroup),
                    (split_scaled, lifted_inner),
                    (split_left, open_left),
                    (staged, step_a),
                    (split_right, step_b),
                    (start_right, close_right),
                ],
            );
            chained
        };

        let bridge = d.const_app(
            p.normalize_congr,
            &[
                left_num, left_den, left_pos, right_num, right_den, right_pos, identity,
            ],
        );
        let left_collapsed = normalize(d, left_num, left_den, left_pos);
        let right_collapsed = normalize(d, right_num, right_den, right_pos);
        let mid_left = rmul(d, renormalised_a, sum);
        let products = {
            let first = rmul(d, a, b);
            let second = rmul(d, a, c);
            radd(d, first, second)
        };
        let undo_right = rsymm(d, products, right_collapsed, collapse_right);
        let start = rmul(d, a, sum);
        let (_, proof) = rchain(
            d,
            start,
            &[
                (mid_left, step_left),
                (left_collapsed, collapse_left),
                (right_collapsed, bridge),
                (products, undo_right),
            ],
        );
        (stmt, proof)
    })
}

/// One side of a monotonicity law: a compound rational, together with the
/// *unnormalised* numerator/denominator its cross lemma relates it to.
struct Side {
    num: ExprId,
    den: ExprId,
    scale: ExprId,
    positive: ExprId,
    big_num: ExprId,
    big_den: ExprId,
    big_atoms: Vec<ExprId>,
    nat_atoms: Vec<ExprId>,
    nat_positives: Vec<ExprId>,
    cross: ExprId,
}

/// A right-nested `Nat` product of `atoms`, with its positivity.
fn nat_product(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    atoms: &[ExprId],
    positives: &[ExprId],
) -> (ExprId, ExprId) {
    let nat = p.int.nat;
    let (&last, front) = atoms.split_last().expect("a product needs a factor");
    let (&last_positive, front_positives) = positives
        .split_last()
        .expect("a product needs a positivity proof per factor");
    let mut value = last;
    let mut proof = last_positive;
    for (index, &atom) in front.iter().enumerate().rev() {
        let combined = NatOps::mul(d, atom, value);
        let combined_proof = d.lemma(
            nat.one_le_mul,
            &[atom, value, front_positives[index], proof],
        );
        value = combined;
        proof = combined_proof;
    }
    (value, proof)
}

/// Move an inequality between two *unnormalised* cross-products onto the two
/// compound rationals' own projections — i.e. turn it into `Rat.le`/`Rat.lt`.
///
/// Scale by `den L · den R`, substitute both cross lemmas, and cancel the
/// product of every unnormalised denominator. The multiset is the same on both
/// sides by construction; `Flat` checks that it is.
fn lift(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    strict: bool,
    left: &Side,
    right: &Side,
    unnormalised: ExprId,
) -> ExprId {
    let nat = p.int.nat;
    let pair = NatOps::mul(d, left.den, right.den);
    let pair_positive = d.lemma(
        nat.one_le_mul,
        &[left.den, right.den, left.positive, right.positive],
    );
    let lifted_pair = d.of_nat(pair);
    let left_head = d.imul(left.big_num, right.big_den);
    let right_head = d.imul(right.big_num, left.big_den);
    let scaled = if strict {
        d.lemma(
            p.int_mul_lt_mul_right,
            &[left_head, right_head, pair, pair_positive, unnormalised],
        )
    } else {
        d.lemma(
            p.int_mul_le_mul_right,
            &[left_head, right_head, pair, unnormalised],
        )
    };

    let mut all_big = left.big_atoms.clone();
    all_big.extend(right.big_atoms.iter().copied());
    let mut all_nat = left.nat_atoms.clone();
    all_nat.extend(right.nat_atoms.iter().copied());
    let mut all_positive = left.nat_positives.clone();
    all_positive.extend(right.nat_positives.iter().copied());
    let (factor, factor_positive) = nat_product(d, p, &all_nat, &all_positive);
    let factor_scale = d.of_nat(factor);

    let mut canonical_left = vec![left.num, right.scale];
    canonical_left.extend(all_big.iter().copied());
    let mut canonical_right = vec![right.num, left.scale];
    canonical_right.extend(all_big.iter().copied());

    // One side: the scaled cross-product, rewritten onto `num · scale`.
    let side = |d: &mut IntDev<'_>,
                this: &Side,
                other: &Side,
                canonical: &[ExprId]|
     -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
        let mut from = Flat::begin_product(
            d,
            this.big_num,
            &[this.big_num],
            other.big_den,
            &other.big_atoms,
        );
        from.scale(d, lifted_pair, &[left.scale, right.scale]);
        let mut order = vec![this.big_num, this.scale];
        order.extend(other.big_atoms.iter().copied());
        order.push(other.scale);
        from.perm(d, &order);
        let mut prefix = vec![this.num];
        prefix.extend(this.big_atoms.iter().copied());
        let back = {
            let forward_left = super::ops::iprod(d, &prefix);
            let forward_right = super::ops::iprod(d, &[this.big_num, this.scale]);
            d.isymm(forward_left, forward_right, this.cross)
        };
        from.rewrite_prefix(d, 2, &prefix, back);
        from.perm(d, canonical);
        let (from_start, canon, from_proof) = from.finish(d);

        let mut to = Flat::begin_product(d, this.num, &[this.num], other.scale, &[other.scale]);
        to.scale(d, factor_scale, &all_big);
        let (to_start, _, to_proof) = to.finish(d);
        let goal_head = d.imul(this.num, other.scale);
        (from_start, canon, from_proof, to_start, {
            let _ = goal_head;
            to_proof
        })
    };

    let (from_left, canon_left, proof_left, to_left, proof_to_left) =
        side(d, left, right, &canonical_left);
    let (from_right, canon_right, proof_right, to_right, proof_to_right) =
        side(d, right, left, &canonical_right);

    let relation = if strict {
        |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ilt(x, y)
    } else {
        |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ile(x, y)
    };
    let staged = d.int_eq_rewrite(from_left, canon_left, proof_left, scaled, &|d, x| {
        relation(d, x, from_right)
    });
    let both = d.int_eq_rewrite(from_right, canon_right, proof_right, staged, &|d, x| {
        relation(d, canon_left, x)
    });
    let back_left = d.isymm(to_left, canon_left, proof_to_left);
    let back_right = d.isymm(to_right, canon_right, proof_to_right);
    let lowered = d.int_eq_rewrite(canon_left, to_left, back_left, both, &|d, x| {
        relation(d, x, canon_right)
    });
    let aligned = d.int_eq_rewrite(canon_right, to_right, back_right, lowered, &|d, x| {
        relation(d, to_left, x)
    });
    let goal_left = d.imul(left.num, right.scale);
    let goal_right = d.imul(right.num, left.scale);
    if strict {
        d.lemma(
            p.int_lt_of_mul_lt_mul_right,
            &[goal_left, goal_right, factor, factor_positive, aligned],
        )
    } else {
        d.lemma(
            p.int_le_of_mul_le_mul_right,
            &[goal_left, goal_right, factor, factor_positive, aligned],
        )
    }
}

/// `add_le_add` and `add_lt_add_of_le_of_lt`.
fn declare_additive_monotone(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    let law = |d: &mut IntDev<'_>,
               name,
               statement: &dyn Fn(&mut IntDev<'_>, RatPrelude, &[ExprId]) -> ExprId,
               strict: bool|
     -> Result<(), KernelError> {
        rat_theorem(d, name, 4, &|d, v| {
            let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
            let stmt = statement(d, p, v);
            let pa = parts(d, a);
            let pb = parts(d, b);
            let pc = parts(d, c);
            let pe = parts(d, e);

            let first_ty = {
                let l = d.imul(pa.num, pb.scale);
                let r = d.imul(pb.num, pa.scale);
                d.ile(l, r)
            };
            let second_ty = {
                let l = d.imul(pc.num, pe.scale);
                let r = d.imul(pe.num, pc.scale);
                if strict { d.ilt(l, r) } else { d.ile(l, r) }
            };
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);

            let sum_left = radd(d, a, c);
            let sum_right = radd(d, b, e);
            let left_big_num = {
                let head = d.imul(pa.num, pc.scale);
                let tail = d.imul(pc.num, pa.scale);
                d.iadd(head, tail)
            };
            let right_big_num = {
                let head = d.imul(pb.num, pe.scale);
                let tail = d.imul(pe.num, pb.scale);
                d.iadd(head, tail)
            };
            let left_big_den_nat = NatOps::mul(d, pa.den, pc.den);
            let right_big_den_nat = NatOps::mul(d, pb.den, pe.den);
            let left_big_den = d.of_nat(left_big_den_nat);
            let right_big_den = d.of_nat(right_big_den_nat);
            let left = Side {
                num: num(d, sum_left),
                den: den(d, sum_left),
                scale: den_z(d, sum_left),
                positive: den_pos(d, sum_left),
                big_num: left_big_num,
                big_den: left_big_den,
                big_atoms: vec![pa.scale, pc.scale],
                nat_atoms: vec![pa.den, pc.den],
                nat_positives: vec![pa.positive, pc.positive],
                cross: d.lemma(p.add_cross, &[a, c]),
            };
            let right = Side {
                num: num(d, sum_right),
                den: den(d, sum_right),
                scale: den_z(d, sum_right),
                positive: den_pos(d, sum_right),
                big_num: right_big_num,
                big_den: right_big_den,
                big_atoms: vec![pb.scale, pe.scale],
                nat_atoms: vec![pb.den, pe.den],
                nat_positives: vec![pb.positive, pe.positive],
                cross: d.lemma(p.add_cross, &[b, e]),
            };

            // The unnormalised inequality: distribute, and each summand is one
            // hypothesis scaled by the two denominators it does not mention.
            let unnormalised = {
                let ab_head = d.imul(pa.num, pb.scale);
                let ba_head = d.imul(pb.num, pa.scale);
                let ce_head = d.imul(pc.num, pe.scale);
                let ec_head = d.imul(pe.num, pc.scale);
                let cross_ce = NatOps::mul(d, pc.den, pe.den);
                let cross_ab = NatOps::mul(d, pa.den, pb.den);
                let lifted_ce = d.of_nat(cross_ce);
                let lifted_ab = d.of_nat(cross_ab);
                let scaled_first =
                    d.lemma(p.int_mul_le_mul_right, &[ab_head, ba_head, cross_ce, h1]);
                let scaled_second = if strict {
                    let positive =
                        d.lemma(nat.one_le_mul, &[pa.den, pb.den, pa.positive, pb.positive]);
                    d.lemma(
                        p.int_mul_lt_mul_right,
                        &[ce_head, ec_head, cross_ab, positive, h2],
                    )
                } else {
                    d.lemma(p.int_mul_le_mul_right, &[ce_head, ec_head, cross_ab, h2])
                };

                let ac_head = d.imul(pa.num, pc.scale);
                let ca_head = d.imul(pc.num, pa.scale);
                let be_head = d.imul(pb.num, pe.scale);
                let eb_head = d.imul(pe.num, pb.scale);
                let term_first = d.imul(ac_head, right_big_den);
                let term_second = d.imul(ca_head, right_big_den);
                let goal_first = d.imul(be_head, left_big_den);
                let goal_second = d.imul(eb_head, left_big_den);

                let align_first = {
                    let from = Flat::begin_product(
                        d,
                        ab_head,
                        &[pa.num, pb.scale],
                        lifted_ce,
                        &[pc.scale, pe.scale],
                    );
                    let to = Flat::begin_product(
                        d,
                        ac_head,
                        &[pa.num, pc.scale],
                        right_big_den,
                        &[pb.scale, pe.scale],
                    );
                    agree(d, &[pa.num, pb.scale, pc.scale, pe.scale], from, to)
                };
                let align_first_right = {
                    let from = Flat::begin_product(
                        d,
                        ba_head,
                        &[pb.num, pa.scale],
                        lifted_ce,
                        &[pc.scale, pe.scale],
                    );
                    let to = Flat::begin_product(
                        d,
                        be_head,
                        &[pb.num, pe.scale],
                        left_big_den,
                        &[pa.scale, pc.scale],
                    );
                    agree(d, &[pb.num, pa.scale, pc.scale, pe.scale], from, to)
                };
                let align_second = {
                    let from = Flat::begin_product(
                        d,
                        ce_head,
                        &[pc.num, pe.scale],
                        lifted_ab,
                        &[pa.scale, pb.scale],
                    );
                    let to = Flat::begin_product(
                        d,
                        ca_head,
                        &[pc.num, pa.scale],
                        right_big_den,
                        &[pb.scale, pe.scale],
                    );
                    agree(d, &[pc.num, pa.scale, pb.scale, pe.scale], from, to)
                };
                let align_second_right = {
                    let from = Flat::begin_product(
                        d,
                        ec_head,
                        &[pe.num, pc.scale],
                        lifted_ab,
                        &[pa.scale, pb.scale],
                    );
                    let to = Flat::begin_product(
                        d,
                        eb_head,
                        &[pe.num, pb.scale],
                        left_big_den,
                        &[pa.scale, pc.scale],
                    );
                    agree(d, &[pe.num, pa.scale, pb.scale, pc.scale], from, to)
                };

                let from_first = d.imul(ab_head, lifted_ce);
                let from_first_right = d.imul(ba_head, lifted_ce);
                let from_second = d.imul(ce_head, lifted_ab);
                let from_second_right = d.imul(ec_head, lifted_ab);
                let first_aligned = {
                    let staged = d.int_eq_rewrite(
                        from_first,
                        term_first,
                        align_first,
                        scaled_first,
                        &|d, x| d.ile(x, from_first_right),
                    );
                    d.int_eq_rewrite(
                        from_first_right,
                        goal_first,
                        align_first_right,
                        staged,
                        &|d, x| d.ile(term_first, x),
                    )
                };
                let relation = if strict {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ilt(x, y)
                } else {
                    |d: &mut IntDev<'_>, x: ExprId, y: ExprId| d.ile(x, y)
                };
                let second_aligned = {
                    let staged = d.int_eq_rewrite(
                        from_second,
                        term_second,
                        align_second,
                        scaled_second,
                        &|d, x| relation(d, x, from_second_right),
                    );
                    d.int_eq_rewrite(
                        from_second_right,
                        goal_second,
                        align_second_right,
                        staged,
                        &|d, x| relation(d, term_second, x),
                    )
                };
                let summed = if strict {
                    d.lemma(
                        int.add_lt_add_of_le_of_lt,
                        &[
                            term_first,
                            goal_first,
                            term_second,
                            goal_second,
                            first_aligned,
                            second_aligned,
                        ],
                    )
                } else {
                    d.lemma(
                        int.add_le_add,
                        &[
                            term_first,
                            goal_first,
                            term_second,
                            goal_second,
                            first_aligned,
                            second_aligned,
                        ],
                    )
                };
                // Re-fold the two distributed products.
                let whole_left = d.imul(left_big_num, right_big_den);
                let whole_right = d.imul(right_big_num, left_big_den);
                let open_left = d.lemma(p.int_right_distrib, &[ac_head, ca_head, right_big_den]);
                let open_right = d.lemma(p.int_right_distrib, &[be_head, eb_head, left_big_den]);
                let split_left = d.iadd(term_first, term_second);
                let split_right = d.iadd(goal_first, goal_second);
                let back_left = d.isymm(whole_left, split_left, open_left);
                let back_right = d.isymm(whole_right, split_right, open_right);
                let staged =
                    d.int_eq_rewrite(split_left, whole_left, back_left, summed, &|d, x| {
                        relation(d, x, split_right)
                    });
                d.int_eq_rewrite(split_right, whole_right, back_right, staged, &|d, x| {
                    relation(d, whole_left, x)
                })
            };

            let body = lift(d, p, strict, &left, &right, unnormalised);
            let proof = {
                let with_second = d.lam_fv(h2_fv, second_ty, body);
                d.lam_fv(h1_fv, first_ty, with_second)
            };
            (stmt, proof)
        })
    };
    law(d, p.add_le_add, &statements::add_le_add, false)?;
    law(
        d,
        p.add_lt_add_of_le_of_lt,
        &statements::add_lt_add_of_le_of_lt,
        true,
    )
}

/// `0 ≤ a → b ≤ c → a·b ≤ a·c`.
fn declare_multiplicative_monotone(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    rat_theorem(d, p.mul_le_mul_of_nonneg_left, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let stmt = statements::mul_le_mul_of_nonneg_left(d, p, v);
        let pa = parts(d, a);
        let pb = parts(d, b);
        let pc = parts(d, c);

        let zero_rat = d.kernel().const_(p.zero, vec![]);
        let first_ty = rle(d, p, zero_rat, a);
        let second_ty = {
            let l = d.imul(pb.num, pc.scale);
            let r = d.imul(pc.num, pb.scale);
            d.ile(l, r)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let product_left = rmul(d, a, b);
        let product_right = rmul(d, a, c);
        let left_big_num = d.imul(pa.num, pb.num);
        let right_big_num = d.imul(pa.num, pc.num);
        let left_big_den_nat = NatOps::mul(d, pa.den, pb.den);
        let right_big_den_nat = NatOps::mul(d, pa.den, pc.den);
        let left_big_den = d.of_nat(left_big_den_nat);
        let right_big_den = d.of_nat(right_big_den_nat);
        let left = Side {
            num: num(d, product_left),
            den: den(d, product_left),
            scale: den_z(d, product_left),
            positive: den_pos(d, product_left),
            big_num: left_big_num,
            big_den: left_big_den,
            big_atoms: vec![pa.scale, pb.scale],
            nat_atoms: vec![pa.den, pb.den],
            nat_positives: vec![pa.positive, pb.positive],
            cross: d.lemma(p.mul_cross, &[a, b]),
        };
        let right = Side {
            num: num(d, product_right),
            den: den(d, product_right),
            scale: den_z(d, product_right),
            positive: den_pos(d, product_right),
            big_num: right_big_num,
            big_den: right_big_den,
            big_atoms: vec![pa.scale, pc.scale],
            nat_atoms: vec![pa.den, pc.den],
            nat_positives: vec![pa.positive, pc.positive],
            cross: d.lemma(p.mul_cross, &[a, c]),
        };

        let unnormalised = {
            // `0 ≤ n_a · d_a`, the factor the `Int` law multiplies by.
            let numerator_nonneg = d.lemma(p.int_nonneg_of_nonneg, &[a, h1]);
            let denominator_nonneg = d.lemma(p.int_zero_le_of_nat, &[pa.den]);
            let factor = d.imul(pa.num, pa.scale);
            let factor_nonneg = d.lemma(
                int.mul_nonneg,
                &[pa.num, pa.scale, numerator_nonneg, denominator_nonneg],
            );
            let bc_head = d.imul(pb.num, pc.scale);
            let cb_head = d.imul(pc.num, pb.scale);
            let base = d.lemma(
                int.mul_le_mul_of_nonneg_left,
                &[factor, bc_head, cb_head, factor_nonneg, h2],
            );
            let from_left = d.imul(factor, bc_head);
            let from_right = d.imul(factor, cb_head);
            let to_left = d.imul(left_big_num, right_big_den);
            let to_right = d.imul(right_big_num, left_big_den);
            let align_left = {
                let from = Flat::begin_product(
                    d,
                    factor,
                    &[pa.num, pa.scale],
                    bc_head,
                    &[pb.num, pc.scale],
                );
                let to = Flat::begin_product(
                    d,
                    left_big_num,
                    &[pa.num, pb.num],
                    right_big_den,
                    &[pa.scale, pc.scale],
                );
                agree(d, &[pa.num, pb.num, pa.scale, pc.scale], from, to)
            };
            let align_right = {
                let from = Flat::begin_product(
                    d,
                    factor,
                    &[pa.num, pa.scale],
                    cb_head,
                    &[pc.num, pb.scale],
                );
                let to = Flat::begin_product(
                    d,
                    right_big_num,
                    &[pa.num, pc.num],
                    left_big_den,
                    &[pa.scale, pb.scale],
                );
                agree(d, &[pa.num, pc.num, pa.scale, pb.scale], from, to)
            };
            let staged = d.int_eq_rewrite(from_left, to_left, align_left, base, &|d, x| {
                d.ile(x, from_right)
            });
            d.int_eq_rewrite(from_right, to_right, align_right, staged, &|d, x| {
                d.ile(to_left, x)
            })
        };

        let body = lift(d, p, false, &left, &right, unnormalised);
        let proof = {
            let with_second = d.lam_fv(h2_fv, second_ty, body);
            d.lam_fv(h1_fv, first_ty, with_second)
        };
        (stmt, proof)
    })
}
