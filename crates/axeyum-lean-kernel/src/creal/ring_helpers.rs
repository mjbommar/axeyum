//! Shared `CReal` ring-algebra proof-term builders, `pub(super)` to the
//! `creal` module tree.
//!
//! This module exists because two of `CReal`'s private per-file proof-term
//! helpers stopped being duplicated in only two files and started being
//! duplicated in three: [`right_distrib`] was built independently in
//! `creal/power.rs` and `creal/derivative.rs`, and [`add4_comm`] was built
//! independently in `creal/series.rs` and `creal/derivative.rs`.
//! `creal/derivative.rs`'s own doc comments on its former local copies said,
//! for each, that it was "rebuilt here rather than imported... since
//! `power.rs`'s/`series.rs`'s copy is private to that module" — i.e. the
//! duplication was a direct consequence of there being no shared home, not a
//! deliberate choice to keep the proof terms independent. Byte-for-byte
//! comparison confirmed both pairs were identical before this promotion, so
//! this module gives them the shared home the comments were already pointing
//! at, and both call sites now build the exact same proof term they did
//! before (verified via `Kernel::add_declaration`, not just `cargo check` —
//! see `creal/creal_tests.rs`).
//!
//! `CReal.abs_add_le`'s private BUILDER was never merged here, and the
//! reasoning still stands: `series.rs`'s old copy discharged `neg(add a b) ~
//! add(neg a)(neg b)` via its own private `neg_add`, `derivative.rs`'s
//! discharges the identical *statement* via its own `neg_add_distrib` (a
//! different proof term built for `sq_le_abs_sq`), and merging the two
//! builders into one shared route would mean picking one over the other —
//! exactly the "merging two subtly different helpers into one" risk this
//! module is meant to avoid, not invite.
//!
//! **That is a different question from whether callers re-derive the
//! STATEMENT, and by the time `CReal.abs_add_le` became a public kernel
//! declaration (`uniform_continuity::declare_abs_add_le`) that second
//! question had its own cheap answer: cite the theorem.** `series.rs`,
//! `derivative.rs` and `deriv_unique.rs` no longer carry a private
//! `abs_add_le` copy at all — every call site now does `d.lemma(p.abs_add_le,
//! &[a, b])`, and `series.rs`'s own `neg_add` (only ever called from its
//! local `abs_add_le`) went with it, dead code once its one caller was gone.
//! `derivative.rs`'s `neg_add_distrib` survives: unlike `neg_add`, it has
//! other callers. The only surviving private `abs_add_le` PROOF-TERM BUILDER
//! is `uniform_continuity.rs`'s own, because it is what makes the public
//! declaration provable in the first place — nothing can cite a theorem
//! before it exists.
//!
//! `cadd`/`cmul`/`echain` below are minimal private restatements of the
//! identical helpers already private to `power.rs`/`series.rs`/
//! `derivative.rs` — needed so [`right_distrib`] and [`add4_comm`] have
//! something to call, and deliberately not promoted themselves: that
//! duplication is wider (three-plus call sites each) and out of scope here.

use super::CRealPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

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

/// `Equiv (mul (add a b) c) (add (mul a c) (mul b c))` — the missing
/// distributivity direction, the sum on the **left** of the product.
/// `CReal.left_distrib` only distributes a sum on the right; this builds the
/// missing direction from `mul_comm` plus `left_distrib`. Formerly duplicated
/// verbatim in `creal/power.rs` and `creal/derivative.rs`.
pub(super) fn right_distrib(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let ab = cadd(d, p, a, b);
    let lhs = cmul(d, p, ab, c);
    let c_ab = cmul(d, p, c, ab);
    let h1 = d.lemma(p.mul_comm, &[ab, c]); // lhs ~ c_ab

    let ca = cmul(d, p, c, a);
    let cb = cmul(d, p, c, b);
    let dist = cadd(d, p, ca, cb);
    let h2 = d.lemma(p.left_distrib, &[c, a, b]); // c_ab ~ dist

    let ac = cmul(d, p, a, c);
    let bc = cmul(d, p, b, c);
    let target = cadd(d, p, ac, bc);
    let h3a = d.lemma(p.mul_comm, &[c, a]); // ca ~ ac
    let h3b = d.lemma(p.mul_comm, &[c, b]); // cb ~ bc
    let h3 = d.lemma(p.add_congr, &[ca, ac, cb, bc, h3a, h3b]); // dist ~ target

    echain(d, p, lhs, &[(c_ab, h1), (dist, h2), (target, h3)])
}

/// `Equiv (add (add a b) (add c dd)) (add (add a c) (add b dd))` — swap the
/// middle two of a four-term sum. Returns `(target, proof)`. Formerly
/// duplicated verbatim in `creal/series.rs` and `creal/derivative.rs`.
pub(super) fn add4_comm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let cd = cadd(d, p, c, dd);
    let bd = cadd(d, p, b, dd);
    let ab = cadd(d, p, a, b);
    let start = cadd(d, p, ab, cd);

    // start ~ a + (b + (c+d))
    let bcd = cadd(d, p, b, cd);
    let s1 = cadd(d, p, a, bcd);
    let h1 = d.lemma(p.add_assoc, &[a, b, cd]);

    // b+(c+d) ~ (b+c)+d
    let bc = cadd(d, p, b, c);
    let bc_d = cadd(d, p, bc, dd);
    let s2 = cadd(d, p, a, bc_d);
    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let h_bcd = d.lemma(p.add_assoc, &[b, c, dd]); // (b+c)+d ~ b+(c+d)
    let h2_inner = d.lemma(p.equiv_symm, &[bc_d, bcd, h_bcd]); // b+(c+d) ~ (b+c)+d
    let h2 = d.lemma(p.add_congr, &[a, a, bcd, bc_d, refl_a, h2_inner]);

    // (b+c) ~ (c+b)
    let cb = cadd(d, p, c, b);
    let cb_d = cadd(d, p, cb, dd);
    let s3 = cadd(d, p, a, cb_d);
    let h_comm = d.lemma(p.add_comm, &[b, c]); // b+c ~ c+b
    let refl_dd = d.lemma(p.equiv_refl, &[dd]);
    let h_comm_d = d.lemma(p.add_congr, &[bc, cb, dd, dd, h_comm, refl_dd]); // (b+c)+d ~ (c+b)+d
    let h3 = d.lemma(p.add_congr, &[a, a, bc_d, cb_d, refl_a, h_comm_d]);

    // (c+b)+d ~ c+(b+d)
    let cbd = cadd(d, p, c, bd);
    let s4 = cadd(d, p, a, cbd);
    let h_assoc2 = d.lemma(p.add_assoc, &[c, b, dd]); // (c+b)+d ~ c+(b+d)
    let h4 = d.lemma(p.add_congr, &[a, a, cb_d, cbd, refl_a, h_assoc2]);

    // a+(c+(b+d)) ~ (a+c)+(b+d)
    let ac = cadd(d, p, a, c);
    let target = cadd(d, p, ac, bd);
    let h_assoc3 = d.lemma(p.add_assoc, &[a, c, bd]); // target ~ s4
    let h5 = d.lemma(p.equiv_symm, &[target, s4, h_assoc3]); // s4 ~ target

    let proof = echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (target, h5)],
    );
    (target, proof)
}
