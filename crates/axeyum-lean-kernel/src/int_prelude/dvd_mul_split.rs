//! `Int.dvd_mul_split : ∀ (c a b : Int), Iff (dvd c (mul a b)) (∃ c1 c2, And
//! (dvd c1 a) (And (dvd c2 b) (Eq Int (mul c1 c2) c)))` -- Mathlib's
//! `Int.dvd_mul` (`F:ml430-int-dvd-mul-3a7b94cd`), the ℤ sibling of
//! `nat_prelude::dvd_mul_split::declare_dvd_mul_split`
//! (`docs/plan/status/343-dvd-mul-split.md`).
//!
//! **Not named `Int.dvd_mul`** for the same reason the `Nat` mirror isn't
//! named `Nat.dvd_mul`: `dvd_mul_split` is the name that lane checked free in
//! *both* preludes, kept here for symmetry.
//!
//! # None of the three blockers `343-dvd-mul-split.md` named turned out to be
//! needed as stated -- verified in the tree before writing a line of proof.
//!
//! 1. **"A general `Int.gcd_mul_right`"** -- not needed. The real-content
//!    step never scales an `Int.gcd` by a signed factor: it routes entirely
//!    through `natAbs` values and the already-proved `Nat.gcd_mul_right`, so
//!    the sign of `b` never has to be split on or reconstructed. This is
//!    what avoids the `eq_or_eq_neg_of_nat_abs_eq`-style sign-guessing
//!    machinery the status doc correctly identified as missing.
//! 2. **"An Int-level cancellation lemma for a nonzero common factor"** --
//!    not needed either: the one cancellation the proof performs is at the
//!    `Nat` level (`natAbs`-magnitude arithmetic), where
//!    `Nat.mul_left_cancel_of_pos` already applies once the common factor is
//!    shown positive.
//! 3. **"Establishing `g1 ≠ 0` from `c ≠ 0`"** -- genuinely needed, and
//!    genuinely cheap: `Nat.eq_zero_of_gcd_eq_zero_left` plus a local copy of
//!    `ring.rs`'s private `nat_abs_zero_implies_int_zero` (`natAbs x = 0 →
//!    x = 0`, by `Int.rec`) compose directly -- no case split on `c`'s sign,
//!    no excluded middle beyond the single `c = 0 ∨ c ≠ 0` split the
//!    statement itself needs.
//!
//! # Strategy
//!
//! Route entirely through `natAbs c`, `natAbs a`, `natAbs b` for the hard
//! content, bridging back to `Int` divisibility only at the hypothesis and
//! at the final `c2 ∣ b` conclusion, via the already-proved sign-agnostic
//! bridges `nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd` (`gcd.rs`). The
//! *witnesses* `c1 := g1`, `c2 := w` are genuine `Int` values throughout
//! (`g1` is manifestly nonnegative; `w` comes from an `Int`-level `dvd_elim`
//! on `gcd_dvd_left`, so it already carries whatever sign the equation
//! `c = g1*w` forces) -- never reconstructed from a `Nat` witness after the
//! fact, which is the sign-ambiguous route the status doc warned off.
//!
//! **Reverse (`mpr`).** Same four-factor regroup as the `Nat` proof
//! (`imul_mul_mul_comm`, built from `Int.mul_assoc`/`Int.mul_comm` since no
//! `Int.mul_left_comm` field exists). Fully uniform, no case split.
//!
//! **Forward (`mp`), case split on `c = 0 ∨ c ≠ 0` (`Int.eq_em`).**
//!
//! - `c = 0`: `h : dvd 0 (a*b)` gives `a*b = 0` (`zero_dvd_elim`), so
//!   `Int.mul_eq_zero` splits into `a = 0` or `b = 0`, giving witnesses
//!   `(0, b)` or `(a, 0)` respectively. The general `g1 := gcd(c,a)`
//!   construction below cannot fire here (it needs `g1 ≠ 0` from `c ≠ 0`),
//!   the same corner the `Nat` proof hit.
//! - `c ≠ 0`: let `nc, na, nb := natAbs c, natAbs a, natAbs b` and
//!   `g1_nat := Nat.gcd nc na`, `c1 := ofNat g1_nat`.
//!   - `dvd c1 a` is `gcd_dvd_right c a` directly (`Int.gcd c a` δ-reduces to
//!     `Nat.gcd nc na`, accepted by `def_eq` with no bridging lemma).
//!   - `gcd_dvd_left c a : dvd c1 c`; `Int`-level `dvd_elim` gives a witness
//!     `w` with `c = c1*w`. `c2 := w`; `symm` is the third conjunct.
//!   - The real content, `dvd w b`: bridge `h : c ∣ a*b` to `nc ∣ na*nb`
//!     (`nat_abs_dvd_nat_abs_of_dvd` + `nat_abs_mul`); combine with the
//!     trivial `nc ∣ nc*nb` (`Nat.dvd_mul`) via `Nat.dvd_gcd` into
//!     `nc ∣ gcd (nc*nb) (na*nb)`; `Nat.gcd_mul_right` rewrites the gcd to
//!     `g1_nat*nb`, giving `nc ∣ g1_nat*nb`; substituting
//!     `nc = g1_nat * natAbs w` (from `c = c1*w` via `natAbs`/`nat_abs_mul`)
//!     gives `g1_nat*(natAbs w) ∣ g1_nat*nb`; cancelling the common factor
//!     `g1_nat` (`g1_nat ≠ 0` from `c ≠ 0` as above, then
//!     `Nat.zero_lt_of_ne_zero` and `Nat.mul_left_cancel_of_pos`, via a local
//!     Nat-level `dvd_cancel_left_of_ne_zero` -- a straight copy of
//!     `nat_prelude/dvd_mul_split.rs`'s own `dvd_cancel_left_of_pos`, built
//!     from only `NatOps` default methods so it works verbatim from an
//!     `IntDev` context) gives `natAbs w ∣ nb`; `dvd_of_nat_abs_dvd` lifts
//!     that to `dvd w b`.

use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// `Int`-level local term-building helpers, this development's per-file-copy
// convention (see `int_prelude/dvd.rs`, `int_prelude/gcd.rs` for originals of
// the same names/shapes).
// ---------------------------------------------------------------------------

/// `Int.dvd`'s witness predicate `fun c => Eq Int b (a*c)`.
fn idvd_predicate(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ac = d.imul(a, c);
    let body = d.ieq(b, ac);
    d.lam_fv(c_fv, int_ty, body)
}

/// `Int.dvd a b`.
fn idvd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().dvd;
    d.const_app(f, &[a, b])
}

/// `Exists.intro.{1} Int (idvd_predicate a b) witness proof : Int.dvd a b`.
fn idvd_intro(d: &mut IntDev<'_>, a: ExprId, b: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
    let pred = idvd_predicate(d, a, b);
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    let int_ty = d.int_ty();
    d.apply(intro, &[int_ty, pred, witness, proof])
}

/// Eliminate `witness : Int.dvd a b` into `target`, given a continuation
/// consuming a concrete (bound) witness `c` and `proof : Eq Int b (a*c)`.
fn idvd_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    witness: ExprId,
    continuation: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let pred = idvd_predicate(d, a, b);
    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let ac = d.imul(a, c);
        let eq_ty = d.ieq(b, ac);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, c, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(c_fv, int_ty, with_eq)
    };
    int_exists_elim(d, pred, target, witness, minor)
}

/// Eliminate `witness : Exists Int predicate` into `target`, given
/// `minor : ∀ (u : Int), predicate u → target`.
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, predicate])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// `Eq Int x zero` from `h_dvd : Int.dvd zero_int x`.
fn zero_dvd_elim(d: &mut IntDev<'_>, x: ExprId, h_dvd: ExprId) -> ExprId {
    let p = d.int();
    let zero_int = d.izero();
    let pred = idvd_predicate(d, zero_int, x);
    let goal = d.ieq(x, zero_int);
    let int_ty = d.int_ty();

    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let zc = d.imul(zero_int, c);
        let heq_ty = d.ieq(x, zc);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let cz = d.imul(c, zero_int);
        let comm = d.const_app(p.mul_comm, &[zero_int, c]); // Eq Int zc cz
        let mz = d.const_app(p.mul_zero, &[c]); // Eq Int cz zero_int
        let (_, chained) = d.ichain(zc, &[(cz, comm), (zero_int, mz)]);
        let result = d.itrans(x, zc, zero_int, heq, chained);
        let with_heq = d.lam_fv(heq_fv, heq_ty, result);
        d.lam_fv(c_fv, int_ty, with_heq)
    };
    int_exists_elim(d, pred, goal, h_dvd, minor)
}

/// `∀ (x : Int), Eq Nat (natAbs x) Nat.zero → Eq Int x Int.zero`. Local copy
/// of `ring.rs`'s private `nat_abs_zero_implies_int_zero`: `Int.rec` case
/// split on `x`; `ofNat` branch pushes the `Nat` hypothesis through `ofNat`
/// (`nat_eq_to_int`); `negSucc` branch is refuted directly by
/// `Nat.succ_ne_zero`.
fn nat_abs_zero_implies_int_zero(d: &mut IntDev<'_>, x: ExprId) -> ExprId {
    use super::ops::{Branch, Shape, case_split};
    let p = d.int();

    let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
        let y = args[0];
        let magnitude = d.const_app(p.nat_abs, &[y]);
        let zero_nat = d.zero();
        let hyp = d.eq(magnitude, zero_nat);
        let izero = d.izero();
        let concl = d.ieq(y, izero);
        d.arrow(hyp, concl)
    };
    case_split(d, &[x], &statement, &|d, branches: &[Branch]| {
        let (shape, field) = branches[0];
        match shape {
            Shape::OfNat => {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero_nat = d.zero();
                let hyp_ty = d.eq(field, zero_nat);
                let proved = d.nat_eq_to_int(field, zero_nat, h, &|d, v| d.of_nat(v));
                d.lam_fv(h_fv, hyp_ty, proved)
            }
            Shape::NegSucc => {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero_nat = d.zero();
                let successor = d.succ(field);
                let hyp_ty = d.eq(successor, zero_nat);
                let nat = p.nat;
                let refuted = d.lemma(nat.succ_ne_zero, &[field]);
                let false_pf = d.apply(refuted, &[h]);
                let ns = d.neg_succ(field);
                let izero = d.izero();
                let target = d.ieq(ns, izero);
                let body = d.absurd(target, false_pf);
                d.lam_fv(h_fv, hyp_ty, body)
            }
        }
    })
}

/// `Eq Int (mul x (mul y z)) (mul y (mul x z))` -- `Int` transport of
/// `nat_prelude/binomial.rs`'s `mul_left_comm` (no `Int.mul_left_comm` field
/// exists, so built here from `mul_assoc`/`mul_comm` directly).
fn imul_left_comm(d: &mut IntDev<'_>, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let p = d.int();
    let yz = d.imul(y, z);
    let start = d.imul(x, yz);
    let xy = d.imul(x, y);
    let xy_z = d.imul(xy, z);
    let h_assoc1 = d.const_app(p.mul_assoc, &[x, y, z]); // Eq xy_z start
    let h1 = d.isymm(xy_z, start, h_assoc1); // Eq start xy_z
    let yx = d.imul(y, x);
    let yx_z = d.imul(yx, z);
    let h_comm = d.const_app(p.mul_comm, &[x, y]); // Eq xy yx
    let h2 = d.icongr(xy, yx, h_comm, &|d, t| d.imul(t, z)); // Eq xy_z yx_z
    let xz = d.imul(x, z);
    let target = d.imul(y, xz);
    let h3 = d.const_app(p.mul_assoc, &[y, x, z]); // Eq yx_z target
    let (_, proof) = d.ichain(start, &[(xy_z, h1), (yx_z, h2), (target, h3)]);
    proof
}

/// `Eq Int (mul (mul a b) (mul c dd)) (mul (mul a c) (mul b dd))` -- `Int`
/// transport of `nat_prelude/dvd_mul_split.rs`'s `mul_mul_mul_comm`.
fn imul_mul_mul_comm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, dd: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.imul(a, b);
    let cd = d.imul(c, dd);
    let start = d.imul(ab, cd);

    let bcd = d.imul(b, cd);
    let step1 = d.const_app(p.mul_assoc, &[a, b, cd]); // Eq start (a*bcd)
    let a_bcd = d.imul(a, bcd);

    let bd = d.imul(b, dd);
    let cbd = d.imul(c, bd);
    let step2 = imul_left_comm(d, b, c, dd); // Eq bcd cbd
    let congr2 = d.icongr(bcd, cbd, step2, &|d, t| d.imul(a, t)); // Eq a_bcd (a*cbd)
    let a_cbd = d.imul(a, cbd);

    let ac = d.imul(a, c);
    let target = d.imul(ac, bd);
    let step3 = d.const_app(p.mul_assoc, &[a, c, bd]); // Eq target a_cbd
    let step3_rev = d.isymm(target, a_cbd, step3); // Eq a_cbd target

    let (_, proof) = d.ichain(
        start,
        &[(a_bcd, step1), (a_cbd, congr2), (target, step3_rev)],
    );
    proof
}

// ---------------------------------------------------------------------------
// `Nat`-level dvd machinery, typed for an `IntDev` context. Every method used
// (`dvd_predicate`, `mul`, `eq`, `chain`, `symm`, `congr`, `lam_fv`, `apply`,
// `fresh_fvar`, `nat_ty`, `level_one`, `prelude`, `refl`, `dvd`, `gcd`,
// `nat_rewrite`) is a `NatOps` default method (or an `IntDev` inherent one of
// the same generic shape), hardcoded to `Nat` internally, and `IntDev`
// implements `NatOps` -- so `nat_dvd_elim`/`nat_dvd_intro`/
// `dvd_cancel_left_of_ne_zero` are byte-for-byte
// `nat_prelude/dvd_mul_split.rs`'s `dvd_elim`/`dvd_intro`/
// `dvd_cancel_left_of_pos`, only the parameter type changed from `NatDev` to
// `IntDev`.
// ---------------------------------------------------------------------------

fn nat_dvd_elim(
    d: &mut IntDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

fn nat_dvd_intro(
    d: &mut IntDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, proof])
}

/// Given `k_pos : Le 1 k` and `dvd_hyp : dvd (mul k a) (mul k b)`, build a
/// proof of `dvd a b`.
fn dvd_cancel_left_of_ne_zero(
    d: &mut IntDev<'_>,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    dvd_hyp: ExprId,
) -> ExprId {
    let p = d.prelude();
    let ka = d.mul(k, a);
    let kb = d.mul(k, b);
    let goal = d.dvd(a, b);
    nat_dvd_elim(d, ka, kb, goal, dvd_hyp, &|d, q, eq_proof| {
        // eq_proof : Eq kb (mul ka q)
        let ka_q = d.mul(ka, q);
        let aq = d.mul(a, q);
        let k_aq = d.mul(k, aq);
        let assoc = d.lemma(p.mul_assoc, &[k, a, q]); // Eq ka_q k_aq
        let (_, kb_eq_k_aq) = d.chain(kb, &[(ka_q, eq_proof), (k_aq, assoc)]);
        let cancelled = d.lemma(p.mul_left_cancel_of_pos, &[k, b, aq, k_pos, kb_eq_k_aq]); // Eq b aq
        nat_dvd_intro(d, a, b, q, cancelled)
    })
}

// ---------------------------------------------------------------------------
// `∃ c1 c2, And (dvd c1 a) (And (dvd c2 b) (Eq Int (mul c1 c2) c))` -- the
// type, its introduction, and its elimination. `Int`-quantified counterpart
// of `nat_prelude/dvd_mul_split.rs`'s `split_exists_ty`/`_intro`/`_elim`.
// ---------------------------------------------------------------------------

fn split_body_ty(
    d: &mut IntDev<'_>,
    c1: ExprId,
    c2: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let logic = d.int().logic;
    let dvd_c1_a = idvd(d, c1, a);
    let dvd_c2_b = idvd(d, c2, b);
    let c1c2 = d.imul(c1, c2);
    let eq_c1c2_c = d.ieq(c1c2, c);
    let inner = d.const_app(logic.and, &[dvd_c2_b, eq_c1c2_c]);
    d.const_app(logic.and, &[dvd_c1_a, inner])
}

pub(super) fn split_exists_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let exists_name = d.int().logic.exists_;

    let c1_fv = d.fresh_fvar();
    let c1 = d.kernel().fvar(c1_fv);
    let inner_predicate = {
        let c2_fv = d.fresh_fvar();
        let c2 = d.kernel().fvar(c2_fv);
        let body = split_body_ty(d, c1, c2, a, b, c);
        d.lam_fv(c2_fv, int_ty, body)
    };
    let exists = d.kernel().const_(exists_name, vec![one]);
    let inner_exists = d.apply(exists, &[int_ty, inner_predicate]);
    let outer_predicate = d.lam_fv(c1_fv, int_ty, inner_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[int_ty, outer_predicate])
}

#[allow(clippy::too_many_arguments)]
pub(super) fn split_exists_intro(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    c1: ExprId,
    c2: ExprId,
    body_proof: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let exists_name = d.int().logic.exists_;

    let c2_predicate = {
        let c2_fv = d.fresh_fvar();
        let c2_var = d.kernel().fvar(c2_fv);
        let body = split_body_ty(d, c1, c2_var, a, b, c);
        d.lam_fv(c2_fv, int_ty, body)
    };
    let intro = d.kernel().const_(intro_name, vec![one]);
    let c2_exists_proof = d.apply(intro, &[int_ty, c2_predicate, c2, body_proof]);

    let c1_predicate = {
        let c1_fv = d.fresh_fvar();
        let c1_var = d.kernel().fvar(c1_fv);
        let c1_body = {
            let c2_fv2 = d.fresh_fvar();
            let c2_var2 = d.kernel().fvar(c2_fv2);
            let body = split_body_ty(d, c1_var, c2_var2, a, b, c);
            let c2_predicate2 = d.lam_fv(c2_fv2, int_ty, body);
            let exists = d.kernel().const_(exists_name, vec![one]);
            d.apply(exists, &[int_ty, c2_predicate2])
        };
        d.lam_fv(c1_fv, int_ty, c1_body)
    };
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[int_ty, c1_predicate, c1, c2_exists_proof])
}

#[allow(clippy::too_many_arguments)]
fn split_exists_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    goal: ExprId,
    witness: ExprId,
    continuation: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.int().logic.exists_;
    let exists_rec_name = d.int().logic.exists_rec;

    let outer_predicate = {
        let c1_fv = d.fresh_fvar();
        let c1_var = d.kernel().fvar(c1_fv);
        let inner_predicate = {
            let c2_fv = d.fresh_fvar();
            let c2_var = d.kernel().fvar(c2_fv);
            let body = split_body_ty(d, c1_var, c2_var, a, b, c);
            d.lam_fv(c2_fv, int_ty, body)
        };
        let exists_c = d.kernel().const_(exists_name, vec![one]);
        let inner_exists = d.apply(exists_c, &[int_ty, inner_predicate]);
        d.lam_fv(c1_fv, int_ty, inner_exists)
    };
    let outer_ty = {
        let exists_c = d.kernel().const_(exists_name, vec![one]);
        d.apply(exists_c, &[int_ty, outer_predicate])
    };
    let outer_motive = d.kernel().lam(anon, outer_ty, goal, BinderInfo::Default);

    let outer_minor = {
        let c1_fv = d.fresh_fvar();
        let c1_var = d.kernel().fvar(c1_fv);

        let inner_predicate = {
            let c2_fv = d.fresh_fvar();
            let c2_var = d.kernel().fvar(c2_fv);
            let body = split_body_ty(d, c1_var, c2_var, a, b, c);
            d.lam_fv(c2_fv, int_ty, body)
        };
        let inner_ty = {
            let exists_c = d.kernel().const_(exists_name, vec![one]);
            d.apply(exists_c, &[int_ty, inner_predicate])
        };
        let inner_motive = d.kernel().lam(anon, inner_ty, goal, BinderInfo::Default);
        let inner_minor = {
            let c2_fv = d.fresh_fvar();
            let c2_var = d.kernel().fvar(c2_fv);
            let body_ty = split_body_ty(d, c1_var, c2_var, a, b, c);
            let body_fv = d.fresh_fvar();
            let body_var = d.kernel().fvar(body_fv);
            let result = continuation(d, c1_var, c2_var, body_var);
            let with_body = d.lam_fv(body_fv, body_ty, result);
            d.lam_fv(c2_fv, int_ty, with_body)
        };
        let inner_pf_fv = d.fresh_fvar();
        let inner_pf_var = d.kernel().fvar(inner_pf_fv);
        let inner_rec = d.kernel().const_(exists_rec_name, vec![one]);
        let inner_result = d.apply(
            inner_rec,
            &[
                int_ty,
                inner_predicate,
                inner_motive,
                inner_minor,
                inner_pf_var,
            ],
        );
        let with_inner = d.lam_fv(inner_pf_fv, inner_ty, inner_result);
        d.lam_fv(c1_fv, int_ty, with_inner)
    };
    let outer_rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(
        outer_rec,
        &[int_ty, outer_predicate, outer_motive, outer_minor, witness],
    )
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

/// `Int.dvd_mul_split : ∀ c a b, Iff (dvd c (mul a b)) (∃ c1 c2, And (dvd c1
/// a) (And (dvd c2 b) (Eq Int (mul c1 c2) c)))`. See the module doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_dvd_mul_split(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let logic = p.logic;

    d.int_theorem(p.dvd_mul_split, 3, &|d, values| {
        let (c, a, b) = (values[0], values[1], values[2]);
        let ab = d.imul(a, b);
        let dvd_c_ab = idvd(d, c, ab);
        let exists_ty = split_exists_ty(d, a, b, c);
        let stmt = d.const_app(logic.iff, &[dvd_c_ab, exists_ty]);

        // ---- mpr: the exists implies dvd c (a*b), uniformly, no case split.
        let mpr = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = split_exists_elim(d, a, b, c, dvd_c_ab, w, &|d, c1, c2, body_proof| {
                let dvd_c2_b = idvd(d, c2, b);
                let c1c2 = d.imul(c1, c2);
                let eq_c1c2_c = d.ieq(c1c2, c);
                let dvd_c1_a = idvd(d, c1, a);
                let inner_ty = d.const_app(logic.and, &[dvd_c2_b, eq_c1c2_c]);
                let dvd_c1_a_proof = d.and_left(dvd_c1_a, inner_ty, body_proof);
                let inner_proof = d.and_right(dvd_c1_a, inner_ty, body_proof);
                let dvd_c2_b_proof = d.and_left(dvd_c2_b, eq_c1c2_c, inner_proof);
                let eq_c1c2_c_proof = d.and_right(dvd_c2_b, eq_c1c2_c, inner_proof);

                idvd_elim(d, c1, a, dvd_c_ab, dvd_c1_a_proof, &|d, p1, eq_a_c1p1| {
                    idvd_elim(d, c2, b, dvd_c_ab, dvd_c2_b_proof, &|d, p2, eq_b_c2p2| {
                        let c1p1 = d.imul(c1, p1);
                        let c2p2 = d.imul(c2, p2);
                        let congr_left = d.icongr(a, c1p1, eq_a_c1p1, &|d, t| d.imul(t, b));
                        let ab2 = d.imul(c1p1, b);
                        let congr_right = d.icongr(b, c2p2, eq_b_c2p2, &|d, t| d.imul(c1p1, t));
                        let ab3 = d.imul(c1p1, c2p2);
                        let regroup = imul_mul_mul_comm(d, c1, p1, c2, p2);
                        let c1c2_val = d.imul(c1, c2);
                        let p1p2 = d.imul(p1, p2);
                        let ab4 = d.imul(c1c2_val, p1p2);
                        let congr_c =
                            d.icongr(c1c2_val, c, eq_c1c2_c_proof, &|d, t| d.imul(t, p1p2));
                        let c_p1p2 = d.imul(c, p1p2);
                        let (_, eq_ab_c_p1p2) = d.ichain(
                            ab,
                            &[
                                (ab2, congr_left),
                                (ab3, congr_right),
                                (ab4, regroup),
                                (c_p1p2, congr_c),
                            ],
                        );
                        idvd_intro(d, c, ab, p1p2, eq_ab_c_p1p2)
                    })
                })
            });
            d.lam_fv(w_fv, exists_ty, body)
        };

        // ---- mp: dvd c (a*b) implies the exists. Case split on c = 0 ∨ c ≠ 0.
        let izero = d.izero();
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // dvd c ab
            let dvd_c_ab_ty = idvd(d, c, ab);

            let em_c = d.lemma(p.eq_em, &[c, izero]);
            let c_eq0_ty = d.ieq(c, izero);
            let c_ne0_ty = d.not(c_eq0_ty);
            let target = split_exists_ty(d, a, b, c);

            let result = d.or_elim(
                c_eq0_ty,
                c_ne0_ty,
                target,
                em_c,
                &|d, hc| {
                    // hc : Eq Int c izero
                    let dvd0_ab = d.int_eq_rewrite(c, izero, hc, h, &|d, y| idvd(d, y, ab));
                    let ab_eq_zero = zero_dvd_elim(d, ab, dvd0_ab);
                    let disj = d.lemma(p.mul_eq_zero, &[a, b, ab_eq_zero]); // Or (a=0) (b=0)
                    let a_eq0 = d.ieq(a, izero);
                    let b_eq0 = d.ieq(b, izero);
                    let inner_target = split_exists_ty(d, a, b, c);

                    d.or_elim(
                        a_eq0,
                        b_eq0,
                        inner_target,
                        disj,
                        &|d, ha| {
                            // ha : Eq Int a izero. witnesses (izero, b).
                            let dvd_izero_a = {
                                let refl_izero = d.lemma(p.dvd_refl, &[izero]);
                                let ha_symm = d.isymm(a, izero, ha);
                                d.int_eq_rewrite(izero, a, ha_symm, refl_izero, &|d, y| {
                                    idvd(d, izero, y)
                                })
                            };
                            let dvd_b_b = d.lemma(p.dvd_refl, &[b]);
                            let mul_izero_b = d.imul(izero, b);
                            let eq_mul_c = {
                                let b_izero = d.imul(b, izero);
                                let comm = d.const_app(p.mul_comm, &[izero, b]);
                                let mz = d.const_app(p.mul_zero, &[b]);
                                let hc_symm = d.isymm(c, izero, hc);
                                let (_, chained) =
                                    d.ichain(mul_izero_b, &[(b_izero, comm), (izero, mz)]);
                                d.itrans(mul_izero_b, izero, c, chained, hc_symm)
                            };
                            let dvd_b_b_ty = idvd(d, b, b);
                            let eq_mul_c_ty = d.ieq(mul_izero_b, c);
                            let dvd_izero_a_ty = idvd(d, izero, a);
                            let inner_ty = d.const_app(logic.and, &[dvd_b_b_ty, eq_mul_c_ty]);
                            let inner_and = d.const_app(
                                logic.and_intro,
                                &[dvd_b_b_ty, eq_mul_c_ty, dvd_b_b, eq_mul_c],
                            );
                            let full_and = d.const_app(
                                logic.and_intro,
                                &[dvd_izero_a_ty, inner_ty, dvd_izero_a, inner_and],
                            );
                            split_exists_intro(d, a, b, c, izero, b, full_and)
                        },
                        &|d, hb| {
                            // hb : Eq Int b izero. witnesses (a, izero).
                            let dvd_a_a = d.lemma(p.dvd_refl, &[a]);
                            let dvd_izero_b = {
                                let refl_izero = d.lemma(p.dvd_refl, &[izero]);
                                let hb_symm = d.isymm(b, izero, hb);
                                d.int_eq_rewrite(izero, b, hb_symm, refl_izero, &|d, y| {
                                    idvd(d, izero, y)
                                })
                            };
                            let mul_a_izero = d.imul(a, izero);
                            let eq_mul_c = {
                                let mz = d.const_app(p.mul_zero, &[a]);
                                let hc_symm = d.isymm(c, izero, hc);
                                d.itrans(mul_a_izero, izero, c, mz, hc_symm)
                            };
                            let dvd_izero_b_ty = idvd(d, izero, b);
                            let eq_mul_c_ty = d.ieq(mul_a_izero, c);
                            let dvd_a_a_ty = idvd(d, a, a);
                            let inner_ty = d.const_app(logic.and, &[dvd_izero_b_ty, eq_mul_c_ty]);
                            let inner_and = d.const_app(
                                logic.and_intro,
                                &[dvd_izero_b_ty, eq_mul_c_ty, dvd_izero_b, eq_mul_c],
                            );
                            let full_and = d.const_app(
                                logic.and_intro,
                                &[dvd_a_a_ty, inner_ty, dvd_a_a, inner_and],
                            );
                            split_exists_intro(d, a, b, c, a, izero, full_and)
                        },
                    )
                },
                &|d, hc_ne| {
                    // hc_ne : Not (Eq Int c izero).
                    let nc = d.const_app(p.nat_abs, &[c]);
                    let na = d.const_app(p.nat_abs, &[a]);
                    let nb = d.const_app(p.nat_abs, &[b]);
                    let g1_nat = d.const_app(p.nat.gcd, &[nc, na]); // Nat.gcd nc na
                    let g1 = d.of_nat(g1_nat);

                    let h1 = d.lemma(p.gcd_dvd_right, &[c, a]); // dvd (ofNat (Int.gcd c a)) a, def_eq dvd g1 a
                    let dvd_g1_c = d.lemma(p.gcd_dvd_left, &[c, a]); // dvd g1 c (def_eq)

                    let inner_target = split_exists_ty(d, a, b, c);
                    idvd_elim(d, g1, c, inner_target, dvd_g1_c, &|d, w, eq_c_g1w| {
                        // eq_c_g1w : Eq Int c (mul g1 w)
                        let gw = d.imul(g1, w);
                        let eq_gw_c = d.isymm(c, gw, eq_c_g1w); // Eq Int (mul g1 w) c

                        // --- real content: dvd w b ---
                        let bridge0 = d.lemma(p.nat_abs_dvd_nat_abs_of_dvd, &[c, ab, h]);
                        // bridge0 : Nat.dvd nc (natAbs ab)
                        let nat_abs_ab = d.const_app(p.nat_abs, &[ab]);
                        let mul_na_nb = d.mul(na, nb);
                        let step_b = d.lemma(p.nat_abs_mul, &[a, b]); // Eq Nat (natAbs ab) (mul na nb)
                        let big_h =
                            d.nat_rewrite(nat_abs_ab, mul_na_nb, step_b, bridge0, &|d, y| {
                                d.dvd(nc, y)
                            });
                        // big_h : Nat.dvd nc (mul na nb)

                        let dvd_nc_ncnb = d.lemma(p.nat.dvd_mul, &[nc, nb]); // Nat.dvd nc (mul nc nb)
                        let nc_nb = d.mul(nc, nb);
                        let h3 =
                            d.lemma(p.nat.dvd_gcd, &[nc, nc_nb, mul_na_nb, dvd_nc_ncnb, big_h]);
                        // h3 : Nat.dvd nc (Nat.gcd nc_nb mul_na_nb)

                        let gmr = d.lemma(p.nat.gcd_mul_right, &[nc, na, nb]);
                        // gmr : Eq Nat (Nat.gcd nc_nb mul_na_nb) (mul (Nat.gcd nc na) nb)
                        //     = Eq Nat (Nat.gcd nc_nb mul_na_nb) (mul g1_nat nb)   [g1_nat built identically]
                        let gcd_expr = d.gcd(nc_nb, mul_na_nb);
                        let g1_nb = d.mul(g1_nat, nb);
                        let h4 = d.nat_rewrite(gcd_expr, g1_nb, gmr, h3, &|d, y| d.dvd(nc, y));
                        // h4 : Nat.dvd nc (mul g1_nat nb)

                        // KEQ : Eq Nat nc (mul g1_nat (natAbs w))
                        let nat_abs_w = d.const_app(p.nat_abs, &[w]);
                        let refl_nc = d.refl(nc);
                        let step1 = d.int_eq_rewrite(c, gw, eq_c_g1w, refl_nc, &|d, y| {
                            let ny = d.const_app(p.nat_abs, &[y]);
                            d.eq(nc, ny)
                        });
                        // step1 : Eq Nat nc (natAbs gw)
                        let nat_abs_gw = d.const_app(p.nat_abs, &[gw]);
                        let step2 = d.lemma(p.nat_abs_mul, &[g1, w]); // Eq Nat (natAbs gw) (mul (natAbs g1) nat_abs_w)
                        let g1_natabsw = d.mul(g1_nat, nat_abs_w);
                        let (_, keq) = d.chain(nc, &[(nat_abs_gw, step1), (g1_natabsw, step2)]);
                        // keq : Eq Nat nc (mul g1_nat nat_abs_w)  (def_eq bridges natAbs g1 / g1_nat)

                        let dvd_hyp =
                            d.nat_rewrite(nc, g1_natabsw, keq, h4, &|d, cand| d.dvd(cand, g1_nb));
                        // dvd_hyp : Nat.dvd (mul g1_nat nat_abs_w) (mul g1_nat nb)

                        // g1_nat ≠ 0, from c ≠ 0.
                        let zero_nat = d.zero();
                        let g1_eq_zero_ty = d.eq(g1_nat, zero_nat);
                        let g1_ne_zero = {
                            let h0_fv = d.fresh_fvar();
                            let h0 = d.kernel().fvar(h0_fv);
                            let nc_eq_zero =
                                d.lemma(p.nat.eq_zero_of_gcd_eq_zero_left, &[nc, na, h0]);
                            let c_eq_zero_fn = nat_abs_zero_implies_int_zero(d, c);
                            let c_is_zero = d.apply(c_eq_zero_fn, &[nc_eq_zero]);
                            let false_pf = d.apply(hc_ne, &[c_is_zero]);
                            d.lam_fv(h0_fv, g1_eq_zero_ty, false_pf)
                        };
                        let g1_pos = d.lemma(p.nat.zero_lt_of_ne_zero, &[g1_nat, g1_ne_zero]); // Lt 0 g1_nat

                        let dvd_w_b_nat =
                            dvd_cancel_left_of_ne_zero(d, g1_nat, nat_abs_w, nb, g1_pos, dvd_hyp);
                        // dvd_w_b_nat : Nat.dvd (natAbs w) (natAbs b)
                        let h2 = d.lemma(p.dvd_of_nat_abs_dvd, &[w, b, dvd_w_b_nat]); // dvd w b

                        // --- assemble ---
                        let dvd_c2_b_ty = idvd(d, w, b);
                        let eq_c1c2_c_ty = d.ieq(gw, c);
                        let dvd_c1_a_ty = idvd(d, g1, a);
                        let inner_ty = d.const_app(logic.and, &[dvd_c2_b_ty, eq_c1c2_c_ty]);
                        let inner_and =
                            d.const_app(logic.and_intro, &[dvd_c2_b_ty, eq_c1c2_c_ty, h2, eq_gw_c]);
                        let full_and =
                            d.const_app(logic.and_intro, &[dvd_c1_a_ty, inner_ty, h1, inner_and]);
                        split_exists_intro(d, a, b, c, g1, w, full_and)
                    })
                },
            );
            d.lam_fv(h_fv, dvd_c_ab_ty, result)
        };

        let proof = d.const_app(logic.iff_intro, &[dvd_c_ab, exists_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}
