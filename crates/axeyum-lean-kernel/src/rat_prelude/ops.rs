//! The proof-construction layer for the rational development.
//!
//! `Rat` is built over the *already constructed* `ℤ`, so the development runs
//! on [`IntDev`] — the same struct the integer scripts use — rather than on a
//! development of its own. The `Rat`-specific builders below are free functions
//! taking a `Copy` [`RatPrelude`] instead of methods, because `IntDev` carries
//! the `Int` names and has nowhere to put a second prelude. That keeps every
//! closure in this module `&mut IntDev<'_>`, so `Int` and `Rat` reasoning
//! interleave without a wrapper type in between.

use super::RatPrelude;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// --- carrier and field builders -------------------------------------------

/// The expression `Rat`.
pub(crate) fn rat_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().rat;
    d.kernel().const_(name, vec![])
}

/// `Rat.num q`.
pub(crate) fn num(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_num;
    d.const_app(f, &[q])
}

/// `Rat.den q`.
pub(crate) fn den(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_den;
    d.const_app(f, &[q])
}

/// `Int.ofNat (Rat.den q)` — the denominator, seen as an integer, which is the
/// only shape the cross-multiplication statements ever use it in.
pub(crate) fn den_z(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let raw = den(d, q);
    d.of_nat(raw)
}

/// `Rat.den_pos q : 1 ≤ Rat.den q`.
pub(crate) fn den_pos(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_den_pos;
    d.const_app(f, &[q])
}

/// `Rat.reduced q : gcd (natAbs (Rat.num q)) (Rat.den q) = 1`.
pub(crate) fn reduced(d: &mut IntDev<'_>, q: ExprId) -> ExprId {
    let f = d.int().rat_reduced;
    d.const_app(f, &[q])
}

/// `Rat.mk n den positive reduced`.
pub(crate) fn mk(
    d: &mut IntDev<'_>,
    n: ExprId,
    denominator: ExprId,
    positive: ExprId,
    reduced_proof: ExprId,
) -> ExprId {
    let f = d.int().rat_mk;
    d.const_app(f, &[n, denominator, positive, reduced_proof])
}

/// `Rat.normalize n den positive`.
pub(crate) fn normalize(
    d: &mut IntDev<'_>,
    n: ExprId,
    denominator: ExprId,
    positive: ExprId,
) -> ExprId {
    let f = d.int().rat_normalize;
    d.const_app(f, &[n, denominator, positive])
}

/// The type `1 ≤ den` — `Rat`'s positivity field.
pub(crate) fn positive_ty(d: &mut IntDev<'_>, denominator: ExprId) -> ExprId {
    let unit = d.num(1);
    NatOps::le(d, unit, denominator)
}

/// The type `gcd (natAbs n) den = 1` — `Rat`'s reducedness field.
pub(crate) fn reduced_ty(d: &mut IntDev<'_>, n: ExprId, denominator: ExprId) -> ExprId {
    let nat_abs = d.int().nat_abs;
    let magnitude = d.const_app(nat_abs, &[n]);
    let common = NatOps::gcd(d, magnitude, denominator);
    let unit = d.num(1);
    d.eq(common, unit)
}

/// `1 ≤ succ k`, the positivity every `succ`-shaped denominator carries for
/// free.
pub(crate) fn one_le_succ(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let p = d.int().nat;
    let zero = d.zero();
    let base = d.lemma(p.zero_le, &[k]);
    d.lemma(p.le_succ_succ, &[zero, k, base])
}

// --- operations ------------------------------------------------------------

/// `Rat.add a b`.
pub(crate) fn radd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().rat_add;
    d.const_app(f, &[a, b])
}

/// `Rat.mul a b`.
pub(crate) fn rmul(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().rat_mul;
    d.const_app(f, &[a, b])
}

/// `Rat.neg a`.
pub(crate) fn rneg(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let f = d.int().rat_neg;
    d.const_app(f, &[a])
}

/// `Rat.zero`.
pub(crate) fn rzero(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `Rat.one`.
pub(crate) fn rone(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// `Rat.le a b`.
pub(crate) fn rle(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.le, &[a, b])
}

/// `Rat.lt a b`.
pub(crate) fn rlt(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.lt, &[a, b])
}

// --- Eq at Rat -------------------------------------------------------------

/// `Eq.{1} Rat a b` — the carrier is `Sort 1`, like `Int`.
pub(crate) fn req(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.eq;
    let eq = d.kernel().const_(name, vec![one]);
    let carrier = rat_ty(d);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} Rat a`.
pub(crate) fn rrefl(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.eq_refl;
    let refl = d.kernel().const_(name, vec![one]);
    let carrier = rat_ty(d);
    d.apply(refl, &[carrier, a])
}

/// `Eq.rec.{0,1} Rat p motive refl_case q h`.
pub(crate) fn rtransport(
    d: &mut IntDev<'_>,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = d.kernel().level_zero();
    let one = d.level_one();
    let name = d.int().logic.eq_rec;
    let rec = d.kernel().const_(name, vec![zero, one]);
    let carrier = rat_ty(d);
    d.apply(rec, &[carrier, p, motive, refl_case, q, h])
}

/// `fun (x : Rat) (_ : Eq Rat a x) => body(x)`.
pub(crate) fn req_motive(
    d: &mut IntDev<'_>,
    a: ExprId,
    body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let concl = body(d, x);
    let hyp = req(d, a, x);
    let anon = d.anon_name();
    let inner = d.kernel().lam(anon, hyp, concl, BinderInfo::Default);
    let carrier = rat_ty(d);
    d.lam_fv(x_fv, carrier, inner)
}

/// `h : Eq Rat a b ⊢ Eq Rat b a`.
pub(crate) fn rsymm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let motive = req_motive(d, a, &|d, x| req(d, x, a));
    let refl_case = rrefl(d, a);
    rtransport(d, a, motive, refl_case, b, h)
}

/// `h1 : Eq Rat a b`, `h2 : Eq Rat b c ⊢ Eq Rat a c`.
pub(crate) fn rtrans(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let motive = req_motive(d, b, &|d, x| req(d, a, x));
    rtransport(d, b, motive, h1, c, h2)
}

/// Chain `Eq Rat start …` through `(next, step)` pairs.
pub(crate) fn rchain(
    d: &mut IntDev<'_>,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = rrefl(d, start);
    for &(next, step) in steps {
        proof = rtrans(d, start, current, next, proof, step);
        current = next;
    }
    (current, proof)
}

/// Congruence at `Rat`: `h : Eq Rat a b ⊢ Eq Rat (f a) (f b)`.
pub(crate) fn rcongr(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = req_motive(d, a, &|d, x| {
        let fx = f(d, x);
        req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    rtransport(d, a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b`, derive `Eq Rat (f a) (f b)`.
///
/// The `ℕ → ℚ` companion of
/// [`IntDev::nat_eq_to_int`](crate::int_prelude::ops::IntDev::nat_eq_to_int).
/// Every `Rat.natDivSucc` identity whose content lives in the *numerator* or
/// the *index* is a `ℕ` equation whose consequence is a `ℚ` one, and this is
/// the only way across.
pub(crate) fn nat_eq_to_rat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = NatOps::eq_motive(d, a, &|d, x| {
        let fx = f(d, x);
        req(d, fa, fx)
    });
    let refl_case = rrefl(d, fa);
    NatOps::transport(d, a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b` and a proof of `motive a`, derive `motive b`.
pub(crate) fn nat_rewrite_prop(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    proof: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let built = NatOps::eq_motive(d, a, motive);
    NatOps::transport(d, a, built, proof, b, h)
}

/// From `h : Eq Rat p q` and a proof of `motive p`, derive `motive q`.
pub(crate) fn rat_eq_rewrite(
    d: &mut IntDev<'_>,
    p: ExprId,
    q: ExprId,
    h: ExprId,
    proof: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let built = req_motive(d, p, motive);
    rtransport(d, p, built, proof, q, h)
}

/// From `h : Eq Int a b`, derive `Eq Nat (f a) (f b)` — the direction
/// `Int.natAbs` reasoning runs in, where the equation is between integers and
/// the conclusion is about naturals.
pub(crate) fn int_eq_to_nat(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.ieq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.itransport(a, motive, refl_case, b, h)
}

/// Case-analyse a **positive** natural: `1 ≤ n` rules the `zero` branch out, so
/// only the `succ` branch has to be supplied.
///
/// `target` is a function of the natural because the `Nat.rec` motive replaces
/// `n` throughout: `on_succ` receives `j` and must prove `target (succ j)`,
/// which is where `negOfNat (succ j) ≡ negSucc j` and `1 ≤ succ j` become
/// available definitionally. This is the combinator every "a positive natural
/// is a successor" step in the `Int` sign arguments runs through, so the
/// impossible branch is discharged in exactly one place.
pub(crate) fn pos_cases(
    d: &mut IntDev<'_>,
    n: ExprId,
    positive: ExprId,
    target: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    on_succ: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_level = d.kernel().level_zero();
    let nat_prelude = d.prelude();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hypothesis = positive_ty(d, x);
        let conclusion = target(d, x);
        let body = d.arrow(hypothesis, conclusion);
        d.lam_fv(x_fv, nat, body)
    };
    let zero_case = {
        let zero = d.zero();
        let hypothesis = positive_ty(d, zero);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let impossible = d.lemma(nat_prelude.not_succ_le_zero, &[zero, h]);
        let goal = target(d, zero);
        let body = d.absurd(goal, impossible);
        d.lam_fv(h_fv, hypothesis, body)
    };
    let succ_case = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_ty = {
            let hypothesis = positive_ty(d, j);
            let conclusion = target(d, j);
            d.arrow(hypothesis, conclusion)
        };
        let ih_fv = d.fresh_fvar();
        let successor = d.succ(j);
        let hypothesis = positive_ty(d, successor);
        let h_fv = d.fresh_fvar();
        let body = on_succ(d, j);
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_h);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let rec = d.kernel().const_(nat_prelude.rec, vec![zero_level]);
    let selected = d.apply(rec, &[motive, zero_case, succ_case, n]);
    d.apply(selected, &[positive])
}

// --- products, as multisets of factors --------------------------------------

/// `a0 * (a1 * (… * a_{n-1}))`, right-nested.
///
/// # Panics
///
/// Panics on an empty factor list — a product with no factors would need a unit
/// and nothing here ever wants one.
pub(crate) fn iprod(d: &mut IntDev<'_>, atoms: &[ExprId]) -> ExprId {
    let (&last, front) = atoms.split_last().expect("a product needs a factor");
    let mut acc = last;
    for &atom in front.iter().rev() {
        acc = d.imul(atom, acc);
    }
    acc
}

/// `Eq Int (iprod xs) (xs[i] * iprod rest)`, where `rest` is `xs` with position
/// `i` removed. Requires `xs.len() >= 2`.
fn iprod_pull(d: &mut IntDev<'_>, xs: &[ExprId], i: usize) -> ExprId {
    let int = d.int();
    if i == 0 {
        // `iprod xs` IS `xs[0] * iprod xs[1..]` — the same term, not merely
        // equal to it.
        let whole = iprod(d, xs);
        return d.irefl(whole);
    }
    let head = xs[0];
    let tail = &xs[1..];
    let chosen = xs[i];
    if tail.len() == 1 {
        // `head * chosen = chosen * head`, and `iprod [head]` is `head`.
        return d.lemma(int.mul_comm, &[head, chosen]);
    }
    let mut tail_rest: Vec<ExprId> = tail.to_vec();
    tail_rest.remove(i - 1);
    let inner = iprod_pull(d, tail, i - 1);
    let tail_product = iprod(d, tail);
    let rest_product = iprod(d, &tail_rest);
    let pulled = d.imul(chosen, rest_product);
    // head * iprod tail = head * (chosen * iprod rest)
    let first = d.icongr(tail_product, pulled, inner, &|d, t| d.imul(head, t));
    let nested = d.imul(head, pulled);
    // = (head * chosen) * iprod rest
    let flat_head = d.imul(head, chosen);
    let flat = d.imul(flat_head, rest_product);
    let assoc = d.lemma(int.mul_assoc, &[head, chosen, rest_product]);
    let second = d.isymm(flat, nested, assoc);
    // = (chosen * head) * iprod rest
    let commuted_head = d.imul(chosen, head);
    let commute = d.lemma(int.mul_comm, &[head, chosen]);
    let third = d.icongr(flat_head, commuted_head, commute, &|d, t| {
        d.imul(t, rest_product)
    });
    let commuted = d.imul(commuted_head, rest_product);
    // = chosen * (head * iprod rest), and `head * iprod rest` IS `iprod (head :: rest)`.
    let fourth = d.lemma(int.mul_assoc, &[chosen, head, rest_product]);
    let regrouped = {
        let inner_product = d.imul(head, rest_product);
        d.imul(chosen, inner_product)
    };
    let start = d.imul(head, tail_product);
    let (_, chained) = d.ichain(
        start,
        &[
            (nested, first),
            (flat, second),
            (commuted, third),
            (regrouped, fourth),
        ],
    );
    chained
}

/// `Eq Int (iprod xs) (iprod ys)` when `ys` is a permutation of `xs`.
///
/// Multiplication is associative and commutative, so a product is really a
/// *multiset* of factors — but the kernel does not know that, and every
/// cross-multiplication identity in this module is one multiset rewritten as
/// another. Doing that by hand is where these proofs would otherwise go wrong,
/// so it is done once here: selection sort, with `mul_assoc`/`mul_comm` as the
/// only steps.
///
/// # Panics
///
/// Panics if `ys` is not a permutation of `xs` — that is a bug in the caller,
/// not a provable-or-not question, and the kernel would reject the term anyway.
pub(crate) fn iprod_perm(d: &mut IntDev<'_>, xs: &[ExprId], ys: &[ExprId]) -> ExprId {
    assert_eq!(xs.len(), ys.len(), "iprod_perm needs equal lengths");
    if xs.len() == 1 {
        assert_eq!(xs[0], ys[0], "iprod_perm was given a non-permutation");
        let single = xs[0];
        return d.irefl(single);
    }
    let index = xs
        .iter()
        .position(|&atom| atom == ys[0])
        .expect("iprod_perm was given a non-permutation");
    let mut rest: Vec<ExprId> = xs.to_vec();
    rest.remove(index);
    let pulled = iprod_pull(d, xs, index);
    let inner = iprod_perm(d, &rest, &ys[1..]);
    let rest_product = iprod(d, &rest);
    let tail_product = iprod(d, &ys[1..]);
    let chosen = ys[0];
    let middle = d.imul(chosen, rest_product);
    let step = d.icongr(rest_product, tail_product, inner, &|d, t| d.imul(chosen, t));
    let start = iprod(d, xs);
    let target = iprod(d, ys);
    let (_, chained) = d.ichain(start, &[(middle, pulled), (target, step)]);
    chained
}

/// From `h : Eq Int (x*y) (u*v)`, prove `iprod ([x,y] ++ rest) = iprod ([u,v] ++ rest)`.
///
/// The regroup-rewrite-regroup step every cross-multiplication argument runs:
/// `x*(y*R) = (x*y)*R = (u*v)*R = u*(v*R)`.
pub(crate) fn iprod_head_rewrite(
    d: &mut IntDev<'_>,
    x: ExprId,
    y: ExprId,
    rest: &[ExprId],
    u: ExprId,
    v: ExprId,
    h: ExprId,
) -> ExprId {
    let int = d.int();
    let tail = iprod(d, rest);
    let start = {
        let inner = d.imul(y, tail);
        d.imul(x, inner)
    };
    let flat_from = {
        let head = d.imul(x, y);
        d.imul(head, tail)
    };
    let flat_to = {
        let head = d.imul(u, v);
        d.imul(head, tail)
    };
    let target = {
        let inner = d.imul(v, tail);
        d.imul(u, inner)
    };
    let assoc_out = {
        let forward = d.lemma(int.mul_assoc, &[x, y, tail]);
        d.isymm(flat_from, start, forward)
    };
    let from_head = d.imul(x, y);
    let to_head = d.imul(u, v);
    let rewritten = d.icongr(from_head, to_head, h, &|d, t| d.imul(t, tail));
    let assoc_in = d.lemma(int.mul_assoc, &[u, v, tail]);
    let (_, chained) = d.ichain(
        start,
        &[
            (flat_from, assoc_out),
            (flat_to, rewritten),
            (target, assoc_in),
        ],
    );
    chained
}

/// `Eq Int ((a*b)*c) ((x*y)*z)` when `[x,y,z]` is a permutation of `[a,b,c]`.
///
/// The order arguments all scale a cross-product by a third denominator and
/// then need the factors in a different order; this is that step.
pub(crate) fn iregroup3(d: &mut IntDev<'_>, from: [ExprId; 3], to: [ExprId; 3]) -> ExprId {
    let int = d.int();
    let start = {
        let head = d.imul(from[0], from[1]);
        d.imul(head, from[2])
    };
    let flat_from = iprod(d, &from);
    let opened = d.lemma(int.mul_assoc, &[from[0], from[1], from[2]]);
    let flat_to = iprod(d, &to);
    let permuted = iprod_perm(d, &from, &to);
    let target = {
        let head = d.imul(to[0], to[1]);
        d.imul(head, to[2])
    };
    let closed = {
        let forward = d.lemma(int.mul_assoc, &[to[0], to[1], to[2]]);
        d.isymm(target, flat_to, forward)
    };
    let (_, chained) = d.ichain(
        start,
        &[(flat_from, opened), (flat_to, permuted), (target, closed)],
    );
    chained
}

/// `Eq Int ((iprod xs) * (iprod ys)) (iprod (xs ++ ys))`.
pub(crate) fn iprod_append(d: &mut IntDev<'_>, xs: &[ExprId], ys: &[ExprId]) -> ExprId {
    let int = d.int();
    if xs.len() == 1 {
        // `x * iprod ys` IS `iprod ([x] ++ ys)`.
        let head = xs[0];
        let tail = iprod(d, ys);
        let joined = d.imul(head, tail);
        return d.irefl(joined);
    }
    let head = xs[0];
    let rest = &xs[1..];
    let rest_product = iprod(d, rest);
    let ys_product = iprod(d, ys);
    let xs_product = iprod(d, xs);
    let start = d.imul(xs_product, ys_product);
    let opened = d.lemma(int.mul_assoc, &[head, rest_product, ys_product]);
    let inner_start = d.imul(rest_product, ys_product);
    let nested = d.imul(head, inner_start);
    let joined_rest: Vec<ExprId> = rest.iter().chain(ys.iter()).copied().collect();
    let rest_joined = iprod(d, &joined_rest);
    let inner = iprod_append(d, rest, ys);
    let step = d.icongr(inner_start, rest_joined, inner, &|d, t| d.imul(head, t));
    let target = d.imul(head, rest_joined);
    let (_, chained) = d.ichain(start, &[(nested, opened), (target, step)]);
    chained
}

/// From `h : iprod from = iprod to`, prove `iprod (from ++ rest) = iprod (to ++ rest)`.
pub(crate) fn iprod_prefix_rewrite(
    d: &mut IntDev<'_>,
    from: &[ExprId],
    to: &[ExprId],
    rest: &[ExprId],
    h: ExprId,
) -> ExprId {
    if rest.is_empty() {
        return h;
    }
    let from_product = iprod(d, from);
    let to_product = iprod(d, to);
    let rest_product = iprod(d, rest);
    let from_all: Vec<ExprId> = from.iter().chain(rest.iter()).copied().collect();
    let to_all: Vec<ExprId> = to.iter().chain(rest.iter()).copied().collect();
    let start = iprod(d, &from_all);
    let split_from = d.imul(from_product, rest_product);
    let append_from = iprod_append(d, from, rest);
    let back = d.isymm(split_from, start, append_from);
    let split_to = d.imul(to_product, rest_product);
    let step = d.icongr(from_product, to_product, h, &|d, t| d.imul(t, rest_product));
    let target = iprod(d, &to_all);
    let append_to = iprod_append(d, to, rest);
    let (_, chained) = d.ichain(
        start,
        &[(split_from, back), (split_to, step), (target, append_to)],
    );
    chained
}

/// A product being carried, as a factor **multiset**, with a running proof that
/// the expression it started from equals the right-nested product of those
/// factors.
///
/// Cross-multiplication arguments are all the same shape — scale by a
/// denominator, reorder the factors, substitute a cross lemma for some of them,
/// reorder again — and doing that inline is where these proofs go wrong. Here
/// the reordering is checked (`iprod_perm` panics on a non-permutation) and the
/// proof is assembled once.
pub(crate) struct Flat {
    atoms: Vec<ExprId>,
    start: ExprId,
    proof: ExprId,
}

impl Flat {
    /// Start from `left * right`, where `left` is definitionally `iprod ls` and
    /// `right` definitionally `iprod rs`.
    ///
    /// The definitional slack is what makes this usable: `ofNat (a*b)` and
    /// `ofNat a * ofNat b` are the same term to the kernel, so a denominator
    /// product can be split into its factors for free — but only when it is
    /// nested to the right, which is why every scaling factor below is written
    /// `x * (y * z)`.
    pub(crate) fn begin_product(
        d: &mut IntDev<'_>,
        left: ExprId,
        ls: &[ExprId],
        right: ExprId,
        rs: &[ExprId],
    ) -> Self {
        let start = d.imul(left, right);
        let atoms: Vec<ExprId> = ls.iter().chain(rs.iter()).copied().collect();
        let proof = iprod_append(d, ls, rs);
        Self {
            atoms,
            start,
            proof,
        }
    }

    /// Multiply through by `factor`, which must be definitionally
    /// `iprod factor_atoms`.
    pub(crate) fn scale(&mut self, d: &mut IntDev<'_>, factor: ExprId, factor_atoms: &[ExprId]) {
        let current = iprod(d, &self.atoms);
        let scaled_start = d.imul(self.start, factor);
        let scaled_current = d.imul(current, factor);
        let lifted = d.icongr(self.start, current, self.proof, &|d, t| d.imul(t, factor));
        let joined: Vec<ExprId> = self
            .atoms
            .iter()
            .chain(factor_atoms.iter())
            .copied()
            .collect();
        let target = iprod(d, &joined);
        let append = iprod_append(d, &self.atoms, factor_atoms);
        let (_, chained) = d.ichain(scaled_start, &[(scaled_current, lifted), (target, append)]);
        self.start = scaled_start;
        self.atoms = joined;
        self.proof = chained;
    }

    /// Reorder the factors.
    pub(crate) fn perm(&mut self, d: &mut IntDev<'_>, to: &[ExprId]) {
        let current = iprod(d, &self.atoms);
        let next = iprod(d, to);
        let step = iprod_perm(d, &self.atoms, to);
        self.proof = d.itrans(self.start, current, next, self.proof, step);
        self.atoms = to.to_vec();
    }

    /// Replace the first `n` factors, given `h : iprod (first n) = iprod to`.
    pub(crate) fn rewrite_prefix(
        &mut self,
        d: &mut IntDev<'_>,
        n: usize,
        to: &[ExprId],
        h: ExprId,
    ) {
        let rest: Vec<ExprId> = self.atoms[n..].to_vec();
        let prefix: Vec<ExprId> = self.atoms[..n].to_vec();
        let current = iprod(d, &self.atoms);
        let step = iprod_prefix_rewrite(d, &prefix, to, &rest, h);
        let joined: Vec<ExprId> = to.iter().chain(rest.iter()).copied().collect();
        let next = iprod(d, &joined);
        self.proof = d.itrans(self.start, current, next, self.proof, step);
        self.atoms = joined;
    }

    /// The expression this started from, the normal form it reached, and the
    /// proof that they are equal.
    pub(crate) fn finish(self, d: &mut IntDev<'_>) -> (ExprId, ExprId, ExprId) {
        let current = iprod(d, &self.atoms);
        (self.start, current, self.proof)
    }
}

// --- declaration plumbing --------------------------------------------------

/// Declare `theorem name : ∀ (x_0 … x_{arity-1} : Rat), stmt := fun … => proof`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel **refused**
/// the proof.
pub(crate) fn rat_theorem(
    d: &mut IntDev<'_>,
    name: NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (stmt, proof) = build(d, &vars);
    let mut ty = stmt;
    let mut value = proof;
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, carrier, ty);
        value = d.lam_fv(fv, carrier, value);
    }
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// Eliminate a balanced Bézout certificate `∃ mp mn np nn, g + m·mn + n·nn = m·mp + n·np`
/// into `target`.
///
/// A local copy of the integer-free eliminator `nat_prelude::bezout` keeps
/// private: the four nested predicates are rebuilt from
/// [`NatOps::bezout_equation`], which is public, so the shape cannot drift from
/// the introduction form even though the code is not shared.
pub(crate) fn bezout_elim(
    d: &mut IntDev<'_>,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    target: ExprId,
    certificate: ExprId,
    minor: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.prelude().logic.exists_;
    let rec_name = d.prelude().logic.exists_rec;

    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);

    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let nn_predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let nn_exists = d.apply(exists, &[nat, nn_predicate]);
    let np_predicate = d.lam_fv(np_fv, nat, nn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let np_exists = d.apply(exists, &[nat, np_predicate]);
    let mn_predicate = d.lam_fv(mn_fv, nat, np_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mn_exists = d.apply(exists, &[nat, mn_predicate]);
    let mp_predicate = d.lam_fv(mp_fv, nat, mn_exists);
    let exists = d.kernel().const_(exists_name, vec![one]);
    let mp_exists = d.apply(exists, &[nat, mp_predicate]);

    let equation_fv = d.fresh_fvar();
    let equation_proof = d.kernel().fvar(equation_fv);
    let core = minor(d, mp, mn, np, nn, equation_proof);
    let nn_minor = {
        let with_equation = d.lam_fv(equation_fv, equation, core);
        d.lam_fv(nn_fv, nat, with_equation)
    };
    let np_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, nn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, nn_predicate, motive, nn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, nn_exists, eliminated);
        d.lam_fv(np_fv, nat, with_witness)
    };
    let mn_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, np_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, np_predicate, motive, np_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, np_exists, eliminated);
        d.lam_fv(mn_fv, nat, with_witness)
    };
    let mp_minor = {
        let witness_fv = d.fresh_fvar();
        let witness = d.kernel().fvar(witness_fv);
        let motive = d.kernel().lam(anon, mn_exists, target, BinderInfo::Default);
        let rec = d.kernel().const_(rec_name, vec![one]);
        let eliminated = d.apply(rec, &[nat, mn_predicate, motive, mn_minor, witness]);
        let with_witness = d.lam_fv(witness_fv, mn_exists, eliminated);
        d.lam_fv(mp_fv, nat, with_witness)
    };
    let motive = d.kernel().lam(anon, mp_exists, target, BinderInfo::Default);
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[nat, mp_predicate, motive, mp_minor, certificate])
}
