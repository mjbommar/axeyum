//! The **borrow** of `Int.subNatNat`, and everything that was blocked on it.
//!
//! `Int.subNatNat m n` is `Nat.rec … (Nat.sub n m)`: it returns
//! `Int.ofNat (m-n)` when the scrutinee `n-m` is `0` and `Int.negSucc k` when it
//! is `succ k`. On *variables* neither `Nat.sub` reduces, so the term is stuck
//! and every mixed-sign branch of `Int.add` inherits the stall. That single fact
//! is why `add_assoc`, `left_distrib`, `add_le_add` and `add_lt_add_of_le_of_lt`
//! were all still asserted: each mixes `Int.add` with a second operation, and
//! the interesting branches need to know *which constructor* the borrow lands
//! in.
//!
//! The development below answers that in three steps.
//!
//! 1. **Shift.** `subNatNat (m+k) (n+k) = subNatNat m n` — proved by induction
//!    on `k` from the one-step `subNatNat (m+1) (n+1) = subNatNat m n`, which is
//!    two rewrites by `Nat.succ_sub_succ`, one for the value and one for the
//!    scrutinee. Shifting is the only thing `subNatNat` respects definitionally
//!    once its arguments are opaque.
//! 2. **Two anchors.** `subNatNat m 0 = ofNat m` and `subNatNat 0 k = negOfNat k`.
//!    The second is two `Eq.refl`s; the first needs `Nat.sub 0 m = 0`, since the
//!    scrutinee `0-m` is stuck on `m` even though the answer is not.
//!    Shifting an anchor gives the two **characterisations**:
//!    `subNatNat (n+i) n = ofNat i` and `subNatNat m (m+k) = negOfNat k`.
//! 3. **Elimination.** `Nat.le_total` plus `Nat.le_dest` says every pair `(m,n)`
//!    is `(n+i, n)` or `(m, m+(j+1))`, so the two characterisations cover every
//!    case. [`IntPrelude::sub_nat_nat_elim`](super::IntPrelude::sub_nat_nat_elim)
//!    packages that as a case-analysis principle, and every lemma after it is
//!    two branches instead of an open-ended stall.
//!
//! Note `subNatNat m (m+k) = negOfNat k` rather than `= negSucc (k-1)`: stating
//! it with `negOfNat` keeps `k = 0` in range, which is exactly what the
//! multiplicative lemmas need (a scale of `0` collapses a negative factor).

use super::ops::{IntDev, exists_elim};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// --- small `Nat` steps the scripts spell out repeatedly ----------------------

/// `Nat.add_comm a b : Eq Nat (a+b) (b+a)`.
fn add_comm(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let name = d.int().nat.add_comm;
    d.const_app(name, &[a, b])
}

/// `Nat.add_assoc a b c : Eq Nat ((a+b)+c) (a+(b+c))`.
fn add_assoc(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let name = d.int().nat.add_assoc;
    d.const_app(name, &[a, b, c])
}

/// `Nat.succ_add a b : Eq Nat ((a+1)+b) ((a+b)+1)`.
fn succ_add(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let name = d.int().nat.succ_add;
    d.const_app(name, &[a, b])
}

/// `Nat.left_distrib a b c : Eq Nat (a*(b+c)) (a*b + a*c)`.
fn left_distrib(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let name = d.int().nat.left_distrib;
    d.const_app(name, &[a, b, c])
}

// --- the raw borrow ---------------------------------------------------------

/// `Nat.rec.{1} (fun _ => Int) (Int.ofNat value) (fun k _ => Int.negSucc k) scrutinee`
/// — `Int.subNatNat`'s body with its two `Nat.sub` occurrences left as holes.
///
/// `subNatNat m n` is definitionally `borrow (m-n) (n-m)`, so a rewrite of
/// either hole is a rewrite of the whole term. They must be rewritten
/// *separately*: the value sits under the `Nat.rec`'s zero-minor and the
/// scrutinee is its major premise, so no single one-hole context covers both.
fn borrow(d: &mut IntDev<'_>, value: ExprId, scrutinee: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
    let minor_zero = d.of_nat(value);
    let minor_succ = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ih_fv = d.fresh_fvar();
        let body = d.neg_succ(k);
        let inner = d.lam_fv(ih_fv, int_ty, body);
        d.lam_fv(k_fv, nat, inner)
    };
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[motive, minor_zero, minor_succ, scrutinee])
}

/// Declare the shift lemmas, the two anchors, the two characterisations, and
/// the elimination principle.
pub(super) fn declare_borrow_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // subNatNat_succ_succ : subNatNat (m+1) (n+1) = subNatNat m n.
    //
    // `Nat.succ_sub_succ` rewrites the value and then the scrutinee; after both
    // the term is syntactically `subNatNat m n`'s body.
    d.theorem(p.sub_nat_nat_succ_succ, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let (sm, sn) = {
            let sm = d.succ(m);
            let sn = d.succ(n);
            (sm, sn)
        };
        let big_value = d.sub(sm, sn);
        let big_scrutinee = d.sub(sn, sm);
        let small_value = d.sub(m, n);
        let small_scrutinee = d.sub(n, m);
        let stmt = {
            let left = d.sub_nat_nat(sm, sn);
            let right = d.sub_nat_nat(m, n);
            d.ieq(left, right)
        };
        let succ_sub_succ = d.int().nat.succ_sub_succ;
        let value_step = {
            let h = d.const_app(succ_sub_succ, &[m, n]);
            d.nat_eq_to_int(big_value, small_value, h, &|d, t| {
                borrow(d, t, big_scrutinee)
            })
        };
        let scrutinee_step = {
            let h = d.const_app(succ_sub_succ, &[n, m]);
            d.nat_eq_to_int(big_scrutinee, small_scrutinee, h, &|d, t| {
                borrow(d, small_value, t)
            })
        };
        let start = d.sub_nat_nat(sm, sn);
        let middle = borrow(d, small_value, big_scrutinee);
        let end = d.sub_nat_nat(m, n);
        let proof = d.itrans(start, middle, end, value_step, scrutinee_step);
        (stmt, proof)
    })?;

    // subNatNat_zero : subNatNat m 0 = ofNat m.
    //
    // The *value* `m-0` reduces to `m` on its own; the *scrutinee* `0-m` does
    // not, so this is one rewrite by `Nat.sub_eq_zero_of_le 0 m (Nat.zero_le m)`
    // and then the zero-minor fires.
    d.theorem(p.sub_nat_nat_zero, 1, &|d, v| {
        let m = v[0];
        let zero = d.zero();
        let stmt = {
            let left = d.sub_nat_nat(m, zero);
            let right = d.of_nat(m);
            d.ieq(left, right)
        };
        let scrutinee = d.sub(zero, m);
        let collapse = {
            let bound = {
                let name = d.int().nat.zero_le;
                d.const_app(name, &[m])
            };
            let name = d.int().nat.sub_eq_zero_of_le;
            d.const_app(name, &[zero, m, bound])
        };
        let restored = d.symm(scrutinee, zero, collapse);
        let base = {
            let target = d.of_nat(m);
            d.irefl(target)
        };
        let value = d.sub(m, zero);
        let proof = d.nat_rewrite(zero, scrutinee, restored, base, &|d, t| {
            let left = borrow(d, value, t);
            let right = d.of_nat(m);
            d.ieq(left, right)
        });
        (stmt, proof)
    })?;

    // zero_subNatNat : subNatNat 0 k = negOfNat k. Both branches are `Eq.refl`:
    // the scrutinee is `k-0 ≡ k`, so splitting `k` fires the `Nat.rec` directly.
    d.theorem(p.zero_sub_nat_nat, 1, &|d, v| {
        let k = v[0];
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let zero = d.zero();
            let left = d.sub_nat_nat(zero, t);
            let right = d.neg_of_nat(t);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let target = d.of_nat(zero);
                d.irefl(target)
            },
            &|d, j, _ih| {
                let target = d.neg_succ(j);
                d.irefl(target)
            },
            k,
        );
        (stmt, proof)
    })?;

    // subNatNat_add_add : subNatNat (m+k) (n+k) = subNatNat m n, by induction on
    // `k` — `Nat.add` recurses on its second argument, so `m+(k+1)` is
    // definitionally `(m+k)+1` and the step is exactly `subNatNat_succ_succ`.
    d.theorem(p.sub_nat_nat_add_add, 3, &|d, v| {
        let (m, n, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let shifted_left = NatOps::add(d, m, t);
            let shifted_right = NatOps::add(d, n, t);
            let left = d.sub_nat_nat(shifted_left, shifted_right);
            let right = d.sub_nat_nat(m, n);
            d.ieq(left, right)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let target = d.sub_nat_nat(m, n);
                d.irefl(target)
            },
            &|d, j, ih| {
                let shifted_left = NatOps::add(d, m, j);
                let shifted_right = NatOps::add(d, n, j);
                let start = {
                    let successor = d.succ(j);
                    let left = NatOps::add(d, m, successor);
                    let right = NatOps::add(d, n, successor);
                    d.sub_nat_nat(left, right)
                };
                let middle = d.sub_nat_nat(shifted_left, shifted_right);
                let end = d.sub_nat_nat(m, n);
                let step = {
                    let name = d.int().sub_nat_nat_succ_succ;
                    d.const_app(name, &[shifted_left, shifted_right])
                };
                d.itrans(start, middle, end, step, ih)
            },
            k,
        );
        (stmt, proof)
    })?;

    // subNatNat_add_add_left : the same shift written on the left, which is the
    // orientation both characterisations and every later script want.
    d.theorem(p.sub_nat_nat_add_add_left, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let stmt = {
            let left = {
                let a = NatOps::add(d, k, m);
                let b = NatOps::add(d, k, n);
                d.sub_nat_nat(a, b)
            };
            let right = d.sub_nat_nat(m, n);
            d.ieq(left, right)
        };
        let right_shifted = {
            let name = d.int().sub_nat_nat_add_add;
            d.const_app(name, &[m, n, k])
        };
        let target = d.sub_nat_nat(m, n);
        let first = {
            let from = NatOps::add(d, m, k);
            let to = NatOps::add(d, k, m);
            let h = add_comm(d, m, k);
            let other = NatOps::add(d, n, k);
            d.nat_rewrite(from, to, h, right_shifted, &|d, t| {
                let left = d.sub_nat_nat(t, other);
                d.ieq(left, target)
            })
        };
        let proof = {
            let from = NatOps::add(d, n, k);
            let to = NatOps::add(d, k, n);
            let h = add_comm(d, n, k);
            let fixed = NatOps::add(d, k, m);
            d.nat_rewrite(from, to, h, first, &|d, t| {
                let left = d.sub_nat_nat(fixed, t);
                d.ieq(left, target)
            })
        };
        (stmt, proof)
    })?;

    // subNatNat_add_left : subNatNat (n+i) n = ofNat i — shift the `m 0` anchor
    // by `n`. `Nat.add n 0` is definitionally `n`, so no rewrite is needed to
    // line the shifted anchor up with the statement.
    d.theorem(p.sub_nat_nat_add_left, 2, &|d, v| {
        let (n, i) = (v[0], v[1]);
        let zero = d.zero();
        let stmt = {
            let sum = NatOps::add(d, n, i);
            let left = d.sub_nat_nat(sum, n);
            let right = d.of_nat(i);
            d.ieq(left, right)
        };
        let shift = {
            let name = d.int().sub_nat_nat_add_add_left;
            d.const_app(name, &[n, i, zero])
        };
        let anchor = {
            let name = d.int().sub_nat_nat_zero;
            d.const_app(name, &[i])
        };
        let start = {
            let sum = NatOps::add(d, n, i);
            d.sub_nat_nat(sum, n)
        };
        let middle = d.sub_nat_nat(i, zero);
        let end = d.of_nat(i);
        let proof = d.itrans(start, middle, end, shift, anchor);
        (stmt, proof)
    })?;

    // subNatNat_add_right : subNatNat m (m+k) = negOfNat k — the `0 k` anchor
    // shifted by `m`.
    d.theorem(p.sub_nat_nat_add_right, 2, &|d, v| {
        let (m, k) = (v[0], v[1]);
        let zero = d.zero();
        let stmt = {
            let sum = NatOps::add(d, m, k);
            let left = d.sub_nat_nat(m, sum);
            let right = d.neg_of_nat(k);
            d.ieq(left, right)
        };
        let shift = {
            let name = d.int().sub_nat_nat_add_add_left;
            d.const_app(name, &[m, zero, k])
        };
        let anchor = {
            let name = d.int().zero_sub_nat_nat;
            d.const_app(name, &[k])
        };
        let start = {
            let sum = NatOps::add(d, m, k);
            d.sub_nat_nat(m, sum)
        };
        let middle = d.sub_nat_nat(zero, k);
        let end = d.neg_of_nat(k);
        let proof = d.itrans(start, middle, end, shift, anchor);
        (stmt, proof)
    })?;

    declare_elim(d)
}

/// The free variables the elimination principle's proof body reads.
struct Elim {
    /// The motive `P : Int → Prop`.
    predicate: ExprId,
    /// The first argument of the borrow.
    m: ExprId,
    /// The second argument of the borrow.
    n: ExprId,
    /// `hp : ∀ i, n+i = m → P (ofNat i)`.
    positive: ExprId,
    /// `hn : ∀ i, m+(i+1) = n → P (negSucc i)`.
    negative: ExprId,
}

/// `P (subNatNat m n)` from `hi : n+i = m` — the borrow did not fire.
fn positive_case(d: &mut IntDev<'_>, e: &Elim, i: ExprId, hi: ExprId) -> ExprId {
    let value = d.of_nat(i);
    let characterisation = {
        let name = d.int().sub_nat_nat_add_left;
        d.const_app(name, &[e.n, i])
    };
    let sum = NatOps::add(d, e.n, i);
    let located = d.nat_rewrite(sum, e.m, hi, characterisation, &|d, t| {
        let left = d.sub_nat_nat(t, e.n);
        let right = d.of_nat(i);
        d.ieq(left, right)
    });
    let borrowed = d.sub_nat_nat(e.m, e.n);
    let restored = d.isymm(borrowed, value, located);
    let base = d.apply(e.positive, &[i, hi]);
    let predicate = e.predicate;
    d.int_eq_rewrite(value, borrowed, restored, base, &|d, x| {
        d.apply(predicate, &[x])
    })
}

/// `P (subNatNat m n)` from `hj : m+(j+1) = n` — the borrow fired.
fn negative_case(d: &mut IntDev<'_>, e: &Elim, j: ExprId, hj: ExprId) -> ExprId {
    let successor = d.succ(j);
    let value = d.neg_succ(j);
    let characterisation = {
        let name = d.int().sub_nat_nat_add_right;
        d.const_app(name, &[e.m, successor])
    };
    let sum = NatOps::add(d, e.m, successor);
    let located = d.nat_rewrite(sum, e.n, hj, characterisation, &|d, t| {
        let left = d.sub_nat_nat(e.m, t);
        let right = d.neg_succ(j);
        d.ieq(left, right)
    });
    let borrowed = d.sub_nat_nat(e.m, e.n);
    let restored = d.isymm(borrowed, value, located);
    let base = d.apply(e.negative, &[j, hj]);
    let predicate = e.predicate;
    d.int_eq_rewrite(value, borrowed, restored, base, &|d, x| {
        d.apply(predicate, &[x])
    })
}

/// Declare `Int.subNatNat_elim`.
///
/// `Nat.le_total m n` splits into the two orders; `Nat.le_dest` turns each into
/// an explicit difference. In the `m ≤ n` half the difference may still be `0`
/// — which is the *non*-borrowing case — so that half splits the witness once
/// more, and `0` is routed to the positive branch.
fn declare_elim(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();

    let motive_ty = d.arrow(int_ty, prop);
    let predicate_fv = d.fresh_fvar();
    let predicate = d.kernel().fvar(predicate_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let positive_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sum = NatOps::add(d, n, i);
        let hypothesis = d.eq(sum, m);
        let value = d.of_nat(i);
        let conclusion = d.apply(predicate, &[value]);
        let inner = d
            .kernel()
            .pi(anon, hypothesis, conclusion, BinderInfo::Default);
        d.pi_fv(i_fv, nat, inner)
    };
    let negative_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let successor = d.succ(i);
        let sum = NatOps::add(d, m, successor);
        let hypothesis = d.eq(sum, n);
        let value = d.neg_succ(i);
        let conclusion = d.apply(predicate, &[value]);
        let inner = d
            .kernel()
            .pi(anon, hypothesis, conclusion, BinderInfo::Default);
        d.pi_fv(i_fv, nat, inner)
    };

    let positive_fv = d.fresh_fvar();
    let positive = d.kernel().fvar(positive_fv);
    let negative_fv = d.fresh_fvar();
    let negative = d.kernel().fvar(negative_fv);

    let goal = {
        let borrowed = d.sub_nat_nat(m, n);
        d.apply(predicate, &[borrowed])
    };

    let context = Elim {
        predicate,
        m,
        n,
        positive,
        negative,
    };

    let body = {
        let forward = NatOps::le(d, m, n);
        let backward = NatOps::le(d, n, m);
        let total = {
            let name = d.int().nat.le_total;
            d.const_app(name, &[m, n])
        };
        d.or_elim(
            forward,
            backward,
            goal,
            total,
            // m ≤ n: the difference `k` may be zero, so split it.
            &|d, bound| {
                let witness = {
                    let name = d.int().nat.le_dest;
                    d.const_app(name, &[m, n, bound])
                };
                let difference = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let sum = NatOps::add(d, m, k);
                    let body = d.eq(sum, n);
                    d.lam_fv(k_fv, nat, body)
                };
                let minor = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let implication = d.induct(
                        &|d, t| {
                            let sum = NatOps::add(d, m, t);
                            let hypothesis = d.eq(sum, n);
                            d.arrow(hypothesis, goal)
                        },
                        &|d| {
                            let zero = d.zero();
                            let sum = NatOps::add(d, m, zero);
                            let hypothesis = d.eq(sum, n);
                            let h_fv = d.fresh_fvar();
                            let h = d.kernel().fvar(h_fv);
                            // `m+0 ≡ m`, so `h : m = n` and its symmetry is the
                            // `n+0 = m` the positive branch asks for.
                            let flipped = d.symm(sum, n, h);
                            let body = positive_case(d, &context, zero, flipped);
                            d.lam_fv(h_fv, hypothesis, body)
                        },
                        &|d, j, _ih| {
                            let successor = d.succ(j);
                            let sum = NatOps::add(d, m, successor);
                            let hypothesis = d.eq(sum, n);
                            let h_fv = d.fresh_fvar();
                            let h = d.kernel().fvar(h_fv);
                            let body = negative_case(d, &context, j, h);
                            d.lam_fv(h_fv, hypothesis, body)
                        },
                        k,
                    );
                    let sum = NatOps::add(d, m, k);
                    let hypothesis = d.eq(sum, n);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let applied = d.apply(implication, &[h]);
                    let with_h = d.lam_fv(h_fv, hypothesis, applied);
                    d.lam_fv(k_fv, nat, with_h)
                };
                exists_elim(d, difference, goal, witness, minor)
            },
            // n ≤ m: the borrow never fires.
            &|d, bound| {
                let witness = {
                    let name = d.int().nat.le_dest;
                    d.const_app(name, &[n, m, bound])
                };
                let difference = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let sum = NatOps::add(d, n, i);
                    let body = d.eq(sum, m);
                    d.lam_fv(i_fv, nat, body)
                };
                let minor = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let sum = NatOps::add(d, n, i);
                    let hypothesis = d.eq(sum, m);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let body = positive_case(d, &context, i, h);
                    let with_h = d.lam_fv(h_fv, hypothesis, body);
                    d.lam_fv(i_fv, nat, with_h)
                };
                exists_elim(d, difference, goal, witness, minor)
            },
        )
    };

    let ty = {
        let with_negative = d.pi_fv(negative_fv, negative_ty, goal);
        let with_positive = d.pi_fv(positive_fv, positive_ty, with_negative);
        let with_n = d.pi_fv(n_fv, nat, with_positive);
        let with_m = d.pi_fv(m_fv, nat, with_n);
        d.pi_fv(predicate_fv, motive_ty, with_m)
    };
    let value = {
        let with_negative = d.lam_fv(negative_fv, negative_ty, body);
        let with_positive = d.lam_fv(positive_fv, positive_ty, with_negative);
        let with_n = d.lam_fv(n_fv, nat, with_positive);
        let with_m = d.lam_fv(m_fv, nat, with_n);
        d.lam_fv(predicate_fv, motive_ty, with_m)
    };
    d.declare_theorem(p.sub_nat_nat_elim, ty, value)
}

/// Apply [`IntPrelude::sub_nat_nat_elim`](super::IntPrelude::sub_nat_nat_elim)
/// to prove `motive (subNatNat m n)`.
pub(super) fn by_borrow(
    d: &mut IntDev<'_>,
    m: ExprId,
    n: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    on_positive: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    on_negative: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let predicate = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let body = motive(d, z);
        d.lam_fv(z_fv, int_ty, body)
    };
    let positive = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sum = NatOps::add(d, n, i);
        let hypothesis = d.eq(sum, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = on_positive(d, i, h);
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(i_fv, nat, with_h)
    };
    let negative = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let successor = d.succ(i);
        let sum = NatOps::add(d, m, successor);
        let hypothesis = d.eq(sum, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = on_negative(d, i, h);
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(i_fv, nat, with_h)
    };
    let name = d.int().sub_nat_nat_elim;
    d.const_app(name, &[predicate, m, n, positive, negative])
}

/// Declare the additive lemmas: `Int.add` against a stuck `subNatNat` on either
/// side, and against a stuck `negOfNat`.
pub(super) fn declare_add_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // ofNat_add_subNatNat : ofNat m + subNatNat n q = subNatNat (m+n) q.
    d.theorem(p.of_nat_add_sub_nat_nat, 3, &|d, v| {
        let (m, n, q) = (v[0], v[1], v[2]);
        let motive = |d: &mut IntDev<'_>, z: ExprId| {
            let scale = d.of_nat(m);
            let left = d.iadd(scale, z);
            let sum = NatOps::add(d, m, n);
            let right = d.sub_nat_nat(sum, q);
            d.ieq(left, right)
        };
        let stmt = {
            let borrowed = d.sub_nat_nat(n, q);
            motive(d, borrowed)
        };
        let proof = by_borrow(
            d,
            n,
            q,
            &motive,
            // n = q+i: both sides are `ofNat (m+i)` once `m+n` is rewritten as
            // `q + (m+i)`.
            &|d, i, hi| {
                let shifted = NatOps::add(d, m, i);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_left;
                    d.const_app(name, &[q, shifted])
                };
                let source = NatOps::add(d, q, shifted);
                let goal_sum = NatOps::add(d, m, n);
                let rearranged = {
                    let start = NatOps::add(d, q, shifted);
                    let regrouped = {
                        let inner = NatOps::add(d, q, m);
                        NatOps::add(d, inner, i)
                    };
                    let step_one = {
                        let h = add_assoc(d, q, m, i);
                        let left = NatOps::add(d, q, m);
                        let right = NatOps::add(d, left, i);
                        d.symm(right, start, h)
                    };
                    let commuted = {
                        let inner = NatOps::add(d, m, q);
                        NatOps::add(d, inner, i)
                    };
                    let step_two = {
                        let from = NatOps::add(d, q, m);
                        let to = NatOps::add(d, m, q);
                        let h = add_comm(d, q, m);
                        d.congr(from, to, h, &|d, t| NatOps::add(d, t, i))
                    };
                    let regrouped_again = {
                        let inner = NatOps::add(d, q, i);
                        NatOps::add(d, m, inner)
                    };
                    let step_three = add_assoc(d, m, q, i);
                    let step_four = {
                        let from = NatOps::add(d, q, i);
                        d.congr(from, n, hi, &|d, t| NatOps::add(d, m, t))
                    };
                    let (_, proof) = d.chain(
                        start,
                        &[
                            (regrouped, step_one),
                            (commuted, step_two),
                            (regrouped_again, step_three),
                            (goal_sum, step_four),
                        ],
                    );
                    proof
                };
                let located =
                    d.nat_rewrite(source, goal_sum, rearranged, characterisation, &|d, t| {
                        let left = d.sub_nat_nat(t, q);
                        let right = d.of_nat(shifted);
                        d.ieq(left, right)
                    });
                let borrowed = d.sub_nat_nat(goal_sum, q);
                let value = d.of_nat(shifted);
                d.isymm(borrowed, value, located)
            },
            // q = n+(j+1): shift the whole difference down by `n`.
            &|d, j, hj| {
                let successor = d.succ(j);
                let shift = {
                    let name = d.int().sub_nat_nat_add_add;
                    d.const_app(name, &[m, successor, n])
                };
                let source = NatOps::add(d, successor, n);
                let commuted = {
                    let start = NatOps::add(d, successor, n);
                    let swapped = NatOps::add(d, n, successor);
                    let step_one = add_comm(d, successor, n);
                    let (_, proof) = d.chain(start, &[(swapped, step_one), (q, hj)]);
                    proof
                };
                let goal_sum = NatOps::add(d, m, n);
                let target = d.sub_nat_nat(m, successor);
                let located = d.nat_rewrite(source, q, commuted, shift, &|d, t| {
                    let left = d.sub_nat_nat(goal_sum, t);
                    d.ieq(left, target)
                });
                let borrowed = d.sub_nat_nat(goal_sum, q);
                d.isymm(borrowed, target, located)
            },
        );
        (stmt, proof)
    })?;

    // subNatNat_add_ofNat : subNatNat a b + ofNat p = subNatNat (a+p) b.
    d.theorem(p.sub_nat_nat_add_of_nat, 3, &|d, v| {
        let (a, b, k) = (v[0], v[1], v[2]);
        let borrowed = d.sub_nat_nat(a, b);
        let scale = d.of_nat(k);
        let stmt = {
            let left = d.iadd(borrowed, scale);
            let sum = NatOps::add(d, a, k);
            let right = d.sub_nat_nat(sum, b);
            d.ieq(left, right)
        };
        let commuted = {
            let name = d.int().add_comm;
            d.const_app(name, &[borrowed, scale])
        };
        let pushed = {
            let name = d.int().of_nat_add_sub_nat_nat;
            d.const_app(name, &[k, a, b])
        };
        let start = d.iadd(borrowed, scale);
        let middle = d.iadd(scale, borrowed);
        let reordered = {
            let sum = NatOps::add(d, k, a);
            d.sub_nat_nat(sum, b)
        };
        let end = {
            let sum = NatOps::add(d, a, k);
            d.sub_nat_nat(sum, b)
        };
        let fix = {
            let from = NatOps::add(d, k, a);
            let to = NatOps::add(d, a, k);
            let h = add_comm(d, k, a);
            d.nat_eq_to_int(from, to, h, &|d, t| d.sub_nat_nat(t, b))
        };
        let (_, proof) = d.ichain(
            start,
            &[(middle, commuted), (reordered, pushed), (end, fix)],
        );
        (stmt, proof)
    })?;

    // subNatNat_add_negSucc : subNatNat a b + negSucc p = subNatNat a (b+(p+1)).
    d.theorem(p.sub_nat_nat_add_neg_succ, 3, &|d, v| {
        let (a, b, k) = (v[0], v[1], v[2]);
        let successor = d.succ(k);
        let motive = |d: &mut IntDev<'_>, z: ExprId| {
            let negative = d.neg_succ(k);
            let left = d.iadd(z, negative);
            let sum = NatOps::add(d, b, successor);
            let right = d.sub_nat_nat(a, sum);
            d.ieq(left, right)
        };
        let stmt = {
            let borrowed = d.sub_nat_nat(a, b);
            motive(d, borrowed)
        };
        let proof = by_borrow(
            d,
            a,
            b,
            &motive,
            // a = b+i: shift `subNatNat (b+i) (b+(k+1))` down by `b`.
            &|d, i, hi| {
                let shift = {
                    let name = d.int().sub_nat_nat_add_add_left;
                    d.const_app(name, &[b, i, successor])
                };
                let source = NatOps::add(d, b, i);
                let raised = NatOps::add(d, b, successor);
                let target = d.sub_nat_nat(i, successor);
                let located = d.nat_rewrite(source, a, hi, shift, &|d, t| {
                    let left = d.sub_nat_nat(t, raised);
                    d.ieq(left, target)
                });
                let borrowed = d.sub_nat_nat(a, raised);
                d.isymm(borrowed, target, located)
            },
            // b = a+(j+1): the sum is `negOfNat ((j+1)+(k+1))`, which has to be
            // matched against the branch's own `negSucc ((j+k)+1)`.
            &|d, j, hj| {
                let inner = d.succ(j);
                let excess = NatOps::add(d, inner, successor);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_right;
                    d.const_app(name, &[a, excess])
                };
                let source = NatOps::add(d, a, excess);
                let raised = NatOps::add(d, b, successor);
                let regrouped = {
                    let start = NatOps::add(d, a, excess);
                    let step_one = {
                        let left = NatOps::add(d, a, inner);
                        let right = NatOps::add(d, left, successor);
                        let h = add_assoc(d, a, inner, successor);
                        d.symm(right, start, h)
                    };
                    let grouped = {
                        let left = NatOps::add(d, a, inner);
                        NatOps::add(d, left, successor)
                    };
                    let step_two = {
                        let from = NatOps::add(d, a, inner);
                        d.congr(from, b, hj, &|d, t| NatOps::add(d, t, successor))
                    };
                    let (_, proof) = d.chain(start, &[(grouped, step_one), (raised, step_two)]);
                    proof
                };
                let excess_value = d.neg_of_nat(excess);
                let located =
                    d.nat_rewrite(source, raised, regrouped, characterisation, &|d, t| {
                        let left = d.sub_nat_nat(a, t);
                        d.ieq(left, excess_value)
                    });
                // `negOfNat ((j+1)+(k+1))` ι-reduces to `negSucc ((j+1)+k)`;
                // `Nat.succ_add` turns that into the branch's `negSucc ((j+k)+1)`.
                let shifted = NatOps::add(d, inner, k);
                let normalised = {
                    let flat = NatOps::add(d, j, k);
                    let target = d.succ(flat);
                    let h = succ_add(d, j, k);
                    d.nat_eq_to_int(shifted, target, h, &|d, t| d.neg_succ(t))
                };
                let borrowed = d.sub_nat_nat(a, raised);
                let end = {
                    let flat = NatOps::add(d, j, k);
                    let target = d.succ(flat);
                    d.neg_succ(target)
                };
                let (_, forward) =
                    d.ichain(borrowed, &[(excess_value, located), (end, normalised)]);
                d.isymm(borrowed, end, forward)
            },
        );
        (stmt, proof)
    })?;

    // negSucc_add_subNatNat : negSucc m + subNatNat a b = subNatNat a (b+(m+1)).
    d.theorem(p.neg_succ_add_sub_nat_nat, 3, &|d, v| {
        let (k, a, b) = (v[0], v[1], v[2]);
        let successor = d.succ(k);
        let negative = d.neg_succ(k);
        let borrowed = d.sub_nat_nat(a, b);
        let stmt = {
            let left = d.iadd(negative, borrowed);
            let sum = NatOps::add(d, b, successor);
            let right = d.sub_nat_nat(a, sum);
            d.ieq(left, right)
        };
        let commuted = {
            let name = d.int().add_comm;
            d.const_app(name, &[negative, borrowed])
        };
        let pushed = {
            let name = d.int().sub_nat_nat_add_neg_succ;
            d.const_app(name, &[a, b, k])
        };
        let start = d.iadd(negative, borrowed);
        let middle = d.iadd(borrowed, negative);
        let end = {
            let sum = NatOps::add(d, b, successor);
            d.sub_nat_nat(a, sum)
        };
        let proof = d.itrans(start, middle, end, commuted, pushed);
        (stmt, proof)
    })?;

    // ofNat_add_negOfNat : ofNat u + negOfNat v = subNatNat u v.
    d.theorem(p.of_nat_add_neg_of_nat, 2, &|d, v| {
        let (u, w) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let scale = d.of_nat(u);
            let negative = d.neg_of_nat(t);
            let left = d.iadd(scale, negative);
            let right = d.sub_nat_nat(u, t);
            d.ieq(left, right)
        };
        let stmt = motive(d, w);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let anchor = {
                    let name = d.int().sub_nat_nat_zero;
                    d.const_app(name, &[u])
                };
                let borrowed = d.sub_nat_nat(u, zero);
                let value = d.of_nat(u);
                d.isymm(borrowed, value, anchor)
            },
            &|d, j, _ih| {
                let successor = d.succ(j);
                let target = d.sub_nat_nat(u, successor);
                d.irefl(target)
            },
            w,
        );
        (stmt, proof)
    })?;

    // negOfNat_add_ofNat : negOfNat v + ofNat u = subNatNat u v.
    d.theorem(p.neg_of_nat_add_of_nat, 2, &|d, v| {
        let (w, u) = (v[0], v[1]);
        let negative = d.neg_of_nat(w);
        let scale = d.of_nat(u);
        let stmt = {
            let left = d.iadd(negative, scale);
            let right = d.sub_nat_nat(u, w);
            d.ieq(left, right)
        };
        let commuted = {
            let name = d.int().add_comm;
            d.const_app(name, &[negative, scale])
        };
        let pushed = {
            let name = d.int().of_nat_add_neg_of_nat;
            d.const_app(name, &[u, w])
        };
        let start = d.iadd(negative, scale);
        let middle = d.iadd(scale, negative);
        let end = d.sub_nat_nat(u, w);
        let proof = d.itrans(start, middle, end, commuted, pushed);
        (stmt, proof)
    })?;

    // negOfNat_add_negOfNat : negOfNat u + negOfNat v = negOfNat (u+v).
    d.theorem(p.neg_of_nat_add_neg_of_nat, 2, &|d, v| {
        let (u, w) = (v[0], v[1]);
        let motive = |d: &mut IntDev<'_>, t: ExprId| {
            let left_value = d.neg_of_nat(t);
            let right_value = d.neg_of_nat(w);
            let left = d.iadd(left_value, right_value);
            let sum = NatOps::add(d, t, w);
            let right = d.neg_of_nat(sum);
            d.ieq(left, right)
        };
        let stmt = motive(d, u);
        let proof = d.induct(
            &motive,
            // u = 0: `ofNat 0 + negOfNat v` is `subNatNat 0 v`, i.e. `negOfNat v`,
            // and `0+v` needs `Nat.zero_add` to become `v`.
            &|d| {
                let zero = d.zero();
                let pushed = {
                    let name = d.int().of_nat_add_neg_of_nat;
                    d.const_app(name, &[zero, w])
                };
                let anchor = {
                    let name = d.int().zero_sub_nat_nat;
                    d.const_app(name, &[w])
                };
                let restore = {
                    let sum = NatOps::add(d, zero, w);
                    let h = {
                        let name = d.int().nat.zero_add;
                        d.const_app(name, &[w])
                    };
                    let forward = d.nat_eq_to_int(sum, w, h, &|d, t| d.neg_of_nat(t));
                    let from = d.neg_of_nat(sum);
                    let to = d.neg_of_nat(w);
                    d.isymm(from, to, forward)
                };
                let start = {
                    let left_value = d.of_nat(zero);
                    let right_value = d.neg_of_nat(w);
                    d.iadd(left_value, right_value)
                };
                let borrowed = d.sub_nat_nat(zero, w);
                let value = d.neg_of_nat(w);
                let end = {
                    let sum = NatOps::add(d, zero, w);
                    d.neg_of_nat(sum)
                };
                let (_, proof) = d.ichain(
                    start,
                    &[(borrowed, pushed), (value, anchor), (end, restore)],
                );
                proof
            },
            // u = i+1: split `v` too. Neither branch uses the hypothesis; the
            // recursion only exposes the constructors `negOfNat` is stuck on.
            &|d, i, _ih| {
                let inner_motive = |d: &mut IntDev<'_>, t: ExprId| {
                    let successor = d.succ(i);
                    let left_value = d.neg_of_nat(successor);
                    let right_value = d.neg_of_nat(t);
                    let left = d.iadd(left_value, right_value);
                    let sum = NatOps::add(d, successor, t);
                    let right = d.neg_of_nat(sum);
                    d.ieq(left, right)
                };
                d.induct(
                    &inner_motive,
                    &|d| {
                        let target = d.neg_succ(i);
                        d.irefl(target)
                    },
                    &|d, j, _ih| {
                        let successor = d.succ(i);
                        let shifted = NatOps::add(d, successor, j);
                        let flat = NatOps::add(d, i, j);
                        let target = d.succ(flat);
                        let h = succ_add(d, i, j);
                        let forward = d.nat_eq_to_int(shifted, target, h, &|d, t| d.neg_succ(t));
                        let from = d.neg_succ(shifted);
                        let to = d.neg_succ(target);
                        d.isymm(from, to, forward)
                    },
                    w,
                )
            },
            u,
        );
        (stmt, proof)
    })?;

    Ok(())
}

/// `negOfNat_add_subNatNat : ∀ mag base offset, negOfNat mag + subNatNat base
/// offset = subNatNat base (offset+mag)`.
///
/// The bridge this file was missing: every add lemma above pairs `Int.add`
/// with a *pure* `ofNat`/`negSucc` operand on one side; this is the first with
/// a second `negOfNat` landing on a `subNatNat`, which is what
/// `Int.ediv_add_emod`'s two negative-dividend branches need
/// (`crates/axeyum-lean-kernel/src/int_prelude/division.rs`). Proved the same
/// way as everything else here — `sub_nat_nat_elim` via [`by_borrow`] — by
/// re-anchoring whichever of [`IntPrelude::neg_of_nat_add_of_nat`] or
/// [`IntPrelude::neg_of_nat_add_neg_of_nat`] the borrow's outcome calls for.
pub(super) fn declare_neg_of_nat_add_sub_nat_nat(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.neg_of_nat_add_sub_nat_nat, 3, &|d, v| {
        let (mag, base, offset) = (v[0], v[1], v[2]);
        let negative = d.neg_of_nat(mag);
        let shifted_offset = NatOps::add(d, offset, mag);
        let motive = |d: &mut IntDev<'_>, z: ExprId| {
            let left = d.iadd(negative, z);
            let right = d.sub_nat_nat(base, shifted_offset);
            d.ieq(left, right)
        };
        let stmt = {
            let borrowed = d.sub_nat_nat(base, offset);
            motive(d, borrowed)
        };
        let proof = by_borrow(
            d,
            base,
            offset,
            &motive,
            // The borrow did not fire: `offset+i = base`, answer `ofNat i`.
            &|d, i, hi| {
                let start = {
                    let value = d.of_nat(i);
                    d.iadd(negative, value)
                };
                let mid1 = d.sub_nat_nat(i, mag);
                let step1 = {
                    let name = d.int().neg_of_nat_add_of_nat;
                    d.const_app(name, &[mag, i])
                };
                let mid2 = {
                    let a = NatOps::add(d, offset, i);
                    let b = NatOps::add(d, offset, mag);
                    d.sub_nat_nat(a, b)
                };
                let step2 = {
                    let name = d.int().sub_nat_nat_add_add_left;
                    let forward = d.const_app(name, &[offset, i, mag]);
                    d.isymm(mid2, mid1, forward)
                };
                let end = d.sub_nat_nat(base, shifted_offset);
                let step3 = {
                    let sum_oi = NatOps::add(d, offset, i);
                    d.nat_eq_to_int(sum_oi, base, hi, &|d, x| d.sub_nat_nat(x, shifted_offset))
                };
                let (_, chained) = d.ichain(start, &[(mid1, step1), (mid2, step2), (end, step3)]);
                chained
            },
            // The borrow fired: `base+(i+1) = offset`, answer `negSucc i`.
            &|d, i, hi| {
                let succ_i = d.succ(i);
                let start = {
                    let value = d.neg_of_nat(succ_i);
                    d.iadd(negative, value)
                };
                let sum1 = NatOps::add(d, mag, succ_i);
                let mid1 = d.neg_of_nat(sum1);
                let step1 = {
                    let name = d.int().neg_of_nat_add_neg_of_nat;
                    d.const_app(name, &[mag, succ_i])
                };
                let sum2 = NatOps::add(d, succ_i, mag);
                let mid2 = d.neg_of_nat(sum2);
                let step2 = {
                    let h = add_comm(d, mag, succ_i);
                    d.nat_eq_to_int(sum1, sum2, h, &|d, x| d.neg_of_nat(x))
                };
                let anchor_sum = NatOps::add(d, base, sum2);
                let mid3 = d.sub_nat_nat(base, anchor_sum);
                let step3 = {
                    let name = d.int().sub_nat_nat_add_right;
                    let anchor = d.const_app(name, &[base, sum2]);
                    d.isymm(mid3, mid2, anchor)
                };
                let mid4 = d.sub_nat_nat(base, shifted_offset);
                let step4 = {
                    let reindexed = {
                        let mid_assoc = {
                            let a = NatOps::add(d, base, succ_i);
                            NatOps::add(d, a, mag)
                        };
                        let h_assoc_fwd = add_assoc(d, base, succ_i, mag);
                        let h_assoc = d.symm(mid_assoc, anchor_sum, h_assoc_fwd);
                        let h_congr = {
                            let sum = NatOps::add(d, base, succ_i);
                            d.congr(sum, offset, hi, &|d, x| NatOps::add(d, x, mag))
                        };
                        let (_, chained) = d.chain(
                            anchor_sum,
                            &[(mid_assoc, h_assoc), (shifted_offset, h_congr)],
                        );
                        chained
                    };
                    d.nat_eq_to_int(anchor_sum, shifted_offset, reindexed, &|d, x| {
                        d.sub_nat_nat(base, x)
                    })
                };
                let (_, chained) = d.ichain(
                    start,
                    &[(mid1, step1), (mid2, step2), (mid3, step3), (mid4, step4)],
                );
                chained
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare the multiplicative lemmas: `Int.mul` against a stuck `subNatNat`.
pub(super) fn declare_mul_lemmas(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    // ofNat_mul_subNatNat : ofNat m * subNatNat p q = subNatNat (m*p) (m*q).
    d.theorem(p.of_nat_mul_sub_nat_nat, 3, &|d, v| {
        let (m, left, right) = (v[0], v[1], v[2]);
        let scaled_left = NatOps::mul(d, m, left);
        let scaled_right = NatOps::mul(d, m, right);
        let motive = |d: &mut IntDev<'_>, z: ExprId| {
            let scale = d.of_nat(m);
            let product = d.imul(scale, z);
            let target = d.sub_nat_nat(scaled_left, scaled_right);
            d.ieq(product, target)
        };
        let stmt = {
            let borrowed = d.sub_nat_nat(left, right);
            motive(d, borrowed)
        };
        let proof = by_borrow(
            d,
            left,
            right,
            &motive,
            &|d, i, hi| {
                let scaled = NatOps::mul(d, m, i);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_left;
                    d.const_app(name, &[scaled_right, scaled])
                };
                let source = NatOps::add(d, scaled_right, scaled);
                let distributed = {
                    let start = NatOps::add(d, scaled_right, scaled);
                    let joined = {
                        let sum = NatOps::add(d, right, i);
                        NatOps::mul(d, m, sum)
                    };
                    let step_one = {
                        let h = left_distrib(d, m, right, i);
                        let sum = NatOps::add(d, right, i);
                        let product = NatOps::mul(d, m, sum);
                        d.symm(product, start, h)
                    };
                    let step_two = {
                        let sum = NatOps::add(d, right, i);
                        d.congr(sum, left, hi, &|d, t| NatOps::mul(d, m, t))
                    };
                    let (_, proof) = d.chain(start, &[(joined, step_one), (scaled_left, step_two)]);
                    proof
                };
                let value = d.of_nat(scaled);
                let located = d.nat_rewrite(
                    source,
                    scaled_left,
                    distributed,
                    characterisation,
                    &|d, t| {
                        let borrowed = d.sub_nat_nat(t, scaled_right);
                        let value = d.of_nat(scaled);
                        d.ieq(borrowed, value)
                    },
                );
                let borrowed = d.sub_nat_nat(scaled_left, scaled_right);
                d.isymm(borrowed, value, located)
            },
            &|d, j, hj| {
                let successor = d.succ(j);
                let scaled = NatOps::mul(d, m, successor);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_right;
                    d.const_app(name, &[scaled_left, scaled])
                };
                let source = NatOps::add(d, scaled_left, scaled);
                let distributed = {
                    let start = NatOps::add(d, scaled_left, scaled);
                    let joined = {
                        let sum = NatOps::add(d, left, successor);
                        NatOps::mul(d, m, sum)
                    };
                    let step_one = {
                        let h = left_distrib(d, m, left, successor);
                        let sum = NatOps::add(d, left, successor);
                        let product = NatOps::mul(d, m, sum);
                        d.symm(product, start, h)
                    };
                    let step_two = {
                        let sum = NatOps::add(d, left, successor);
                        d.congr(sum, right, hj, &|d, t| NatOps::mul(d, m, t))
                    };
                    let (_, proof) =
                        d.chain(start, &[(joined, step_one), (scaled_right, step_two)]);
                    proof
                };
                let value = d.neg_of_nat(scaled);
                let located = d.nat_rewrite(
                    source,
                    scaled_right,
                    distributed,
                    characterisation,
                    &|d, t| {
                        let borrowed = d.sub_nat_nat(scaled_left, t);
                        let value = d.neg_of_nat(scaled);
                        d.ieq(borrowed, value)
                    },
                );
                let borrowed = d.sub_nat_nat(scaled_left, scaled_right);
                d.isymm(borrowed, value, located)
            },
        );
        (stmt, proof)
    })?;

    // negSucc_mul_subNatNat : negSucc m * subNatNat p q = subNatNat ((m+1)*q) ((m+1)*p).
    // The same two cases with the roles of the two products swapped, because a
    // negative scale reverses which side of the difference dominates.
    d.theorem(p.neg_succ_mul_sub_nat_nat, 3, &|d, v| {
        let (m, left, right) = (v[0], v[1], v[2]);
        let scale = d.succ(m);
        let scaled_left = NatOps::mul(d, scale, left);
        let scaled_right = NatOps::mul(d, scale, right);
        let motive = |d: &mut IntDev<'_>, z: ExprId| {
            let negative = d.neg_succ(m);
            let product = d.imul(negative, z);
            let target = d.sub_nat_nat(scaled_right, scaled_left);
            d.ieq(product, target)
        };
        let stmt = {
            let borrowed = d.sub_nat_nat(left, right);
            motive(d, borrowed)
        };
        let proof = by_borrow(
            d,
            left,
            right,
            &motive,
            &|d, i, hi| {
                let scaled = NatOps::mul(d, scale, i);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_right;
                    d.const_app(name, &[scaled_right, scaled])
                };
                let source = NatOps::add(d, scaled_right, scaled);
                let distributed = {
                    let start = NatOps::add(d, scaled_right, scaled);
                    let joined = {
                        let sum = NatOps::add(d, right, i);
                        NatOps::mul(d, scale, sum)
                    };
                    let step_one = {
                        let h = left_distrib(d, scale, right, i);
                        let sum = NatOps::add(d, right, i);
                        let product = NatOps::mul(d, scale, sum);
                        d.symm(product, start, h)
                    };
                    let step_two = {
                        let sum = NatOps::add(d, right, i);
                        d.congr(sum, left, hi, &|d, t| NatOps::mul(d, scale, t))
                    };
                    let (_, proof) = d.chain(start, &[(joined, step_one), (scaled_left, step_two)]);
                    proof
                };
                let value = d.neg_of_nat(scaled);
                let located = d.nat_rewrite(
                    source,
                    scaled_left,
                    distributed,
                    characterisation,
                    &|d, t| {
                        let borrowed = d.sub_nat_nat(scaled_right, t);
                        let value = d.neg_of_nat(scaled);
                        d.ieq(borrowed, value)
                    },
                );
                let borrowed = d.sub_nat_nat(scaled_right, scaled_left);
                d.isymm(borrowed, value, located)
            },
            &|d, j, hj| {
                let successor = d.succ(j);
                let scaled = NatOps::mul(d, scale, successor);
                let characterisation = {
                    let name = d.int().sub_nat_nat_add_left;
                    d.const_app(name, &[scaled_left, scaled])
                };
                let source = NatOps::add(d, scaled_left, scaled);
                let distributed = {
                    let start = NatOps::add(d, scaled_left, scaled);
                    let joined = {
                        let sum = NatOps::add(d, left, successor);
                        NatOps::mul(d, scale, sum)
                    };
                    let step_one = {
                        let h = left_distrib(d, scale, left, successor);
                        let sum = NatOps::add(d, left, successor);
                        let product = NatOps::mul(d, scale, sum);
                        d.symm(product, start, h)
                    };
                    let step_two = {
                        let sum = NatOps::add(d, left, successor);
                        d.congr(sum, right, hj, &|d, t| NatOps::mul(d, scale, t))
                    };
                    let (_, proof) =
                        d.chain(start, &[(joined, step_one), (scaled_right, step_two)]);
                    proof
                };
                let value = d.of_nat(scaled);
                let located = d.nat_rewrite(
                    source,
                    scaled_right,
                    distributed,
                    characterisation,
                    &|d, t| {
                        let borrowed = d.sub_nat_nat(t, scaled_left);
                        let value = d.of_nat(scaled);
                        d.ieq(borrowed, value)
                    },
                );
                let borrowed = d.sub_nat_nat(scaled_right, scaled_left);
                d.isymm(borrowed, value, located)
            },
        );
        (stmt, proof)
    })?;

    Ok(())
}
