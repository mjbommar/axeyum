//! Additive, multiplicative, subtraction, and finite-sum theorems.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Structural subtraction laws needed before subtraction can interact with
/// order. Both are kernel-checked consequences of the recursive definitions.
pub(super) fn declare_subtraction_theorems(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // succ_sub_succ : ∀ n m, sub (succ n) (succ m) = sub n m
    d.theorem(p.succ_sub_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let sx = d.succ(x);
            let lhs = d.sub(sn, sx);
            let rhs = d.sub(n, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| d.refl(n),
            &|d, j, ih| {
                let sn = d.succ(n);
                let sj = d.succ(j);
                let lhs = d.sub(sn, sj);
                let rhs = d.sub(n, j);
                d.congr(lhs, rhs, ih, &|d, x| d.pred(x))
            },
            m,
        );
        (stmt, proof)
    })?;

    // sub_self : ∀ n, sub n n = zero
    d.theorem(p.sub_self, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.sub(x, x);
            let zero = d.zero();
            d.eq(lhs, zero)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let start = d.sub(sj, sj);
                let middle = d.sub(j, j);
                let h1 = d.lemma(p.succ_sub_succ, &[j, j]);
                let zero = d.zero();
                let (_end, proof) = d.chain(start, &[(middle, h1), (zero, ih)]);
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `zero_add`, `succ_add`, `add_comm`, `add_assoc`, `add_right_comm`.
pub(super) fn declare_additive_theorems(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    // zero_add : ∀ n, add zero n = n   (induction on n)
    d.theorem(p.zero_add, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.add(z, x);
            d.eq(lhs, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                let z = d.zero();
                let lhs = d.add(z, j);
                d.congr(lhs, j, ih, &|d, x| d.succ(x))
            },
            n,
        );
        (stmt, proof)
    })?;

    // succ_add : ∀ n m, add (succ n) m = succ (add n m)   (induction on m)
    d.theorem(p.succ_add, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.add(sn, x);
            let inner = d.add(n, x);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let sn = d.succ(n);
                d.refl(sn)
            },
            &|d, j, ih| {
                let sn = d.succ(n);
                let lhs = d.add(sn, j);
                let inner = d.add(n, j);
                let rhs = d.succ(inner);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_comm : ∀ n m, add n m = add m n   (induction on m)
    d.theorem(p.add_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.add(n, x);
            let rhs = d.add(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let za = d.add(z, n);
                let h = d.lemma(p.zero_add, &[n]);
                d.symm(za, n, h)
            },
            &|d, j, ih| {
                let lhs = d.add(n, j);
                let rhs = d.add(j, n);
                let h1 = d.congr(lhs, rhs, ih, &|d, x| d.succ(x));
                let s_lhs = d.succ(lhs);
                let s_rhs = d.succ(rhs);
                let sj = d.succ(j);
                let sj_n = d.add(sj, n);
                let h_sa = d.lemma(p.succ_add, &[j, n]);
                let h2 = d.symm(sj_n, s_rhs, h_sa);
                d.trans(s_lhs, s_rhs, sj_n, h1, h2)
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_assoc : ∀ a b c, add (add a b) c = add a (add b c)   (induction on c)
    d.theorem(p.add_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.add(a, b);
            let lhs = d.add(ab, x);
            let bx = d.add(b, x);
            let rhs = d.add(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.add(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                let ab = d.add(a, b);
                let lhs = d.add(ab, j);
                let bj = d.add(b, j);
                let rhs = d.add(a, bj);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            c,
        );
        (stmt, proof)
    })?;

    // add_right_comm : ∀ x y z, add (add x y) z = add (add x z) y   (no induction)
    // Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md):
    // a pure ring-rearrangement chain (add_assoc/add_comm/add_assoc), now
    // searched for and emitted rather than hand-assembled. `ring`'s own
    // `sort_items` deliberately does NOT call `Nat.add_right_comm` (it
    // derives the same swap inline) so this declaration is not circular.
    crate::ring::nat::declare(d, &p, p.add_right_comm, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let xy = d.add(x, y);
        let lhs = d.add(xy, z);
        let xz = d.add(x, z);
        let rhs = d.add(xz, y);
        d.eq(lhs, rhs)
    })?;

    // succ_injective : ∀ n m, succ n = succ m → n = m
    // Applying the checked predecessor definition to both sides computes to
    // the desired equality; no constructor-disjointness axiom is involved.
    d.theorem(p.succ_injective, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let hyp_ty = d.eq(sn, sm);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.congr(sn, sm, h, &|d, x| d.pred(x));
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        let conclusion = d.eq(n, m);
        let stmt = d.arrow(hyp_ty, conclusion);
        (stmt, proof)
    })?;

    // add_right_cancel : ∀ n m k, n + k = m + k → n = m
    // Induction follows the argument on which `add` recurses.
    d.theorem(p.add_right_cancel, 3, &|d, v| {
        let (n, m, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let nx = d.add(n, x);
            let mx = d.add(m, x);
            let hyp = d.eq(nx, mx);
            let conclusion = d.eq(n, m);
            d.arrow(hyp, conclusion)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let hyp_ty = d.eq(n, m);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                d.lam_fv(h_fv, hyp_ty, h)
            },
            &|d, j, ih| {
                let nj = d.add(n, j);
                let mj = d.add(m, j);
                let snj = d.succ(nj);
                let smj = d.succ(mj);
                let hyp_ty = d.eq(snj, smj);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let stripped = d.lemma(p.succ_injective, &[nj, mj, h]);
                let body = d.apply(ih, &[stripped]);
                d.lam_fv(h_fv, hyp_ty, body)
            },
            k,
        );
        (stmt, proof)
    })?;

    // add_left_cancel : ∀ a b c, a + b = a + c → b = c
    // Commute the common operand to the right and reuse the inductive theorem.
    d.theorem(p.add_left_cancel, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.add(a, b);
        let ac = d.add(a, c);
        let hyp_ty = d.eq(ab, ac);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ba = d.add(b, a);
        let ca = d.add(c, a);
        let h1 = d.lemma(p.add_comm, &[b, a]);
        let h3 = d.lemma(p.add_comm, &[a, c]);
        let (_end, right_common) = d.chain(ba, &[(ab, h1), (ac, h), (ca, h3)]);
        let body = d.lemma(p.add_right_cancel, &[b, c, a, right_common]);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        let conclusion = d.eq(b, c);
        let stmt = d.arrow(hyp_ty, conclusion);
        (stmt, proof)
    })?;
    Ok(())
}

/// `zero_mul`, `succ_mul`, `mul_comm`, `mul_one`, `one_mul`, `left_distrib`,
/// `mul_assoc`.
pub(super) fn declare_multiplicative_theorems(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    // zero_mul : ∀ n, mul zero n = zero   (induction on n)
    d.theorem(p.zero_mul, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.mul(z, x);
            d.eq(lhs, z)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            // mul zero (succ j) ≡ add (mul zero j) zero ≡ mul zero j, so the
            // induction hypothesis *is* the step, up to definitional equality.
            &|_d, _j, ih| ih,
            n,
        );
        (stmt, proof)
    })?;

    // succ_mul : ∀ n m, mul (succ n) m = add (mul n m) m   (induction on m)
    d.theorem(p.succ_mul, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.mul(sn, x);
            let nm = d.mul(n, x);
            let rhs = d.add(nm, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ succ (add (mul (succ n) j) n) = succ (add (add (mul n j) n) j)
                let sn = d.succ(n);
                let snj = d.mul(sn, j);
                let start = d.add(snj, n);
                let nj = d.mul(n, j);
                let nj_j = d.add(nj, j);
                let s1 = d.add(nj_j, n);
                let h1 = d.congr(snj, nj_j, ih, &|d, t| d.add(t, n));
                let nj_n = d.add(nj, n);
                let s2 = d.add(nj_n, j);
                let h2 = d.lemma(p.add_right_comm, &[nj, j, n]);
                let (end, inner) = d.chain(start, &[(s1, h1), (s2, h2)]);
                d.congr(start, end, inner, &|d, t| d.succ(t))
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_comm : ∀ n m, mul n m = mul m n   (induction on m)
    d.theorem(p.mul_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.mul(n, x);
            let rhs = d.mul(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let zn = d.mul(z, n);
                let h = d.lemma(p.zero_mul, &[n]);
                d.symm(zn, z, h)
            },
            &|d, j, ih| {
                // goal ≡ add (mul n j) n = mul (succ j) n
                let nj = d.mul(n, j);
                let start = d.add(nj, n);
                let jn = d.mul(j, n);
                let s1 = d.add(jn, n);
                let h1 = d.congr(nj, jn, ih, &|d, t| d.add(t, n));
                let sj = d.succ(j);
                let s2 = d.mul(sj, n);
                let h_sm = d.lemma(p.succ_mul, &[j, n]);
                let h2 = d.symm(s2, s1, h_sm);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_one : ∀ a, mul a 1 = a
    // mul a (succ zero) ≡ add (mul a zero) a ≡ add zero a, so `zero_add a`
    // already has this type up to definitional equality.
    d.theorem(p.mul_one, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let lhs = d.mul(a, one);
        let stmt = d.eq(lhs, a);
        let proof = d.lemma(p.zero_add, &[a]);
        (stmt, proof)
    })?;

    // one_mul : ∀ a, mul 1 a = a
    d.theorem(p.one_mul, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let z = d.zero();
        let start = d.mul(one, a);
        let za = d.mul(z, a);
        let s1 = d.add(za, a);
        let h1 = d.lemma(p.succ_mul, &[z, a]);
        let s2 = d.add(z, a);
        let h_zm = d.lemma(p.zero_mul, &[a]);
        let h2 = d.congr(za, z, h_zm, &|d, t| d.add(t, a));
        let h3 = d.lemma(p.zero_add, &[a]);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (a, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    })?;

    // left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)  (ind. on c)
    d.theorem(p.left_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let bx = d.add(b, x);
            let lhs = d.mul(a, bx);
            let ab = d.mul(a, b);
            let ax = d.mul(a, x);
            let rhs = d.add(ab, ax);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.mul(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                // goal ≡ add (mul a (add b j)) a = add (mul a b) (add (mul a j) a)
                let bj = d.add(b, j);
                let a_bj = d.mul(a, bj);
                let start = d.add(a_bj, a);
                let ab = d.mul(a, b);
                let aj = d.mul(a, j);
                let ab_aj = d.add(ab, aj);
                let s1 = d.add(ab_aj, a);
                let h1 = d.congr(a_bj, ab_aj, ih, &|d, t| d.add(t, a));
                let aj_a = d.add(aj, a);
                let s2 = d.add(ab, aj_a);
                let h2 = d.lemma(p.add_assoc, &[ab, aj, a]);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;

    // right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
    // Derive the right-handed law from commutativity and left distribution.
    //
    // NOT a `crate::ring::nat` retirement target, deliberately: `ring`'s own
    // `Problem::distribute` USES `right_distrib` as a primitive lemma to
    // distribute a multi-summand sum over a product (`docs/plan/status/
    // 460-ring-tactic-1.md`) — routing this declaration through the
    // producer would try to prove `right_distrib` from itself and fails
    // with `KernelError::UnknownConst` (the name does not exist yet at this
    // point in prelude construction). `left_distrib` and `right_distrib`
    // are foundational to the producer, not identities it can retire.
    d.theorem(p.right_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let sum = d.add(a, b);
        let start = d.mul(sum, c);
        let commuted = d.mul(c, sum);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let distributed = d.add(ca, cb);
        let ac = d.mul(a, c);
        let bc = d.mul(b, c);
        let target = d.add(ac, bc);
        let h1 = d.lemma(p.mul_comm, &[sum, c]);
        let h2 = d.lemma(p.left_distrib, &[c, a, b]);
        let ca_to_ac = d.lemma(p.mul_comm, &[c, a]);
        let h3 = d.congr(ca, ac, ca_to_ac, &|d, value| d.add(value, cb));
        let cb_to_bc = d.lemma(p.mul_comm, &[c, b]);
        let h4 = d.congr(cb, bc, cb_to_bc, &|d, value| d.add(ac, value));
        let partly_commuted = d.add(ac, cb);
        let (_, proof) = d.chain(
            start,
            &[
                (commuted, h1),
                (distributed, h2),
                (partly_commuted, h3),
                (target, h4),
            ],
        );
        (d.eq(start, target), proof)
    })?;

    // mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)   (induction on c)
    d.theorem(p.mul_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.mul(a, b);
            let lhs = d.mul(ab, x);
            let bx = d.mul(b, x);
            let rhs = d.mul(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ add (mul (mul a b) j) (mul a b) = mul a (add (mul b j) b)
                let ab = d.mul(a, b);
                let abj = d.mul(ab, j);
                let start = d.add(abj, ab);
                let bj = d.mul(b, j);
                let a_bj = d.mul(a, bj);
                let s1 = d.add(a_bj, ab);
                let h1 = d.congr(abj, a_bj, ih, &|d, t| d.add(t, ab));
                let bj_b = d.add(bj, b);
                let s2 = d.mul(a, bj_b);
                let h_ld = d.lemma(p.left_distrib, &[a, bj, b]);
                let h2 = d.symm(s2, s1, h_ld);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;

    // pow_add : ∀ a m n, a^(m+n) = a^m * a^n   (induction on n)
    //
    // Closes fact `F:nat-pow-add`. The ledger chose it: its `depends_on`
    // (`F:nat-mul-assoc`, `F:nat-mul-comm`) were already settled, which is the
    // self-extension loop picking its own next goal rather than a person doing it.
    //
    // Both cases lean on the definitional equations rather than on rewriting,
    // because `add` and `pow` recurse on their SECOND argument:
    //   base  `add m zero ≡ m` and `pow a zero ≡ 1`, so the goal is
    //         `a^m = a^m * 1` — exactly `mul_one` reversed;
    //   step  `add m (succ j) ≡ succ (add m j)` and
    //         `pow a (succ x) ≡ (a^x) * a`, so the goal already reads
    //         `a^(m+j) * a = a^m * a^(succ j)` with no rewriting needed to get
    //         there, and the chain is IH, associativity, then `pow_succ` back.
    d.theorem(p.pow_add, 3, &|d, v| {
        let (a, m, n) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sum = d.add(m, x);
            let lhs = d.pow(a, sum);
            let pow_m = d.pow(a, m);
            let pow_x = d.pow(a, x);
            let rhs = d.mul(pow_m, pow_x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                // `a^(m+0)` and `a^0` both compute, leaving `a^m = a^m * 1`.
                let pow_m = d.pow(a, m);
                let one = {
                    let zero = d.zero();
                    d.succ(zero)
                };
                let product = d.mul(pow_m, one);
                // `mul_one` reads `a^m * 1 = a^m`, so the symm runs from the
                // PRODUCT; passing these the other way round is a TypeMismatch.
                let h = d.lemma(p.mul_one, &[pow_m]);
                d.symm(product, pow_m, h)
            },
            &|d, j, ih| {
                let pow_m = d.pow(a, m);
                let pow_j = d.pow(a, j);
                let sum_mj = d.add(m, j);
                let pow_sum = d.pow(a, sum_mj);
                // `a^(m + succ j)` computes to `a^(m+j) * a`.
                let start = d.mul(pow_sum, a);
                let ih_applied = d.mul(pow_m, pow_j);
                let after_ih = d.mul(ih_applied, a);
                let h_ih = d.congr(pow_sum, ih_applied, ih, &|d, t| d.mul(t, a));
                let inner = d.mul(pow_j, a);
                let associated = d.mul(pow_m, inner);
                let h_assoc = d.lemma(p.mul_assoc, &[pow_m, pow_j, a]);
                let succ_j = d.succ(j);
                let pow_succ_j = d.pow(a, succ_j);
                let end = d.mul(pow_m, pow_succ_j);
                let h_pow = d.lemma(p.pow_succ, &[a, j]);
                let h_pow_rev = d.symm(pow_succ_j, inner, h_pow);
                let h_end = d.congr(inner, pow_succ_j, h_pow_rev, &|d, t| d.mul(pow_m, t));
                let (_, proof) = d.chain(
                    start,
                    &[(after_ih, h_ih), (associated, h_assoc), (end, h_end)],
                );
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.mul_eq_zero` — `ℕ` has no zero divisors.
///
/// Called *after* `declare_no_confusion` (not from inside
/// [`declare_multiplicative_theorems`], where `mul`/`succ_mul`/`add_succ` are
/// available but `Nat.succ_ne_zero` is not yet declared): the contradiction
/// branch below needs `succ_ne_zero`.
///
/// A constructor case-split on both factors, not full induction (the
/// induction hypotheses are built but never used): at `a = 0` the left
/// disjunct is immediate; at `a = succ x`, case on `b`; at `b = 0` the right
/// disjunct is immediate; at `b = succ y` the product is `succ_mul` then
/// `add_succ` away from a bare successor, which `succ_ne_zero` refutes
/// against the `a * b = 0` hypothesis.
pub(super) fn declare_mul_no_zero_divisors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mul_eq_zero : ∀ a b, mul a b = 0 → a = 0 ∨ b = 0
    d.theorem(p.mul_eq_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);

        let conclusion = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let zero = d.zero();
            let left = d.eq(x, zero);
            let zero = d.zero();
            let right = d.eq(y, zero);
            d.const_app(p.logic.or, &[left, right])
        };

        let stmt = {
            let zero = d.zero();
            let product = d.mul(a, b);
            let hyp = d.eq(product, zero);
            let goal = conclusion(d, a, b);
            d.arrow(hyp, goal)
        };

        // The motive for the outer case-split on `a`, closing over `b`.
        let claim_a = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let product = d.mul(x, b);
            let hyp = d.eq(product, zero);
            let goal = conclusion(d, x, b);
            d.arrow(hyp, goal)
        };

        let at_zero_a = |d: &mut NatDev<'_>| {
            let h_fv = d.fresh_fvar();
            let zero = d.zero();
            let product = d.mul(zero, b);
            let zero2 = d.zero();
            let hyp_ty = d.eq(product, zero2);
            let zero3 = d.zero();
            let left = d.eq(zero3, zero3);
            let right = d.eq(b, zero3);
            let refl = d.refl(zero3);
            let body = d.const_app(p.logic.or_inl, &[left, right, refl]);
            d.lam_fv(h_fv, hyp_ty, body)
        };

        let at_succ_a = |d: &mut NatDev<'_>, x: ExprId, _ih: ExprId| {
            // The motive for the inner case-split on `b`, closing over the
            // predecessor `x` bound by the outer step.
            let claim_b = |d: &mut NatDev<'_>, y: ExprId| {
                let zero = d.zero();
                let sx = d.succ(x);
                let product = d.mul(sx, y);
                let hyp = d.eq(product, zero);
                let goal = conclusion(d, sx, y);
                d.arrow(hyp, goal)
            };

            let at_zero_b = |d: &mut NatDev<'_>| {
                let h_fv = d.fresh_fvar();
                let sx = d.succ(x);
                let zero = d.zero();
                let product = d.mul(sx, zero);
                let zero2 = d.zero();
                let hyp_ty = d.eq(product, zero2);
                let zero3 = d.zero();
                let left = d.eq(sx, zero3);
                let right = d.eq(zero3, zero3);
                let refl = d.refl(zero3);
                let body = d.const_app(p.logic.or_inr, &[left, right, refl]);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            let at_succ_b = |d: &mut NatDev<'_>, y: ExprId, _ih: ExprId| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let sx = d.succ(x);
                let sy = d.succ(y);
                let product = d.mul(sx, sy);
                let zero = d.zero();
                let hyp_ty = d.eq(product, zero);
                let goal = conclusion(d, sx, sy);

                // `mul (succ x) (succ y) = succ (add (mul x (succ y)) y)`,
                // via `succ_mul` then `add_succ`.
                let scaled = d.mul(x, sy);
                let expanded = d.add(scaled, sy);
                let step1 = d.lemma(p.succ_mul, &[x, sy]);
                let inner_sum = d.add(scaled, y);
                let bumped = d.succ(inner_sum);
                let step2 = d.lemma(p.add_succ, &[scaled, y]);
                let (_last, chained) = d.chain(product, &[(expanded, step1), (bumped, step2)]);
                let flipped = d.symm(product, bumped, chained);
                let zero2 = d.zero();
                let located = d.trans(bumped, product, zero2, flipped, h);
                let contradiction = d.lemma(p.succ_ne_zero, &[inner_sum, located]);

                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let level = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
                let anon = d.anon_name();
                let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
                let body = d.apply(rec, &[motive, contradiction]);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            d.induct(&claim_b, &at_zero_b, &at_succ_b, b)
        };

        let proof = d.induct(&claim_a, &at_zero_a, &at_succ_a, a);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_eq_zero` — the additive twin of [`declare_mul_no_zero_divisors`].
///
/// Built for `nat-assoc-dichotomy`'s `land_aux_assoc_of_fuel` attempt
/// (`docs/plan/status/247-nat-bitwise-assoc.md`): the successor row of
/// `landAux`/`lorAux`/`ldiffAux` is `2 * rec + bit`, and deciding whether
/// that COMPOUND value is zero (needed once it appears in an ARGUMENT
/// position of an outer application, where the outer guard cannot resolve
/// by mere unfolding) needs `2 * rec = 0 ∧ bit = 0` from this lemma, then
/// `rec = 0` from the ALREADY-EXISTING `Nat.mul_eq_zero` (eliminating the
/// `2 = 0` disjunct inline via `Nat.succ_ne_zero` — no
/// `mul_eq_zero_of_left`/`eq_zero_of_mul_eq_zero`-style lemma is needed on
/// top of `mul_eq_zero`, contrary to one reading of that status doc's item
/// 1: `mul_eq_zero` alone, plus the one-line disjunct elimination, already
/// gets you from `mul 2 x = 0` to `x = 0`).
///
/// Unlike `mul_eq_zero`'s nested case-split on BOTH factors, this is a
/// single [`cases_zero_succ`] on `b` alone, because `Nat.add` recurses on
/// its RIGHT argument only: at `b = 0`, `add a 0` is defeq to `a`, so the
/// hypothesis `Eq (add a 0) 0` already HAS the shape `Eq a 0` (no rewriting
/// needed, `h` is reused directly at the left conjunct); at `b = succ y`,
/// `add a (succ y)` is defeq to `succ (add a y)` in a SINGLE iota step (no
/// `succ_mul`/`add_succ`-style bridging lemma needed, unlike `mul_eq_zero`'s
/// succ/succ leaf), so `h` is reused directly as the argument
/// `Nat.succ_ne_zero` needs.
pub(super) fn declare_add_no_zero_summands(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // add_eq_zero : ∀ a b, add a b = 0 → a = 0 ∧ b = 0
    d.theorem(p.add_eq_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);

        let conclusion = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let zero = d.zero();
            let left = d.eq(x, zero);
            let zero = d.zero();
            let right = d.eq(y, zero);
            d.const_app(p.logic.and, &[left, right])
        };

        let stmt = {
            let zero = d.zero();
            let sum = d.add(a, b);
            let hyp = d.eq(sum, zero);
            let goal = conclusion(d, a, b);
            d.arrow(hyp, goal)
        };

        // The motive for the case-split on `b`, closing over `a`.
        let claim_b = |d: &mut NatDev<'_>, y: ExprId| {
            let zero = d.zero();
            let sum = d.add(a, y);
            let hyp = d.eq(sum, zero);
            let goal = conclusion(d, a, y);
            d.arrow(hyp, goal)
        };

        let at_zero = |d: &mut NatDev<'_>| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zero = d.zero();
            let sum = d.add(a, zero); // defeq `a`
            let hyp_ty = d.eq(sum, zero);
            let left_ty = d.eq(a, zero);
            let zero2 = d.zero();
            let right_ty = d.eq(zero2, zero2);
            let refl_right = d.refl(zero2);
            // `h : Eq (add a 0) 0` is defeq to `Eq a 0` (add's base row is
            // the constant identity), so `h` is accepted directly where
            // `left_ty` is expected -- no rewrite step.
            let body = d.const_app(p.logic.and_intro, &[left_ty, right_ty, h, refl_right]);
            d.lam_fv(h_fv, hyp_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, y: ExprId| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let sy = d.succ(y);
            let sum = d.add(a, sy);
            let zero = d.zero();
            let hyp_ty = d.eq(sum, zero);
            let goal = conclusion(d, a, sy);

            // `sum` is defeq to `succ (add a y)` in one iota step, so `h`
            // (typed `Eq sum zero`) is accepted directly as the witness
            // `succ_ne_zero` needs -- no `add_succ` bridging lemma.
            let inner_sum = d.add(a, y);
            let contradiction = d.lemma(p.succ_ne_zero, &[inner_sum, h]);

            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let level = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam_fv(h_fv, hyp_ty, body)
        };

        let proof = cases_zero_succ(d, b, &claim_b, &at_zero, &at_succ);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.zero_or_succ` — see [`NatPrelude::zero_or_succ`]'s doc for why this
/// is stated as an equational `Or`-fact rather than left as bare
/// [`cases_zero_succ`] elimination: `d.lemma(p.zero_or_succ, &[x])` gives a
/// disjunction fact naming `x` (any term, not just a bound variable), which
/// `or_elim` then consumes without disturbing `x`'s own formula.
///
/// Proved by [`cases_zero_succ`] on a FRESH bound `n`: at `n = 0`, `Or_inl`
/// with `Eq.refl 0`; at `n = succ pred`, `Or_inr` with
/// `exists_intro pred (Eq.refl (succ pred))` — the witness `pred` IS the
/// predecessor `cases_zero_succ` exposes, and `succ pred` is trivially
/// `Eq.refl`-equal to the candidate the outer motive substituted.
pub(super) fn declare_zero_or_succ(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let level_one = d.level_one();

    // exists_pred(target) : Nat -> Prop := fun pred => Eq target (succ pred)
    let exists_pred = |d: &mut NatDev<'_>, nat: ExprId, target: ExprId| -> ExprId {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let succ_pred = d.succ(pred);
        let body = d.eq(target, succ_pred);
        d.lam_fv(pred_fv, nat, body)
    };

    // conclusion(target) : Or (Eq target 0) (Exists Nat (exists_pred target))
    let conclusion =
        |d: &mut NatDev<'_>, nat: ExprId, level_one: crate::LevelId, target: ExprId| -> ExprId {
            let zero = d.zero();
            let left = d.eq(target, zero);
            let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let predicate = exists_pred(d, nat, target);
            let right = d.apply(exists_const, &[nat, predicate]);
            d.const_app(p.logic.or, &[left, right])
        };

    d.theorem(p.zero_or_succ, 1, &|d, v| {
        let n = v[0];

        let motive = |d: &mut NatDev<'_>, target: ExprId| conclusion(d, nat, level_one, target);
        let stmt = motive(d, n);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let left = d.eq(zero, zero);
            let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let predicate = exists_pred(d, nat, zero);
            let right = d.apply(exists_const, &[nat, predicate]);
            let refl = d.refl(zero);
            d.const_app(p.logic.or_inl, &[left, right, refl])
        };

        let at_succ = |d: &mut NatDev<'_>, pred: ExprId| -> ExprId {
            let succ_pred = d.succ(pred);
            let zero = d.zero();
            let left = d.eq(succ_pred, zero);
            let predicate = exists_pred(d, nat, succ_pred);
            let exists_const = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let right = d.apply(exists_const, &[nat, predicate]);
            let refl = d.refl(succ_pred);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            let witness_proof = d.apply(intro, &[nat, predicate, pred, refl]);
            d.const_app(p.logic.or_inr, &[left, right, witness_proof])
        };

        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;
    Ok(())
}

/// The first reusable finite-sum algebra needed by the Rado sharpness proof.
/// This is a checked theorem over [`NatPrelude::sum_range`], not a specialized
/// test-only recurrence.
pub(super) fn declare_finite_sum_theorems(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // sumRange_congr : ∀ f g n,
    //   (∀ i, f i = g i) → sumRange f n = sumRange g n
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let gi = d.apply(g, &[i]);
            let eq = d.eq(fi, gi);
            d.pi_fv(i_fv, nat, eq)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.sum_range(f, x);
            let rhs = d.sum_range(g, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let f_prior = d.sum_range(f, j);
                let g_prior = d.sum_range(g, j);
                let fj = d.apply(f, &[j]);
                let gj = d.apply(g, &[j]);
                let start = d.add(f_prior, fj);
                let mid = d.add(g_prior, fj);
                let h1 = d.congr(f_prior, g_prior, ih, &|d, t| d.add(t, fj));
                let end = d.add(g_prior, gj);
                let pointwise_j = d.apply(h, &[j]);
                let h2 = d.congr(fj, gj, pointwise_j, &|d, t| d.add(g_prior, t));
                let (_, proof) = d.chain(start, &[(mid, h1), (end, h2)]);
                proof
            },
            n,
        );
        let ty = {
            let with_h = d.pi_fv(h_fv, pointwise, stmt);
            let over_n = d.pi_fv(n_fv, nat, with_h);
            let over_g = d.pi_fv(g_fv, fn_ty, over_n);
            d.pi_fv(f_fv, fn_ty, over_g)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, pointwise, proof);
            let over_n = d.lam_fv(n_fv, nat, with_h);
            let over_g = d.lam_fv(g_fv, fn_ty, over_n);
            d.lam_fv(f_fv, fn_ty, over_g)
        };
        d.declare_theorem(p.sum_range_congr, ty, value)?;
    }

    // mul_sumRange : ∀ a f n,
    //   a * sumRange f n = sumRange (fun i => a * f i) n
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let scaled_fn = |d: &mut NatDev<'_>| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let body = d.mul(a, fi);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs_sum = d.sum_range(f, x);
            let lhs = d.mul(a, lhs_sum);
            let scaled = scaled_fn(d);
            let rhs = d.sum_range(scaled, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let prior = d.sum_range(f, j);
                let fj = d.apply(f, &[j]);
                let extended = d.add(prior, fj);
                let start = d.mul(a, extended);
                let a_prior = d.mul(a, prior);
                let a_fj = d.mul(a, fj);
                let distributed = d.add(a_prior, a_fj);
                let h1 = d.lemma(p.left_distrib, &[a, prior, fj]);
                let scaled = scaled_fn(d);
                let scaled_prior = d.sum_range(scaled, j);
                let end = d.add(scaled_prior, a_fj);
                let h2 = d.congr(a_prior, scaled_prior, ih, &|d, t| d.add(t, a_fj));
                let (_, proof) = d.chain(start, &[(distributed, h1), (end, h2)]);
                proof
            },
            n,
        );
        let ty = {
            let over_n = d.pi_fv(n_fv, nat, stmt);
            let over_f = d.pi_fv(f_fv, fn_ty, over_n);
            d.pi_fv(a_fv, nat, over_f)
        };
        let value = {
            let over_n = d.lam_fv(n_fv, nat, proof);
            let over_f = d.lam_fv(f_fv, fn_ty, over_n);
            d.lam_fv(a_fv, nat, over_f)
        };
        d.declare_theorem(p.mul_sum_range, ty, value)?;
    }

    d.theorem(p.mul_sum_range_pow, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let power_fn = |d: &mut NatDev<'_>, shifted: bool| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let exponent = if shifted { d.succ(i) } else { i };
            let body = d.pow(a, exponent);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let unshifted = power_fn(d, false);
            let shifted = power_fn(d, true);
            let sum = d.sum_range(unshifted, x);
            let lhs = d.mul(a, sum);
            let rhs = d.sum_range(shifted, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let unshifted = power_fn(d, false);
                let shifted = power_fn(d, true);
                let sum = d.sum_range(unshifted, j);
                let shifted_sum = d.sum_range(shifted, j);
                let power = d.pow(a, j);
                let start = {
                    let extended = d.add(sum, power);
                    d.mul(a, extended)
                };
                let a_sum = d.mul(a, sum);
                let a_power = d.mul(a, power);
                let distributed = d.add(a_sum, a_power);
                let h1 = d.lemma(p.left_distrib, &[a, sum, power]);
                let with_ih = d.add(shifted_sum, a_power);
                let h2 = d.congr(a_sum, shifted_sum, ih, &|d, t| d.add(t, a_power));
                let power_a = d.mul(power, a);
                let commuted = d.add(shifted_sum, power_a);
                let h_comm = d.lemma(p.mul_comm, &[a, power]);
                let h3 = d.congr(a_power, power_a, h_comm, &|d, t| d.add(shifted_sum, t));
                let successor_power = {
                    let sj = d.succ(j);
                    d.pow(a, sj)
                };
                let end = d.add(shifted_sum, successor_power);
                let h_pow = d.lemma(p.pow_succ, &[a, j]);
                let h_pow_rev = d.symm(successor_power, power_a, h_pow);
                let h4 = d.congr(power_a, successor_power, h_pow_rev, &|d, t| {
                    d.add(shifted_sum, t)
                });
                let (_, proof) = d.chain(
                    start,
                    &[(distributed, h1), (with_ih, h2), (commuted, h3), (end, h4)],
                );
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}
