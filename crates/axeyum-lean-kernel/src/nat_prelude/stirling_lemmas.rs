//! The equation and boundary theory of [`stirling`](super::stirling)'s
//! `Nat.stirlingFirst`/`Nat.stirlingSecond` — the ten
//! `Mathlib.Combinatorics.Enumerative.Stirling` mirrors that ADR-1100 opened
//! the vocabulary for and, per ADR-0653, deliberately declared nothing about.
//!
//! # Why these mirrors flip honestly
//!
//! The criterion is the def-vs-theorem one: *if Mathlib's `def` is the same
//! function, the mirror is our statement; if our definitional body is
//! Mathlib's theorem about a structurally different `def`, it stays open.*
//! Read at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
//! `Mathlib/Combinatorics/Enumerative/Stirling.lean:51` and `:113`:
//!
//! ```text
//! def stirlingFirst : ℕ → ℕ → ℕ        def stirlingSecond : ℕ → ℕ → ℕ
//!   | 0, 0 => 1                          | 0, 0 => 1
//!   | 0, _ + 1 => 0                      | 0, _ + 1 => 0
//!   | _ + 1, 0 => 0                      | _ + 1, 0 => 0
//!   | n + 1, k + 1 =>                    | n + 1, k + 1 =>
//!       n * stirlingFirst n (k + 1)          (k + 1) * stirlingSecond n (k + 1)
//!         + stirlingFirst n k                  + stirlingSecond n k
//! ```
//!
//! That is [`super::stirling`]'s body verbatim, and the equation compiler
//! produces exactly our shape: an outer recursion on the first argument
//! yielding a whole row, an inner one selecting the column. Mathlib itself
//! proves `stirlingFirst_zero`, `stirlingFirst_zero_succ`,
//! `stirlingFirst_succ_zero` and `stirlingFirst_succ_succ` by **`rfl`**, which
//! is the check that the four defining equations are definitional on its side
//! as well as ours. This is the opposite situation to `Nat.multichoose`, where
//! our body is Mathlib's *theorem* about a differently-built `def` and the
//! mirrors must stay open.
//!
//! # What each proof costs
//!
//! Four of the ten are `Eq.refl`: our recursor reduces at a literal `0` or a
//! `succ` constructor in either position, so
//! `stirlingFirst (n+1) (k+1) ≡ n * stirlingFirst n (k+1) + stirlingFirst n k`
//! holds by δβι and needs no equation lemma.
//!
//! The other six all route through one shape, and it is [`super::choose`]'s
//! `choose_eq_zero_of_lt` shape: induction on the row index with an inner
//! **case split** (not induction) on the column, where the `k = 0` arm is
//! vacuous (`Nat.not_succ_le_zero` / `Nat.lt_irrefl`) and the `k = succ k'`
//! arm strips one `succ` off the hypothesis with `le_of_succ_le_succ` /
//! `le_succ_of_le` to reach the outer hypothesis at **two** columns.
//! `stirlingFirst`/`stirlingSecond` differ only in the recursive column's
//! coefficient, which is `mul_zero`'d away in both cases — so
//! [`declare_eq_zero_of_lt`] is written once and instantiated twice.
//!
//! # The three operand orders that decide whether a term reduces
//!
//! * `Nat.add` recurses on its RIGHT argument, so `add X zero ≡ X` while
//!   `add zero X` is stuck. Every `stirling _ (n+1) 0 ≡ 0` collapse used here
//!   is the first form, and the `zero` produced by `mul_zero` always lands in
//!   the LEFT slot where it does not reduce — which is why the chains below
//!   end on a literal (`Eq.refl 0` / `Eq.refl 1`) rather than on `zero_add`.
//! * `Nat.mul` recurses on its RIGHT argument, so `mul c zero ≡ zero` is free
//!   but `mul c (succ zero)` is NOT `c`; `mul_one` is a real theorem and
//!   `stirlingFirst_succ_self_left` has to use it.
//! * `Nat.factorial (succ n) ≡ factorial n * succ n` — the multiplication is
//!   the OPPOSITE order from Mathlib's `Nat.factorial_succ`, so
//!   `stirlingFirst_one_right` needs one `mul_comm` that Mathlib's proof does
//!   not.
//!
//! Nothing here forms a numeral larger than `2`, so the unary-numeral cost
//! `CLAUDE.md` documents never comes into play.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::{ExprId, NameId};

/// Which of the two triangles a shared proof is being built for. The two
/// definitions differ ONLY in the recursive column's coefficient, so every
/// proof that multiplies that coefficient by a zero is identical.
#[derive(Clone, Copy)]
enum Kind {
    /// `Nat.stirlingFirst` — coefficient is the row predecessor `n`.
    First,
    /// `Nat.stirlingSecond` — coefficient is the column index `k + 1`.
    Second,
}

/// `Nat.stirlingFirst n k` / `Nat.stirlingSecond n k`.
fn value_at(d: &mut NatDev<'_>, name: NameId, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(name, &[n, k])
}

/// `False.rec` into `goal` — the two vacuous `k = 0` arms below.
fn absurd(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// The four defining equations, one `Eq.refl` each.
///
/// Each is `Eq.refl` at the RIGHT-hand side and the kernel closes the
/// declaration by reducing the left: the recursor's scrutinee is a literal
/// `0` or a `succ` in both positions, so no argument is ever stuck.
fn declare_defining_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let first = p.stirling_first;

    // stirlingFirst_zero : stirlingFirst 0 0 = 1
    {
        let zero = d.zero();
        let lhs = value_at(d, first, zero, zero);
        let one = d.num(1);
        let ty = d.eq(lhs, one);
        let value = d.refl(one);
        d.declare_theorem(p.stirling_first_zero, ty, value)?;
    }

    // stirlingFirst_zero_succ : ∀ k, stirlingFirst 0 (succ k) = 0
    d.theorem(p.stirling_first_zero_succ, 1, &|d, v| {
        let k = v[0];
        let zero = d.zero();
        let sk = d.succ(k);
        let lhs = value_at(d, first, zero, sk);
        let rhs = d.zero();
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;

    // stirlingFirst_succ_zero : ∀ n, stirlingFirst (succ n) 0 = 0
    d.theorem(p.stirling_first_succ_zero, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let zero = d.zero();
        let lhs = value_at(d, first, sn, zero);
        let rhs = d.zero();
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;

    // stirlingFirst_succ_succ :
    //   ∀ n k, stirlingFirst (succ n) (succ k)
    //            = n * stirlingFirst n (succ k) + stirlingFirst n k
    d.theorem(p.stirling_first_succ_succ, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sn = d.succ(n);
        let sk = d.succ(k);
        let lhs = value_at(d, first, sn, sk);
        let at_sk = value_at(d, first, n, sk);
        let at_k = value_at(d, first, n, k);
        let scaled = d.mul(n, at_sk);
        let rhs = d.add(scaled, at_k);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;

    Ok(())
}

/// `stirling{First,Second}_eq_zero_of_lt : ∀ n k, Lt n k → stirling n k = 0`.
///
/// Induction on `n`; inside each arm a `Nat.rec` on `k` used only to expose
/// its SHAPE (the motive is the arrow `Lt _ k → _`, so each branch
/// re-introduces its own specialized hypothesis). The `n = succ m`,
/// `k = succ k'` leaf is the only real step: `h : Lt (succ m) (succ k')` is
/// `Le (succ (succ m)) (succ k')`, so `le_of_succ_le_succ` gives `Lt m k'` and
/// `le_succ_of_le` gives `Lt m (succ k')`, hitting the outer hypothesis at
/// both columns the recursive equation mentions.
fn declare_eq_zero_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    kind: Kind,
) -> Result<(), KernelError> {
    let p = *p;
    let (name, theorem_name) = match kind {
        Kind::First => (p.stirling_first, p.stirling_first_eq_zero_of_lt),
        Kind::Second => (p.stirling_second, p.stirling_second_eq_zero_of_lt),
    };
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.lt(n, k);
        let lhs = value_at(d, name, n, k);
        let zero = d.zero();
        let eqn = d.eq(lhs, zero);
        let body = d.arrow(hyp, eqn);
        d.pi_fv(k_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt_n = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            // n = 0
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let zero = d.zero();
                let hyp = d.lt(zero, x);
                let lhs = value_at(d, name, zero, x);
                let zero2 = d.zero();
                let eqn = d.eq(lhs, zero2);
                d.arrow(hyp, eqn)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    // Lt 0 0 is refuted by lt_irrefl.
                    let zero = d.zero();
                    let hyp_ty = d.lt(zero, zero);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let irrefl = d.lemma(p.lt_irrefl, &[zero]);
                    let false_proof = d.apply(irrefl, &[h]);
                    let goal = {
                        let lhs = value_at(d, name, zero, zero);
                        let zero2 = d.zero();
                        d.eq(lhs, zero2)
                    };
                    let body = absurd(d, &p, goal, false_proof);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    // stirling 0 (succ k') ≡ 0 by ι-reduction; the hypothesis
                    // is not consulted.
                    let sk = d.succ(k_prime);
                    let zero = d.zero();
                    let hyp_ty = d.lt(zero, sk);
                    let h_fv = d.fresh_fvar();
                    let rhs = d.zero();
                    let body = d.refl(rhs);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        &|d, m, ih| {
            // n = succ m
            let sm = d.succ(m);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let hyp = d.lt(sm, x);
                let lhs = value_at(d, name, sm, x);
                let zero = d.zero();
                let eqn = d.eq(lhs, zero);
                d.arrow(hyp, eqn)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| {
                    // Lt (succ m) 0 is refuted by not_succ_le_zero.
                    let zero = d.zero();
                    let hyp_ty = d.lt(sm, zero);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let not_le = d.lemma(p.not_succ_le_zero, &[sm]);
                    let false_proof = d.apply(not_le, &[h]);
                    let goal = {
                        let lhs = value_at(d, name, sm, zero);
                        let zero2 = d.zero();
                        d.eq(lhs, zero2)
                    };
                    let body = absurd(d, &p, goal, false_proof);
                    d.lam_fv(h_fv, hyp_ty, body)
                },
                &|d, k_prime, _inner_ih| {
                    let sk = d.succ(k_prime);
                    let hyp_ty = d.lt(sm, sk);
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    // h : Le (succ (succ m)) (succ k') ≡ Lt (succ m) (succ k')
                    let h_k = d.lemma(p.le_of_succ_le_succ, &[sm, k_prime, h]);
                    let ih_k = d.apply(ih, &[k_prime, h_k]);
                    let h_sk = d.lemma(p.le_succ_of_le, &[sm, k_prime, h_k]);
                    let ih_sk = d.apply(ih, &[sk, h_sk]);

                    let at_sk = value_at(d, name, m, sk);
                    let at_k = value_at(d, name, m, k_prime);
                    let coefficient = match kind {
                        Kind::First => m,
                        Kind::Second => sk,
                    };
                    let zero = d.zero();

                    // add (coeff * at_sk) at_k
                    //   → add (coeff * 0) at_k → add (coeff * 0) 0 → 0
                    let scaled = d.mul(coefficient, at_sk);
                    let start = d.add(scaled, at_k);
                    let step_one = d.congr(at_sk, zero, ih_sk, &|d, x| {
                        let scaled = d.mul(coefficient, x);
                        d.add(scaled, at_k)
                    });
                    let mid_one = {
                        let scaled = d.mul(coefficient, zero);
                        d.add(scaled, at_k)
                    };
                    let step_two = d.congr(at_k, zero, ih_k, &|d, x| {
                        let scaled = d.mul(coefficient, zero);
                        d.add(scaled, x)
                    });
                    let mid_two = {
                        let scaled = d.mul(coefficient, zero);
                        d.add(scaled, zero)
                    };
                    // `mul c 0 ≡ 0` and `add 0 0 ≡ 0`, both by ι.
                    let step_three = d.refl(zero);
                    let (_end, final_) = d.chain(
                        start,
                        &[
                            (mid_one, step_one),
                            (mid_two, step_two),
                            (zero, step_three),
                        ],
                    );
                    d.lam_fv(h_fv, hyp_ty, final_)
                },
                k,
            );
            d.lam_fv(k_fv, nat, k_cases)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt_n);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(theorem_name, ty, value)?;
    Ok(())
}

/// `stirlingFirst_self : ∀ n, stirlingFirst n n = 1`.
///
/// Induction on `n`. The step is
/// `stirlingFirst (n+1) (n+1) ≡ n * stirlingFirst n (n+1) + stirlingFirst n n`,
/// where the first summand's factor dies by [`declare_eq_zero_of_lt`] at
/// `n < n+1` and the second is the hypothesis. The residue `add (n * 0) 1`
/// reduces to `1` by ι alone — `add`'s right recursion carries the `succ` out
/// and `mul c 0` collapses — so the chain closes on `Eq.refl 1` rather than
/// needing `zero_add`.
fn declare_stirling_first_self(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let first = p.stirling_first;
    d.theorem(p.stirling_first_self, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let lhs = value_at(d, first, x, x);
            let one = d.num(1);
            d.eq(lhs, one)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let one = d.num(1);
                d.refl(one)
            },
            &|d, m, ih| {
                let sm = d.succ(m);
                let lt = d.lemma(p.lt_succ_self, &[m]);
                let vanishes = d.lemma(p.stirling_first_eq_zero_of_lt, &[m, sm, lt]);
                let at_sm = value_at(d, first, m, sm);
                let at_m = value_at(d, first, m, m);
                let zero = d.zero();
                let one = d.num(1);

                let scaled = d.mul(m, at_sm);
                let start = d.add(scaled, at_m);
                let step_one = d.congr(at_sm, zero, vanishes, &|d, x| {
                    let scaled = d.mul(m, x);
                    d.add(scaled, at_m)
                });
                let mid_one = {
                    let scaled = d.mul(m, zero);
                    d.add(scaled, at_m)
                };
                let step_two = d.congr(at_m, one, ih, &|d, x| {
                    let scaled = d.mul(m, zero);
                    d.add(scaled, x)
                });
                let mid_two = {
                    let scaled = d.mul(m, zero);
                    d.add(scaled, one)
                };
                let step_three = d.refl(one);
                let (_end, final_) = d.chain(
                    start,
                    &[(mid_one, step_one), (mid_two, step_two), (one, step_three)],
                );
                final_
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `stirlingFirst_one_right : ∀ n, stirlingFirst (succ n) 1 = factorial n`.
///
/// Induction on `n`. `stirlingFirst (n+2) 1 ≡ (n+1) * stirlingFirst (n+1) 1`
/// — the `+ stirlingFirst (n+1) 0` summand is `add _ 0` and vanishes by ι —
/// so the step is the hypothesis followed by ONE `mul_comm`, because this
/// prelude's `factorial_succ` is `factorial n * succ n` where Mathlib's is
/// `succ n * factorial n`.
fn declare_stirling_first_one_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let first = p.stirling_first;
    d.theorem(p.stirling_first_one_right, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let one = d.num(1);
            let lhs = value_at(d, first, sx, one);
            let rhs = d.factorial(x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                // stirlingFirst 1 1 ≡ 1 ≡ factorial 0
                let one = d.num(1);
                d.refl(one)
            },
            &|d, m, ih| {
                let sm = d.succ(m);
                let one = d.num(1);
                let at_one = value_at(d, first, sm, one);
                let fact_m = d.factorial(m);
                let fact_sm = d.factorial(sm);

                let start = d.mul(sm, at_one);
                let step_one = d.congr(at_one, fact_m, ih, &|d, x| d.mul(sm, x));
                let mid_one = d.mul(sm, fact_m);
                let step_two = d.lemma(p.mul_comm, &[sm, fact_m]);
                let mid_two = d.mul(fact_m, sm);
                // factorial_succ : factorial (succ m) = factorial m * succ m
                let fact_succ = d.lemma(p.factorial_succ, &[m]);
                let step_three = d.symm(fact_sm, mid_two, fact_succ);
                let (_end, final_) = d.chain(
                    start,
                    &[
                        (mid_one, step_one),
                        (mid_two, step_two),
                        (fact_sm, step_three),
                    ],
                );
                final_
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `stirlingFirst_succ_self_left : ∀ n, stirlingFirst (succ n) n = choose (succ n) 2`.
///
/// Induction on `n`. The step reduces the left to
/// `(n+1) * stirlingFirst (n+1) (n+1) + stirlingFirst (n+1) n`, closes the
/// first factor with [`declare_stirling_first_self`] and the second summand
/// with the hypothesis, then meets Pascal's rule from the other side:
/// `choose (n+2) 2 = choose (n+1) 1 + choose (n+1) 2` with `choose_one_right`.
/// `mul_one` is unavoidable here — `mul c (succ zero)` is `add (mul c zero) c`,
/// i.e. `add zero c`, which `Nat.add`'s right recursion leaves stuck.
fn declare_stirling_first_succ_self_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let first = p.stirling_first;
    d.theorem(p.stirling_first_succ_self_left, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let lhs = value_at(d, first, sx, x);
            let two = d.num(2);
            let rhs = d.choose(sx, two);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                // stirlingFirst 1 0 ≡ 0, and choose 1 2 ≡ 0 + 0 ≡ 0.
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, m, ih| {
                let sm = d.succ(m);
                let ssm = d.succ(sm);
                let one = d.num(1);
                let two = d.num(2);

                let diagonal = value_at(d, first, sm, sm);
                let below = value_at(d, first, sm, m);
                let self_one = d.lemma(p.stirling_first_self, &[sm]);
                let choose_sm_two = d.choose(sm, two);
                let choose_sm_one = d.choose(sm, one);
                let choose_ssm_two = d.choose(ssm, two);

                let scaled = d.mul(sm, diagonal);
                let start = d.add(scaled, below);
                let step_one = d.congr(diagonal, one, self_one, &|d, x| {
                    let scaled = d.mul(sm, x);
                    d.add(scaled, below)
                });
                let mid_one = {
                    let scaled = d.mul(sm, one);
                    d.add(scaled, below)
                };
                let step_two = d.congr(below, choose_sm_two, ih, &|d, x| {
                    let scaled = d.mul(sm, one);
                    d.add(scaled, x)
                });
                let mid_two = {
                    let scaled = d.mul(sm, one);
                    d.add(scaled, choose_sm_two)
                };
                let mul_one = d.lemma(p.mul_one, &[sm]);
                let scaled_one = d.mul(sm, one);
                let step_three =
                    d.congr(scaled_one, sm, mul_one, &|d, x| d.add(x, choose_sm_two));
                let mid_three = d.add(sm, choose_sm_two);
                // choose_one_right sm : choose sm 1 = sm
                let choose_one = d.lemma(p.choose_one_right, &[sm]);
                let choose_one_symm = d.symm(choose_sm_one, sm, choose_one);
                let step_four = d.congr(sm, choose_sm_one, choose_one_symm, &|d, x| {
                    d.add(x, choose_sm_two)
                });
                let mid_four = d.add(choose_sm_one, choose_sm_two);
                // Pascal at (sm, 1): choose (succ sm) 2 = choose sm 1 + choose sm 2
                let pascal = d.lemma(p.choose_succ_succ, &[sm, one]);
                let step_five = d.symm(choose_ssm_two, mid_four, pascal);
                let (_end, final_) = d.chain(
                    start,
                    &[
                        (mid_one, step_one),
                        (mid_two, step_two),
                        (mid_three, step_three),
                        (mid_four, step_four),
                        (choose_ssm_two, step_five),
                    ],
                );
                final_
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `stirlingSecond_one_right : ∀ n, stirlingSecond (succ n) 1 = 1`.
///
/// Induction on `n`. `stirlingSecond (n+2) 1 ≡ 1 * stirlingSecond (n+1) 1`
/// (the `+ stirlingSecond (n+1) 0` summand is `add _ 0`), so the step is the
/// hypothesis and then `mul 1 1 ≡ 1` by ι — no `one_mul` needed, because the
/// hypothesis has already turned the stuck factor into a literal.
fn declare_stirling_second_one_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let second = p.stirling_second;
    d.theorem(p.stirling_second_one_right, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let one = d.num(1);
            let lhs = value_at(d, second, sx, one);
            let one2 = d.num(1);
            d.eq(lhs, one2)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let one = d.num(1);
                d.refl(one)
            },
            &|d, m, ih| {
                let sm = d.succ(m);
                let one = d.num(1);
                let at_one = value_at(d, second, sm, one);
                let start = d.mul(one, at_one);
                let step_one = d.congr(at_one, one, ih, &|d, x| d.mul(one, x));
                let mid_one = d.mul(one, one);
                let step_two = d.refl(one);
                let (_end, final_) = d.chain(start, &[(mid_one, step_one), (one, step_two)]);
                final_
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare the ten `Mathlib.Combinatorics.Enumerative.Stirling` mirrors.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_stirling_lemmas_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_defining_equations(d, p)?;
    declare_eq_zero_of_lt(d, p, Kind::First)?;
    declare_eq_zero_of_lt(d, p, Kind::Second)?;
    declare_stirling_first_self(d, p)?;
    declare_stirling_first_one_right(d, p)?;
    declare_stirling_first_succ_self_left(d, p)?;
    declare_stirling_second_one_right(d, p)?;
    Ok(())
}
