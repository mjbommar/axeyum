//! `Nat.add_choose_mul_factorial_mul_factorial : ∀ i j, (i+j).choose j *
//! i! * j! = (i+j)!` -- an `ml430` mirror. New module (not `choose.rs` or
//! `desc_factorial.rs`, both already dense) since this is the one theorem
//! that needs a piece of BOTH: the falling-factorial/`choose` bridge
//! ([`NatPrelude::desc_factorial_eq_factorial_mul_choose`], `desc_factorial.rs`)
//! and a new "complement" identity this prelude did not previously have.
//!
//! # The missing piece
//!
//! [`NatPrelude::desc_factorial_eq_factorial_mul_choose`] gives
//! `descFactorial n k = k! * choose n k` for ANY `n, k`. Instantiated at
//! `n := i+j, k := j`, that is `descFactorial (i+j) j = j! * choose (i+j)
//! j`. What is still missing is the "complement" fact that multiplying the
//! falling factorial by `i!` recovers `(i+j)!` -- i.e. `descFactorial (i+j)
//! j` IS `(i+j)! / i!`, stated without division:
//!
//! `descFactorial (i+j) j * i! = (i+j)!`                              (*)
//!
//! [`desc_factorial_add_eq_factorial_at`] proves (*) by induction on `j`
//! with `i` held fixed (the same "generalize the OTHER variable" shape
//! `bit_order.rs::declare_self_lt_two_pow_add` uses for `Lt a (pow 2 (add a
//! b))`), via [`NatPrelude::desc_factorial_succ_eq_succ_mul`] -- the
//! "front-peel" identity `descFactorial (succ n) (succ k) = (succ n) *
//! descFactorial n k` -- rather than `desc_factorial.rs`'s own
//! bottom-peeling recursion (`descFactorial n (succ k) = (n-k) *
//! descFactorial n k`), which would force reasoning about `Nat.sub` at a
//! moving index. Setting `n' := i+j` at each step, `i + succ j` is `refl`-
//! `succ n'` (`Nat.add` recurses on its right argument), so
//! `desc_factorial_succ_eq_succ_mul(n', j)` applies with NO extra rewrite:
//!
//! Base (`j=0`): `descFactorial (i+0) 0 * i! = 1 * i! = i!` (`desc_factorial_zero`,
//! `one_mul`), and `(i+0)! = i!` (`refl`, `add`'s own zero case). So the base
//! case IS `one_mul(i!)` directly.
//!
//! Step (`j=k` -> `j=succ k`, `ih : descFactorial (i+k) k * i! = (i+k)!`):
//! `descFactorial (i+succ k) (succ k)` is `refl`-`descFactorial (succ n')
//! (succ k)` where `n' := i+k`, so `desc_factorial_succ_eq_succ_mul(n', k)`
//! gives it equal to `(succ n') * descFactorial n' k`. Multiplying both
//! sides by `i!`, reassociating (`mul_assoc`), and rewriting `descFactorial
//! n' k * i!` via `ih` leaves `(succ n') * (i+k)!`, which `mul_comm` then
//! `factorial_succ(n')` (reversed) identifies with `(succ n')! = (i + succ
//! k)!` (`refl`, `add`'s own succ case).
//!
//! # Assembling the target
//!
//! `add_choose_mul_factorial_mul_factorial(i, j)` chains (*) at `(i, j)`
//! with [`NatPrelude::desc_factorial_eq_factorial_mul_choose`] `(i+j, j)`
//! and two rearrangement steps (`mul_comm`, `mul_assoc`) to reach the
//! `ml430` statement's exact associativity, `(choose(i+j,j) * i!) * j! =
//! (i+j)!`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.descFactorial n k`.
fn desc_factorial(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.desc_factorial, &[n, k])
}

/// `descFactorial (i+j) j * i! = (i+j)!`, for the GIVEN `i` (a captured
/// symbolic term, possibly a bound fvar from the caller's own theorem) and
/// `j` (the induction target). See the module doc for the route.
///
/// `pub(super)` rather than `pub` per this crate's "extract, don't
/// re-derive" convention: `add_desc_factorial_asc_factorial.rs`'s
/// `Nat.ascFactorial_eq_div` reuses this same identity rather than
/// re-proving it by a second induction.
pub(super) fn desc_factorial_add_eq_factorial_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let p = *p;
    let fact_i = d.factorial(i);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let aix = d.add(i, x);
        let df = desc_factorial(d, &p, aix, x);
        let lhs = d.mul(df, fact_i);
        let rhs = d.factorial(aix);
        d.eq(lhs, rhs)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId { d.lemma(p.one_mul, &[fact_i]) };

    let step = |d: &mut NatDev<'_>, k: ExprId, ih: ExprId| -> ExprId {
        let n_ik = d.add(i, k);
        let sn = d.succ(n_ik);
        let sk = d.succ(k);

        // Step A: desc_factorial_succ_eq_succ_mul(n_ik, k)
        //   Eq(descFactorial(sn, sk), mul(sn, descFactorial(n_ik, k)))
        let step_a = d.lemma(p.desc_factorial_succ_eq_succ_mul, &[n_ik, k]);
        let df_sn_sk = desc_factorial(d, &p, sn, sk);
        let df_nik_k = desc_factorial(d, &p, n_ik, k);
        let mul_sn_df = d.mul(sn, df_nik_k);

        let start = d.mul(df_sn_sk, fact_i);
        let step1 = d.congr(df_sn_sk, mul_sn_df, step_a, &|d, x| d.mul(x, fact_i));
        let target1 = d.mul(mul_sn_df, fact_i);

        // Step B: mul_assoc(sn, df_nik_k, fact_i)
        //   Eq(mul(mul(sn,df),fact_i), mul(sn, mul(df,fact_i)))
        let assoc_eq = d.lemma(p.mul_assoc, &[sn, df_nik_k, fact_i]);
        let df_fact_i = d.mul(df_nik_k, fact_i);
        let target2 = d.mul(sn, df_fact_i);

        // Step C: congr ih under (fun x => mul(sn, x))
        //   ih : Eq(mul(df_nik_k, fact_i), factorial(n_ik))
        let fact_n_ik = d.factorial(n_ik);
        let step3 = d.congr(df_fact_i, fact_n_ik, ih, &|d, x| d.mul(sn, x));
        let target3 = d.mul(sn, fact_n_ik);

        // Step D: mul_comm(sn, fact_n_ik)
        let comm_eq = d.lemma(p.mul_comm, &[sn, fact_n_ik]);
        let target4 = d.mul(fact_n_ik, sn);

        // Step E: factorial_succ(n_ik) reversed
        //   Eq(factorial(sn), mul(fact_n_ik, sn)) -> Eq(target4, target5)
        let fact_succ_eq = d.lemma(p.factorial_succ, &[n_ik]);
        let target5 = d.factorial(sn);
        let step5 = d.symm(target5, target4, fact_succ_eq);

        let (_e, proof) = d.chain(
            start,
            &[
                (target1, step1),
                (target2, assoc_eq),
                (target3, step3),
                (target4, comm_eq),
                (target5, step5),
            ],
        );
        proof
    };

    d.induct(&motive, &base, &step, j)
}

/// `Nat.add_choose_mul_factorial_mul_factorial`: `∀ i j, (i+j).choose j *
/// i! * j! = (i+j)!`. See the module doc for the assembly.
pub(super) fn declare_add_choose_mul_factorial_mul_factorial(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_choose_mul_factorial_mul_factorial, 2, &|d, v| {
        let (i, j) = (v[0], v[1]);
        let n_ij = d.add(i, j);

        // (*) : descFactorial (i+j) j * i! = (i+j)!
        let star = desc_factorial_add_eq_factorial_at(d, &p, i, j);

        // desc_factorial_eq_factorial_mul_choose(i+j, j) :
        //   Eq(descFactorial(i+j,j), mul(factorial(j), choose(i+j,j)))
        let h2 = d.lemma(p.desc_factorial_eq_factorial_mul_choose, &[n_ij, j]);

        let df = desc_factorial(d, &p, n_ij, j);
        let choose_ij = d.choose(n_ij, j);
        let fact_i = d.factorial(i);
        let fact_j = d.factorial(j);

        // LHS of the theorem, exactly as `ml430` states it:
        // (choose(i+j,j) * i!) * j!
        let choose_mul_i = d.mul(choose_ij, fact_i);
        let lhs = d.mul(choose_mul_i, fact_j);

        // Step a: mul_comm(choose*i!, j!) : Eq(lhs, mul(j!, choose*i!))
        let step_a = d.lemma(p.mul_comm, &[choose_mul_i, fact_j]);
        let target1 = d.mul(fact_j, choose_mul_i);

        // Step b: mul_assoc(j!, choose, i!) reversed :
        //   mul_assoc(fact_j, choose_ij, fact_i) :
        //     Eq(mul(mul(fact_j,choose_ij),fact_i), mul(fact_j,mul(choose_ij,fact_i)))
        //   i.e. Eq(target2, target1); reverse to get Eq(target1, target2).
        let fact_j_choose = d.mul(fact_j, choose_ij);
        let target2 = d.mul(fact_j_choose, fact_i);
        let assoc_eq = d.lemma(p.mul_assoc, &[fact_j, choose_ij, fact_i]);
        let step_b = d.symm(target2, target1, assoc_eq);

        // Step c: congr (symm h2) under (fun x => mul(x, fact_i))
        //   h2 : Eq(df, fact_j_choose) ; symm : Eq(fact_j_choose, df)
        let h2_rev = d.symm(df, fact_j_choose, h2);
        let target3 = d.mul(df, fact_i);
        let step_c = d.congr(fact_j_choose, df, h2_rev, &|d, x| d.mul(x, fact_i));

        // Step d: (*) itself : Eq(mul(df, fact_i), factorial(i+j))
        let target4 = d.factorial(n_ij);

        let (_e, proof) = d.chain(
            lhs,
            &[
                (target1, step_a),
                (target2, step_b),
                (target3, step_c),
                (target4, star),
            ],
        );

        let stmt = d.eq(lhs, target4);
        (stmt, proof)
    })?;
    Ok(())
}
