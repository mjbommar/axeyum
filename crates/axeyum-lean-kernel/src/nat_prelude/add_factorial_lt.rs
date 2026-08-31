//! `Nat.add_factorial_lt_factorial_add : ∀ i n, Le 2 i → Le 1 n → Lt (i +
//! n!) ((i+n)!)` -- an `ml430` mirror
//! (`F:ml430-nat-add-factorial-lt-factorial-add-7501a8c8`) -- and its
//! unconditional-in-`n` corollary `Nat.add_factorial_succ_lt_factorial_add_succ
//! : ∀ i n, Le 2 i → Lt (i + (n+1)!) ((i+n+1)!)`
//! (`F:ml430-nat-add-factorial-succ-lt-factorial-add-succ-ec0fa8d3`), immediate
//! from the first at `n := succ n` via [`NatOps::zero_lt_succ`].
//!
//! The strict statement genuinely needs the hypothesis `2 ≤ i` -- at `i = 1`
//! the corresponding `≤` statement (`add_factorial_le.rs`) is already tight
//! (`1 + 1! = 2 = 1!·2 ... ` no room for strictness at `n` small) -- so the
//! proof cannot reuse `add_factorial_le_factorial_add`'s plain induction on
//! `i` starting at `zero`. Instead: [`NatOps`]'s `le_dest` peels `h : Le 2 i`
//! into a witness `k` with `Eq (add 2 k) i` (`Exists`-eliminated via
//! `Exists.rec`, mirroring `totient_lemmas.rs::declare_count_range_le_of_le`),
//! and the real content is a `k`-indexed strict induction on the statement
//! `Lt (add (add 2 k) n!) (factorial (add (add 2 k) n))` with `n` (and `Le 1
//! n`) held fixed:
//!
//! - **Base** (`k = 0`): `add 2 0 ≡ 2` by `δ/ι` (the RIGHT argument of `add`
//!   is the literal `zero`, so no lemma is needed to erase it), reducing the
//!   goal to `2 + n! < (2+n)!`. [`base_case_two`] proves this directly:
//!   `factorial_lt_of_lt` gives `n! < (n+1)!` (`=: F1`) and `factorial_le`
//!   gives `2 ≤ F1` (since `factorial 2 ≡ 2` by pure `δ/ι`, both operands of
//!   its `add`/`mul` chain being literal succ-towers); combined with
//!   `mul_le_mul_left` at `n+1 ≥ 2` this shows `F1 + F1 ≤ (n+1)!·(n+2)`
//!   (`=: the (2+n)! chain`, unfolded by the SAME `δ/ι` two-step `factorial
//!   (succ x) ≡ mul (factorial x) (succ x) ≡ add (mul (factorial x) x)
//!   (factorial x)` the `≤` proof's module doc names), and `succ(nfact) ≤ F1`
//!   plus `2 ≤ F1` give `nfact + 3 ≤ F1 + F1` (three lots of one-succ/two-succ
//!   slack, chained through `add_le_add_left`/`add_le_add_right`/`le_trans`).
//!   The one nontrivial rewrite either side of this needs is `add 2 x ≡ succ
//!   (succ x)`, which is NOT `δ/ι` (the literal `2` sits on the LEFT of a
//!   symbolic right argument, where `add` recurses) -- built once by
//!   [`two_add_eq_succ_succ`] via two `succ_add` steps and one `zero_add`
//!   step, and reused for both `x := n` (to unfold the goal's factorial
//!   argument) and `x := nfact` (to unfold the goal's left summand).
//! - **Step** (`k → succ k`): `add 2 (succ k) ≡ succ (add 2 k)` by `δ/ι`
//!   (here the literal argument sits on the RIGHT of `add`'s recursion, so
//!   this direction IS free), so writing `I := add 2 k`, the IH `Lt (add I
//!   n!) (factorial (add I n))` is *already* `Le (succ (add I n!)) (factorial
//!   (add I n))` by `Lt`'s own definition -- one `succ` ahead of
//!   `add_factorial_le_factorial_add`'s step-case IH. [`step_case`] is
//!   therefore that same step function (`le_succ_succ` then the
//!   `one_le_mul`/`add_le_add_left`/`add_comm` growth argument, `le_trans` to
//!   close), applied to an IH that is already one `succ` ahead, which lands
//!   exactly on the goal's required `succ (succ (…))` shape with no slack
//!   lost or needed beyond what `mul (factorial (add I n)) (add I n) ≥ 1`
//!   already supplies.
//!
//! Every intermediate `Eq`/`Le`/`Lt` term below is built against whichever
//! `δ/ι`-reduced form is easiest to construct; the kernel's own `whnf`-based
//! defeq check reconciles it against the differently-shaped goal at the
//! final `add_declaration`, so (per this prelude's standing convention) no
//! extra congruence step is spelled out purely to make two definitionally
//! equal terms syntactically identical.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::{BinderInfo, ExprId};

/// Given `proof : Le a b1` and `eq_b1_b2 : Eq b1 b2`, build `Le a b2`.
fn le_transport_rhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    b1: ExprId,
    b2: ExprId,
    eq_b1_b2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b1, &|d, x| d.le(a, x));
    d.transport(b1, motive, proof, b2, eq_b1_b2)
}

/// Given `proof : Le a1 b` and `eq_a1_a2 : Eq a1 a2`, build `Le a2 b`.
fn le_transport_lhs(
    d: &mut NatDev<'_>,
    a1: ExprId,
    a2: ExprId,
    b: ExprId,
    eq_a1_a2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a1, &|d, x| d.le(x, b));
    d.transport(a1, motive, proof, a2, eq_a1_a2)
}

/// Given `proof : Lt a b1` and `eq_b1_b2 : Eq b1 b2`, build `Lt a b2`.
fn lt_transport_rhs(
    d: &mut NatDev<'_>,
    a: ExprId,
    b1: ExprId,
    b2: ExprId,
    eq_b1_b2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b1, &|d, x| d.lt(a, x));
    d.transport(b1, motive, proof, b2, eq_b1_b2)
}

/// Given `proof : Lt a1 b` and `eq_a1_a2 : Eq a1 a2`, build `Lt a2 b`.
fn lt_transport_lhs(
    d: &mut NatDev<'_>,
    a1: ExprId,
    a2: ExprId,
    b: ExprId,
    eq_a1_a2: ExprId,
    proof: ExprId,
) -> ExprId {
    let motive = d.eq_motive(a1, &|d, x| d.lt(x, b));
    d.transport(a1, motive, proof, a2, eq_a1_a2)
}

/// Build `(succ (succ x), proof : Eq (add 2 x) (succ (succ x)))`, via
/// `succ_add` applied twice (peeling both literal `succ`s off `2`'s left
/// position) and `zero_add` once (erasing the base `add zero x`). See the
/// module doc: this is the one rewrite the whole file needs because `add`
/// recurses on its RIGHT argument, so a literal on the LEFT of a symbolic
/// right operand is stuck, unlike a literal on the right (free by `δ/ι`).
fn two_add_eq_succ_succ(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let zero = d.zero();
    let one = d.succ(zero);
    let two = d.succ(one);
    let add2x = d.add(two, x);

    // e1 : Eq (add (succ one) x) (succ (add one x))
    let e1 = d.lemma(p.succ_add, &[one, x]);
    let add1x = d.add(one, x);
    let next1 = d.succ(add1x);

    // e2_inner : Eq (add (succ zero) x) (succ (add zero x))
    let e2_inner = d.lemma(p.succ_add, &[zero, x]);
    let addzx = d.add(zero, x);
    let succ_addzx = d.succ(addzx);
    let e2 = d.congr(add1x, succ_addzx, e2_inner, &|d, y| d.succ(y));
    let next2 = d.succ(succ_addzx);

    // e3_inner : Eq (add zero x) x
    let e3_inner = d.lemma(p.zero_add, &[x]);
    let sx = d.succ(x);
    let e3a = d.congr(addzx, x, e3_inner, &|d, y| d.succ(y)); // Eq (succ addzx) (succ x)
    let e3 = d.congr(succ_addzx, sx, e3a, &|d, y| d.succ(y)); // Eq (succ succ_addzx) (succ succ x)
    let next3 = d.succ(sx);

    d.chain(add2x, &[(next1, e1), (next2, e2), (next3, e3)])
}

/// The `k = 0` base case: `Lt (add 2 nfact) (factorial (add 2 n))`, given
/// `hn : Le 1 n`. See the module doc for the derivation.
fn base_case_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    nfact: ExprId,
    hn: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let s = d.succ(n);
    let f1 = d.factorial(s);

    // h_lt_nfact_f1 : Lt nfact f1, via `factorial_lt_of_lt(s, n, hn, n < s)`.
    let lt_succ_self_n = d.lemma(p.lt_succ_self, &[n]); // Lt n s
    let h_lt_nfact_f1 = d.lemma(p.factorial_lt_of_lt, &[s, n, hn, lt_succ_self_n]);

    // h_s_ge2 : Le 2 s, via `le_succ_succ(1, n, hn)`.
    let h_s_ge2 = d.lemma(p.le_succ_succ, &[one, n, hn]);

    // h_f1_ge2 : Le (factorial 2) f1 -- defeq Le 2 f1, since `factorial 2 ≡ 2`
    // by pure δ/ι (both operands are literal succ-towers all the way down).
    let h_f1_ge2 = d.lemma(p.factorial_le, &[two, s, h_s_ge2]);

    // h_f1_le_mulf1s : Le f1 (mul f1 s), via `mul f1 1 = f1` transported
    // across `mul_le_mul_left(f1, 1, 2, 1≤2)` then chained with
    // `mul_le_mul_left(f1, 2, s, h_s_ge2)`.
    let h_1_le_2 = d.lemma(p.le_succ, &[one]); // Le 1 (succ 1) = Le 1 2
    let h_mulf1_1_le_2 = d.lemma(p.mul_le_mul_left, &[f1, one, two, h_1_le_2]);
    let mul_f1_1 = d.mul(f1, one);
    let mul_f1_2 = d.mul(f1, two);
    let eq_mulf1one = d.lemma(p.mul_one, &[f1]); // Eq (mul f1 1) f1
    let h_f1_le_mulf12 = le_transport_lhs(d, mul_f1_1, f1, mul_f1_2, eq_mulf1one, h_mulf1_1_le_2);
    let h_mulf12_le_mulf1s = d.lemma(p.mul_le_mul_left, &[f1, two, s, h_s_ge2]);
    let mul_f1_s = d.mul(f1, s);
    let h_f1_le_mulf1s = d.lemma(
        p.le_trans,
        &[f1, mul_f1_2, mul_f1_s, h_f1_le_mulf12, h_mulf12_le_mulf1s],
    );

    // h_f1f1_le : Le (add f1 f1) (add (mul f1 s) f1) -- defeq Le (add f1 f1)
    // (factorial (succ s)).
    let f2_actual = d.add(mul_f1_s, f1);
    let h_f1f1_le = d.lemma(p.add_le_add_right, &[f1, f1, mul_f1_s, h_f1_le_mulf1s]);

    // Combine `succ nfact ≤ f1` (from h_lt_nfact_f1, defeq) and `2 ≤ f1` into
    // `add (succ nfact) 2 ≤ add f1 f1` -- defeq `succ (succ (succ nfact)) ≤
    // add f1 f1`, since the RIGHT operand of the outer `add` is the literal
    // `2`.
    let succ_nfact = d.succ(nfact);
    let add_f1_f1 = d.add(f1, f1);
    let h_step1 = d.lemma(p.add_le_add_right, &[f1, succ_nfact, f1, h_lt_nfact_f1]);
    let h_step2 = d.lemma(p.add_le_add_left, &[succ_nfact, two, f1, h_f1_ge2]);
    let add_succnfact_f1 = d.add(succ_nfact, f1);
    let add_succnfact_two = d.add(succ_nfact, two);
    let h_step_combined = d.lemma(
        p.le_trans,
        &[
            add_succnfact_two,
            add_succnfact_f1,
            add_f1_f1,
            h_step2,
            h_step1,
        ],
    );
    let h_final_pre = d.lemma(
        p.le_trans,
        &[
            add_succnfact_two,
            add_f1_f1,
            f2_actual,
            h_step_combined,
            h_f1f1_le,
        ],
    );
    // h_final_pre : Le (add (succ nfact) 2) f2_actual
    //             ≡defeq Le (succ (succ (succ nfact))) f2_actual
    //             =      Lt (succ (succ nfact)) f2_actual

    // Transport into the stated goal `Lt (add 2 nfact) (factorial (add 2 n))`.
    let (succ_succ_nfact, eq2nfact) = two_add_eq_succ_succ(d, &p, nfact);
    let add2nfact = d.add(two, nfact);
    let eq2nfact_rev = d.symm(add2nfact, succ_succ_nfact, eq2nfact);
    let h_mid = lt_transport_lhs(
        d,
        succ_succ_nfact,
        add2nfact,
        f2_actual,
        eq2nfact_rev,
        h_final_pre,
    );

    let (succ_succ_n, eq2n) = two_add_eq_succ_succ(d, &p, n);
    let add2n = d.add(two, n);
    let fact_add2n = d.factorial(add2n);
    let fact_ssn = d.factorial(succ_succ_n);
    let eq_fact_congr = d.congr(add2n, succ_succ_n, eq2n, &|d, x| d.factorial(x)); // Eq(fact_add2n, fact_ssn)
    let eq_fact_rev = d.symm(fact_add2n, fact_ssn, eq_fact_congr); // Eq(fact_ssn, fact_add2n)

    lt_transport_rhs(d, add2nfact, f2_actual, fact_add2n, eq_fact_rev, h_mid)
}

/// The `k → succ k` step case. `ih : Lt (add (add 2 k) nfact) (factorial
/// (add (add 2 k) n))`; produces the same statement at `succ k`. See the
/// module doc.
fn step_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    nfact: ExprId,
    hn: ExprId,
    j: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let i = d.add(two, j);
    let si = d.succ(i);

    let a0 = d.add(i, nfact);
    let addin = d.add(i, n);
    let g = d.factorial(addin);

    // eq_lhs : Eq (add si nfact) (succ a0)
    let eq_lhs = d.lemma(p.succ_add, &[i, nfact]);

    // eq_rhs : Eq (factorial (add si n)) (factorial (succ addin))
    let eq_rhs_inner = d.lemma(p.succ_add, &[i, n]); // Eq(add si n, succ addin)
    let add_si_n = d.add(si, n);
    let succ_addin = d.succ(addin);
    let eq_rhs = d.congr(add_si_n, succ_addin, eq_rhs_inner, &|d, x| d.factorial(x));

    // `factorial (succ addin) ≡defeq add (mul g addin) g`.
    let mul_g_in = d.mul(g, addin);
    let y = d.add(mul_g_in, g);

    // step1 : Le (succ (succ a0)) (succ g), via `le_succ_succ` on
    // `ih : Lt a0 g = Le (succ a0) g`.
    let succ_a0 = d.succ(a0);
    let step1 = d.lemma(p.le_succ_succ, &[succ_a0, g, ih]);

    // Growth: `1 ≤ mul g addin` (from `1 ≤ g` and `1 ≤ addin`), lifted to
    // `add g 1 ≤ add g (mul g addin)` -- defeq `succ g ≤ add g mul_g_in` --
    // then commuted to land on `y = add mul_g_in g`.
    let n_i = d.add(n, i);
    let le_n_addni = d.lemma(p.le_add_right, &[n, i]); // Le n (add n i)
    let comm_ni = d.lemma(p.add_comm, &[n, i]); // Eq (add n i) (add i n) = addin
    let le_n_addin = le_transport_rhs(d, n, n_i, addin, comm_ni, le_n_addni); // Le n addin
    let one_le_addin = d.lemma(p.le_trans, &[one, n, addin, hn, le_n_addin]);
    let one_le_g = d.lemma(p.one_le_factorial, &[addin]);
    let one_le_prod = d.lemma(p.one_le_mul, &[g, addin, one_le_g, one_le_addin]);

    let add_g_one = d.add(g, one);
    let add_g_mul = d.add(g, mul_g_in);
    let growth0 = d.lemma(p.add_le_add_left, &[g, one, mul_g_in, one_le_prod]); // Le(add_g_one, add_g_mul)
    let comm_growth = d.lemma(p.add_comm, &[mul_g_in, g]); // Eq(y, add_g_mul)
    let comm_growth_rev = d.symm(y, add_g_mul, comm_growth); // Eq(add_g_mul, y)
    let growth = le_transport_rhs(d, add_g_one, add_g_mul, y, comm_growth_rev, growth0); // Le(add_g_one, y)

    let succ_g = d.succ(g);
    let succ_succ_a0 = d.succ(succ_a0);
    let core = d.lemma(p.le_trans, &[succ_succ_a0, succ_g, y, step1, growth]);
    // core : Le (succ (succ a0)) y  ==  Lt (succ a0) y

    // Transport back to `Lt (add si nfact) (factorial (add si n))`.
    let add_si_nfact = d.add(si, nfact);
    let eq_lhs_rev = d.symm(add_si_nfact, succ_a0, eq_lhs);
    let h_mid = lt_transport_lhs(d, succ_a0, add_si_nfact, y, eq_lhs_rev, core);
    let fact_add_si_n = d.factorial(add_si_n);
    let fact_succ_addin = d.factorial(succ_addin);
    let eq_rhs_rev = d.symm(fact_add_si_n, fact_succ_addin, eq_rhs);
    lt_transport_rhs(d, add_si_nfact, y, fact_add_si_n, eq_rhs_rev, h_mid)
}

/// `Nat.add_factorial_lt_factorial_add : ∀ i n, Le 2 i → Le 1 n → Lt (add i
/// (factorial n)) (factorial (add i n))`. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_add_factorial_lt_factorial_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_factorial_lt_factorial_add, 2, &|d, v| {
        let (i, n) = (v[0], v[1]);
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let one_lvl = d.level_one();
        let two = d.num(2);
        let one = d.num(1);
        let nfact = d.factorial(n);

        let hyp1_ty = d.le(two, i);
        let hyp2_ty = d.le(one, n);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let two_k = d.add(two, k);
            let body = d.eq(two_k, i);
            d.lam_fv(k_fv, nat, body)
        };
        let represented_ty = {
            let exists_ = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            d.apply(exists_, &[nat, pred])
        };
        let represented = d.lemma(p.le_dest, &[two, i, h1]);

        let concl_lhs = d.add(i, nfact);
        let concl_i_n = d.add(i, n);
        let concl_rhs = d.factorial(concl_i_n);
        let conclusion = d.lt(concl_lhs, concl_rhs);

        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let two_k = d.add(two, k);
            let e_ty = d.eq(two_k, i);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);

            let motive_k = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let two = d.num(2);
                let idx = d.add(two, x);
                let lhs = d.add(idx, nfact);
                let idxn = d.add(idx, n);
                let rhs = d.factorial(idxn);
                d.lt(lhs, rhs)
            };
            let base = |d: &mut NatDev<'_>| -> ExprId { base_case_two(d, &p, n, nfact, h2) };
            let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
                step_case(d, &p, n, nfact, h2, j, ih)
            };
            let p_k = d.induct(&motive_k, &base, &step, k);

            let motive_e = d.eq_motive(two_k, &|d, x| {
                let lhs = d.add(x, nfact);
                let xn = d.add(x, n);
                let rhs = d.factorial(xn);
                d.lt(lhs, rhs)
            });
            let final_proof = d.transport(two_k, motive_e, p_k, i, e);

            let with_e = d.lam_fv(e_fv, e_ty, final_proof);
            d.lam_fv(k_fv, nat, with_e)
        };

        let motive_outer = d
            .kernel()
            .lam(anon, represented_ty, conclusion, BinderInfo::Default);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let body = d.apply(rec, &[nat, pred, motive_outer, minor, represented]);

        let stmt = {
            let with_h2 = d.arrow(hyp2_ty, conclusion);
            d.arrow(hyp1_ty, with_h2)
        };
        let proof = {
            let with_h2 = d.lam_fv(h2_fv, hyp2_ty, body);
            d.lam_fv(h1_fv, hyp1_ty, with_h2)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_factorial_succ_lt_factorial_add_succ : ∀ i n, Le 2 i → Lt (add i
/// (factorial (add n 1))) (factorial (add (add i n) 1))`. Immediate
/// corollary of [`declare_add_factorial_lt_factorial_add`] at `n := succ n`,
/// discharging its `Le 1 (succ n)` hypothesis with
/// [`NatOps::zero_lt_succ`]. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_add_factorial_succ_lt_factorial_add_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_factorial_succ_lt_factorial_add_succ, 2, &|d, v| {
        let (i, n) = (v[0], v[1]);
        let two = d.num(2);
        let one = d.num(1);
        let hyp_ty = d.le(two, i);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sn = d.succ(n);
        let hn = d.zero_lt_succ(n); // Le 1 (succ n)
        let proof = d.lemma(p.add_factorial_lt_factorial_add, &[i, sn, h, hn]);

        let n1 = d.add(n, one);
        let fact_n1 = d.factorial(n1);
        let lhs = d.add(i, fact_n1);
        let i_n = d.add(i, n);
        let i_n_1 = d.add(i_n, one);
        let rhs = d.factorial(i_n_1);
        let concl = d.lt(lhs, rhs);

        let stmt = d.arrow(hyp_ty, concl);
        let full_proof = d.lam_fv(h_fv, hyp_ty, proof);
        (stmt, full_proof)
    })?;
    Ok(())
}
