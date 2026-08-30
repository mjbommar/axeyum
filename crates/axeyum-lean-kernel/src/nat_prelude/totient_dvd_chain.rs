//! `Nat.totient_dvd_of_dvd` and `Nat.eq_or_eq_of_totient_eq_totient` — the two
//! `ml430` totient mirrors ADR-0668 names as unblocked, closed by the
//! prime-peeling chain that ADR describes rather than by the Euler product.
//!
//! ## Target 1: `Nat.totient_dvd_of_dvd : a ∣ b → φ(a) ∣ φ(b)`
//!
//! Built from [`declare_totient_dvd_totient_mul`], the fully general (no
//! hypothesis at all) form
//!
//! ```text
//! Nat.totient_dvd_totient_mul : ∀ k a, Dvd (totient a) (totient (mul a k))
//! ```
//!
//! by well-founded induction on `k` (`Nat.lt`, the same generic fixpoint
//! `Nat.gcd` and `Nat.exists_prime_factorization` use), mirroring
//! `factorization.rs`'s peeling shape but simpler: no "≥ 2" guard is needed
//! because `k = 0` (`totient(mul a 0) ≡ 0` by iota, closed by `dvd_zero`) and
//! `k = 1` (`mul a 1 = a` by `mul_one`, closed by `dvd_refl`) are both
//! ordinary base cases rather than an excluded range. For `k = succ k' ≥ 2`,
//! [`Nat.exists_prime_dvd`](super::NatPrelude::exists_prime_dvd) supplies a
//! prime `q ∣ k`, the induction hypothesis at the strictly smaller cofactor
//! `k' = k / q` gives `φ(a) ∣ φ(a·k')`, and
//! [`totient_dvd_totient_mul_prime`](super::NatPrelude::totient_dvd_totient_mul_prime)
//! extends that one more step to `φ(a·k') ∣ φ(a·k' ·q) = φ(a·k)`;
//! `Nat.dvd_trans` closes the chain. `Nat.totient_dvd_of_dvd` itself is then
//! one `exists_rec` unpacking `a ∣ b` into `b = a·k` and transporting.
//!
//! No factor multiset is named anywhere: the chain is built from **some**
//! factorisation of `b / a` (whichever prime `exists_prime_dvd` happens to
//! return at each step), and nothing ever compares two factorisations.
//!
//! ## Target 3: `Nat.eq_or_eq_of_totient_eq_totient : a ∣ b → φ(a) = φ(b) →
//! a = b ∨ 2·a = b`
//!
//! Needs the SAME chain with the per-step multiplier tracked, because
//! divisibility alone cannot rule out `φ(a) = φ(b)` holding for a long chain.
//! [`declare_totient_mul_cofactor_bound`] is the bound that makes it work:
//!
//! ```text
//! Nat.totient_mul_cofactor_bound : ∀ k a, Le one (totient a) → Le two k →
//!   Or (Le (mul two (totient a)) (totient (mul a k)))
//!      (And (Eq k two) (Eq (totient (mul a k)) (totient a)))
//! ```
//!
//! i.e. for any cofactor `k ≥ 2`, either `φ(a·k) ≥ 2·φ(a)` outright, or
//! `k = 2` and `φ(a·k) = φ(a)` exactly. The step proof for `k = succ k' ≥ 2`
//! peels a prime `q ∣ k` exactly as Target 1 does, giving `k = q·k'`
//! (`k'` the strictly smaller cofactor), and splits on `k'`:
//!
//! - **`k' = 1`** (so `k = q`, a single prime step): the per-step multiplier
//!   is `totient q = q - 1` in the coprime branch or `q` in the dividing
//!   branch. Splitting further on `q = 2` vs `q > 2`
//!   (`Nat.lt_or_eq_of_le` at `2 ≤ q`) shows the multiplier is `≥ 2` in every
//!   case EXCEPT `q = 2` and coprime (`gcd 2 a = 1`, i.e. `a` odd), which is
//!   exactly the bound's second disjunct.
//! - **`k' ≥ 2`**: the induction hypothesis at `k'` already gives
//!   `φ(a·k') ≥ 2·φ(a)` (its second disjunct cannot re-fire here because that
//!   needs `k' = 2` exactly, and even then a further prime step at least
//!   multiplies by 1, keeping `φ(a·k) ≥ φ(a·k') ≥ 2·φ(a)`). So the FIRST
//!   disjunct holds unconditionally once depth ≥ 2, regardless of what the
//!   next prime step's multiplier is — the only way to reach the bound's
//!   second disjunct is a chain of length exactly 1.
//!
//! Every numeric claim here — including that the second disjunct is reached
//! ONLY at `k = 2` and only with `a` odd, and that no chain of length ≥ 2
//! reaches it — is checked exhaustively, with genuinely-failing negative
//! controls, by `scripts/tests/check-totient-dvd-chain-numerics.py`.
//!
//! `Nat.eq_or_eq_of_totient_eq_totient` itself unpacks `a ∣ b` into `b =
//! a·k`, splits `k` into `k = 0` (forces `a = 0` via `totient_eq_zero`, both
//! disjuncts trivially satisfiable via `a = b = 0`), `k = 1` (`a = b`
//! directly), and `k ≥ 2` (the bound lemma: the totient-equality hypothesis
//! refutes the first disjunct — `totient(a) ≥ 1` from `totient_eq_zero`'s
//! contrapositive, combined with `φ(a·k) = φ(a) < 2·φ(a)` — leaving only the
//! second, `k = 2 ∧ φ(a·k) = φ(a)`, from which `2·a = b` follows by
//! `mul_comm` and the extracted `b = a·k` equation).
//!
//! ## Magnitudes
//!
//! Every numeral this file forms is a small literal (`0`, `1`, `2`) or a
//! bound free variable; nothing here evaluates a large `pow`/`mul`, so no
//! magnitude budget is at risk (see `totient_prime_pow.rs`'s module doc for
//! why that matters in this prelude).

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local term builders and small private helpers. Per this prelude's house
// style (`factorization.rs`'s module doc) each file keeps its own copies
// rather than sharing a private module.
// ============================================================================

/// The two conjuncts of primality, spelled inline exactly as
/// `totient_prime_pow.rs`, `factorization.rs`, `primes.rs` and `fermat.rs`
/// all spell them: `Le two x` and `∀ c, dvd c x → c = 1 ∨ c = x`. This
/// prelude has no `Prime` predicate.
fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let two_le = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp = d.dvd(c, x);
    let is_one = d.eq(c, one);
    let is_x = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[is_one, is_x]);
    let inner = d.arrow(hyp, disjunction);
    let divisor_clause = d.pi_fv(c_fv, nat, inner);
    (two_le, divisor_clause)
}

/// `(2 ≤ x) ∧ (∀ c, c ∣ x → c = 1 ∨ c = x)`.
fn prime_ty(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let (two_le, divisor_clause) = prime_parts(d, p, x);
    d.const_app(p.logic.and, &[two_le, divisor_clause])
}

/// Non-dependent `Or.rec` into a fixed goal type — both minors already
/// include their own binder for the corresponding disjunct's hypothesis.
#[allow(clippy::too_many_arguments)]
fn or_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d
        .kernel()
        .lam(anon, or_ty, goal, crate::BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, or_proof],
    )
}

/// From `heq : Eq n (mul pw q)`, `hp2 : Le two pw`, `hq1 : Le one q`, derive
/// `Lt q n`. Verbatim copy of `factorization.rs`'s private
/// `derive_q_lt_n` (this prelude's house style duplicates rather than
/// shares such helpers) — `pw ≥ 2` gives `2*q ≤ pw*q = n`
/// (`mul_le_mul_left` + `mul_comm`), and `2*q = q+q ≥ q+1 = succ q` since
/// `q ≥ 1` (`add_le_add_left`; `q+1 ≡ succ q` is definitional), so
/// `succ q ≤ n`.
#[allow(clippy::too_many_arguments)]
fn derive_cofactor_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pw: ExprId,
    n: ExprId,
    q: ExprId,
    heq: ExprId,
    hp2: ExprId,
    hq1: ExprId,
) -> ExprId {
    let one_v = d.num(1);
    let two = d.num(2);

    let step_a = d.lemma(p.mul_le_mul_left, &[q, two, pw, hp2]);
    let mc1 = d.lemma(p.mul_comm, &[q, two]);
    let mc2 = d.lemma(p.mul_comm, &[q, pw]);

    let q_two = d.mul(q, two);
    let q_pw = d.mul(q, pw);
    let two_q = d.mul(two, q);
    let pw_q = d.mul(pw, q);

    let motive_l = d.eq_motive(q_two, &|d, x| d.le(x, q_pw));
    let step_b = d.transport(q_two, motive_l, step_a, two_q, mc1);

    let motive_r = d.eq_motive(q_pw, &|d, x| d.le(two_q, x));
    let step_c = d.transport(q_pw, motive_r, step_b, pw_q, mc2);

    let heq_sym = d.symm(n, pw_q, heq);
    let motive_n = d.eq_motive(pw_q, &|d, x| d.le(two_q, x));
    let step_d = d.transport(pw_q, motive_n, step_c, n, heq_sym);

    let sm = d.lemma(p.succ_mul, &[one_v, q]);
    let one_mul_q = d.lemma(p.one_mul, &[q]);
    let one_q = d.mul(one_v, q);
    let cong_add = d.congr(one_q, q, one_mul_q, &|d, x| d.add(x, q));
    let add_one_q_q = d.add(one_q, q);
    let q_q = d.add(q, q);
    let two_q_eq_add_qq = d.trans(two_q, add_one_q_q, q_q, sm, cong_add);

    let motive_e = d.eq_motive(two_q, &|d, x| d.le(x, n));
    let step_e = d.transport(two_q, motive_e, step_d, q_q, two_q_eq_add_qq);

    let al = d.lemma(p.add_le_add_left, &[q, one_v, q, hq1]);
    let succ_q = d.succ(q);
    d.lemma(p.le_trans, &[succ_q, q_q, n, al, step_e])
}

/// Given `heq2 : Eq kx (mul q kprime)`, derive `Eq (mul a kx) (mul (mul a
/// kprime) q)` — the reassociation both `declare_totient_dvd_totient_mul`
/// and `declare_totient_mul_cofactor_bound` need to rewrite `totient (mul a
/// kx)` into `totient (mul x' q)` for `x' := mul a kprime`, the shape
/// `totient_dvd_totient_mul_prime` consumes.
fn reassociate_cofactor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    q: ExprId,
    kprime: ExprId,
    kx: ExprId,
    heq2: ExprId,
) -> ExprId {
    let mul_q_kprime = d.mul(q, kprime);
    let mul_kprime_q = d.mul(kprime, q);
    let comm1 = d.lemma(p.mul_comm, &[q, kprime]);
    let heq2b = d.trans(kx, mul_q_kprime, mul_kprime_q, heq2, comm1);

    let mul_a_kx = d.mul(a, kx);
    let mul_a_mul_kprime_q = d.mul(a, mul_kprime_q);
    let step1 = d.congr(kx, mul_kprime_q, heq2b, &|d, x| d.mul(a, x));

    let x_prime = d.mul(a, kprime);
    let mul_x_prime_q = d.mul(x_prime, q);
    let assoc = d.lemma(p.mul_assoc, &[a, kprime, q]);
    // assoc : Eq (mul (mul a kprime) q) (mul a (mul kprime q))
    let assoc_sym = d.symm(mul_x_prime_q, mul_a_mul_kprime_q, assoc);

    d.trans(
        mul_a_kx,
        mul_a_mul_kprime_q,
        mul_x_prime_q,
        step1,
        assoc_sym,
    )
}

// ============================================================================
// `Nat.totient_dvd_totient_mul` — the fully general form, no hypothesis.
// ============================================================================

/// `Nat.totient_dvd_totient_mul : ∀ k a, Dvd (totient a) (totient (mul a
/// k))` — Target 1's engine. By well-founded induction on `k` (`Nat.lt`):
/// `k = 0` is `dvd_zero` (`totient (mul a 0) ≡ 0` by iota, since `mul`
/// recurses on its right argument), `k = 1` is `dvd_refl` transported along
/// `mul_one`, and `k = succ k' ≥ 2` peels a prime `q ∣ k` via
/// `exists_prime_dvd`, applies the induction hypothesis at the strictly
/// smaller cofactor `k' = k / q`, and extends one step with
/// `totient_dvd_totient_mul_prime`.
///
/// No factor multiset is named: the chain is built from **some**
/// factorisation of `k`, and nothing ever compares two factorisations
/// (ADR-0668).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_dvd_totient_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let zero_lvl = d.kernel().level_zero();

    // family(k) := ∀ a, Dvd (totient a) (totient (mul a k))
    let family_body = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let tot_a = d.const_app(p.totient, &[a]);
        let mul_ak = d.mul(a, k);
        let tot_ak = d.const_app(p.totient, &[mul_ak]);
        let body = d.dvd(tot_a, tot_ak);
        d.pi_fv(a_fv, nat, body)
    };

    let relation = d.kernel().const_(p.lt, vec![]);
    let family = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = family_body(d, k);
        d.lam_fv(k_fv, nat, body)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    let step = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let ih_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let lt_ty = d.lt(y, x);
            let family_y = family_body(d, y);
            let inner = d.arrow(lt_ty, family_y);
            d.pi_fv(y_fv, nat, inner)
        };
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);

        // `x` is a FREE VARIABLE here (the well-founded fix's own bound
        // variable), not a literal `0`/`succ _`. `cases_zero_succ`'s plain
        // `Nat.rec` case split gives a proof for a FRESH, unrelated
        // predecessor variable — it does NOT hand back an equation "x = succ
        // (that variable)", so a `Lt _ (succ that_variable)` built inside such
        // a branch cannot be transported to the `Lt _ x` the outer `ih`
        // demands. `Nat.zero_or_succ` (`x = 0 ∨ ∃ p, x = succ p`) gives a
        // genuine equation naming `x`, which is what makes the `ih`
        // application at the smaller cofactor legal.
        let goal = family_body(d, x);
        let disj = d.lemma(p.zero_or_succ, &[x]);
        let zero = d.zero();
        let eq_zero_ty = d.eq(x, zero);
        let succ_pred_ty = {
            let pv_fv = d.fresh_fvar();
            let pv = d.kernel().fvar(pv_fv);
            let spv = d.succ(pv);
            let body = d.eq(x, spv);
            d.lam_fv(pv_fv, nat, body)
        };
        let succ_ex_ty = {
            let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            d.apply(exists_c, &[nat, succ_pred_ty])
        };

        // ---- x = 0 ----
        let case_zero = {
            let hz_fv = d.fresh_fvar();
            let hz = d.kernel().fvar(hz_fv);
            let proof_at_zero = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let tot_a = d.const_app(p.totient, &[a]);
                let dz = d.lemma(p.dvd_zero, &[tot_a]);
                d.lam_fv(a_fv, nat, dz)
            };
            let hz_sym = d.symm(x, zero, hz);
            let motive_x = d.eq_motive(zero, &|d, t| family_body(d, t));
            let result = d.transport(zero, motive_x, proof_at_zero, x, hz_sym);
            d.lam_fv(hz_fv, eq_zero_ty, result)
        };

        // ---- x = succ pv ----
        let case_succ = {
            let hex_fv = d.fresh_fvar();
            let hex = d.kernel().fvar(hex_fv);
            let motive_ex = {
                let anon = d.anon_name();
                d.kernel()
                    .lam(anon, succ_ex_ty, goal, crate::BinderInfo::Default)
            };
            let minor = {
                let pv_fv = d.fresh_fvar();
                let pv = d.kernel().fvar(pv_fv);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let kx = d.succ(pv);
                let heq_ty = d.eq(x, kx);

                let disj_kx = d.lemma(p.two_le_succ_or_eq_one, &[pv]);
                let two = d.num(2);
                let one = d.num(1);
                let two_le_ty = d.le(two, kx);
                let eq_one_ty = d.eq(kx, one);
                let goal_kx = family_body(d, kx);

                // -- kx = 1 --
                let right_minor = {
                    let heq1_fv = d.fresh_fvar();
                    let heq1 = d.kernel().fvar(heq1_fv);
                    let a_fv = d.fresh_fvar();
                    let a = d.kernel().fvar(a_fv);
                    let tot_a = d.const_app(p.totient, &[a]);
                    let mul_a1 = d.mul(a, one);
                    let mo = d.lemma(p.mul_one, &[a]);
                    let mo_sym = d.symm(mul_a1, a, mo);
                    let dref = d.lemma(p.dvd_refl, &[tot_a]);
                    let motive_a = d.eq_motive(a, &|d, y| {
                        let toty = d.const_app(p.totient, &[y]);
                        d.dvd(tot_a, toty)
                    });
                    let proof_at_1 = d.transport(a, motive_a, dref, mul_a1, mo_sym);
                    let heq1_sym = d.symm(kx, one, heq1);
                    let motive_kx = d.eq_motive(one, &|d, y| {
                        let maxk = d.mul(a, y);
                        let totk = d.const_app(p.totient, &[maxk]);
                        d.dvd(tot_a, totk)
                    });
                    let result = d.transport(one, motive_kx, proof_at_1, kx, heq1_sym);
                    let body = d.lam_fv(a_fv, nat, result);
                    d.lam_fv(heq1_fv, eq_one_ty, body)
                };

                // -- kx >= 2 --
                let left_minor = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let ep = d.lemma(p.exists_prime_dvd, &[kx, h2]);

                    let pred_outer = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let prime_q_ty = prime_ty(d, &p, q);
                        let dvd_q_kx = d.dvd(q, kx);
                        let conj = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_kx]);
                        d.lam_fv(q_fv, nat, conj)
                    };
                    let motive_outer = {
                        let h_fv = d.fresh_fvar();
                        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                        let ex_ty = d.apply(ex_const, &[nat, pred_outer]);
                        d.lam_fv(h_fv, ex_ty, goal_kx)
                    };
                    let minor_outer = {
                        let q_fv = d.fresh_fvar();
                        let q = d.kernel().fvar(q_fv);
                        let hpand_fv = d.fresh_fvar();
                        let hpand = d.kernel().fvar(hpand_fv);
                        let (two_le_q_ty, divisor_q_ty) = prime_parts(d, &p, q);
                        let prime_q_ty = d.const_app(p.logic.and, &[two_le_q_ty, divisor_q_ty]);
                        let dvd_q_kx_ty = d.dvd(q, kx);
                        let hpand_ty = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_kx_ty]);

                        let prime_q = and_left(d, prime_q_ty, dvd_q_kx_ty, hpand);
                        let dvd_q_kx = and_right(d, prime_q_ty, dvd_q_kx_ty, hpand);
                        let hp2 = and_left(d, two_le_q_ty, divisor_q_ty, prime_q);

                        let pred_kprime = d.dvd_predicate(q, kx);
                        let motive_kprime = {
                            let h_fv = d.fresh_fvar();
                            let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                            let ex_ty = d.apply(ex_const, &[nat, pred_kprime]);
                            d.lam_fv(h_fv, ex_ty, goal_kx)
                        };
                        let minor_kprime = {
                            let kprime_fv = d.fresh_fvar();
                            let kprime = d.kernel().fvar(kprime_fv);
                            let heq2_fv = d.fresh_fvar();
                            let heq2 = d.kernel().fvar(heq2_fv);
                            let mul_q_kprime = d.mul(q, kprime);
                            let heq2_ty = d.eq(kx, mul_q_kprime);

                            let le_refl_one = d.lemma(p.le_refl, &[one]);
                            let le_one_two = d.lemma(p.le_step, &[one, one, le_refl_one]);
                            let h1_kx = d.lemma(p.le_trans, &[one, two, kx, le_one_two, h2]);
                            let motive_h1 = d.eq_motive(kx, &|d, y| {
                                let one_e = d.num(1);
                                d.le(one_e, y)
                            });
                            let h1_mul = d.transport(kx, motive_h1, h1_kx, mul_q_kprime, heq2);
                            let hq1 = d.lemma(p.one_le_right_of_mul, &[q, kprime, h1_mul]);

                            // `Lt kprime kx`, then transported to `Lt kprime x`
                            // via `heq : Eq x kx` — the outer `ih` is stated
                            // in terms of `x`, not `kx`.
                            let lt_proof_kx =
                                derive_cofactor_lt(d, &p, q, kx, kprime, heq2, hp2, hq1);
                            let heq_sym_lt = d.symm(x, kx, heq);
                            let motive_lt = d.eq_motive(kx, &|d, t| d.lt(kprime, t));
                            let lt_proof_x = d.transport(kx, motive_lt, lt_proof_kx, x, heq_sym_lt);

                            let a_fv = d.fresh_fvar();
                            let a = d.kernel().fvar(a_fv);
                            let tot_a = d.const_app(p.totient, &[a]);

                            let ih_kprime = d.apply(ih, &[kprime, lt_proof_x]);
                            let h1 = d.apply(ih_kprime, &[a]);

                            let x_prime = d.mul(a, kprime);
                            let tot_x_prime = d.const_app(p.totient, &[x_prime]);
                            let step_lemma =
                                d.lemma(p.totient_dvd_totient_mul_prime, &[x_prime, q]);
                            let h2step = d.apply(step_lemma, &[prime_q]);

                            let mul_x_prime_q = d.mul(x_prime, q);
                            let tot_x_prime_q = d.const_app(p.totient, &[mul_x_prime_q]);
                            let h_trans = d.lemma(
                                p.dvd_trans,
                                &[tot_a, tot_x_prime, tot_x_prime_q, h1, h2step],
                            );

                            let final_eq = reassociate_cofactor(d, &p, a, q, kprime, kx, heq2);
                            let mul_a_kx = d.mul(a, kx);
                            let tot_congr = d.congr(mul_a_kx, mul_x_prime_q, final_eq, &|d, y| {
                                d.const_app(p.totient, &[y])
                            });
                            let tot_ak = d.const_app(p.totient, &[mul_a_kx]);
                            let tot_congr_sym = d.symm(tot_ak, tot_x_prime_q, tot_congr);
                            let motive_final = d.eq_motive(tot_x_prime_q, &|d, t| d.dvd(tot_a, t));
                            let result = d.transport(
                                tot_x_prime_q,
                                motive_final,
                                h_trans,
                                tot_ak,
                                tot_congr_sym,
                            );

                            let body = d.lam_fv(a_fv, nat, result);
                            let inner = d.lam_fv(heq2_fv, heq2_ty, body);
                            d.lam_fv(kprime_fv, nat, inner)
                        };
                        let exists_rec_kprime =
                            d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                        let body_dvd = d.apply(
                            exists_rec_kprime,
                            &[nat, pred_kprime, motive_kprime, minor_kprime, dvd_q_kx],
                        );
                        let with_hpand = d.lam_fv(hpand_fv, hpand_ty, body_dvd);
                        d.lam_fv(q_fv, nat, with_hpand)
                    };
                    let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                    let body = d.apply(
                        exists_rec_outer,
                        &[nat, pred_outer, motive_outer, minor_outer, ep],
                    );
                    d.lam_fv(h2_fv, two_le_ty, body)
                };

                let proof_at_kx = or_cases(
                    d,
                    &p,
                    two_le_ty,
                    eq_one_ty,
                    goal_kx,
                    left_minor,
                    right_minor,
                    disj_kx,
                );

                let heq_sym = d.symm(x, kx, heq);
                let motive_x2 = d.eq_motive(kx, &|d, t| family_body(d, t));
                let result = d.transport(kx, motive_x2, proof_at_kx, x, heq_sym);

                let body = d.lam_fv(heq_fv, heq_ty, result);
                d.lam_fv(pv_fv, nat, body)
            };
            let exists_rec_ = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body = d.apply(exists_rec_, &[nat, succ_pred_ty, motive_ex, minor, hex]);
            d.lam_fv(hex_fv, succ_ex_ty, body)
        };

        let body = or_cases(
            d, &p, eq_zero_ty, succ_ex_ty, goal, case_zero, case_succ, disj,
        );
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        d.lam_fv(x_fv, nat, with_ih)
    };

    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one_lvl, zero_lvl]);
    let value = d.apply(fix, &[nat, relation, family, well_founded, step]);

    let stmt = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = family_body(d, k);
        d.pi_fv(k_fv, nat, body)
    };
    d.declare_theorem(p.totient_dvd_totient_mul, stmt, value)?;
    Ok(())
}

// ============================================================================
// `Nat.totient_dvd_of_dvd` — Target 1, the `ml430` mirror itself.
// ============================================================================

/// `Nat.totient_dvd_of_dvd : ∀ a b, Dvd a b → Dvd (totient a) (totient b)` —
/// `F:ml430-nat-totient-dvd-of-dvd-9622e44a`. Unpack `a ∣ b` into `b = a*k`
/// (`exists_rec`), apply [`declare_totient_dvd_totient_mul`] at `(k, a)`, and
/// transport along the extracted equation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_dvd_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    d.theorem(p.totient_dvd_of_dvd, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let dvd_ty = d.dvd(a, b);
        let tot_a = d.const_app(p.totient, &[a]);
        let tot_b = d.const_app(p.totient, &[b]);
        let target = d.dvd(tot_a, tot_b);
        let stmt = d.arrow(dvd_ty, target);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let pred_k = d.dvd_predicate(a, b);
        let motive_k = {
            let hh_fv = d.fresh_fvar();
            let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            let ex_ty = d.apply(ex_const, &[nat, pred_k]);
            d.lam_fv(hh_fv, ex_ty, target)
        };
        let minor_k = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let mul_ak = d.mul(a, k);
            let heq_ty = d.eq(b, mul_ak);

            let chain = d.lemma(p.totient_dvd_totient_mul, &[k, a]);
            let heq_sym = d.symm(b, mul_ak, heq);
            let motive_b = d.eq_motive(mul_ak, &|d, t| {
                let tot_t = d.const_app(p.totient, &[t]);
                d.dvd(tot_a, tot_t)
            });
            let result = d.transport(mul_ak, motive_b, chain, b, heq_sym);

            let body = d.lam_fv(heq_fv, heq_ty, result);
            d.lam_fv(k_fv, nat, body)
        };
        let exists_rec_ = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let proof = d.apply(exists_rec_, &[nat, pred_k, motive_k, minor_k, h]);
        let value = d.lam_fv(h_fv, dvd_ty, proof);
        (stmt, value)
    })?;
    Ok(())
}

/// Declare everything in this file, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_totient_dvd_chain_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_totient_dvd_totient_mul(d, p)?;
    declare_totient_dvd_of_dvd(d, p)?;
    Ok(())
}
