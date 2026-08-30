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
//! ## Target 3: `Nat.eq_or_eq_of_totient_eq_totient` —
//! `a ∣ b → φ(a) = φ(b) → a = b ∨ 2·a = b`
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
use super::helpers::{and_left, and_right, iff_forward};
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

// ============================================================================
// Target 3: `Nat.eq_or_eq_of_totient_eq_totient`, via
// `Nat.totient_mul_cofactor_bound`.
// ============================================================================

/// `Or (Le two kprime) (Eq kprime one)`, from `hq1 : Le one kprime`. Unlike
/// [`super::totient_prime_pow`]-style helpers this is a genuine `Or`-typed
/// FACT (not a `Nat.rec` case split discarding the equation back to
/// `kprime`), built the same way [`NatPrelude::zero_or_succ`] is meant to be
/// consumed: `le_dest` exposes `kprime` as `succ kk` for a fresh `kk`, then
/// [`NatPrelude::two_le_succ_or_eq_one`] supplies the disjunction at `kk`,
/// transported back onto `kprime` via the exposed equation (not
/// case-analysed further — the whole `Or` is transported in one motive).
fn one_le_dichotomy(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    kprime: ExprId,
    hq1: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = *p;
    let nat = d.nat_ty();
    let one_v = d.num(1);
    let two = d.num(2);
    let one_lvl = d.level_one();

    let two_le_ty = d.le(two, kprime);
    let eq_one_ty = d.eq(kprime, one_v);
    let goal = d.const_app(p.logic.or, &[two_le_ty, eq_one_ty]);

    let dest = d.lemma(p.le_dest, &[one_v, kprime, hq1]);
    let pred_kk = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let one_kk = d.add(one_v, kk);
        let eqn = d.eq(one_kk, kprime);
        d.lam_fv(kk_fv, nat, eqn)
    };
    let motive_kk = {
        let h_fv = d.fresh_fvar();
        let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        let ex_ty = d.apply(ex_const, &[nat, pred_kk]);
        d.lam_fv(h_fv, ex_ty, goal)
    };
    let minor_kk = {
        let kk_fv = d.fresh_fvar();
        let kk = d.kernel().fvar(kk_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let one_kk = d.add(one_v, kk);
        let hk_ty = d.eq(one_kk, kprime);

        let zero_v = d.zero();
        let sa = d.lemma(p.succ_add, &[zero_v, kk]);
        let za = d.lemma(p.zero_add, &[kk]);
        let zero_kk = d.add(zero_v, kk);
        let succ_kk = d.succ(kk);
        let cong = d.congr(zero_kk, kk, za, &|d, x| d.succ(x));
        let succ_zero_kk = d.succ(zero_kk);
        let add_one_kk_eq_succ_kk = d.trans(one_kk, succ_zero_kk, succ_kk, sa, cong);
        let symm_add_one_kk = d.symm(one_kk, succ_kk, add_one_kk_eq_succ_kk);
        let succ_kk_eq_kprime = d.trans(succ_kk, one_kk, kprime, symm_add_one_kk, hk);

        let tw = d.lemma(p.two_le_succ_or_eq_one, &[kk]);
        let motive_or = d.eq_motive(succ_kk, &|d, x| {
            let two_e = d.num(2);
            let one_e = d.num(1);
            let l = d.le(two_e, x);
            let r = d.eq(x, one_e);
            d.const_app(p.logic.or, &[l, r])
        });
        let transported = d.transport(succ_kk, motive_or, tw, kprime, succ_kk_eq_kprime);

        let inner = d.lam_fv(hk_fv, hk_ty, transported);
        d.lam_fv(kk_fv, nat, inner)
    };
    let exists_rec_kk = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    let disj = d.apply(exists_rec_kk, &[nat, pred_kk, motive_kk, minor_kk, dest]);
    (two_le_ty, eq_one_ty, disj)
}

/// `Le x (mul two x)`, for ANY `x` (no positivity needed): `mul two x = add
/// x x` (via `mul_comm` plus `mul`'s own iota unfold at the concrete literal
/// `two`, closed by `zero_add`), and `le_add_right(x, x)` gives `Le x (add x
/// x)` directly.
fn le_self_two_mul(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let two = d.num(2);

    let comm = d.lemma(p.mul_comm, &[two, x]);
    let mul_two_x = d.mul(two, x);
    let mul_x_two = d.mul(x, two);

    let zero_x = d.add(zero, x);
    let za = d.lemma(p.zero_add, &[x]);
    let cong_za = d.congr(zero_x, x, za, &|d, y| d.add(y, x));
    // `cong_za : Eq (add zero_x x) (add x x)`, and `add zero_x x` is
    // DEFEQ to `mul_x_two` (`mul` iota-unfolds twice at the concrete `two`).
    let add_x_x = d.add(x, x);
    let two_mul_eq_add = d.trans(mul_two_x, mul_x_two, add_x_x, comm, cong_za);

    let ladd = d.lemma(p.le_add_right, &[x, x]);
    let two_mul_eq_add_sym = d.symm(mul_two_x, add_x_x, two_mul_eq_add);
    let motive = d.eq_motive(add_x_x, &|d, y| d.le(x, y));
    d.transport(add_x_x, motive, ladd, mul_two_x, two_mul_eq_add_sym)
}

/// The single-prime-step bound: `Or (Le (mul two (totient ap)) (totient (mul
/// ap q))) (And (Eq q two) (Eq (totient (mul ap q)) (totient ap)))`, for a
/// prime `q` (`prime_q : PrimeCond q`, `hp2 : Le two q`) and any `ap`.
///
/// One case split on [`NatPrelude::coprime_or_dvd_of_prime`]:
///
/// - **dvd branch** (`q ∣ ap`): [`NatPrelude::totient_mul_of_dvd`] gives
///   `totient (ap*q) = totient(ap)*q`, and `q ≥ 2` (`hp2`) makes this ALWAYS
///   the first disjunct — no further split on `q` needed.
/// - **coprime branch** (`gcd q ap = 1`):
///   [`NatPrelude::totient_mul_of_coprime`] plus
///   [`NatPrelude::totient_prime`] give `totient (ap*q) =
///   totient(ap)*(q-1)`. Splitting `q` via `Nat.lt_or_eq_of_le` at `2 ≤ q`:
///   `q = 2` gives the multiplier `q-1 = 1` exactly — the second disjunct,
///   the ONLY way this whole bound's second disjunct is ever reached; `q >
///   2` gives `q-1 ≥ 2` (via `Nat.pred_le_pred` at `3 ≤ q`, using `sub q 1 ≡
///   pred q` by pure iota — `sub`'s recursion is on its RIGHT argument,
///   `one`, which is concrete regardless of `q`) — the first disjunct.
fn single_prime_step_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ap: ExprId,
    q: ExprId,
    prime_q: ExprId,
    hp2: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let tot_ap = d.const_app(p.totient, &[ap]);
    let apq = d.mul(ap, q);
    let tot_apq = d.const_app(p.totient, &[apq]);
    let two_tot_ap = d.mul(two, tot_ap);
    let left_ty = d.le(two_tot_ap, tot_apq);
    let eq_q_two_ty = d.eq(q, two);
    let eq_tot_ty = d.eq(tot_apq, tot_ap);
    let right_ty = d.const_app(p.logic.and, &[eq_q_two_ty, eq_tot_ty]);
    let goal = d.const_app(p.logic.or, &[left_ty, right_ty]);

    let decided = d.lemma(p.coprime_or_dvd_of_prime, &[q, ap, prime_q]);
    let gcd_q_ap = d.gcd(q, ap);
    let coprime_ty = d.eq(gcd_q_ap, one);
    let dvd_ty = d.dvd(q, ap);

    // --- COPRIME branch ---
    let coprime_minor = {
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let gcd_ap_q = d.gcd(ap, q);
        let comm = d.lemma(p.gcd_comm, &[q, ap]);
        let comm_sym = d.symm(gcd_q_ap, gcd_ap_q, comm);
        let hx = d.trans(gcd_ap_q, gcd_q_ap, one, comm_sym, hc);

        let eqmul = d.lemma(p.totient_mul_of_coprime, &[ap, q, hx]);
        let tot_q = d.const_app(p.totient, &[q]);
        let mul_tot_ap_tot_q = d.mul(tot_ap, tot_q);

        let tot_q_eq = d.lemma(p.totient_prime, &[q, prime_q]);
        let sub_q_1 = d.sub(q, one);
        let cong_step = d.congr(tot_q, sub_q_1, tot_q_eq, &|d, t| d.mul(tot_ap, t));
        let mul_tot_ap_sub = d.mul(tot_ap, sub_q_1);
        let combined = d.trans(tot_apq, mul_tot_ap_tot_q, mul_tot_ap_sub, eqmul, cong_step);

        let split2 = d.lemma(p.lt_or_eq_of_le, &[two, q, hp2]);
        let lt2q_ty = d.lt(two, q);
        let eq2q_ty = d.eq(two, q);

        // -- Eq two q (q = 2, the only reachable second-disjunct case) --
        let case_eq2 = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let qeq2 = d.symm(two, q, h2);
            let sub2_1 = d.sub(two, one);
            let subcong = d.congr(q, two, qeq2, &|d, x| d.sub(x, one));
            let one_refl = d.refl(one);
            let sub_eq_one = d.trans(sub_q_1, sub2_1, one, subcong, one_refl);
            let cong2 = d.congr(sub_q_1, one, sub_eq_one, &|d, t| d.mul(tot_ap, t));
            let mul_tot_ap_one = d.mul(tot_ap, one);
            let mo = d.lemma(p.mul_one, &[tot_ap]);
            let step_a = d.trans(mul_tot_ap_sub, mul_tot_ap_one, tot_ap, cong2, mo);
            let final_eq = d.trans(tot_apq, mul_tot_ap_sub, tot_ap, combined, step_a);
            let and_proof =
                d.const_app(p.logic.and_intro, &[eq_q_two_ty, eq_tot_ty, qeq2, final_eq]);
            let or_r = d.const_app(p.logic.or_inr, &[left_ty, right_ty, and_proof]);
            d.lam_fv(h2_fv, eq2q_ty, or_r)
        };

        // -- Lt two q (q > 2) --
        let case_lt2 = {
            let h3_fv = d.fresh_fvar();
            let h3 = d.kernel().fvar(h3_fv);
            let succ_two = d.succ(two);
            let two_le_sub = d.lemma(p.pred_le_pred, &[succ_two, q, h3]);
            let ml = d.lemma(p.mul_le_mul_left, &[tot_ap, two, sub_q_1, two_le_sub]);
            let mul_tot_ap_two = d.mul(tot_ap, two);
            let motive_le = d.eq_motive(mul_tot_ap_sub, &|d, x| d.le(mul_tot_ap_two, x));
            let combined_sym = d.symm(tot_apq, mul_tot_ap_sub, combined);
            let step_b = d.transport(mul_tot_ap_sub, motive_le, ml, tot_apq, combined_sym);
            let comm_two = d.lemma(p.mul_comm, &[tot_ap, two]);
            let motive_le2 = d.eq_motive(mul_tot_ap_two, &|d, x| d.le(x, tot_apq));
            let step_c = d.transport(mul_tot_ap_two, motive_le2, step_b, two_tot_ap, comm_two);
            let or_intro_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, step_c]);
            d.lam_fv(h3_fv, lt2q_ty, or_intro_l)
        };

        let inner = or_cases(d, &p, lt2q_ty, eq2q_ty, goal, case_lt2, case_eq2, split2);
        d.lam_fv(hc_fv, coprime_ty, inner)
    };

    // --- DVD branch: q | ap always gives multiplier q >= 2 ---
    let dvd_minor = {
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);
        let eqmul = d.lemma(p.totient_mul_of_dvd, &[ap, q]);
        let eqmul_applied = d.apply(eqmul, &[hd]);
        let mul_tot_ap_q = d.mul(tot_ap, q);
        let ml = d.lemma(p.mul_le_mul_left, &[tot_ap, two, q, hp2]);
        let mul_tot_ap_two = d.mul(tot_ap, two);
        let eqmul_sym = d.symm(tot_apq, mul_tot_ap_q, eqmul_applied);
        let motive_le = d.eq_motive(mul_tot_ap_q, &|d, x| d.le(mul_tot_ap_two, x));
        let step_a = d.transport(mul_tot_ap_q, motive_le, ml, tot_apq, eqmul_sym);
        let comm_two = d.lemma(p.mul_comm, &[tot_ap, two]);
        let motive_le2 = d.eq_motive(mul_tot_ap_two, &|d, x| d.le(x, tot_apq));
        let step_b = d.transport(mul_tot_ap_two, motive_le2, step_a, two_tot_ap, comm_two);
        let or_intro_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, step_b]);
        d.lam_fv(hd_fv, dvd_ty, or_intro_l)
    };

    or_cases(
        d,
        &p,
        coprime_ty,
        dvd_ty,
        goal,
        coprime_minor,
        dvd_minor,
        decided,
    )
}

/// `Nat.totient_mul_cofactor_bound : ∀ k a, Le one (totient a) → Le two k →
/// Or (Le (mul two (totient a)) (totient (mul a k))) (And (Eq k two) (Eq
/// (totient (mul a k)) (totient a)))`.
///
/// By well-founded induction on the cofactor `k` (`Nat.lt`), the same
/// generic fixpoint [`declare_totient_dvd_totient_mul`] uses. The `Le two k`
/// guard means `k < 2` never needs handling inside the step (`factorization.
/// rs`'s pattern) — no `zero_or_succ` split is needed here, unlike
/// [`declare_totient_dvd_totient_mul`], because this family's `ih` is never
/// applied to a value that needs relating back to the fix's own bound
/// variable through an equation exposed by a `Nat.rec` case split; `k` here
/// IS that bound variable throughout.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_mul_cofactor_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let zero_lvl = d.kernel().level_zero();

    let family_body = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let tot_a = d.const_app(p.totient, &[a]);
        let one = d.num(1);
        let two = d.num(2);
        let hpos_ty = d.le(one, tot_a);
        let two_le_k_ty = d.le(two, k);
        let mul_ak = d.mul(a, k);
        let tot_ak = d.const_app(p.totient, &[mul_ak]);
        let two_tot_a = d.mul(two, tot_a);
        let left_ty = d.le(two_tot_a, tot_ak);
        let eq_k_two_ty = d.eq(k, two);
        let eq_tot_ty = d.eq(tot_ak, tot_a);
        let right_ty = d.const_app(p.logic.and, &[eq_k_two_ty, eq_tot_ty]);
        let disj_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
        let inner = d.arrow(two_le_k_ty, disj_ty);
        let body = d.arrow(hpos_ty, inner);
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

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let tot_a = d.const_app(p.totient, &[a]);
        let one = d.num(1);
        let two = d.num(2);
        let hpos_ty = d.le(one, tot_a);
        let hpos_fv = d.fresh_fvar();
        let hpos = d.kernel().fvar(hpos_fv);
        let h2_ty = d.le(two, x);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let mul_ax = d.mul(a, x);
        let tot_ax = d.const_app(p.totient, &[mul_ax]);
        let two_tot_a = d.mul(two, tot_a);
        let left_ty = d.le(two_tot_a, tot_ax);
        let eq_x_two_ty = d.eq(x, two);
        let eq_tot_ty = d.eq(tot_ax, tot_a);
        let right_ty = d.const_app(p.logic.and, &[eq_x_two_ty, eq_tot_ty]);
        let goal = d.const_app(p.logic.or, &[left_ty, right_ty]);

        let ep = d.lemma(p.exists_prime_dvd, &[x, h2]);

        let pred_outer = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let prime_q_ty = prime_ty(d, &p, q);
            let dvd_q_x = d.dvd(q, x);
            let conj = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_x]);
            d.lam_fv(q_fv, nat, conj)
        };
        let motive_outer = {
            let h_fv = d.fresh_fvar();
            let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            let ex_ty = d.apply(ex_const, &[nat, pred_outer]);
            d.lam_fv(h_fv, ex_ty, goal)
        };
        let minor_outer = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let hpand_fv = d.fresh_fvar();
            let hpand = d.kernel().fvar(hpand_fv);
            let (two_le_q_ty, divisor_q_ty) = prime_parts(d, &p, q);
            let prime_q_ty = d.const_app(p.logic.and, &[two_le_q_ty, divisor_q_ty]);
            let dvd_q_x_ty = d.dvd(q, x);
            let hpand_ty = d.const_app(p.logic.and, &[prime_q_ty, dvd_q_x_ty]);

            let prime_q = and_left(d, prime_q_ty, dvd_q_x_ty, hpand);
            let dvd_q_x = and_right(d, prime_q_ty, dvd_q_x_ty, hpand);
            let hp2 = and_left(d, two_le_q_ty, divisor_q_ty, prime_q);

            let pred_kprime = d.dvd_predicate(q, x);
            let motive_kprime = {
                let h_fv = d.fresh_fvar();
                let ex_const = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                let ex_ty = d.apply(ex_const, &[nat, pred_kprime]);
                d.lam_fv(h_fv, ex_ty, goal)
            };
            let minor_kprime = {
                let kprime_fv = d.fresh_fvar();
                let kprime = d.kernel().fvar(kprime_fv);
                let heq2_fv = d.fresh_fvar();
                let heq2 = d.kernel().fvar(heq2_fv);
                let mul_q_kprime = d.mul(q, kprime);
                let heq2_ty = d.eq(x, mul_q_kprime);

                let le_refl_one = d.lemma(p.le_refl, &[one]);
                let le_one_two = d.lemma(p.le_step, &[one, one, le_refl_one]);
                let h1_x = d.lemma(p.le_trans, &[one, two, x, le_one_two, h2]);
                let motive_h1 = d.eq_motive(x, &|d, y| {
                    let one_e = d.num(1);
                    d.le(one_e, y)
                });
                let h1_mul = d.transport(x, motive_h1, h1_x, mul_q_kprime, heq2);
                let hq1 = d.lemma(p.one_le_right_of_mul, &[q, kprime, h1_mul]);
                let lt_proof = derive_cofactor_lt(d, &p, q, x, kprime, heq2, hp2, hq1);

                let x_prime = d.mul(a, kprime);
                let tot_x_prime = d.const_app(p.totient, &[x_prime]);

                let (two_le_kp_ty, eq_one_kp_ty, disj_kp) = one_le_dichotomy(d, &p, kprime, hq1);

                // ---- kprime = 1: use single_prime_step_bound(a, q) directly ----
                let case_kp1 = {
                    let heqkp1_fv = d.fresh_fvar();
                    let heqkp1 = d.kernel().fvar(heqkp1_fv);

                    // x_prime = mul a kprime = mul a 1 = a
                    let mo_a = d.lemma(p.mul_one, &[a]);
                    let cong_xp = d.congr(kprime, one, heqkp1, &|d, t| d.mul(a, t));
                    let mul_a_one = d.mul(a, one);
                    let xp_eq_mul_a_one = d.trans(x_prime, mul_a_one, a, cong_xp, mo_a);

                    // x = mul q kprime = mul q 1 = q
                    let mo_q = d.lemma(p.mul_one, &[q]);
                    let cong_x = d.congr(kprime, one, heqkp1, &|d, t| d.mul(q, t));
                    let mul_q_one = d.mul(q, one);
                    let mul_q_kp_eq_q = d.trans(mul_q_kprime, mul_q_one, q, cong_x, mo_q);
                    let x_eq_q = d.trans(x, mul_q_kprime, q, heq2, mul_q_kp_eq_q);

                    let bound = single_prime_step_bound(d, &p, a, q, prime_q, hp2);
                    // bound : Or (Le two_tot_a (totient (mul a q)))
                    //            (And (Eq q two) (Eq (totient (mul a q)) tot_a))
                    let mul_a_q = d.mul(a, q);
                    let tot_a_q = d.const_app(p.totient, &[mul_a_q]);
                    let left_q_ty = d.le(two_tot_a, tot_a_q);
                    let eq_q_two_ty = d.eq(q, two);
                    let eq_tot_q_ty = d.eq(tot_a_q, tot_a);
                    let right_q_ty = d.const_app(p.logic.and, &[eq_q_two_ty, eq_tot_q_ty]);

                    // rewrite `mul a q` -> `mul a x` via `x_eq_q`
                    let mul_a_x = d.mul(a, x);
                    let mul_a_x_eq_mul_a_q = d.congr(x, q, x_eq_q, &|d, y| d.mul(a, y));
                    // mul_a_x_eq_mul_a_q : Eq (mul a x) (mul a q)

                    let case_left = {
                        let hl_fv = d.fresh_fvar();
                        let hl = d.kernel().fvar(hl_fv);
                        let motive = d.eq_motive(mul_a_q, &|d, t| {
                            let tott = d.const_app(p.totient, &[t]);
                            d.le(two_tot_a, tott)
                        });
                        let sym_maq = d.symm(mul_a_x, mul_a_q, mul_a_x_eq_mul_a_q);
                        let result = d.transport(mul_a_q, motive, hl, mul_a_x, sym_maq);
                        let or_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, result]);
                        d.lam_fv(hl_fv, left_q_ty, or_l)
                    };
                    let case_right = {
                        let hr_fv = d.fresh_fvar();
                        let hr = d.kernel().fvar(hr_fv);
                        let eq_q2 = and_left(d, eq_q_two_ty, eq_tot_q_ty, hr);
                        let eq_totq = and_right(d, eq_q_two_ty, eq_tot_q_ty, hr);
                        // Eq x two : trans(x, q, two, x_eq_q, eq_q2)
                        let x_eq_two = d.trans(x, q, two, x_eq_q, eq_q2);
                        // Eq (totient (mul a x)) tot_a
                        let motive2 = d.eq_motive(mul_a_q, &|d, t| {
                            let tott = d.const_app(p.totient, &[t]);
                            d.eq(tott, tot_a)
                        });
                        let sym_maq2 = d.symm(mul_a_x, mul_a_q, mul_a_x_eq_mul_a_q);
                        let eq_tot_ax = d.transport(mul_a_q, motive2, eq_totq, mul_a_x, sym_maq2);
                        let and_p = d.const_app(
                            p.logic.and_intro,
                            &[eq_x_two_ty, eq_tot_ty, x_eq_two, eq_tot_ax],
                        );
                        let or_r = d.const_app(p.logic.or_inr, &[left_ty, right_ty, and_p]);
                        d.lam_fv(hr_fv, right_q_ty, or_r)
                    };
                    let result = or_cases(
                        d, &p, left_q_ty, right_q_ty, goal, case_left, case_right, bound,
                    );
                    let _ = xp_eq_mul_a_one;
                    d.lam_fv(heqkp1_fv, eq_one_kp_ty, result)
                };

                // ---- kprime >= 2 ----
                let case_kp_ge2 = {
                    let h2kp_fv = d.fresh_fvar();
                    let h2kp = d.kernel().fvar(h2kp_fv);
                    let ih_kprime = d.apply(ih, &[kprime, lt_proof]);
                    let ih_result = d.apply(ih_kprime, &[a]);
                    let ih_result = d.apply(ih_result, &[hpos]);
                    let ih_result = d.apply(ih_result, &[h2kp]);
                    // ih_result : Or (Le two_tot_a (totient x_prime))
                    //                (And (Eq kprime two) (Eq (totient x_prime) tot_a))
                    let left_kp_ty = d.le(two_tot_a, tot_x_prime);
                    let eq_kp2_ty = d.eq(kprime, two);
                    let eq_totxp_ty = d.eq(tot_x_prime, tot_a);
                    let right_kp_ty = d.const_app(p.logic.and, &[eq_kp2_ty, eq_totxp_ty]);

                    // final equation relating (mul a x) to (mul x_prime q)
                    let final_eq = reassociate_cofactor(d, &p, a, q, kprime, x, heq2);
                    let mul_a_x2 = d.mul(a, x);
                    let mul_xp_q = d.mul(x_prime, q);
                    let tot_mul_xp_q = d.const_app(p.totient, &[mul_xp_q]);
                    let tot_congr = d.congr(mul_a_x2, mul_xp_q, final_eq, &|d, y| {
                        d.const_app(p.totient, &[y])
                    });
                    let tot_congr_sym = d.symm(tot_ax, tot_mul_xp_q, tot_congr);

                    let case_ih_left = {
                        let hl_fv = d.fresh_fvar();
                        let hl = d.kernel().fvar(hl_fv);
                        // hl : Le two_tot_a tot_x_prime
                        let mono = le_self_two_mul(d, &p, tot_x_prime);
                        // NOT directly useful; instead use: from hl and the
                        // per-step monotone bound Le tot_x_prime tot_mul_xp_q.
                        let _ = mono;
                        let step_bound = single_prime_step_bound(d, &p, x_prime, q, prime_q, hp2);
                        // step_bound : Or (Le (mul two tot_x_prime) tot_mul_xp_q)
                        //                 (And (Eq q two) (Eq tot_mul_xp_q tot_x_prime))
                        let two_tot_xp = d.mul(two, tot_x_prime);
                        let sl_ty = d.le(two_tot_xp, tot_mul_xp_q);
                        let sq2_ty = d.eq(q, two);
                        let stot_ty = d.eq(tot_mul_xp_q, tot_x_prime);
                        let sr_ty = d.const_app(p.logic.and, &[sq2_ty, stot_ty]);

                        let case_sl = {
                            let hsl_fv = d.fresh_fvar();
                            let hsl = d.kernel().fvar(hsl_fv);
                            // hsl : Le two_tot_xp tot_mul_xp_q
                            // hl  : Le two_tot_a tot_x_prime
                            // want: Le two_tot_a tot_mul_xp_q, via
                            //   two_tot_a <= tot_x_prime <= two_tot_xp <= tot_mul_xp_q
                            // (tot_x_prime <= two_tot_xp is le_self_two_mul)
                            let selfle = le_self_two_mul(d, &p, tot_x_prime);
                            let step1 = d.lemma(
                                p.le_trans,
                                &[two_tot_a, tot_x_prime, two_tot_xp, hl, selfle],
                            );
                            let step2 = d.lemma(
                                p.le_trans,
                                &[two_tot_a, two_tot_xp, tot_mul_xp_q, step1, hsl],
                            );
                            let motive = d.eq_motive(tot_mul_xp_q, &|d, t| d.le(two_tot_a, t));
                            let result =
                                d.transport(tot_mul_xp_q, motive, step2, tot_ax, tot_congr_sym);
                            let or_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, result]);
                            d.lam_fv(hsl_fv, sl_ty, or_l)
                        };
                        let case_sr = {
                            // q = 2 here; but also x_prime's coprimality with 2
                            // is irrelevant -- we simply have an equation
                            // tot_mul_xp_q = tot_x_prime, and combine with
                            // hl : Le two_tot_a tot_x_prime to get
                            // Le two_tot_a tot_mul_xp_q -- WRONG DIRECTION,
                            // this would need tot_x_prime <= tot_mul_xp_q only
                            // (true, via le_refl + eq), so:
                            let hsr_fv = d.fresh_fvar();
                            let hsr = d.kernel().fvar(hsr_fv);
                            let stot = and_right(d, sq2_ty, stot_ty, hsr);
                            // stot : Eq tot_mul_xp_q tot_x_prime
                            let motive = d.eq_motive(tot_x_prime, &|d, t| d.le(two_tot_a, t));
                            let stot_sym = d.symm(tot_mul_xp_q, tot_x_prime, stot);
                            let result0 =
                                d.transport(tot_x_prime, motive, hl, tot_mul_xp_q, stot_sym);
                            let motive2 = d.eq_motive(tot_mul_xp_q, &|d, t| d.le(two_tot_a, t));
                            let result =
                                d.transport(tot_mul_xp_q, motive2, result0, tot_ax, tot_congr_sym);
                            let or_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, result]);
                            d.lam_fv(hsr_fv, sr_ty, or_l)
                        };
                        let result =
                            or_cases(d, &p, sl_ty, sr_ty, goal, case_sl, case_sr, step_bound);
                        d.lam_fv(hl_fv, left_kp_ty, result)
                    };
                    let case_ih_right = {
                        let hr_fv = d.fresh_fvar();
                        let hr = d.kernel().fvar(hr_fv);
                        let eq_kp2 = and_left(d, eq_kp2_ty, eq_totxp_ty, hr);
                        let eq_totxp = and_right(d, eq_kp2_ty, eq_totxp_ty, hr);
                        // x_prime = mul a kprime ~ mul a two, via eq_kp2
                        let mul_a_two = d.mul(a, two);
                        let xp_eq_mul_a_two = d.congr(kprime, two, eq_kp2, &|d, t| d.mul(a, t));
                        // Dvd two (mul a two) via dvd_mul_left, then transport
                        // back to Dvd two x_prime.
                        let dvd_two_mul_a_two = d.lemma(p.dvd_mul_left, &[two, a]);
                        let motive_dvd = d.eq_motive(mul_a_two, &|d, t| d.dvd(two, t));
                        let xp_eq_mul_a_two_sym = d.symm(x_prime, mul_a_two, xp_eq_mul_a_two);
                        let dvd_two_xp = d.transport(
                            mul_a_two,
                            motive_dvd,
                            dvd_two_mul_a_two,
                            x_prime,
                            xp_eq_mul_a_two_sym,
                        );

                        let split_q = d.lemma(p.lt_or_eq_of_le, &[two, q, hp2]);
                        let lt2q_ty = d.lt(two, q);
                        let eq2q_ty = d.eq(two, q);

                        let case_qeq2 = {
                            let hq2_fv = d.fresh_fvar();
                            let hq2 = d.kernel().fvar(hq2_fv);
                            // q = 2, and 2 | x_prime, so totient_mul_of_dvd
                            // applies directly at (x_prime, q) via dvd_two_xp
                            // transported along hq2.
                            let motive_dvd2 = d.eq_motive(two, &|d, y| d.dvd(y, x_prime));
                            let dvd_q_xp = d.transport(two, motive_dvd2, dvd_two_xp, q, hq2);
                            let eqmul = d.lemma(p.totient_mul_of_dvd, &[x_prime, q]);
                            let eqmul_applied = d.apply(eqmul, &[dvd_q_xp]);
                            // eqmul_applied : Eq tot_mul_xp_q (mul tot_x_prime q)
                            let mul_txp_q = d.mul(tot_x_prime, q);
                            let comm_q = d.lemma(p.mul_comm, &[tot_x_prime, q]);
                            // comm_q : Eq mul_txp_q (mul q tot_x_prime)
                            let mul_q_txp = d.mul(q, tot_x_prime);
                            let motive_c = d.eq_motive(q, &|d, y| {
                                let myx = d.mul(y, tot_x_prime);
                                d.eq(mul_txp_q, myx)
                            });
                            let hq2_sym = d.symm(two, q, hq2);
                            let cong_q2 = d.congr(q, two, hq2_sym, &|d, y| d.mul(y, tot_x_prime));
                            let _ = motive_c;
                            let two_txp = d.mul(two, tot_x_prime);
                            let mul_txp_q_eq_two_txp =
                                d.trans(mul_txp_q, mul_q_txp, two_txp, comm_q, cong_q2);
                            let tot_mxq_eq_two_txp = d.trans(
                                tot_mul_xp_q,
                                mul_txp_q,
                                two_txp,
                                eqmul_applied,
                                mul_txp_q_eq_two_txp,
                            );
                            // tot_mxq_eq_two_txp : Eq tot_mul_xp_q two_txp
                            let le_refl_two_txp = d.lemma(p.le_refl, &[two_txp]);
                            let motive_le = d.eq_motive(two_txp, &|d, t| d.le(two_txp, t));
                            let two_txp_eq_tot_mxq =
                                d.symm(tot_mul_xp_q, two_txp, tot_mxq_eq_two_txp);
                            let step_le = d.transport(
                                two_txp,
                                motive_le,
                                le_refl_two_txp,
                                tot_mul_xp_q,
                                two_txp_eq_tot_mxq,
                            );
                            // step_le : Le two_txp tot_mul_xp_q
                            let motive_final = d.eq_motive(tot_x_prime, &|d, t| {
                                let twot = d.mul(two, t);
                                d.le(twot, tot_mul_xp_q)
                            });
                            let step_final =
                                d.transport(tot_x_prime, motive_final, step_le, tot_a, eq_totxp);
                            // step_final : Le two_tot_a tot_mul_xp_q
                            let motive_ret = d.eq_motive(tot_mul_xp_q, &|d, t| d.le(two_tot_a, t));
                            let result = d.transport(
                                tot_mul_xp_q,
                                motive_ret,
                                step_final,
                                tot_ax,
                                tot_congr_sym,
                            );
                            let or_l = d.const_app(p.logic.or_inl, &[left_ty, right_ty, result]);
                            d.lam_fv(hq2_fv, eq2q_ty, or_l)
                        };

                        let case_qgt2 = {
                            let hq3_fv = d.fresh_fvar();
                            let hq3 = d.kernel().fvar(hq3_fv);
                            let bound = single_prime_step_bound(d, &p, x_prime, q, prime_q, hp2);
                            let two_txp = d.mul(two, tot_x_prime);
                            let sl_ty = d.le(two_txp, tot_mul_xp_q);
                            let sq2_ty = d.eq(q, two);
                            let stot_ty = d.eq(tot_mul_xp_q, tot_x_prime);
                            let sr_ty = d.const_app(p.logic.and, &[sq2_ty, stot_ty]);
                            let case_l = {
                                let hl2_fv = d.fresh_fvar();
                                let hl2 = d.kernel().fvar(hl2_fv);
                                let motive_final = d.eq_motive(tot_x_prime, &|d, t| {
                                    let twot = d.mul(two, t);
                                    d.le(twot, tot_mul_xp_q)
                                });
                                let step_final =
                                    d.transport(tot_x_prime, motive_final, hl2, tot_a, eq_totxp);
                                let motive_ret =
                                    d.eq_motive(tot_mul_xp_q, &|d, t| d.le(two_tot_a, t));
                                let result = d.transport(
                                    tot_mul_xp_q,
                                    motive_ret,
                                    step_final,
                                    tot_ax,
                                    tot_congr_sym,
                                );
                                let or_l =
                                    d.const_app(p.logic.or_inl, &[left_ty, right_ty, result]);
                                d.lam_fv(hl2_fv, sl_ty, or_l)
                            };
                            let case_r = {
                                // q = 2 contradicts hq3 : Lt two q via lt_irrefl
                                let hr2_fv = d.fresh_fvar();
                                let hr2 = d.kernel().fvar(hr2_fv);
                                let eqq2 = and_left(d, sq2_ty, stot_ty, hr2);
                                let motive_lt = d.eq_motive(q, &|d, y| d.lt(two, y));
                                let lt_two_two = d.transport(q, motive_lt, hq3, two, eqq2);
                                let false_proof = d.lemma(p.lt_irrefl, &[two, lt_two_two]);
                                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                                let anon = d.anon_name();
                                let motive_false = d.kernel().lam(
                                    anon,
                                    false_ty,
                                    goal,
                                    crate::BinderInfo::Default,
                                );
                                let level_zero = d.kernel().level_zero();
                                let false_rec =
                                    d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                                let ex_falso = d.apply(false_rec, &[motive_false, false_proof]);
                                d.lam_fv(hr2_fv, sr_ty, ex_falso)
                            };
                            let result = or_cases(d, &p, sl_ty, sr_ty, goal, case_l, case_r, bound);
                            d.lam_fv(hq3_fv, lt2q_ty, result)
                        };
                        let result =
                            or_cases(d, &p, lt2q_ty, eq2q_ty, goal, case_qgt2, case_qeq2, split_q);
                        d.lam_fv(hr_fv, right_kp_ty, result)
                    };
                    let result = or_cases(
                        d,
                        &p,
                        left_kp_ty,
                        right_kp_ty,
                        goal,
                        case_ih_left,
                        case_ih_right,
                        ih_result,
                    );
                    d.lam_fv(h2kp_fv, two_le_kp_ty, result)
                };

                let body = or_cases(
                    d,
                    &p,
                    two_le_kp_ty,
                    eq_one_kp_ty,
                    goal,
                    case_kp_ge2,
                    case_kp1,
                    disj_kp,
                );
                let inner = d.lam_fv(heq2_fv, heq2_ty, body);
                d.lam_fv(kprime_fv, nat, inner)
            };
            let exists_rec_kprime = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
            let body_dvd = d.apply(
                exists_rec_kprime,
                &[nat, pred_kprime, motive_kprime, minor_kprime, dvd_q_x],
            );
            let with_hpand = d.lam_fv(hpand_fv, hpand_ty, body_dvd);
            d.lam_fv(q_fv, nat, with_hpand)
        };
        let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let body = d.apply(
            exists_rec_outer,
            &[nat, pred_outer, motive_outer, minor_outer, ep],
        );
        let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_h2);
        let with_a = d.lam_fv(a_fv, nat, with_hpos);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_a);
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
    d.declare_theorem(p.totient_mul_cofactor_bound, stmt, value)?;
    Ok(())
}

/// `Nat.eq_or_eq_of_totient_eq_totient : ∀ a b, Dvd a b → Eq (totient a)
/// (totient b) → Or (Eq a b) (Eq (mul two a) b)` —
/// `F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7`, Target 3.
///
/// Unpacks `a ∣ b` into `b = a*k`. Splits on `a` (`Nat.zero_or_succ`):
/// `a = 0` forces `b = 0` too (`zero_mul`), giving `a = b` directly. For
/// `a ≥ 1` (hence `totient a ≥ 1`, via `Nat.totient_eq_zero`'s
/// contrapositive), splits on `k`: `k = 0` is refuted (it would force
/// `totient a = totient 0 = 0`, contradicting `totient a ≥ 1`); `k = 1`
/// gives `a = b` directly (`mul_one`); `k ≥ 2` invokes
/// [`declare_totient_mul_cofactor_bound`] — its first disjunct
/// (`totient b ≥ 2·totient a`) is refuted by the totient-equality hypothesis
/// combined with `totient a ≥ 1` (`2x ≤ x` is impossible for `x ≥ 1`,
/// `Nat.lt_irrefl` closes it), leaving only the second disjunct, `k = 2`,
/// from which `2·a = b` follows by `mul_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_eq_or_eq_of_totient_eq_totient(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    d.theorem(p.eq_or_eq_of_totient_eq_totient, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let dvd_ty = d.dvd(a, b);
        let tot_a = d.const_app(p.totient, &[a]);
        let tot_b = d.const_app(p.totient, &[b]);
        let tot_eq_ty = d.eq(tot_a, tot_b);
        let two = d.num(2);
        let two_a = d.mul(two, a);
        let eq_ab_ty = d.eq(a, b);
        let eq_2ab_ty = d.eq(two_a, b);
        let target = d.const_app(p.logic.or, &[eq_ab_ty, eq_2ab_ty]);
        let inner_arrow = d.arrow(tot_eq_ty, target);
        let stmt = d.arrow(dvd_ty, inner_arrow);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);

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
            let heqb_fv = d.fresh_fvar();
            let heqb = d.kernel().fvar(heqb_fv);
            let mul_ak = d.mul(a, k);
            let heqb_ty = d.eq(b, mul_ak);

            // heq_tot2 : Eq (totient a) (totient (mul a k))
            let motive_tot = d.eq_motive(b, &|d, x| {
                let totx = d.const_app(p.totient, &[x]);
                d.eq(tot_a, totx)
            });
            let heq_tot2 = d.transport(b, motive_tot, ht, mul_ak, heqb);

            let disj_a = d.lemma(p.zero_or_succ, &[a]);
            let zero = d.zero();
            let eq_a0_ty = d.eq(a, zero);
            let succ_pred_ty_a = {
                let pv_fv = d.fresh_fvar();
                let pv = d.kernel().fvar(pv_fv);
                let spv = d.succ(pv);
                let body = d.eq(a, spv);
                d.lam_fv(pv_fv, nat, body)
            };
            let succ_ex_ty_a = {
                let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                d.apply(exists_c, &[nat, succ_pred_ty_a])
            };

            // ---- a = 0 ----
            let case_a0 = {
                let ha0_fv = d.fresh_fvar();
                let ha0 = d.kernel().fvar(ha0_fv);
                let zm = d.lemma(p.zero_mul, &[k]);
                let cong_a0 = d.congr(a, zero, ha0, &|d, x| d.mul(x, k));
                let zero_k = d.mul(zero, k);
                let a_k_eq_zero = d.trans(mul_ak, zero_k, zero, cong_a0, zm);
                let b_eq_zero = d.trans(b, mul_ak, zero, heqb, a_k_eq_zero);
                let b_eq_zero_sym = d.symm(b, zero, b_eq_zero);
                let final_eq = d.trans(a, zero, b, ha0, b_eq_zero_sym);
                let or_l = d.const_app(p.logic.or_inl, &[eq_ab_ty, eq_2ab_ty, final_eq]);
                d.lam_fv(ha0_fv, eq_a0_ty, or_l)
            };

            // ---- a = succ p (a >= 1) ----
            let case_asucc = {
                let hex_fv = d.fresh_fvar();
                let hex = d.kernel().fvar(hex_fv);
                let motive_ex = {
                    let anon = d.anon_name();
                    d.kernel()
                        .lam(anon, succ_ex_ty_a, target, crate::BinderInfo::Default)
                };
                let minor = {
                    let pv_fv = d.fresh_fvar();
                    let pv = d.kernel().fvar(pv_fv);
                    let ha_fv = d.fresh_fvar();
                    let ha = d.kernel().fvar(ha_fv);
                    let succ_p = d.succ(pv);
                    let ha_ty = d.eq(a, succ_p);

                    let one = d.num(1);
                    let zls = d.lemma(p.zero_lt_succ, &[pv]);
                    // zls : Lt zero (succ p) ~ Le one (succ p)
                    let motive_pos = d.eq_motive(succ_p, &|d, x| {
                        let one_e = d.num(1);
                        d.le(one_e, x)
                    });
                    let ha_sym = d.symm(a, succ_p, ha);
                    let hpos_a = d.transport(succ_p, motive_pos, zls, a, ha_sym);
                    // hpos_a : Le one a

                    // a != 0
                    let a_ne_zero = {
                        let hz_fv = d.fresh_fvar();
                        let hz = d.kernel().fvar(hz_fv);
                        let motive = d.eq_motive(a, &|d, x| {
                            let one_e = d.num(1);
                            d.le(one_e, x)
                        });
                        let le_one_zero = d.transport(a, motive, hpos_a, zero, hz);
                        let nsl = d.lemma(p.not_succ_le_zero, &[zero]);
                        let absurd = d.apply(nsl, &[le_one_zero]);
                        let a_eq_zero_ty = d.eq(a, zero);
                        d.lam_fv(hz_fv, a_eq_zero_ty, absurd)
                    };
                    // totient a != 0
                    let tot_a_ne_zero = {
                        let ht0_fv = d.fresh_fvar();
                        let ht0 = d.kernel().fvar(ht0_fv);
                        let iff_ = d.lemma(p.totient_eq_zero, &[a]);
                        let tot_a_eq_zero_ty = d.eq(tot_a, zero);
                        let fwd = iff_forward(d, tot_a_eq_zero_ty, eq_a0_ty, iff_);
                        let derived = d.apply(fwd, &[ht0]);
                        let absurd = d.apply(a_ne_zero, &[derived]);
                        d.lam_fv(ht0_fv, tot_a_eq_zero_ty, absurd)
                    };
                    let hpos_tot = d.lemma(p.zero_lt_of_ne_zero, &[tot_a, tot_a_ne_zero]);
                    // hpos_tot : Lt zero (totient a) ~ Le one (totient a)

                    // ---- split k ----
                    let disj_k = d.lemma(p.zero_or_succ, &[k]);
                    let eq_k0_ty = d.eq(k, zero);
                    let succ_pred_ty_k = {
                        let pv2_fv = d.fresh_fvar();
                        let pv2 = d.kernel().fvar(pv2_fv);
                        let spv2 = d.succ(pv2);
                        let body = d.eq(k, spv2);
                        d.lam_fv(pv2_fv, nat, body)
                    };
                    let succ_ex_ty_k = {
                        let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
                        d.apply(exists_c, &[nat, succ_pred_ty_k])
                    };

                    // -- k = 0: contradiction --
                    let case_k0 = {
                        let hk0_fv = d.fresh_fvar();
                        let hk0 = d.kernel().fvar(hk0_fv);
                        let motive = d.eq_motive(k, &|d, x| {
                            let max = d.mul(a, x);
                            let totmax = d.const_app(p.totient, &[max]);
                            d.eq(tot_a, totmax)
                        });
                        let heq_tot0 = d.transport(k, motive, heq_tot2, zero, hk0);
                        // heq_tot0 : Eq tot_a (totient (mul a 0)), and
                        // `totient (mul a 0)` is DEFEQ to `zero` (mul a 0
                        // iota-reduces to 0; countRange's own base case gives
                        // totient 0 = 0 by refl).
                        let motive2 = d.eq_motive(tot_a, &|d, x| {
                            let one_e = d.num(1);
                            d.le(one_e, x)
                        });
                        let mul_a0 = d.mul(a, zero);
                        let tot_mul_a0 = d.const_app(p.totient, &[mul_a0]);
                        let le_one_totmul =
                            d.transport(tot_a, motive2, hpos_tot, tot_mul_a0, heq_tot0);
                        // le_one_totmul : Le one (totient (mul a 0)) ~ Le one zero
                        let nsl = d.lemma(p.not_succ_le_zero, &[zero]);
                        let absurd = d.apply(nsl, &[le_one_totmul]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let anon = d.anon_name();
                        let motive_false =
                            d.kernel()
                                .lam(anon, false_ty, target, crate::BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let ex_falso = d.apply(false_rec, &[motive_false, absurd]);
                        d.lam_fv(hk0_fv, eq_k0_ty, ex_falso)
                    };

                    // -- k = succ p2 --
                    let case_ksucc = {
                        let hex2_fv = d.fresh_fvar();
                        let hex2 = d.kernel().fvar(hex2_fv);
                        let motive_ex2 = {
                            let anon = d.anon_name();
                            d.kernel()
                                .lam(anon, succ_ex_ty_k, target, crate::BinderInfo::Default)
                        };
                        let minor2 = {
                            let pv2_fv = d.fresh_fvar();
                            let pv2 = d.kernel().fvar(pv2_fv);
                            let hk_fv = d.fresh_fvar();
                            let hk = d.kernel().fvar(hk_fv);
                            let kx = d.succ(pv2);
                            let hk_ty = d.eq(k, kx);

                            let disj2 = d.lemma(p.two_le_succ_or_eq_one, &[pv2]);
                            let two_le_kx_ty = d.le(two, kx);
                            let eq_kx1_ty = d.eq(kx, one);

                            // -- kx = 1 --
                            let case_kx1 = {
                                let heq1_fv = d.fresh_fvar();
                                let heq1 = d.kernel().fvar(heq1_fv);
                                let k_eq_one = d.trans(k, kx, one, hk, heq1);
                                let mul_a_one = d.mul(a, one);
                                let cong_k1 = d.congr(k, one, k_eq_one, &|d, x| d.mul(a, x));
                                let mo = d.lemma(p.mul_one, &[a]);
                                let mul_ak_eq_a = d.trans(mul_ak, mul_a_one, a, cong_k1, mo);
                                let b_eq_a = d.trans(b, mul_ak, a, heqb, mul_ak_eq_a);
                                let final_eq = d.symm(b, a, b_eq_a);
                                let or_l =
                                    d.const_app(p.logic.or_inl, &[eq_ab_ty, eq_2ab_ty, final_eq]);
                                d.lam_fv(heq1_fv, eq_kx1_ty, or_l)
                            };

                            // -- kx >= 2 --
                            let case_kx_ge2 = {
                                let h2_fv = d.fresh_fvar();
                                let h2 = d.kernel().fvar(h2_fv);
                                let bound = d.lemma(p.totient_mul_cofactor_bound, &[kx, a]);
                                let bound = d.apply(bound, &[hpos_tot]);
                                let bound_result = d.apply(bound, &[h2]);

                                let two_tot_a = d.mul(two, tot_a);
                                let mul_a_kx = d.mul(a, kx);
                                let tot_akx = d.const_app(p.totient, &[mul_a_kx]);
                                let left_b_ty = d.le(two_tot_a, tot_akx);
                                let eq_kx2_ty = d.eq(kx, two);
                                let eq_totakx_ty = d.eq(tot_akx, tot_a);
                                let right_b_ty =
                                    d.const_app(p.logic.and, &[eq_kx2_ty, eq_totakx_ty]);

                                // heq_tot_kx : Eq tot_a (totient (mul a kx))
                                let motive_kx = d.eq_motive(k, &|d, x| {
                                    let max = d.mul(a, x);
                                    let totmax = d.const_app(p.totient, &[max]);
                                    d.eq(tot_a, totmax)
                                });
                                let heq_tot_kx = d.transport(k, motive_kx, heq_tot2, kx, hk);
                                let heq_tot_kx_sym = d.symm(tot_a, tot_akx, heq_tot_kx);

                                let case_bl = {
                                    let hbl_fv = d.fresh_fvar();
                                    let hbl = d.kernel().fvar(hbl_fv);
                                    // hbl : Le two_tot_a tot_akx
                                    let motive = d.eq_motive(tot_akx, &|d, t| d.le(two_tot_a, t));
                                    let h1_sub =
                                        d.transport(tot_akx, motive, hbl, tot_a, heq_tot_kx_sym);
                                    // h1_sub : Le two_tot_a tot_a  -- IMPOSSIBLE

                                    // Eq two_tot_a (add tot_a tot_a)
                                    let comm = d.lemma(p.mul_comm, &[two, tot_a]);
                                    let mul_tot_a_two = d.mul(tot_a, two);
                                    let zero_ta = d.add(zero, tot_a);
                                    let za = d.lemma(p.zero_add, &[tot_a]);
                                    let cong_za =
                                        d.congr(zero_ta, tot_a, za, &|d, y| d.add(y, tot_a));
                                    let add_ta_ta = d.add(tot_a, tot_a);
                                    let two_mul_eq_add =
                                        d.trans(two_tot_a, mul_tot_a_two, add_ta_ta, comm, cong_za);
                                    let motive2 = d.eq_motive(two_tot_a, &|d, t| d.le(t, tot_a));
                                    let h1_sub2 = d.transport(
                                        two_tot_a,
                                        motive2,
                                        h1_sub,
                                        add_ta_ta,
                                        two_mul_eq_add,
                                    );
                                    // h1_sub2 : Le add_ta_ta tot_a

                                    let al =
                                        d.lemma(p.add_le_add_left, &[tot_a, one, tot_a, hpos_tot]);
                                    // al : Le (add tot_a one) (add tot_a tot_a)
                                    //    ~ Le (succ tot_a) add_ta_ta = Lt tot_a add_ta_ta
                                    let ltp = d.lemma(
                                        p.lt_of_lt_of_le,
                                        &[tot_a, add_ta_ta, tot_a, al, h1_sub2],
                                    );
                                    // ltp : Lt tot_a tot_a
                                    let false_proof = d.lemma(p.lt_irrefl, &[tot_a, ltp]);
                                    let false_ty2 = d.kernel().const_(p.logic.false_, vec![]);
                                    let anon2 = d.anon_name();
                                    let motive_false2 = d.kernel().lam(
                                        anon2,
                                        false_ty2,
                                        target,
                                        crate::BinderInfo::Default,
                                    );
                                    let level_zero2 = d.kernel().level_zero();
                                    let false_rec2 =
                                        d.kernel().const_(p.logic.false_rec, vec![level_zero2]);
                                    let ex_falso2 =
                                        d.apply(false_rec2, &[motive_false2, false_proof]);
                                    d.lam_fv(hbl_fv, left_b_ty, ex_falso2)
                                };
                                let case_br = {
                                    let hbr_fv = d.fresh_fvar();
                                    let hbr = d.kernel().fvar(hbr_fv);
                                    let eq_kx2 = and_left(d, eq_kx2_ty, eq_totakx_ty, hbr);
                                    // b = mul a k = mul a kx = mul a two = mul two a
                                    let cong_k_kx = d.congr(k, kx, hk, &|d, x| d.mul(a, x));
                                    let b_eq_mul_a_kx =
                                        d.trans(b, mul_ak, mul_a_kx, heqb, cong_k_kx);
                                    let mul_a_two = d.mul(a, two);
                                    let cong_kx2 = d.congr(kx, two, eq_kx2, &|d, x| d.mul(a, x));
                                    let b_eq_mul_a_two =
                                        d.trans(b, mul_a_kx, mul_a_two, b_eq_mul_a_kx, cong_kx2);
                                    let comm2 = d.lemma(p.mul_comm, &[a, two]);
                                    let b_eq_two_a =
                                        d.trans(b, mul_a_two, two_a, b_eq_mul_a_two, comm2);
                                    let final_eq = d.symm(b, two_a, b_eq_two_a);
                                    let or_r = d.const_app(
                                        p.logic.or_inr,
                                        &[eq_ab_ty, eq_2ab_ty, final_eq],
                                    );
                                    d.lam_fv(hbr_fv, right_b_ty, or_r)
                                };
                                let result = or_cases(
                                    d,
                                    &p,
                                    left_b_ty,
                                    right_b_ty,
                                    target,
                                    case_bl,
                                    case_br,
                                    bound_result,
                                );
                                d.lam_fv(h2_fv, two_le_kx_ty, result)
                            };

                            let result = or_cases(
                                d,
                                &p,
                                two_le_kx_ty,
                                eq_kx1_ty,
                                target,
                                case_kx_ge2,
                                case_kx1,
                                disj2,
                            );
                            let inner = d.lam_fv(hk_fv, hk_ty, result);
                            d.lam_fv(pv2_fv, nat, inner)
                        };
                        let exists_rec2 = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                        let body2 = d.apply(
                            exists_rec2,
                            &[nat, succ_pred_ty_k, motive_ex2, minor2, hex2],
                        );
                        d.lam_fv(hex2_fv, succ_ex_ty_k, body2)
                    };

                    let body_k = or_cases(
                        d,
                        &p,
                        eq_k0_ty,
                        succ_ex_ty_k,
                        target,
                        case_k0,
                        case_ksucc,
                        disj_k,
                    );
                    let inner = d.lam_fv(ha_fv, ha_ty, body_k);
                    d.lam_fv(pv_fv, nat, inner)
                };
                let exists_rec_a = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                let body = d.apply(exists_rec_a, &[nat, succ_pred_ty_a, motive_ex, minor, hex]);
                d.lam_fv(hex_fv, succ_ex_ty_a, body)
            };

            let body_a = or_cases(
                d,
                &p,
                eq_a0_ty,
                succ_ex_ty_a,
                target,
                case_a0,
                case_asucc,
                disj_a,
            );
            let inner = d.lam_fv(heqb_fv, heqb_ty, body_a);
            d.lam_fv(k_fv, nat, inner)
        };
        let exists_rec_ = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let proof_body = d.apply(exists_rec_, &[nat, pred_k, motive_k, minor_k, h]);
        let result = d.lam_fv(ht_fv, tot_eq_ty, proof_body);
        let value = d.lam_fv(h_fv, dvd_ty, result);
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
    declare_totient_mul_cofactor_bound(d, p)?;
    declare_eq_or_eq_of_totient_eq_totient(d, p)?;
    Ok(())
}
