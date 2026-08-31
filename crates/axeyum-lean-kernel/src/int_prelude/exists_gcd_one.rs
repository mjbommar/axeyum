//! `Int.exists_gcd_one`/`Int.exists_gcd_one'` -- two `ml430` mirrors
//! (`F:ml430-int-exists-gcd-one-d8820780`, `F:ml430-int-exists-gcd-one-657db3e2`)
//! stating that dividing a pair by their own `gcd` leaves a coprime pair,
//! with the quotients exhibited as witnesses.
//!
//! Both reuse `gcd.rs`'s already-checked
//! [`declare_gcd_div_gcd_div_gcd`](super::gcd::declare_gcd_div_gcd_div_gcd)
//! for the coprimality half (`gcd (m.ediv c) (n.ediv c) = 1`, `c := ofNat
//! (gcd m n)`) and rebuild that theorem's private `exact` closure locally
//! (`a = c * (a.ediv c)`, given `c ∣ a` and `0 < c`'s `Nat` witness -- see
//! that declaration's own doc for the `emod_eq_zero_iff_dvd`/
//! `ediv_add_emod` derivation) to get `m = c*qm`/`n = c*qn`, commuted via
//! `mul_comm` to the fact's stated `m = qm*c`/`n = qn*c` order.
//!
//! [`declare_exists_gcd_one`] is the unprimed mirror, witnessing `m' :=
//! m.ediv c`, `n' := n.ediv c` directly. [`declare_exists_gcd_one_prime`]
//! is the primed, more general mirror (`g` itself existentially bound,
//! alongside `0 < g`); it reuses the SAME construction with `g := gcd m n`
//! and `h` (the fact's own hypothesis) doubling as the `0 < g` conjunct, so
//! no new arithmetic is needed beyond one more `Exists.intro`/`And.intro`
//! layer.

use super::dvd::idvd;
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Build `Exists Int predicate` / `Exists Nat predicate` witness
/// introduction, parametrized by the quantified type.
fn exists_intro_at(
    d: &mut IntDev<'_>,
    domain: ExprId,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[domain, predicate, witness, proof])
}

/// `Exists domain predicate`.
fn mk_exists_at(d: &mut IntDev<'_>, domain: ExprId, predicate: ExprId) -> ExprId {
    let one = d.level_one();
    let exists_name = d.int().logic.exists_;
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[domain, predicate])
}

/// `fun (n' : Int) => And (Eq Nat (gcd m' n') 1) (And (Eq Int m (m'*c)) (Eq
/// Int n (n'*c)))`, for a fixed outer witness `m'`.
fn coprime_and_eqs(d: &mut IntDev<'_>, m: ExprId, n: ExprId, c: ExprId, m_prime: ExprId) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let n_fv = d.fresh_fvar();
    let n_prime = d.kernel().fvar(n_fv);

    let g2 = d.const_app(p.gcd, &[m_prime, n_prime]);
    let one_nat = d.num(1);
    let eq1 = d.eq(g2, one_nat);

    let m_prime_c = d.imul(m_prime, c);
    let eq2 = d.ieq(m, m_prime_c);
    let n_prime_c = d.imul(n_prime, c);
    let eq3 = d.ieq(n, n_prime_c);

    let and23 = d.const_app(p.logic.and, &[eq2, eq3]);
    let body = d.const_app(p.logic.and, &[eq1, and23]);
    d.lam_fv(n_fv, int_ty, body)
}

/// `fun (m' : Int) => Exists (coprime_and_eqs m')`.
fn outer_witness_pred(d: &mut IntDev<'_>, m: ExprId, n: ExprId, c: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let m_fv = d.fresh_fvar();
    let m_prime = d.kernel().fvar(m_fv);
    let body = {
        let ip = coprime_and_eqs(d, m, n, c, m_prime);
        mk_exists_at(d, int_ty, ip)
    };
    d.lam_fv(m_fv, int_ty, body)
}

/// `a = c * (a.ediv c)`, given `dvd_c_a : idvd(c,a)` and the ambient `h : Lt
/// zero g` (`g` the `Nat` gcd, `c := ofNat g`) that
/// `emod_eq_zero_iff_dvd`/`gcd_div_gcd_div_gcd` both need. Local copy of
/// `gcd.rs::declare_gcd_div_gcd_div_gcd`'s private `exact` closure -- see
/// that declaration's doc for the derivation.
fn exact_division(d: &mut IntDev<'_>, c: ExprId, h: ExprId, a: ExprId, dvd_c_a: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let ediv_ac = d.iediv(a, c);
    let emod_ac = d.iemod(a, c);
    let zero_eq_ty = d.ieq(emod_ac, zero_i);
    let dvd_ty = idvd(d, c, a);
    let iff_ac = d.const_app(p.emod_eq_zero_iff_dvd, &[a, c, h]);
    let mpr = d.const_app(p.logic.iff_mpr, &[zero_eq_ty, dvd_ty, iff_ac]);
    let emod_eq_zero = d.apply(mpr, &[dvd_c_a]);

    let mul_q = d.imul(c, ediv_ac);
    let sum_with_emod = d.iadd(mul_q, emod_ac);
    let full_eq = d.const_app(p.ediv_add_emod, &[a, c]); // Eq(sum_with_emod, a)
    let full_eq_rev = d.isymm(sum_with_emod, a, full_eq); // Eq(a, sum_with_emod)
    let sum_with_zero = d.iadd(mul_q, zero_i);
    let step = d.icongr(emod_ac, zero_i, emod_eq_zero, &|d, x| d.iadd(mul_q, x));
    let add_zero_q = d.const_app(p.add_zero, &[mul_q]); // Eq(sum_with_zero, mul_q)
    let (_, chained) = d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
    d.itrans(a, sum_with_emod, mul_q, full_eq_rev, chained) // Eq(a, c*(a/c))
}

/// Shared core: given `m, n, h : Lt zero g` (`g := gcd m n`, `c := ofNat
/// g`), build `(qm, qn, and_all)` where `qm := m.ediv c`, `qn := n.ediv c`,
/// and `and_all : And (Eq Nat (gcd qm qn) 1) (And (Eq Int m (qm*c)) (Eq Int
/// n (qn*c)))`.
fn build_core(
    d: &mut IntDev<'_>,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    c: ExprId,
    h: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = d.int();
    let dvd_c_m = d.const_app(p.gcd_dvd_left, &[m, n]);
    let dvd_c_n = d.const_app(p.gcd_dvd_right, &[m, n]);
    let m_eq_cqm = exact_division(d, c, h, m, dvd_c_m); // Eq(m, c*qm)
    let n_eq_cqn = exact_division(d, c, h, n, dvd_c_n); // Eq(n, c*qn)

    let qm = d.iediv(m, c);
    let qn = d.iediv(n, c);
    let c_qm = d.imul(c, qm);
    let qm_c = d.imul(qm, c);
    let comm_m = d.const_app(p.mul_comm, &[c, qm]); // Eq(c*qm, qm*c)
    let m_eq_qmc = d.itrans(m, c_qm, qm_c, m_eq_cqm, comm_m);
    let c_qn = d.imul(c, qn);
    let qn_c = d.imul(qn, c);
    let comm_n = d.const_app(p.mul_comm, &[c, qn]); // Eq(c*qn, qn*c)
    let n_eq_qnc = d.itrans(n, c_qn, qn_c, n_eq_cqn, comm_n);

    let coprime = d.lemma(p.gcd_div_gcd_div_gcd, &[m, n, h]); // Eq Nat (gcd qm qn) 1
    let _ = g;

    let eq2_ty = d.ieq(m, qm_c);
    let eq3_ty = d.ieq(n, qn_c);
    let and23 = d.const_app(p.logic.and_intro, &[eq2_ty, eq3_ty, m_eq_qmc, n_eq_qnc]);
    let one_nat = d.num(1);
    let g2 = d.const_app(p.gcd, &[qm, qn]);
    let eq1_ty = d.eq(g2, one_nat);
    let and23_ty = d.const_app(p.logic.and, &[eq2_ty, eq3_ty]);
    let and_all = d.const_app(p.logic.and_intro, &[eq1_ty, and23_ty, coprime, and23]);
    (qm, qn, and_all)
}

/// `Int.exists_gcd_one : ∀ m n, Lt zero (gcd m n) → Exists (fun m' => Exists
/// (fun n' => And (Eq Nat (gcd m' n') 1) (And (Eq Int m (m'*ofNat (gcd m n)))
/// (Eq Int n (n'*ofNat (gcd m n))))))`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_exists_gcd_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.exists_gcd_one, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let g = d.const_app(p.gcd, &[m, n]);
        let zero_nat = d.zero();
        let hyp_ty = d.lt(zero_nat, g);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let c = d.of_nat(g);

        let (qm, qn, and_all) = build_core(d, m, n, g, c, h);

        let int_ty = d.int_ty();
        let ip = coprime_and_eqs(d, m, n, c, qm);
        let inner_ex = exists_intro_at(d, int_ty, ip, qn, and_all);
        let op = outer_witness_pred(d, m, n, c);
        let outer_ex = exists_intro_at(d, int_ty, op, qm, inner_ex);

        let goal = mk_exists_at(d, int_ty, op);
        let stmt = d.arrow(hyp_ty, goal);
        let proof = d.lam_fv(h_fv, hyp_ty, outer_ex);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.exists_gcd_one' : ∀ m n, Lt zero (gcd m n) → Exists (fun g => And (Lt zero g) (Exists (fun m' => Exists (fun n' => And (Eq Nat (gcd m' n') 1) (And (Eq Int m (m'*ofNat g)) (Eq Int n (n'*ofNat g)))))))`.
///
/// Reuses [`declare_exists_gcd_one`]'s construction at `g := gcd m n`; `h`
/// itself is the `Lt zero g` conjunct.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_exists_gcd_one_prime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.exists_gcd_one_prime, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let g = d.const_app(p.gcd, &[m, n]);
        let zero_nat = d.zero();
        let hyp_ty = d.lt(zero_nat, g);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let c = d.of_nat(g);

        let (qm, qn, and_all) = build_core(d, m, n, g, c, h);

        let int_ty = d.int_ty();
        let ip = coprime_and_eqs(d, m, n, c, qm);
        let inner_ex = exists_intro_at(d, int_ty, ip, qn, and_all);
        let op = outer_witness_pred(d, m, n, c);
        let outer_ex = exists_intro_at(d, int_ty, op, qm, inner_ex);
        let exists_m_n = mk_exists_at(d, int_ty, op);

        // `And (Lt zero g) exists_m_n`, at this concrete `g`.
        let and_with_pos = d.const_app(p.logic.and_intro, &[hyp_ty, exists_m_n, h, outer_ex]);

        // Wrap in `Exists (fun g' : Nat => And (Lt zero g') <exists_m_n at g'>)`.
        let nat = d.nat_ty();
        let g_pred = {
            let g_fv = d.fresh_fvar();
            let g_var = d.kernel().fvar(g_fv);
            let c_var = d.of_nat(g_var);
            let hyp_at = d.lt(zero_nat, g_var);
            let op_at = outer_witness_pred(d, m, n, c_var);
            let exists_at = mk_exists_at(d, int_ty, op_at);
            let body = d.const_app(p.logic.and, &[hyp_at, exists_at]);
            d.lam_fv(g_fv, nat, body)
        };
        let full_ex = exists_intro_at(d, nat, g_pred, g, and_with_pos);
        let goal = mk_exists_at(d, nat, g_pred);

        let stmt = d.arrow(hyp_ty, goal);
        let proof = d.lam_fv(h_fv, hyp_ty, full_ex);
        (stmt, proof)
    })?;
    Ok(())
}
