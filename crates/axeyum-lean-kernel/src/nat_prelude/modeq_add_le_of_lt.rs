//! `Nat.mod_eq_add_le_of_lt : ∀ {m a b}, modEq m a b → a < b → a + m ≤ b`.
//! Closes `F:ml430-nat-modeq-add-le-of-lt-c774015b`.
//!
//! `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` (`modular.rs`). Given the
//! witnesses `u, v` with `a + m*u = b + m*v` and `a < b`, the argument is
//! pure order/monotonicity algebra with **no new lemma**: every step below
//! composes `add_le_add_left`/`le_of_add_le_add_left`/`le_of_add_le_add_right`
//! (`order.rs`), `mul_le_mul_left`/`lt_of_mul_lt_mul_left` (`mul_order_lemmas.rs`),
//! and `add_comm`/`add_assoc` (`add_basics.rs`/`algebra.rs`), all already
//! declared. A prior handoff (`docs/plan/status/329-nat-modeq-mirrors.md`)
//! judged this fact to need "2-3 new order/monotonicity lemmas" (an
//! `Lt`-to-existence bridge plus a `m*u>m*v -> u>v` cancellation); the
//! cancellation already existed as `lt_of_mul_lt_mul_left`, and the
//! existence-form `modEq` hands over witnesses directly, so no bridge is
//! needed at all.
//!
//! The chain, writing `X := m*u`, `Y := m*v`:
//!
//!   1. `hlt : a < b` is *definitionally* `Le (succ a) b` (`Nat.lt` unfolds
//!      to exactly that), so it can be fed directly wherever a `Le (succ a) b`
//!      argument is expected -- the same trick `mul_lt_mul_pos_left_core`
//!      uses for its `pos : Lt zero a` hypothesis.
//!   2. `add_le_add_left(X, succ a, b, hlt) : Le (X+succ a) (X+b)`, and
//!      `X+succ a` reduces (by `add`'s right-recursion) to `succ(X+a)` BY
//!      REFL -- so this term already has type `Lt (X+a) (X+b)` up to defeq.
//!   3. Commute `X+a` to `a+X` (`= a+m*u`, the witness equation's LHS
//!      verbatim) and substitute via the witness equation to `b+Y` on that
//!      side, then commute `X+b` to `b+X`: `Lt (b+Y) (b+X)`.
//!   4. `le_of_add_le_add_left(b, succ Y, X, ·) : Le (succ Y) X`, i.e.
//!      `Lt Y X` -- since `b+succ Y` reduces to `succ(b+Y)` BY REFL, no
//!      extra step bridges the succ.
//!   5. `lt_of_mul_lt_mul_left(m, v, u, ·) : Lt v u`, i.e. `Le (succ v) u`.
//!   6. `mul_le_mul_left(m, succ v, u, ·) : Le (m*succ v) (m*u)`, and
//!      `m*succ v` reduces to `Y+m` BY REFL (`mul`'s right-recursion) -- so
//!      this is `Le (Y+m) X`.
//!   7. Add `a` on the left, substitute `a+X` back to `b+Y` via the witness
//!      equation, then regroup `a+(Y+m)` to `(a+m)+Y` via `add_comm`+
//!      `add_assoc`, and cancel the shared `Y` on the right
//!      (`le_of_add_le_add_right`) to reach the goal `Le (a+m) b`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

pub(super) fn declare_mod_eq_add_le_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();

    // mod_eq_add_le_of_lt : modEq m a b → a < b → a + m ≤ b
    d.theorem(p.mod_eq_add_le_of_lt, 3, &|d, v| {
        let (m, a, b) = (v[0], v[1], v[2]);
        let mod_ty = d.mod_eq(m, a, b);
        let lt_ty = d.lt(a, b);
        let a_plus_m = d.add(a, m);
        let target = d.le(a_plus_m, b);

        let mod_fv = d.fresh_fvar();
        let mod_proof = d.kernel().fvar(mod_fv);
        let lt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(lt_fv);

        // Destructure `mod_proof : ∃ u v, a+m*u = b+m*v`, closing over `hlt`.
        let outer_predicate = d.mod_eq_outer_predicate(m, a, b);
        let outer_motive = d.kernel().lam(anon, mod_ty, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_exists = d.mod_eq_inner_exists(m, a, b, u);
            let inner_exists_fv = d.fresh_fvar();
            let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
            let inner_predicate = d.mod_eq_inner_predicate(m, a, b, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, target, BinderInfo::Default);
            let inner_minor = {
                let v_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(v_fv);
                let sum_left = d.mod_eq_sum(m, a, u);
                let sum_right = d.mod_eq_sum(m, b, vv);
                let eq_fv = d.fresh_fvar();
                let eq_ty = d.eq(sum_left, sum_right);
                let eq_proof = d.kernel().fvar(eq_fv);

                let body = core(d, &p, m, a, b, u, vv, hlt, sum_left, sum_right, eq_proof);

                let with_eq = d.lam_fv(eq_fv, eq_ty, body);
                d.lam_fv(v_fv, nat, with_eq)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[nat, inner_predicate, inner_motive, inner_minor, inner_exists_proof],
            );
            let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let one = d.level_one();
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[nat, outer_predicate, outer_motive, outer_minor, mod_proof],
        );

        let with_lt = d.lam_fv(lt_fv, lt_ty, body);
        let proof = d.lam_fv(mod_fv, mod_ty, with_lt);
        let lt_to_target = d.arrow(lt_ty, target);
        let stmt = d.arrow(mod_ty, lt_to_target);
        (stmt, proof)
    })?;

    Ok(())
}

/// The algebra core, given `u, v` and `eq_proof : Eq sum_left sum_right`
/// where `sum_left = a+m*u`, `sum_right = b+m*v`.
#[allow(clippy::too_many_arguments)]
fn core(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    a: ExprId,
    b: ExprId,
    u: ExprId,
    vv: ExprId,
    hlt: ExprId,
    sum_left: ExprId,
    sum_right: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let mu = d.mul(m, u);
    let mv = d.mul(m, vv);
    let succ_a = d.succ(a);

    // step1 : Le (mu+succ a) (mu+b)  == (by refl) Lt (mu+a) (mu+b)
    let step1 = d.lemma(p.add_le_add_left, &[mu, succ_a, b, hlt]);

    // Convert mu+a -> a+mu (== sum_left).
    let mu_a = d.add(mu, a);
    let mu_b = d.add(mu, b);
    let comm_mu_a = d.lemma(p.add_comm, &[mu, a]); // Eq (mu+a) (a+mu)
    let motive1 = d.eq_motive(mu_a, &|d, x| d.lt(x, mu_b));
    let step2 = d.transport(mu_a, motive1, step1, sum_left, comm_mu_a); // Lt sum_left mu_b

    // Substitute sum_left -> sum_right via the witness equation.
    let motive2 = d.eq_motive(sum_left, &|d, x| d.lt(x, mu_b));
    let step3 = d.transport(sum_left, motive2, step2, sum_right, eq_proof); // Lt sum_right mu_b

    // Convert mu+b -> b+mu.
    let b_mu = d.add(b, mu);
    let comm_mu_b = d.lemma(p.add_comm, &[mu, b]); // Eq (mu+b) (b+mu)
    let motive3 = d.eq_motive(mu_b, &|d, x| d.lt(sum_right, x));
    let step4 = d.transport(mu_b, motive3, step3, b_mu, comm_mu_b); // Lt sum_right b_mu
    // sum_right == b+mv, so step4 : Lt (b+mv) (b+mu) == Le (b+succ mv) (b+mu) by refl.

    // Cancel the shared `b`.
    let succ_mv = d.succ(mv);
    let step5 = d.lemma(p.le_of_add_le_add_left, &[b, succ_mv, mu, step4]); // Le (succ mv) mu == Lt mv mu

    // v < u.
    let huv = d.lemma(p.lt_of_mul_lt_mul_left, &[m, vv, u, step5]); // Lt vv u == Le (succ vv) u

    // m*(v+1) <= m*u  == (by refl) Le (mv+m) mu
    let succ_v = d.succ(vv);
    let step6 = d.lemma(p.mul_le_mul_left, &[m, succ_v, u, huv]);

    // Add `a` on the left: Le (a+(mv+m)) (a+mu)
    let mv_m = d.add(mv, m);
    let step7 = d.lemma(p.add_le_add_left, &[a, mv_m, mu, step6]);
    let a_mvm = d.add(a, mv_m);

    // Substitute a+mu (== sum_left) -> sum_right (== b+mv).
    let motive4 = d.eq_motive(sum_left, &|d, x| d.le(a_mvm, x));
    let step8 = d.transport(sum_left, motive4, step7, sum_right, eq_proof); // Le a_mvm sum_right

    // Regroup a+(mv+m) -> (a+m)+mv.
    let m_mv = d.add(m, mv);
    let comm_mv_m = d.lemma(p.add_comm, &[mv, m]); // Eq (mv+m) (m+mv)
    let eq_l1 = d.congr(mv_m, m_mv, comm_mv_m, &|d, x| d.add(a, x)); // Eq (a+(mv+m)) (a+(m+mv))
    let a_m = d.add(a, m);
    let am_mv = d.add(a_m, mv);
    let assoc1 = d.lemma(p.add_assoc, &[a, m, mv]); // Eq ((a+m)+mv) (a+(m+mv))
    let a_mmv = d.add(a, m_mv);
    let assoc1_symm = d.symm(am_mv, a_mmv, assoc1); // Eq (a+(m+mv)) ((a+m)+mv)
    let eq_l = d.trans(a_mvm, a_mmv, am_mv, eq_l1, assoc1_symm); // Eq (a+(mv+m)) ((a+m)+mv)

    let motive5 = d.eq_motive(a_mvm, &|d, x| d.le(x, sum_right));
    let step9 = d.transport(a_mvm, motive5, step8, am_mv, eq_l); // Le ((a+m)+mv) sum_right
    // sum_right == b+mv, so step9 : Le ((a+m)+mv) (b+mv).

    d.lemma(p.le_of_add_le_add_right, &[mv, a_m, b, step9]) // Le (a+m) b
}
