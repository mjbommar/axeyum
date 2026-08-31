//! `∏_{k=1}^m (a·k) = a^m · m!` -- ADR-0990's item A for Gauss's lemma's
//! connecting-theorem assembly, and the second half of that item (the first,
//! `Int.prodRange_const_pow`, landed in `prod.rs` earlier this session).
//!
//! Combines two already-landed facts with no new induction: `Int.prodRange_mul`
//! (`prodRange (fun k => mul (f k) (g k)) m = mul (prodRange f m) (prodRange g
//! m)`) at `f := fun _ => a`, `g := fun k => ofNat (succ k)` -- the EXACT
//! lambda `Int.factorial`'s own `Definition` body uses
//! (`wilson.rs::declare_factorial`), so `prodRange g m` is defeq `factorial
//! m` with no rewrite -- and `Int.prodRange_const_pow` (`prodRange f m = pow
//! a m`). No case split, no new proof obligation beyond chaining the two.

use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun (_ : Nat) => a` -- local copy of `prod.rs`'s private `const_int_fn`
/// (not `pub(super)` there; same per-file-local convention this session's
/// other new files use).
fn const_int_fn(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    d.lam_fv(k_fv, nat, a)
}

/// `fun k => Int.ofNat (Nat.succ k)` -- the exact lambda `Int.factorial`'s
/// own `Definition` uses (`wilson.rs::declare_factorial`), built identically
/// here so `prodRange` applied to it is defeq `Int.factorial`.
fn factorial_index_fn(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.of_nat(sk);
    d.lam_fv(k_fv, nat, body)
}

/// `Int.prodRange_scaled_index_eq_pow_mul_factorial :
///   ∀ a m, Eq Int (prodRange (fun k => mul a (ofNat (succ k))) m)
///     (mul (pow a m) (factorial m))`
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_scaled_index_eq_pow_mul_factorial(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let f = const_int_fn(d, a);
    let g = factorial_index_fn(d);

    let stmt = {
        let scaled = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let ofk = d.of_nat(sk);
            let body = d.imul(a, ofk);
            d.lam_fv(k_fv, nat, body)
        };
        let lhs = d.const_app(p.prod_range, &[scaled, m]);
        let pow_a_m = d.ipow(a, m);
        let fact_m = d.const_app(p.factorial, &[m]);
        let rhs = d.imul(pow_a_m, fact_m);
        d.ieq(lhs, rhs)
    };

    // mul_step : Eq Int (prodRange (fun k => mul (f k) (g k)) m)
    //   (mul (prodRange f m) (prodRange g m))
    let mul_step = d.lemma(p.prod_range_mul, &[f, g, m]);
    let prod_range_f_m = d.const_app(p.prod_range, &[f, m]);
    let prod_range_g_m = d.const_app(p.prod_range, &[g, m]);
    let mul_pf_pg = d.imul(prod_range_f_m, prod_range_g_m);

    // const_pow_step : Eq Int (prodRange f m) (pow a m).
    let const_pow_step = d.lemma(p.prod_range_const_pow, &[a, m]);
    let pow_a_m = d.ipow(a, m);
    let step2 = d.icongr(prod_range_f_m, pow_a_m, const_pow_step, &|d, t| {
        d.imul(t, prod_range_g_m)
    });
    let mul_powam_pg = d.imul(pow_a_m, prod_range_g_m);

    // scaled ≡ (fun k => mul (f k) (g k)) up to beta -- both are `fun k =>
    // mul a (ofNat (succ k))`, so `prod_range_mul`'s stated LHS (built from
    // `f`/`g` applied pointwise) is defeq the STATED `lhs` above; the
    // kernel's own defeq check at `declare_theorem` closes this gap, no
    // explicit rewrite needed.
    let lhs = {
        let scaled = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sk = d.succ(k);
            let ofk = d.of_nat(sk);
            let body = d.imul(a, ofk);
            d.lam_fv(k_fv, nat, body)
        };
        d.const_app(p.prod_range, &[scaled, m])
    };
    let (_e, chained) = d.ichain(lhs, &[(mul_pf_pg, mul_step), (mul_powam_pg, step2)]);
    // chained : Eq Int lhs (mul (pow a m) (prodRange g m)), and
    // `prodRange g m` is defeq `factorial m` (both unfold `g`/`factorial`'s
    // own body to the identical `Nat.rec` application), so `chained` is
    // accepted at the STATED type `Eq Int lhs (mul (pow a m) (factorial m))`
    // by the kernel's own defeq check.

    let ty = {
        let with_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(a_fv, int_ty, with_m)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, chained);
        d.lam_fv(a_fv, int_ty, with_m)
    };
    d.declare_theorem(p.prod_range_scaled_index_eq_pow_mul_factorial, ty, value)
}
