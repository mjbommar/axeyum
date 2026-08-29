//! Two-sided induction over `ℤ`: `Int.induction_on`.
//!
//! `Int.rec` splits an integer into `ofNat n` and `negSucc m` and then hands
//! back a *natural* in each branch. That is a **case split**, not an
//! induction principle for `ℤ`: a caller who wants to reason "from `0`,
//! upward and downward" has to rebuild both `Nat.rec` inductions by hand
//! every time, and until this file nothing in `int_prelude/` did it once.
//! `fibonacci.rs::declare_fib` is the plain case split; `gcd.rs` and
//! `bezout_witnesses.rs` route around the problem entirely by pushing to
//! `natAbs`, which works only when the statement is magnitude-decided
//! (`parity.rs` and `Int.fib_of_odd` are the model). A statement like
//! `Int.fib_add`, whose index arithmetic crosses zero, has no such route.
//!
//! ```text
//! Int.induction_on : ∀ (P : Int → Prop),
//!     P zero
//!   → (∀ n, P n → P (add n one))
//!   → (∀ n, P n → P (sub n one))
//!   → ∀ n, P n
//! ```
//!
//! # Every bridging step is pure reduction
//!
//! This is the whole reason the combinator is cheap, and it is worth
//! recording because the obvious expectation is the opposite (the brief that
//! sized this work called it "comparable-or-more effort than the theorem it
//! blocks"). `ℤ`'s operations are defined by nested `Int.rec` over `Nat`
//! (`defs.rs`), so at a *constructor* argument every step below computes:
//!
//! - `add (ofNat k) one ≡ ofNat (Nat.add k 1) ≡ ofNat (succ k)` — `Nat.add`
//!   recurses on its right argument and the right argument is the literal
//!   `1`, so this reduces with `k` symbolic. (The standing warning about
//!   operand order is exactly what makes this direction free and the mirrored
//!   `add one (ofNat k)` stuck.)
//! - `sub zero one ≡ add zero (negSucc 0) ≡ subNatNat 0 1 ≡ negSucc 0`, since
//!   `Int.sub` is a plain `Definition` (`sub.rs`) and `subNatNat m n`
//!   scrutinises `Nat.sub n m`, here the closed `Nat.sub 1 0 ≡ 1`.
//! - `sub (negSucc k) one ≡ add (negSucc k) (negSucc 0) ≡ negSucc (succ
//!   (Nat.add k 0)) ≡ negSucc (succ k)` — again `Nat.add`'s right argument is
//!   the literal `0`.
//!
//! So no equation lemma, no `Nat.sub` truncation, and no `natAbs` detour is
//! involved anywhere: the two `Nat.rec` inductions below hand the kernel
//! terms whose types are *definitionally* the ones it expects, and
//! `add_declaration`'s own defeq check closes each one. That is also why the
//! down-step is stated with `Int.sub` rather than the `P (add n one) → P n`
//! form: `sub` costs nothing here and is what a caller wants to write.

use super::IntPrelude;
use super::ops::IntDev;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Which deliberate defect [`build`] should inject into the *statement* while
/// leaving the proof value untouched.
///
/// The trusted gate proves whatever it is handed, so a combinator that reads
/// correctly is not thereby correct; each variant here must be **rejected**
/// (`int_prelude_tests`'s `two_sided_induction_*` controls), which is what
/// shows the shipped statement's three hypotheses are each doing work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Mutation {
    /// Ship the real statement.
    None,
    /// Anchor the base at `one` instead of `zero`.
    BaseAtOne,
    /// Replace the up-step hypothesis with a second down-step.
    UpIsAlsoDown,
    /// Replace the down-step hypothesis with a second up-step.
    DownIsAlsoUp,
}

/// The statement and proof of `Int.induction_on`, as a `(ty, value)` pair.
///
/// Factored out so [`declare_induction_on`] and the test file's negative
/// controls build the *same* term: a mutation test that rebuilds the proof by
/// hand proves nothing about the shipped one.
///
/// `mutate` rewrites the hypothesis statements before they are used, so a
/// control can, for example, replace the down-step with a second up-step and
/// confirm the kernel rejects the unchanged proof value.
pub(super) fn build(d: &mut IntDev<'_>, mutate: Mutation) -> (ExprId, ExprId) {
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let motive_ty = d.arrow(int_ty, prop);

    let p_fv = d.fresh_fvar();
    let pvar = d.kernel().fvar(p_fv);

    let izero = d.izero();
    let ione = d.ione();

    // P zero  (or, under `Mutation::BaseAtOne`, the unreachable-from-here `P one`).
    let base_ty = {
        let anchor = if mutate == Mutation::BaseAtOne {
            ione
        } else {
            izero
        };
        d.apply(pvar, &[anchor])
    };

    // `∀ n, P n → P (add n one)` when `upward`, else `∀ n, P n → P (sub n one)`.
    let stepped_ty = |d: &mut IntDev<'_>, upward: bool| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hyp = d.apply(pvar, &[n]);
        let moved = if upward {
            d.iadd(n, ione)
        } else {
            d.isub(n, ione)
        };
        let concl = d.apply(pvar, &[moved]);
        let body = d.arrow(hyp, concl);
        d.pi_fv(n_fv, int_ty, body)
    };

    let up_ty = stepped_ty(d, mutate != Mutation::UpIsAlsoDown);
    let down_ty = stepped_ty(d, mutate == Mutation::DownIsAlsoUp);

    let base_fv = d.fresh_fvar();
    let base = d.kernel().fvar(base_fv);
    let up_fv = d.fresh_fvar();
    let up = d.kernel().fvar(up_fv);
    let down_fv = d.fresh_fvar();
    let down = d.kernel().fvar(down_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let concl = d.apply(pvar, &[n]);

    // Int.rec.{0} (fun x => P x) ofNatBranch negSuccBranch n
    let motive_term = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.apply(pvar, &[x]);
        d.lam_fv(x_fv, int_ty, body)
    };

    // ofNat k: ordinary `Nat.rec` upward from `P zero`.
    let minor_of_nat = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.induct(
            &|d, v| {
                let t = d.of_nat(v);
                d.apply(pvar, &[t])
            },
            &|_d| base,
            &|d, j, ih| {
                let t = d.of_nat(j);
                d.apply(up, &[t, ih])
            },
            k,
        );
        d.lam_fv(k_fv, nat, body)
    };

    // negSucc k: `Nat.rec` downward. The base is `P (negSucc 0)`, i.e. `P (-1)`,
    // reached from `P zero` by ONE down-step -- this is the branch that makes
    // the down hypothesis load-bearing, and the one the negative controls kill.
    let minor_neg_succ = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.induct(
            &|d, v| {
                let t = d.neg_succ(v);
                d.apply(pvar, &[t])
            },
            &|d| d.apply(down, &[izero, base]),
            &|d, j, ih| {
                let t = d.neg_succ(j);
                d.apply(down, &[t, ih])
            },
            k,
        );
        d.lam_fv(k_fv, nat, body)
    };

    let level_zero = d.kernel().level_zero();
    let rec_name = d.int().rec;
    let rec = d.kernel().const_(rec_name, vec![level_zero]);
    let core = d.apply(rec, &[motive_term, minor_of_nat, minor_neg_succ, n]);

    let mut ty = d.pi_fv(n_fv, int_ty, concl);
    ty = d.arrow(down_ty, ty);
    ty = d.arrow(up_ty, ty);
    ty = d.arrow(base_ty, ty);
    ty = d.pi_fv(p_fv, motive_ty, ty);

    let mut value = d.lam_fv(n_fv, int_ty, core);
    value = d.lam_fv(down_fv, down_ty, value);
    value = d.lam_fv(up_fv, up_ty, value);
    value = d.lam_fv(base_fv, base_ty, value);
    value = d.lam_fv(p_fv, motive_ty, value);

    (ty, value)
}

/// `Int.induction_on` — see the module doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_induction_on(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p: IntPrelude = d.int();
    let (ty, value) = build(d, Mutation::None);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.induction_on,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}
