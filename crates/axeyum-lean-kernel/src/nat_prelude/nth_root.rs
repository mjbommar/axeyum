//! `Nat.nthRoot` — the floor `n`-th root, opens `Mathlib.Analysis.
//! SpecialFunctions.Pow.NthRootLemmas` (pinned commit `c5ea0035…`, 13 rows)
//! for the autogenesis screen. The un-owned floor has had zero
//! held-out-safe modules since ADR-0762 (re-measured unchanged after
//! ADR-0830's draw 9); enumeration shows `Nat.nthRoot` alone and
//! `Squarefree` (`squarefree.rs`) alone each open exactly one new
//! held-out-safe module, and R5's two-family minimum needs both together.
//!
//! ## Signature and convention
//!
//! `Nat.nthRoot (n a : Nat) : Nat` — matches Mathlib's own argument order,
//! confirmed against the pinned inventory row for `Nat.nthRoot_zero_left`:
//! the raw `Lean.Expr` dump applies `Nat.nthRoot` to `0` and then `a`
//! (`(Nat.nthRoot 0) a`), i.e. the root degree `n` comes first, the
//! radicand `a` second. `nthRoot 2` is the floor square root; by the same
//! pinned row's convention, `nthRoot 0 a := 1` for every `a` (the "0th
//! root" placeholder, exactly as `x ^ 0 = 1`).
//!
//! ## Recursion scheme, chosen deliberately
//!
//! Mathlib's `Nat.nthRoot` (like its `Nat.sqrt`) is a Newton's-method
//! well-founded recursion — the pinned inventory's own
//! `Nat.nthRoot.lt_pow_go_succ_aux` names an internal `nthRoot.go` and
//! states a Newton step (`a < ((a / b^n + n*b)/(n+1) + 1)^(n+1)`). Going
//! through the equation compiler's `WellFounded.fix` would drag in
//! `Quot.sound`/`propext`, fatal to this project's axiom-freedom metric.
//! [`sqrt.rs`](super::sqrt) already solved exactly this problem for the
//! fixed exponent `n = 2` by **linear search on a fuel argument** —
//! structural recursion, not well-founded recursion, computing the SAME
//! value by a different, simpler algorithm. This file generalizes that
//! device from `mul c c` (squaring) to `pow c n` (an arbitrary captured
//! exponent), rather than reproducing Newton's method.
//!
//! `Nat.nthRootAux (n a fuel : Nat) : Nat` searches upward from `0`:
//!
//! ```text
//! nthRootAux n a 0        ≡ 0
//! nthRootAux n a (succ f) ≡ let c := nthRootAux n a f
//!                           in if (succ c) ^ n <= a then succ c else c
//! ```
//!
//! `n` and `a` are **free, captured** variables — never threaded through
//! `Nat.rec`'s motive — so the motive is the plain accumulator fold `fun _
//! => Nat`, exactly [`sqrtAux`](super::sqrt)'s shape (not
//! [`nth.rs`](super::nth)'s `Nat -> Nat -> Nat` motive, which that file
//! needs only because ITS accumulators genuinely change per fuel step;
//! ours does not — `n` and `a` are constant across the whole search).
//!
//! `Nat.nthRoot n a := if n == 0 then 1 else nthRootAux n a a`. `a` fuel
//! steps always suffice for `n >= 1`: the greatest `m` with `m ^ n <= a` is
//! itself `<= a` (for `m >= 1` and `n >= 1`, `m <= m ^ n`), so the search
//! from `0` needs at most `a` increments. The `n = 0` branch is **not**
//! stylistic: `pow c 0 ≡ 1` for every `c` definitionally, so without this
//! branch the fuel search would find `1 <= a` true at every candidate
//! whenever `a >= 1` and walk all the way to the fuel bound, returning `a`
//! instead of the correct `1`.
//!
//! Both equations hold **definitionally** (β/δ/ι) once `n` is a concrete
//! numeral; see `nat_prelude_tests.rs`'s `nth_root_evaluates_correctly` for
//! the concrete instances checked. No equation lemma or other theorem is
//! declared here (ADR-0653 — the construction and its evaluation test,
//! nothing else): `Nat.nthRoot_zero_left` (a pinned inventory row) becomes
//! `Eq.refl` the moment this construction lands, since `beq 0 0` reduces to
//! `true` regardless of `a` remaining symbolic — a real spend on that pool
//! row for whichever lane later dispatches it, not a theorem declared here.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.nthRootAux n a fuel`.
fn nth_root_aux(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, a: ExprId, fuel: ExprId) -> ExprId {
    d.const_app(p.nth_root_aux, &[n, a, fuel])
}

/// Declare `Nat.nthRootAux` and `Nat.nthRoot`. Definitions only — see this
/// module's doc for why no theorem about either is declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_nth_root_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();

    // --- Nat.nthRootAux : Nat -> Nat -> Nat -> Nat --------------------------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);

        // fuel = zero: the accumulator starts at 0.
        let zero_minor = d.zero();

        // fuel = succ f: one linear-search step, exactly `sqrtAux`'s shape
        // with `pow c n` replacing `mul c c`. `n` and `a` are captured free
        // variables from the outer scope, not threaded through the motive.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let accumulator_fv = d.fresh_fvar();
            let accumulator = d.kernel().fvar(accumulator_fv);
            let candidate = d.succ(accumulator);
            let candidate_pow = d.pow(candidate, n);
            let fits = d.ble(candidate_pow, a);
            let body = d.bool_select_nat(fits, candidate, accumulator);
            let with_accumulator = d.lam_fv(accumulator_fv, nat, body);
            d.lam_fv(predecessor_fv, nat, with_accumulator)
        };

        let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let applied = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let value_term = {
            let with_fuel = d.lam_fv(fuel_fv, nat, applied);
            let with_a = d.lam_fv(a_fv, nat, with_fuel);
            d.lam_fv(n_fv, nat, with_a)
        };
        let ty = {
            let inner2 = d.arrow(nat, nat);
            let inner1 = d.arrow(nat, inner2);
            d.arrow(nat, inner1)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.nth_root_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.nthRoot n a := if n == 0 then 1 else nthRootAux n a a ----------
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);

        let zero = d.zero();
        let one = d.num(1);
        let n_is_zero = d.beq(n, zero);
        let searched = nth_root_aux(d, &p, n, a, a);
        let body = d.bool_select_nat(n_is_zero, one, searched);
        let value_term = {
            let with_a = d.lam_fv(a_fv, nat, body);
            d.lam_fv(n_fv, nat, with_a)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.nth_root,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}
