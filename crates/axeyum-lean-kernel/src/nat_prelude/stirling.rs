//! `Nat.stirlingFirst` and `Nat.stirlingSecond` — open
//! `Mathlib.Combinatorics.Enumerative.Stirling` for the autogenesis screen.
//!
//! ADR-1100 (this lane). These are the SECOND pair of constructions that
//! lane declares; `abundant_deficient.rs` carries the reasoning about why
//! four families are needed and why one of them must sort late. This pair
//! adds a fifth family and — more usefully — a `train`-slot option at cycle
//! index 2 that is topically fresh, so a draw need not register the
//! `Fib`/`Bitwise` combination (whose topic segments a development family
//! already publishes) merely to fill that slot.
//!
//! `natural-stirling-numbers` is measured at 16 screened candidates, R9
//! 0/10, R11 fully clean. It is NOT held-out viable, and that is measured
//! rather than assumed: `Nat.stirlingFirst_zero` is the closed evaluation
//! `Nat.stirlingFirst 0 0 = 1`, which becomes decidable by reduction the
//! instant this definition lands, and it sorts into the alphabetically-first
//! ten a draw takes — so guard R12 (ADR-0695/ADR-0950) refuses the family for
//! `held-out` and only for `held-out`. Development or train is exactly right
//! for it.
//!
//! ## The two recursions
//!
//! Both are Mathlib's own recurrences verbatim, and both are the SAME shape
//! as `Nat.choose` (`choose.rs`): an outer `Nat.rec` on the first argument
//! producing a whole row `Nat → Nat`, an inner `Nat.rec` on the second
//! argument selecting the column.
//!
//! ```text
//! stirlingFirst  0       0       = 1        stirlingSecond 0       0       = 1
//! stirlingFirst  0       (k+1)   = 0        stirlingSecond 0       (k+1)   = 0
//! stirlingFirst  (n+1)   0       = 0        stirlingSecond (n+1)   0       = 0
//! stirlingFirst  (n+1) (k+1) =               stirlingSecond (n+1) (k+1) =
//!     n * stirlingFirst n (k+1)                  (k+1) * stirlingSecond n (k+1)
//!       + stirlingFirst n k                        + stirlingSecond n k
//! ```
//!
//! Three things differ from `Nat.choose` and each is a way to get this wrong
//! that the kernel would accept:
//!
//!   * the `n = 0` row is `1, 0, 0, …` (same as `choose`), but the
//!     `n = succ _` row starts at **`0`**, not `1` — `stirlingFirst (n+1) 0`
//!     and `stirlingSecond (n+1) 0` are both zero, where
//!     `choose (n+1) 0` is one;
//!   * the recursive column carries a **coefficient** `choose` does not
//!     have, and the two definitions differ ONLY in that coefficient: the
//!     row index `n` for the first kind, the column index `k+1` for the
//!     second;
//!   * the coefficient multiplies the `k+1` term (`… n (k+1)`), not the `k`
//!     term — swapping them gives a different, plausible-looking triangle.
//!
//! `stirling_tests.rs` discriminates all three. `(4,2)` is the load-bearing
//! instance: the first kind is `11` and the second is `7`, so a single body
//! bound to both names fails, while the more obvious `(3,2)` would NOT
//! discriminate them (both are `3` there).
//!
//! `Nat.mul`'s operand order is Mathlib's here (`n * stirlingFirst n (k+1)`),
//! which puts the recursive call on the RIGHT. That is the side `Nat.mul`
//! recurses on, so the arithmetic stays stuck at symbolic arguments rather
//! than partially evaluating — the behaviour `CLAUDE.md`'s `Nat.add`/`Nat.mul`
//! asymmetry note wants, and the reason nothing here forms a large numeral.
//!
//! No equation lemma or other theorem is declared here (ADR-0653: the
//! construction and its evaluation test, nothing else).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Which index the recursive column's coefficient comes from.
#[derive(Clone, Copy)]
enum Coefficient {
    /// `n`, the predecessor of the row index — the FIRST kind.
    RowPredecessor,
    /// `k + 1`, the column index — the SECOND kind.
    ColumnSuccessor,
}

/// Build the shared triangle, differing only in [`Coefficient`].
///
/// Factored rather than written twice because the two bodies are otherwise
/// byte-identical, and two copies of a 60-line recursor construction is
/// exactly how a transposed branch survives review.
fn stirling_value(d: &mut NatDev<'_>, p: &NatPrelude, coefficient: Coefficient) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);

    // Row for n = 0: column 0 is 1, every successor column is 0. Identical to
    // `choose`'s own zero row.
    let zero_minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner_motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let base = d.num(1);
        let step = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let zero = d.zero();
            let with_ih = d.lam_fv(ih_fv, nat, zero);
            d.lam_fv(j_fv, nat, with_ih)
        };
        let rec = d.kernel().const_(p.rec, vec![one_level]);
        let body = d.apply(rec, &[inner_motive, base, step, k]);
        d.lam_fv(k_fv, nat, body)
    };

    // Row for n = succ predecessor, given `ih : Nat -> Nat` (the prior row):
    // column 0 is 0 (NOT 1 -- see the module doc), column succ j is
    // `coefficient * ih (succ j) + ih j`.
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner_motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
        let base = d.zero();
        let step = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let inner_ih_fv = d.fresh_fvar();
            let succ_j = d.succ(j);
            let at_succ_j = d.apply(ih, &[succ_j]);
            let at_j = d.apply(ih, &[j]);
            let coeff = match coefficient {
                Coefficient::RowPredecessor => predecessor,
                Coefficient::ColumnSuccessor => succ_j,
            };
            let scaled = d.mul(coeff, at_succ_j);
            let sum = d.add(scaled, at_j);
            let with_inner_ih = d.lam_fv(inner_ih_fv, nat, sum);
            d.lam_fv(j_fv, nat, with_inner_ih)
        };
        let rec = d.kernel().const_(p.rec, vec![one_level]);
        let body = d.apply(rec, &[inner_motive, base, step, k]);
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_ih = d.lam_fv(ih_fv, nat_to_nat, with_k);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };

    let outer_motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let rec = d.kernel().const_(p.rec, vec![one_level]);
    let row = d.apply(rec, &[outer_motive, zero_minor, succ_minor, n]);
    let applied = d.apply(row, &[k]);
    let with_k = d.lam_fv(k_fv, nat, applied);
    d.lam_fv(n_fv, nat, with_k)
}

/// Declare `Nat.stirlingFirst` and `Nat.stirlingSecond`. Definitions only —
/// see this module's doc for why no theorem about either is declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_stirling_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let nat_to_nat = d.arrow(nat, nat);
    let ty = d.arrow(nat, nat_to_nat);

    for (name, coefficient) in [
        (p.stirling_first, Coefficient::RowPredecessor),
        (p.stirling_second, Coefficient::ColumnSuccessor),
    ] {
        let value = stirling_value(d, &p, coefficient);
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            // Strictly greater than `add` (1) and `mul` (2), the two
            // definitions the recursive column calls.
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    Ok(())
}
