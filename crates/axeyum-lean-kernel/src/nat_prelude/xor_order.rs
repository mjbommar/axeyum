//! Order-theoretic facts about `Nat.xor` — dispatched from
//! `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`).
//!
//! # `Nat.lt_xor_cases` stays open
//!
//! Mathlib v4.30 (`Mathlib.Data.Nat.Bitwise`, pinned commit
//! `c5ea00351c28e24afc9f0f84379aa41082b1188f`), read directly rather than
//! paraphrased:
//!
//! ```text
//! theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c
//! ```
//!
//! Every quantifier is over `ℕ`, every operator (`<`, `^^^`, `∨`) has a
//! direct counterpart in this prelude, and `Nat.xor` is already the SAME
//! definition Mathlib uses (`bitwise xor`, `xor.rs`). So the codomain
//! question that killed the six `testBit`-returning-`Bool` mirrors does
//! **not** apply here — this statement is Nat-valued throughout, and an
//! honest flip is possible once (if) it is proved. It is NOT proved by
//! this file, and stays `open`.
//!
//! Mathlib's own proof route is `lt_xor_cases` <- `xor_trichotomy` (an
//! `a ^^^ b ^^^ c ≠ 0 → b^^^c < a ∨ c^^^a < b ∨ a^^^b < c` lemma) <-
//! `exists_most_significant_bit` (∃ the highest bit set in a nonzero `v`)
//! composed with `lt_of_testBit` (agreement above a differing bit, differing
//! AT that bit, forces the order). Two prior lanes
//! (`docs/plan/status/253-nat-xor-parity.md`,
//! `docs/plan/status/254-nat-parity-lowbit.md`) sized this as needing a
//! highest-differing-bit `testBit` induction and left it open; this lane
//! confirms that sizing and narrows exactly what is missing, having read
//! the actual proof route rather than guessed it.
//!
//! ## What THIS prelude already has that the proof route needs
//!
//! More than either prior lane's report credits — `binary.rs`'s `size`
//! addendum (`declare_size_all`) is closer to the needed machinery than
//! "no `size`/`log` connection to `xor`" suggested:
//!
//! - `Nat.size : Nat -> Nat` (`sizeAux n n`, the binary digit count).
//! - `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))` — every `n` fits under
//!   `2^(size n)`.
//! - `Nat.sum_testBit_eq : ∀ n, sumRange (fun i => testBit n i * 2^i)
//!   (size n) = n` — a number IS the sum of its own bits, up to `size n`.
//! - `Nat.zero_of_testBit_eq_zero : ∀ n, (∀ i, testBit n i = 0) → n = 0` —
//!   the contrapositive direction of "a nonzero number has SOME set bit",
//!   though not yet packaged as an existential with a *highest* witness.
//! - `Nat.bitwise_comm` (`bitwise.rs`/`rec_agreement.rs`), general in `f`,
//!   giving `Nat.xor_comm` (below) for free — Mathlib's own
//!   `xor_trichotomy` proof uses `Nat.xor_comm` twice (in its `hbc`/`hca`
//!   steps), so this is genuine, load-bearing progress toward the target,
//!   not an unrelated bonus.
//!
//! ## What is STILL missing, and each is independently substantial
//!
//! 1. **`testBit_xor` (or equivalent)**: `testBit (xor m n) i = Bool.xor
//!    (testBit m i) (testBit n i)` (Nat-valued here: some 0/1 combine of
//!    the two bits). Nothing in this prelude relates `Nat.testBit`
//!    (recursion on the bit INDEX, `testBitAux`) to `Nat.bitwise`/`xor`
//!    (recursion on the VALUE via `/2`, `bitwiseAux`) at a symbolic index.
//!    `rec_agreement.rs` proves agreement between the *general* `bitwise`
//!    recursor and each fixed-`f` `landAux`/`lorAux`/`ldiffAux`
//!    hand-recursion — a DIFFERENT relation (two value-recursions agreeing
//!    at fixed fuel) from relating an index-recursion (`testBitAux`) to a
//!    value-recursion (`bitwiseAux`) at a symbolic bit position. This is a
//!    new agreement lemma, not a specialization of an existing one.
//! 2. **`exists_most_significant_bit`-equivalent**: `∀ n, n ≠ 0 → ∃ i,
//!    testBit n i = 1 ∧ ∀ j, i < j → testBit n j = 0`. `size`/`lt_pow_size`
//!    bound `n` below `2^(size n)`, and the natural WITNESS is
//!    `i := pred (size n)`, but nothing here proves `testBit n (pred (size
//!    n)) = 1` for `n ≠ 0`, nor `testBit n j = 0` for `j >= size n` (the
//!    "above the top bit, everything is zero" half). Both need induction
//!    connecting `sizeAux`'s fuel-vs-zero-guard recursion to `testBitAux`'s
//!    index recursion — plausible FROM this prelude's existing pieces, but
//!    unbuilt, and each half is comparable in size to `size_aux_lt_pow`
//!    itself (`binary.rs`, ~70 lines of proof-term construction for one
//!    direction of one bound).
//! 3. **`lt_of_testBit`-equivalent**: given `i`, `testBit n i = 0`,
//!    `testBit m i = 1`, and `testBit n j = testBit m j` for all `j > i`,
//!    conclude `n < m`. The natural route through this prelude's own
//!    pieces: relate "agreement above `i`" to `n / 2^(i+1) = m / 2^(i+1)`
//!    (needs its own induction — nothing here derives a quotient equality
//!    from a bitwise agreement hypothesis), then decompose `n`/`m` via the
//!    `sum_testBit_eq`-style split at `i` and bound the tail below `2^i` to
//!    force the order. This is a genuinely new theorem, not a corollary.
//! 4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`**:
//!    `xor_trichotomy`'s own proof composes these on top of `testBit_xor`.
//!    `xor_assoc` in particular is what Mathlib's `bitwise_assoc_tac`
//!    exists for specifically because — per that tactic's own comment —
//!    "proving associativity of bitwise operations in general essentially
//!    boils down to a huge case distinction". None of `land_assoc`/
//!    `lor_assoc`-shaped machinery exists in this prelude for ANY bitwise
//!    operator yet (only `_comm` forms do), so this alone is comparable in
//!    scope to landing a whole new operator family.
//!
//! Each of (1)-(4) is independently a multi-declaration undertaking on the
//! scale of `binary.rs`'s `size` addendum or `rec_agreement.rs`'s
//! fuel-agreement lemmas — i.e. its own lane, not a follow-on task. Sizing
//! `lt_xor_cases` honestly puts the full route at 4 further substantial
//! pieces beyond what `Nat.xor_comm` (below) contributes. See
//! `docs/plan/status/260-nat-lt-xor-cases.md` for the handoff.
//!
//! ## `scripts/gen-autogenesis-bitwise-family-projection.py`
//!
//! Checked directly: it names three unrelated `testBit` facts (per
//! `docs/plan/status/244-nat-testbit-bitwise.md`), not `lt-xor-cases`, so it
//! does not pin this fact open independent of provability.

use crate::KernelError;

use super::NatDev;
use super::NatOps;
use super::NatPrelude;
use crate::ExprId;

/// `∀ a b : Bool, Bool.Eq (f a b) (f b a)` for a CONCRETE `f`, proved by
/// nested `Bool.rec` on `a` then `b` — four leaves, each closing by
/// computation. The SAME construction `nat_prelude_tests.rs::bool_fn_comm`
/// already builds and already tests at `f := xor_fn` specifically
/// (`bitwise_comm_applies_at_a_concrete_discriminating_instance`); this is
/// production code building the identical term for `Nat.xor_comm`'s
/// `hf` argument, not a new technique.
fn xor_fn_comm(d: &mut NatDev<'_>, p: &NatPrelude, f_term: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let z = d.kernel().level_zero();
    let bool_rec_name = p.logic.bool_rec;

    let inner_for_literal = |d: &mut NatDev<'_>, lit: ExprId| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let lhs = d.apply(f_term, &[lit, b]);
        let rhs = d.apply(f_term, &[b, lit]);
        let motive_body = d.bool_eq(lhs, rhs);
        let motive = d.lam_fv(b_fv, bool_ty, motive_body);
        let false_leaf = {
            let lhs = d.apply(f_term, &[lit, false_]);
            d.bool_refl(lhs)
        };
        let true_leaf = {
            let lhs = d.apply(f_term, &[lit, true_]);
            d.bool_refl(lhs)
        };
        let bool_rec = d.kernel().const_(bool_rec_name, vec![z]);
        let elim = d.apply(bool_rec, &[motive, false_leaf, true_leaf, b]);
        d.lam_fv(b_fv, bool_ty, elim)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let lhs_ab = d.apply(f_term, &[a, b]);
    let rhs_ab = d.apply(f_term, &[b, a]);
    let inner_eq = d.bool_eq(lhs_ab, rhs_ab);
    let inner_pi = d.pi_fv(b_fv, bool_ty, inner_eq);
    let outer_motive = d.lam_fv(a_fv, bool_ty, inner_pi);

    let at_false = inner_for_literal(d, false_);
    let at_true = inner_for_literal(d, true_);
    let bool_rec = d.kernel().const_(bool_rec_name, vec![z]);
    let elim = d.apply(bool_rec, &[outer_motive, at_false, at_true, a]);
    d.lam_fv(a_fv, bool_ty, elim)
}

/// `Nat.xor_comm : ∀ m n, Eq (xor m n) (xor n m)` — a direct corollary of
/// `Nat.bitwise_comm` at `f := xor_fn` (`xor := bitwise xor_fn`, `xor.rs`),
/// needing only [`xor_fn_comm`]'s Boolean commutativity witness. Genuine
/// infrastructure toward `Nat.lt_xor_cases` (Mathlib's own `xor_trichotomy`
/// proof uses `Nat.xor_comm` twice), not a standalone bonus — see this
/// module's doc for what else the target still needs.
fn declare_xor_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let xor_fn_term = super::bitwise::xor_fn(d);
    let hf = xor_fn_comm(d, &p, xor_fn_term);
    d.theorem(p.xor_comm, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let lhs = d.const_app(p.xor, &[m, n]);
        let rhs = d.const_app(p.xor, &[n, m]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.lemma(p.bitwise_comm, &[xor_fn_term, hf, m, n]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order. `Nat.lt_xor_cases`
/// itself is NOT declared here — see the module doc for exactly what is
/// missing and why it stays `open`.
pub(super) fn declare_xor_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_xor_comm(d, p)?;
    Ok(())
}
