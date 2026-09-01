//! `Rat.det_row_selection` — the SELECTION lemma (ADR-1440 obligation 2),
//! the last obstruction to `det (A*B) = det A * det B` at symbolic `n`.
//!
//! ## The statement is not what it looks like
//!
//! The naive target `det (B o g) n = det (matId o g) n * det B n`, with `g`
//! totally unrestricted, is FALSE. Counterexample: `n=1`, `g 0 = 5`,
//! `B 5 0 = 7`. Then `det (B o g) 1 = B 5 0 = 7` (by `det_one`), while
//! `det (matId o g) 1 = matId 5 0 = 0` (`5 != 0`) so the right side is `0`.
//! `7 != 0`.
//!
//! The correct, general statement needs `MapsInto g n` (`g` sends `[0,n)`
//! into `[0,n)`). `InjectiveOn g n` is NOT an extra hypothesis on the final
//! theorem: when `g` is not injective on `[0,n)`, both sides are `0` for
//! free (`Rat.det_alternating`, since two rows of `B o g` and of
//! `matId o g` coincide) -- but `MapsInto` cannot be dropped, because the
//! injective-and-not-onto case (the counterexample above) is exactly where
//! it fails.
//!
//! ## Route
//!
//! 1. Induct on `n` at the top: `n = 0` is trivial (`det _ 0 = 1` on the
//!    nose); `n = succ n'` is proved directly (the successor step's IH is
//!    unused -- this is a case split, not a real induction), so `n` is
//!    syntactically `succ n'` everywhere below and `Rat.det_row_swap`'s
//!    `succ m` requirement is always already satisfied with `m := n'`.
//! 2. At `succ n'`, decide `InjectiveOn g (succ n')` or produce an explicit
//!    duplicate pair, via a fresh bounded-search decidability construction
//!    (nothing in-tree gives this -- checked, no `not_injective`/
//!    `exists_dup`/decidable-pigeonhole lemma exists anywhere in
//!    `nat_prelude`).
//!    - duplicate branch: `Rat.det_alternating` on both sides directly, `0
//!      = 0 * det B n`. No `MapsInto` needed for this half.
//!    - injective branch: the cursor induction below.
//! 3. The cursor induction, `P(k)`: for FIXED `n'`, `B` (outer, never
//!    recreated across the induction -- only `k` and `g` vary), `∀ g,
//!    InjectiveOn g (succ n') -> MapsInto g (succ n') -> (∀i, Le k i -> Lt i
//!    (succ n') -> g i = i) -> det (B o g) (succ n') = det (matId o g)
//!    (succ n') * det B (succ n')`. Induction on `k`.
//!    - `k=0`: the fixed-point hypothesis forces `g` to be the identity on
//!      all of `[0, succ n')`; `Rat.det_congr` identifies `B o g` with `B`
//!      and `matId o g` with `matId`, then `Rat.det_matId` plus `one_mul`
//!      close it.
//!    - `k -> succ k`: split `Lt k (succ n')` vs `Le (succ n') k`. The
//!      latter makes `P(k)`'s own fixed-point hypothesis vacuously derivable
//!      from `P(succ k)`'s (both ranges are empty), so the IH applies to the
//!      SAME `g` directly, no swap. In the former, pigeonhole
//!      (`Nat.injective_on_imp_surjective_on`) gives `j < succ n'` with `g j
//!      = k`; `j > k` contradicts `g`'s own fixed-point hypothesis (`g` would
//!      have to fix `j`, forcing `j = k`); `j = k` means `g` already fixes
//!      `k`, apply the IH to `g` directly; `j < k` is the real case --
//!      compose `g` with a 2-point swap of `j` and `k` (a fresh, private,
//!      `Nat.beq`-based swap function, NOT `Nat.transposition`: that
//!      definition's pointwise correctness lemmas
//!      (`transposition_eq_at_i` etc, `nat_prelude/transposition.rs`) are
//!      `pub(crate)` but hard-wired to `&mut NatDev<'_>`, not generic over
//!      `NatOps`, so they cannot be called from this file's `IntDev`; ditto
//!      `int_prelude/prod.rs`'s `point_swap` family, which is `pub(super)`
//!      and invisible outside `int_prelude`). `Nat.injective_on_comp` plus
//!      the swap function's own injectivity/`MapsInto` give the composed
//!      function's injectivity/`MapsInto`; `Rat.det_row_swap` relates
//!      `det (B o (g o swap))` to `det (B o g)` (rows `j`, `k` exchanged);
//!      the composed function satisfies `P(k)`'s fixed-point hypothesis, so
//!      the IH closes it.
//!
//! Status: design complete (`ADR-1440` handoff), construction in progress.
