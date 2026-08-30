# Notes: 299-totient-even-exec

Detail moved out of [`../status/299-totient-even-exec.md`](../status/299-totient-even-exec.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- The double-peel decomposition (peel index 0 via `countRange_split(h, 1,
  sw)`, then peel the shifted range's own top index via `countRange`'s
  structural succ equation) — this IS the master equation
  `countRange h L = add sel0 (add rest sel_sw)`, built and verified.
- `hyp1` at `j = 0` giving `h(pred L) = h(0)` directly, with NO case split
  on the boolean value needed for the boundary-sum-is-even argument (`Even
  (add k k)` for either `k = 0` or `k = 1`, uniformly).
- `add_add_add_comm`-based closure for `Even x -> Even y -> Even (add x y)`
  — built as a local `even_add` helper, using the standard per-file
  `add_add_add_comm` copy plus double `Exists` elimination.
- The index correspondence for the recursive case's `hyp1`/`hyp2` re-
  derivation — resolved via `succ_sub_succ(w, j) : sub (succ w)(succ j) =
  sub w j` plus `succ_sub_of_le(pred w, j, _) : sub (succ (pred w)) j =
  succ (sub (pred w) j)`, exactly the two lemmas the plan named, chained
  through `succ_pred_of_pos` to bridge `w` and `succ (pred w)`.
- **The plan's own flagged weakest step — "picking the right induction
  principle" — was right to flag, but the actual resolution is different
  from what the plan sketched.** The plan expected the risk to be in
  `WellFounded.fix`'s mechanics; the real difficulty was that
  `cases_zero_succ`/`Nat.rec` (this prelude's usual case-split device)
  **cannot** be used to split the induction TARGET when a later step needs
  to relate the split value back to that target (here: `Lt w L`, needed to
  invoke the IH at `w`). `Nat.rec`'s step function is proved once, generically,
  for an unrelated fresh predecessor variable — it carries no equation
  connecting that variable to the original target. The fix: split `L` via
  `Nat.zero_or_succ` (an actual `Or (Eq L 0) (Exists pred, Eq L (succ pred))`
  fact, eliminated via `exists_rec`/`or_elim`), which hands you the equation
  needed to derive `Lt w L` by ordinary order-lemma composition. This is a
  reusable lesson beyond this file: **`WellFounded.fix` alone gives you the
  strong-induction STEP; it does not give you a way to relate a
  further-case-split value back to the step's own bound variable — that
  needs an actual equation, from something like `zero_or_succ`, not from
  `Nat.rec`'s generic recursor.**

**Did NOT hold, found only by building and bisecting:**

- One `d.congr` call (in the arithmetic connecting the shifted predicate's
  value to the original predicate via the `add-one`/`succ` bridge) needed
  `nat_congr_bool` instead. `d.congr` hardcodes its conclusion as `Eq Nat`;
  the function being congr'd here (`h : Nat -> Bool`) produces a `Bool`, so
  the built term was `Eq Nat (bool-typed term) (bool-typed term)` — ill-typed,
  surfacing as `TypeMismatch { expected: ExprId(3), got: ExprId(5726) }`
  (`ExprId(3)` is a sort — the CLAUDE.md tell for "the kernel wanted a sort
  here", though in this instance the more precise read is "the kernel wanted
  `Eq`'s implicit type argument to unify with the term's actual type and it
  didn't"). This is exactly the "dev-helper layer hardcodes a carrier"
  family CLAUDE.md's Gotchas section already names (`congr_nat_to`,
  `congr_bool_to_nat` in sibling files) — I had already built and correctly
  used the Bool-aware variant (`nat_congr_bool`, a local copy) everywhere
  else in this file; this was the one call site where I reached for the
  plain `d.congr` out of habit.
- Dispatch order: `declare_count_range_reversal_even` needs `Nat.Even`
  (`declare_parity_all`), which runs AFTER `declare_totient_all`. First
  placement (right after `declare_totient_all`, since that's where
  `count_range`/`count_range_split` come from) gave `UnknownConst`. Moved
  to right after `declare_parity_all`.

## How the bug was found

Every one of 169 baseline `nat_prelude::` tests failed identically
(`TypeMismatch`, same two `ExprId`s) once the declaration was wired in —
exactly the "one bad declaration poisons the shared prelude build" pattern
CLAUDE.md warns about. Per that entry's own remedy, bisected by toggling
scope rather than reading failures: added throwaway `#[cfg(test)]`-style
debug-probe declarations (built inline in `declare_count_range_reversal_
even`, removed before the final commit) that declared each stage of the
construction as its own standalone theorem —
`base_case_zero` / `base_case_one` (passed) → `succ_succ_case` as a whole
(failed) → arithmetic-only sub-block up through `final_eq` (failed) →
checkpoint after `split_a` (passed) → checkpoint after `master_eq` (failed).
That bracketed the defect to the ~15 lines between `split_a` and `master_eq`,
where the one wrong `d.congr` call was.

## What was NOT attempted

`Nat.totient_even` itself — the plan's Steps 0/1/2/4, which wire this lemma
to the `gcd(n-k, n) = gcd(k, n)` chain (`coprime_add_self_right` /
`coprime_self_add_right` / `coprime_symmetric`) and the no-fixed-point
argument (`gcd k (2k) = k`, contradicting `2 < n` when `n = 2k`). None of
that was started. Per the dispatch brief, landing the general lemma alone
is a good outcome, and the remaining risk (per the plan's own Step 0/1/2
writeup) is comparable in size to what this dispatch already did — routing
`n - k` through an `add`-form via `add_sub_cancel_of_le`, then the three-`Iff`
gcd chain, then the fixed-point contradiction, then wiring the whole thing to
`countRange_reversal_even`'s two hypotheses at `h := totient_predicate`
shifted by one.

**For the next lane:** start from `docs/plan/status/295-totient-even.md`'s
Steps 0/1/2/4 (still accurate — nothing in that part of the plan touched
`countRange_reversal_even`'s internals), instantiate
`Nat.countRange_reversal_even` at `L := n - 1`, `h := shift-by-one of
totient_predicate(n)`, and supply the two hypotheses via the gcd chain.
Watch for the SAME class of bug this dispatch hit: any `d.congr`/`bool_
congr_nat`/`nat_congr_bool` call must match its hypothesis's actual
Nat-vs-Bool shape, not just "the function I'm congr-ing through looks like
the one in the sibling call". Simulate the gcd chain numerically in Python
first (the plan already did this for `n` in `[2,40)` — reuse it, don't
re-derive).

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 170 passed, 0
  failed (169 baseline + 1 new).
- `cargo fmt --edition 2024` (per-file, on the three touched files) and
  `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
- `python3 scripts/check-test-attribute-integrity.py`: 0 findings.
- `python3 scripts/validate-facts.py`: 2074 facts, 0 errors (untouched by
  this dispatch — no fact was flipped).
- `the_build_is_deterministic`'s pin moved `93 + 538` → `93 + 539`, taken
  from the panic's own mismatch (`632` vs `631`), not hand-incremented.

## Commits (not pushed)

- `d0d2e6674` — wip, first draft, not compiled (landed early per the
  "commit before any long check" rule).
- `c47aa2f1b` — the working, verified declaration + registration + test +
  pin, on top of the wip commit.
