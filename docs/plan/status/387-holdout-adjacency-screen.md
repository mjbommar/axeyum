# 387 — holdout adjacency screen

<!-- plan-section: lane-status -->

**Status: in progress.** Early commit per the lane rule; incomplete.

Reproduced ADR-0762's finding in memory (pure `select` + `guard`, nothing
written): a draw placing `Init.Data.Nat.Bitwise.Lemmas` and
`Mathlib.Data.Nat.GCD.Basic` into **held-out** returns `GUARD PASSED — 340
entries, 120 held-out rows, 12 held-out families`, beside `natural-bitwise` and
`natural-gcd` which are both **development**. The three-family control refuses
with `R5`, so the machinery is live and simply has no adjacency rule.

Next: turn ADR-0653's prose rule into a guard rule.
