# Status: `natural-bit-decode` closed-evaluation amendment + draw-time screen

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, holdout-closed-evaluation-amendment, 2026-08-30).**
Both parts landed: the amendment (Part 1) and the R12 draw-time screen
(Part 2). All five required gates pass; the R12 addition is mutation-verified
(6 mutations, each killed by exactly the intended test or pair of tests).

**Track:** the fact ledger / autogenesis nursery held-out isolation
**Phase:** repairing the second closed-evaluation breach (ADR-0695 was the
first, `fermat-numbers`) and closing the recurrence at draw time
**Date:** 2026-08-30

## Summary

`check-holdout-closed-evaluation.py` reported `natural-bit-decode` held-out
with 2 of 10 rows (`Nat.bit false 0 = 0`, `Nat.size 1 = 1`) already decided by
reduction over `Nat.bit` (2facd789, 2026-08-28) and `Nat.size` (a7ac623d7,
2026-08-24), both landed days before draw 11 (882ae1a52, 2026-08-30)
preregistered the family. Measured over the whole held-out population (156
rows, both manifests, 2,507-declaration snapshot): these are the ONLY two
closed-shaped rows; no other family is affected. This is ADR-0695's
`fermat-numbers` defect repeated — the second occurrence of "a held-out row
the construction already settles" reaching a committed manifest.

## Delivered

- `docs/research/09-decisions/adr-0950-natural-bit-decode-amended-and-a-draw-time-closed-evaluation-screen.md`
  — the amendment and the draw-time fix, mirroring ADR-0695's shape.
- `artifacts/autogenesis/mathlib-nursery-split-policy-v1.json` — new
  amendment row for `natural-bit-decode` (held-out -> development), naming
  both spent facts and both admitting commits.
- `artifacts/autogenesis/nursery-v2-extension.json` — regenerated via
  `gen-autogenesis-nursery-refill.py` (not hand-edited past the seed): the 10
  `natural-bit-decode` entries' partition flipped to `development`,
  `family_partitions`, `coverage.partition_counts` and `extension_sha256`
  recomputed by the tool. `preregistered_family_partitions` untouched (still
  `held-out`), per R10's contract — the ledger is what records the move.
  `artifacts/autogenesis/nursery-v1.json` is explicitly NOT touched: its own
  generator (`create-autogenesis-mathlib-nursery-split.py --check`) was
  already failing on HEAD before this change, for an unrelated pre-existing
  reason (it does not know about the ADR-0850 `component_split_exemptions`
  field and would delete it on regeneration) — out of this lane's scope, and
  regenerating it would have destroyed another lane's data. Confirmed by
  reproducing the same failure with this lane's edits stashed out.
- `scripts/gen-autogenesis-nursery-refill.py` — R12: a draw-time screen,
  scoped to rows the current draw ADDS, that imports
  `check-holdout-closed-evaluation.py`'s classifier by path (mirroring R11's
  import of `check-holdout-adjacency.py`) and refuses any new `held-out` row
  that is a closed evaluation over constants the kernel environment snapshot
  already declares.
- `scripts/tests/test_gen_autogenesis_nursery_refill.py` —
  `ClosedEvaluationScreenTests`, 6 tests: a real-snapshot replay of the exact
  `natural-bit-decode` spend, three false-positive controls (quantified
  sibling, undeclared constant, dispatchable partition), a ground-inequality
  control that isolates the shape check from the undeclared-name check, and
  a `guard()` integration test.

## Measured

Whole held-out population, both manifests, current 2,507-declaration
snapshot: **2 rows affected, both in `natural-bit-decode`, no other family.**

| gate | result |
|---|---|
| `check-holdout-closed-evaluation.py` | `held_out=146\|closed_shaped=0\|violations=0\|verdict=PASS` |
| `check-autogenesis-nursery.py` | `ready=true\|evaluation=214\|blockers=0` (both v1 and cross-population checks OK) |
| `check-autogenesis-holdout-isolation.py` | `held_out=146\|settled=0\|references=0\|verdict=PASS` |
| `check-dispatchable-frontier.py` | `DISPATCHABLE=33` (floor 10); the amended rows (`F:ml430-nat-bit-false-zero-d996adbf`, `F:ml430-nat-size-one-e23e5f71`, and 6 of the other 8 `natural-bit-decode` rows) now appear in the dispatchable list |
| `validate-facts.py` | `2364 facts checked, 0 errors` |

Cost: held-out shrinks **156 -> 146** rows (v2 extension alone: 140 -> 130,
10 -> 9 families). Per ADR-0762, this does not return
`Mathlib.Data.Nat.{Bits,Size}` to the drawable held-out pool for a future
draw — that is the price of these two rows not having been blind.

## Mutation-verification table (R12, `_closed_evaluation_screen` + its call in `guard()`)

All mutations applied and reverted in this lane's own worktree only
(`scripts/gen-autogenesis-nursery-refill.py`), never in the shared checkout.

| # | mutation | tests killed |
|---|---|---|
| A | drop the `partition != "held-out": continue` filter (screen every partition) | exactly 1: `test_a_dispatchable_row_is_not_screened` |
| B | drop the `is_closed_evaluation(statement)` shape check | exactly 1: `test_a_ground_inequality_is_not_a_closed_evaluation` (added after the first attempt at this mutation survived — see note below) |
| C | drop the `if undeclared: continue` filter | exactly 1: `test_a_closed_row_over_an_undeclared_constant_is_admitted` |
| D | remove the `_closed_evaluation_screen(new_entries, env)` call from `guard()` | exactly 1: `test_guard_integration_refuses_via_r12` |
| E | disable the final `raise RefillError(...)` (`if False and violations:`) | 2, by design: `test_the_real_spent_statements_are_refused_as_a_new_draw` (unit call) and `test_guard_integration_refuses_via_r12` (integration call) — both exercise the same terminal branch through two different call paths, not a redundant guard |

Note on B: the first version of the mutation-kill pass found that
`test_a_quantified_sibling_from_the_same_family_is_admitted` did NOT kill this
mutation — the quantified statement's bound variables (`b`, `m`, `n`) happen
to look "undeclared" on their own, so the undeclared-name filter (guard C)
coincidentally protected the row even with the shape check removed. Added
`test_a_ground_inequality_is_not_a_closed_evaluation` (`Nat.size 1 ≤ Nat.size 1`,
no bound variables, both sides the same already-declared constant, no `=`
sign) specifically to isolate the shape check from the undeclared-name check.
It kills exactly mutation B and nothing else.

## Can this recur?

Yes, narrower than before. R12 closes the case both real incidents actually
were — a construction already admitted, and current in the snapshot, at draw
time — by refusing the draw before the manifest is written. It cannot see a
construction declared in the gap between the last snapshot refresh and a
draw; that residual case is still caught only by the standing
`check-holdout-closed-evaluation.py` gate, one audit cycle later, exactly as
today. So: a third occurrence from a stale-snapshot window is still possible;
a third occurrence of "the construction already existed when the draw ran"
is not, unless R12 itself is bypassed or its import fails silently (which it
cannot: an import failure is a `RefillError`, not a skip).

<!-- plan-section: landed-changes -->

| 2026-08-30 | holdout-closed-evaluation-amendment | ADR-0950; `natural-bit-decode` amended held-out -> development (2 of 10 rows were closed evaluations); R12 draw-time closed-evaluation screen added to `gen-autogenesis-nursery-refill.py`, mutation-verified; all five required gates PASS |
