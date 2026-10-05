# Lane: unblock-index-zero

<!-- plan-section: lane-status -->

Status: complete (2026-08-31). Index 0 is filled; no draw authored.

## What this lane did

ADR-1220 measured that cycle **index 0** was the binding slot for draw 16 and
named `Mathlib.Computability.Primrec.Basic` (11 rows, zero boundary rows, no
churn, no stale review) as the only candidate that fits it, needing
`Nat.Primrec` and `Nat.casesOn`. Both are declared, **construction only**
(ADR-0653), with no theorem about either and no fact registered.

Every ADR-1220 figure was reproduced against a freshly rebuilt `shape_search`
and the real `select()` / `assign_partitions()` / `screen_family()` /
`is_closed_evaluation` — pool 11, boundary rows **0 of 10** read verbatim,
frozen-family churn **0 of 42**, stale reviews **0 of 4**.

Post-declaration the environment is **2706** (exactly +10: 1 definition,
1 inductive, 7 constructors, 1 recursor) and layout RP puts
`natural-primitive-recursion` at index 0 held-out, R9/R10/R12 passing and R11
clean on every hard signal. The one remaining refusal is **R11's authorable
disclosure**, which is a review that must be performed rather than asserted and
belongs to the draw lane.

## The substantive finding

`Nat.Primrec` is an inductive `Prop`, so it **admits no evaluation test** — the
safeguard every definition here leans on, because the kernel cannot tell a
`Definition` is wrong. What replaces it:

1. The predicate does not evaluate but its constructor **indices** do, so the
   evaluation test is recovered one level in.
2. **Closed derivations** assembled from the real constructors and inferred —
   the check no per-constructor assertion can make.
3. A **binder-count** assertion, so a constructor that lost a hypothesis fails
   rather than passing as a weaker statement.

Five mutants, four killing exactly one test each.

## Landed changes

| change | where |
| --- | --- |
| `Nat.casesOn.{u}` and the inductive `Nat.Primrec` | `crates/axeyum-lean-kernel/src/nat_prelude/primrec.rs` |
| the evaluation-test substitute, 4 tests | `crates/axeyum-lean-kernel/src/nat_prelude/primrec_tests.rs` |
| coverage: `Nat.casesOn` + all 8 inductive names by name | `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` |
| the reproducible screen against the real machinery | `docs/research/09-decisions/adr-1240-index-zero-screen.py` |
| the decision | `docs/research/09-decisions/adr-1240-index-zero-is-filled-an-inductive-prop-gives-up-the-evaluation-test.md` |
| environment snapshot 2693 -> 2706 | `artifacts/autogenesis/kernel-environment-snapshot-v1.json` |

## Verification

- `--lib nat_prelude::primrec` 4 passed / 0 failed (nonzero, confirmed).
- `--lib nat_prelude::` **303 passed / 0 failed**, up from 302.
- `gen-autogenesis-nursery-refill.py --check`: manifest **byte-identical** under
  the refreshed snapshot, 420 entries, partition counts unchanged.
- Five gates green before and after; `held_out=166 settled=0 PASS` both times.
- `check-shape-duplicates.py` and `validate-facts.py` both exit 0.

## Next

- **Index 3** wants `Nat.ceilRoot`/`Nat.floorRoot`. Its 3-of-10 boundary count
  is ADR-1220's, measured against Mathlib's `Finsupp` definition which we cannot
  build — **re-measure it against whatever construction is actually written.**
  That route also reds `check-holdout-adjacency.py` until draw 11's
  `natural-nth-root` review is redone, in the same lane.
- The `natural-primitive-recursion` pool is **11 against a floor of 10**. One
  row of slack; declaring `id` would widen it but risks churning other families.
- Ordinary `Nat.Primrec` theorems (`add`, `mul`, `pow`, `pred`, `const`,
  `of_eq`) can land from `development` after the draw, where they cost nothing.
