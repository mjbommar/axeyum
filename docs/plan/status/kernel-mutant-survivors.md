# Lane: kernel-mutant-survivors — closing the ADR-0780 mutant survivors

<!-- plan-section: lane-status -->

**Status:** COMPLETE — all four ADR-0780 mutant survivors closed. Kill table is
8 killed / 0 survived over a 35-case corpus. No P0 in the unmutated kernel.

Decision: [ADR-0815](../../research/09-decisions/adr-0815-a-mutation-aimed-at-a-call-site-cannot-see-a-shared-predicate.md)

## What this lane was for

ADR-0780's kernel differential found zero Axeyum-accepts/Lean-rejects
disagreements, which is the result we wanted, and then mutation-tested the
kernel itself and had **four of eight mutants survive**. A survivor means a
soundness guard was removed and the differential did not notice. The
`inductives` one was unexplained, which made it the most important open item
in L0 — ADR-0717's risk 1 is exactly "our own kernel could have a shared
semantic defect", and this was a place where we removed a check and the
detector shrugged.

## Headline

**All four had one cause between them, and it is not a corpus weakness.**
Three of the four (`inductives`, `projections`, `quotient`) were killed by a
SECOND guard implementing the same predicate at a different call site; only
`literals` was a genuine missing case. A mutation aimed at a call site cannot
be killed when a redundant implementation still rejects — and the fix is to aim
at the predicate, not to write more cases.

### `inductives` — outcome 1: a different real guard rejects

Five measured rebuilds, `--release`, in this worktree.

| # | kernel state | `add_inductive(Bad, …)` |
|---|---|---|
| E1 | unmutated | `Err(NonPositiveInductiveOccurrence)` |
| E2 | positivity `Err` off (`inductive.rs:1933`) — ADR-0780's mutation | `Err(ReflexiveOrNestedNotSupported)` |
| E3 | field-shape classification off (`inductive.rs:2076`) | `Err(NonPositiveInductiveOccurrence)` |
| E4 | **both off** | **`Ok(())`** — P0 |
| E5 | shared predicate `mentions_group_family` `Const` arm → `false` | **`Ok(())`** — P0 |

E1 rules out the possibility ADR-0780 could not: the case does reach the
targeted guard. E2 names the taker-over. E3 shows symmetry. **E4** proves the
pair is jointly load-bearing rather than both being decoration. E5 is the
correctly-aimed single mutation and it KILLS.

`check_group_positive_occurrence` and `open_group_recursive_field_shape` are
the same algorithm written twice; one returns `Some` exactly where the other
returns `Ok`. **No case can separate them** — that impossibility is the
finding, not a corpus gap.

### Survivors closed, and the mutant each new case kills

Detail moved to [`../notes/kernel-mutant-survivors.md`](../notes/kernel-mutant-survivors.md).

