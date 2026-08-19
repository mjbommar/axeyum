# Lane: mutation-harness — a mutation check may not report a result it did not measure

<!-- plan-section: lane-status -->

**A mutant that did not compile was scored as coverage** (`WIP`,
agent-mutation-harness, 2026-08-18). Measured against `mutation_controls.py` as
it stood: replacing `if len(unchecked) > ceiling:` with `if len(unchecked) > >
ceiling:` printed **`killed 0`** and counted the guard as tested. So did a suite
that executed zero tests — the `#![cfg(feature = "full")]` trap. Both push in the
unsafe direction, and every "exactly one test died" in this repository rests on
the mutant having been built and run.

Outcomes are now a closed set of which only `killed N` and `SURVIVED` are
measurements; `DID NOT BUILD`, `DID NOT RUN`, `NOT APPLIED`, `AMBIGUOUS ANCHOR`
and `INCONSISTENT` fail the run in a **separately counted** bucket, because "the
guard is not tested" and "the harness could not tell" have different fixes. A
build probe runs before any test count is believed; the two independent kill
counts (headers, summary) must agree with each other and with the exit status;
collection size must match the baseline. A `cargo` runner covers the route the
defect was found on.

`mutation_controls.py self-demo` produces one of each of the four outcomes from a
real mutation and fails unless the harness names all four; it is wired into both
`just check` and `check.sh`. The harness is mutation-checked against itself
(`mutation-controls`, 24 guards / 31 controls): first run **21 killed, 3
SURVIVED**, all three real, now **24/24**.

The new ambiguous-anchor check found **two dead controls** in
`lra-hypothesis-binding` — one mutating the same copy another control already
drove — plus one genuinely uncovered guard in `bind_structural`, left for the
lane that owns it.

Detail: [`../notes/agent-mutation-harness.md`](../notes/agent-mutation-harness.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `mutation_controls.py`: a mutation check can no longer report a result it did not measure. `DID NOT BUILD` / `DID NOT RUN` / `AMBIGUOUS ANCHOR` / `INCONSISTENT` are distinct from `killed N` and `SURVIVED` and are counted separately; build probe, two independent kill counts, baseline test count, verified restore, and a `cargo` runner for the route the defect was reported on. `self-demo` demonstrates all four outcomes live; `mutation-controls` mutation-checks the harness (24 guards, 31 controls, 24/24 killed after 3 real survivors were fixed). Found and repaired two dead controls in `lra-hypothesis-binding` (53/53). Wired into both `just check` and `check.sh`. |
