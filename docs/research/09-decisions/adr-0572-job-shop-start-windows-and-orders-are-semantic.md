# ADR-0572: Job-shop start windows and orders are semantic

Status: accepted
Date: 2026-08-26
Index-summary: Restrict job-shop start domains by exact chain windows and expose typed machine-order selectors

## Context

ADR-0565 introduced a complete time-indexed job-shop encoding, independent schedule replay,
model lifting, and checked DRAT. Its baseline assigned every operation every start from zero
through `bound - duration`; job precedence clauses then removed the starts impossible under
the operation's own job chain. On `abz7@655`, that produced 381,418 variables and 4,343,486
clauses before search.

Earliest/latest operation windows and same-machine disjunctive ordering are classical
scheduling techniques. The architectural gaps were that Axeyum neither applied the exact
job-chain windows before allocation nor exposed its machine-order bits with semantic labels,
so consumers could not safely construct scheduling-specific proof partitions.

## Decision

Keep ADR-0565's encoder byte-stable and add an opt-in
`encode_job_shop_with_job_windows`. For operation `k` in one job, admit only starts in

```text
sum(duration[0..k]) ..= bound - sum(duration[k..])
```

with an empty domain becoming an explicit CNF contradiction. Every prefix implication and
machine-capacity clause is translated relative to the resulting nonzero domain origin. Model
lifting converts a selected domain offset back to its absolute start and runs the same
independent schedule checker.

Every same-machine operation pair is also exposed as a typed `JobShopMachineOrder`, binding
the machine, both `(job, operation)` identities, and the exact CNF selector. Selector true
means the left operation finishes before the right starts; false means the reverse. The
complete list is deterministic and may be passed to Axeyum's generic cube machinery without
recovering private CNF layout.

## Evidence

- Across every bound 0 through 5 of a two-job/two-machine control, baseline and windowed
  formulas agree on satisfiability; every windowed SAT model lifts and independently replays.
- The control's typed order selectors agree with the actual order of both operation pairs in
  a lifted schedule. Their full Boolean product has a covering DRAT proof accepted by the
  independent checker.
- `ft06@55` shrinks from 3,692 variables / 15,958 clauses to 1,722 / 6,558; its retained
  makespan-55 schedule pins, solves, lifts, and replays. `ft06@54` shrinks from 3,620 / 15,640
  to 1,650 / 6,249 and emits a 1,348-step refutation accepted by Axeyum.
- `abz7@655` shrinks from 381,418 variables / 4,343,486 clauses / 102,215,416 bytes to
  175,170 / 1,689,970 / 35,634,404 bytes. The opt-out formula remains byte-identical at its
  retained SHA-256 `b5cb322a...3f7d`.
- A four-cell product over two typed `abz7` order selectors has a checked two-step covering
  proof. All four 120-second leaf searches and both 600-second monolithic searches remained
  unknown, so this demonstrates sound partition construction but certifies no bound.
- The complete `axeyum-search` test suite, all-target/all-feature Clippy, and rustdoc pass.

## Consequences

The windowed route removes starts already refuted by the job's defining precedence chain
before SAT allocation, while preserving the original encoding for artifact reproduction.
Machine-order descriptors provide a reusable semantic split boundary for local or distributed
search and checked cube composition.

This optimization is prior scheduling mathematics and carries no novelty claim. It changes
neither the meaning of a solver status nor the certification rule: SAT still requires lifted
schedule replay, and UNSAT still requires a proof checked against the exact emitted formula.
