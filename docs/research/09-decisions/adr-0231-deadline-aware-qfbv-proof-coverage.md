# ADR-0231: Deadline-aware QF_BV proof coverage

Status: accepted
Date: 2026-07-17

## Context

ADR-0226 certifies all 169 rows in a declared stride-four/width-at-most-8
generated UNSAT subset, but a stride-one diagnostic blocks indefinitely at
seed 83. The proof-producing CNF core already supports an absolute deadline;
the independent-reference bit-blast miter and composed end-to-end API did not
thread it through. Process-killing the entire fuzz run would lose the row and
make a coverage percentage depend on finishers.

The desired contract is the project's ordinary resource rule: expiry is an
explicit nondecision, never a solver verdict or failed proof. Selected rows
remain in the denominator whether or not the stronger certificate completes.

## Decision

Add `certify_bitblast_by_miter_within` and
`certify_qf_bv_unsat_end_to_end_within`, sharing one absolute deadline across
the composed proof-producing SAT searches. Preserve the existing unbounded
APIs as `deadline=None` wrappers. Map expiry to `Inconclusive` or
`NotCertified`; completed certificates retain independent two-proof recheck.

Extend the standing fuzzer with an optional positive
`AXEYUM_QFBV_PROOF_DEADLINE_MS`. Give standalone CNF DRAT and the composed
end-to-end route separate budgets, count every selected UNSAT in exactly one
outcome per route, and print exact inconclusive/uncovered seeds.

Accept the complete width-at-most-8, stride-one cohort at 100 ms per route as a
wider publication denominator. Keep construction and checker time explicitly
outside the cooperative deadline; process isolation remains the future hard
wall-clock mechanism.

## Evidence

At clean Axeyum `86791f90`, the complete 4,000-formula run has 4,000 Axeyum/Z3
agreements and 1,487/1,487 SAT model replays. Of 2,513 generated UNSAT rows,
1,505 meet the predeclared width-at-most-8 selection (59.888579%):

- CNF DRAT: 1,505 attempted, proved, and rechecked; zero inconclusive;
- end to end: 1,505 attempted, 1,487 certified and rechecked, 18
  `NotCertified`;
- selected end-to-end coverage: 98.803987%; uncovered: 1.196013%.

The exact uncovered seeds are `83, 359, 741, 1063, 1094, 1275, 1437, 1495,
1873, 1906, 2635, 2793, 2826, 2907, 2986, 3127, 3447, 3638`. A preceding
content-equivalent repetition yields the identical list and counts. Exact
command, source/toolchain, policy, and exclusions are committed under
[`bench-results/qfbv-proof-deadline-20260717/`](../../../bench-results/qfbv-proof-deadline-20260717/README.md).

## Consequences

The paper may report 1,505/1,505 CNF DRAT and 1,487/1,505 stronger end-to-end
coverage over the complete declared width-at-most-8 UNSAT cohort. It must keep
the 18 uncovered rows in the denominator and state that cvc5 did not participate
in this proof-specific run; ADR-0225 remains the separate neutral-oracle result.

Seed 83 is no longer a blocking outlier. The bounded API preserves the same
certificate semantics and exposes resource exhaustion without weakening
`Unknown` discipline. Routine CI may retain ADR-0226's cheaper stride-four
sample; the stride-one command is the publication widening gate.

The API does not guarantee a 100 ms whole-call wall time. Lowering, independent
reference construction, CNF encoding, and proof checking remain cooperative
follow-ups or require killable process isolation. Nor does this generated
result establish real-query term-to-CNF faithfulness; ADR-0230 covers only CNF
DRAT on real rows.

## Alternatives

- Exclude seed 83 and divide by finishers: rejected because it inflates
  coverage.
- Count every resource expiry as a proof failure: rejected because it confuses
  capability under a policy with certificate validity.
- Kill the complete fuzz process at one slow row: rejected because later rows
  become unmeasured and the denominator is lost.
- Claim the deadline bounds all certificate work: rejected; only the existing
  proof search is cooperative today.
