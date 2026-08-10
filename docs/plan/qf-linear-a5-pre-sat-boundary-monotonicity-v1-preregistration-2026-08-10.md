# QF linear A5 pre-SAT boundary monotonicity v1 preregistration — 2026-08-10

Result: the target and all three safety controls passed; see the
[v1 result](qf-linear-a5-pre-sat-boundary-monotonicity-v1-result-2026-08-10.md).

## Decision boundary

The structurally valid V2 cross-division capture at exact pushed commit
`5a53012e13757e4f992e6197d83b9f12a6268471` is non-credited. Its lossless
derivation stopped on the permanent monotonicity control
`QF_LRA/sal/windowreal/windowreal-no_t_deadlock-17.smt2`: historical Axeyum,
the retained reference, and the declared status are all `unsat`, while the
fresh capture returned typed resource `unknown` before the first SAT round.

The loss is deterministic rather than timing-sensitive. The current trace has
1,217 arithmetic atoms, 6,526 propositional CNF variables, zero initial theory
clauses, and zero blocking lemmas. Commit `d599b682f` introduced the joint
1,024-atom/4,096-variable pre-SAT boundary after the historical result. Later
captures reproduced the same JSONL bytes but did not run the cross-division
monotonicity derivation; a complete stream is not sufficient evidence of a
valid census.

This note authorizes one bounded safety discriminator. It does not authorize a
general timeout, memory, normalization, online-LRA, route-order, or proof-policy
change, and it does not credit any V2 capture.

## Frozen target and controls

Use the shipped release `explain_corpus` configuration, a 24,000 ms query
timeout, the inherited 8 GiB `RLIMIT_AS`, one file per process, and zero
stderr. Record exact source and binary identity, verdict, trace, wall time, and
peak RSS for every observation.

| Role | Exact suffix | Current pre-SAT counts | Required candidate outcome |
|---|---|---:|---|
| lost monotonicity target | `QF_LRA/sal/windowreal/windowreal-no_t_deadlock-17.smt2` | 1,217 atoms / 6,526 variables | `unsat` in 3/3 observations, each within 24 seconds and below 4 GiB peak RSS |
| original first-solve abort control | `QF_LRA/sal/pursuit/pursuit-safety-16.smt2` | 1,447 / 4,733 | typed pre-SAT resource `unknown`, zero SAT rounds |
| original wide-core/large-skeleton control | `QF_LRA/sal/tgc/tgc_io-safe-20.smt2` | 1,411 / 6,774 | typed pre-SAT resource `unknown`, zero SAT rounds |
| low-atom, very-wide IDL control | `QF_IDL/asp/MazeGeneration/maze-generation-width=19-height=19-density=0.01-run=5.smt2` | 1,084 / 31,944 | typed pre-SAT resource `unknown`, zero SAT rounds |

The controls run only after the target gate passes. Any wrong verdict, process
failure, stderr, timeout overrun, or memory-bound violation rejects the
candidate and stops without an aggregate run.

## Candidate mechanism

Factor the pre-SAT admission decision into a deterministic helper and admit
one additional moderate rectangle only: at most 1,280 arithmetic atoms **and**
at most 8,192 CNF variables. The existing rule remains unchanged outside that
rectangle. In particular, both historical abort controls and the 31,944-
variable IDL control must still decline before the first SAT round.

The bounds are structural, query-independent, and deliberately separate from
available host RAM. Across all 600 non-credited V2 rows, the lost LRA control
is the only current pre-SAT decline inside the proposed rectangle. This is a
measured boundary refinement, not benchmark-name admission.

## Acceptance and restart

If the target and controls pass, add exact helper-boundary regressions, amend
ADR-0377 and the A5 repair record, and run format, strict all-feature solver
Clippy, the complete solver-library suite, deep-input non-recursion, online
arithmetic integrations, QF_LRA differential fuzz, and simplex-LRA fallback
differential tests. A complete exact-commit repository gate remains required
before measurement.

Any accepted behavior change invalidates the entire existing V2 sequence.
After commit, push, and the complete gate, restart QF_LRA from row 1, then
QF_IDL, then QF_RDL under the unchanged V2 capture protocol. Only a fresh
three-division derivation with zero historical losses and wrong verdicts may
authorize residual grouping or a later solver-breadth experiment.
