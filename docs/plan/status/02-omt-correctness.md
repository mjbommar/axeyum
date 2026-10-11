# Lane: omt-correctness — CON-5 objective semantics and limits

<!-- plan-section: lane-status -->

**OMT correctness (`WIP`, omt-correctness, 2026-10-10).** CON-5 O0/O1 patch:
generic objective-bearing solve/model/session calls explicitly decline; text
optimizers share caller budgets and stop unresolved lexicographic prefixes;
integer unboundedness uses replayed affine rays, not numeric search ceilings.
Focused fresh tests: optimize 25, optimize_robustness 14, smtlib 102, all passed.
Ray equality-guard mutation: baseline 4 pass, mutant 3 pass/1 fail. Closed-affine
coefficient controls (including div/mod by zero): 2/2 pass.
Workspace gate failed an untouched CAS timing test (isolated rerun passed).
Initial front-door group failed a timed string fixture (isolated rerun passed);
serial rerun passed all 158 tests. Five linear differential suites passed (20 tests).
Fresh full-feature library gate: 2008 pass/1 fail (EUF pigeonhole timeout
control returned Unknown under the generous budget). Workspace gate is live. Frontier finished 11 pass/1 NRA timing failure (degree 40 retained).
Module-graph ratchet is red with the same parent findings.
Both guard mutations killed exactly one test; independent finite oracle matched
128/128 cases. Next: finish required gates, Python OMT result/model/optimality
API, preemptible ingest. BV/multiobjective probes now receive remaining budgets;
fresh optimize 25 and robustness 16 tests passed, including all four zero-budget
BV entry points. ADR-2300 is
proposed pending validation. Other feedback tracks remain open. Detail:
[consumer plan](../proof-api-consumer-plan-2026-10-10.md).

Evidence and live validation handles: [lane notes](../notes/omt-correctness.md).
