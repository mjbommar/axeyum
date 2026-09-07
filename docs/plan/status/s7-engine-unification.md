# Lane: s7-engine-unification — the native core decides under a theory, and says what it assumed

<!-- plan-section: lane-status -->

**S7 of the [SMT/SAT parity plan](../smt-parity-plan-2026-09-05.md) is in
progress, and it is larger than one lane. This lane lands S7a: the native
core's three declined theory paths (an `assert` conflict, a propagation onto a
falsified literal, a `final_check` conflict) and dynamic atom registration are
implemented, and a CDCL(T) `unsat` now produces the ADR-1704 two-stream
artifact graded at `TrustId::SatRefutationModuloTheory`. Moving `CdclT`'s ten
adapters onto that core is S7b** (`WIP`, s7-engine-unification, 2026-09-06).

<!-- plan-section: landed-changes -->
