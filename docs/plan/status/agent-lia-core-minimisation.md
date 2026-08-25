# Lane: lia-core-minimisation — the width gate that made the solver quit at 5 % budget use is gone

<!-- plan-section: lane-status -->

**Gap #1's one confirmed fix is landed, in the form its diagnosis said to ship
it in: minimisation is budget-driven, not width-gated** (`WIP`,
agent-lia-core-minimisation, 2026-08-21). `dpll_lia.rs` had one constant doing
two jobs — deciding whether a theory conflict core was minimised at all, and
deciding which cores are charged against the wide-clause retention budget. The
[diagnosis](../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§5.2 measured what that costs: the cores too wide to minimise are exactly the
cores whose width then exhausts the retention budget, so a solve declines for
want of the narrow clauses it refused to narrow. The jobs are now separate —
`MINIMIZATION_ORACLE_CALL_BUDGET` (a deterministic **oracle-call** ration, chosen
over wall clock because determinism is a public API promise) admits the pass;
`WIDE_THEORY_CORE_ATOMS` (still 128) only decides retention accounting, by
**retained width** rather than by provenance, which keeps the memory protection
the naive constant bump gives up.

Measured on the pinned 200-file competition lists, three binaries plus z3 4.13.3
run **adjacent in time per file** so contention is shared across the arms:

| division | base | A/B (128→4 096) | **shipped** | vs z3 | vs declared `:status` |
|---|---:|---:|---:|---|---|
| **QF_UFLIA** | 92 | 112 | **114 (+22, −0)** | **0** disagreements / 114 | **0** / 114 |
| QF_IDL (control) | 66 | 66 | **65 (+0, −1)** | **0** / 63 | **0** / 65 |

Detail moved to [`../notes/agent-lia-core-minimisation.md`](../notes/agent-lia-core-minimisation.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `40a1ab969` | `crates/axeyum-solver/src/dpll_lia.rs` + ADR-0538 + `bench-results/lia-core-minimisation-20260821/`: theory-core minimisation rationed by an oracle-call work budget instead of a core-width gate. QF_UFLIA 92 → 114 (+22, −0) at 0 disagreements against z3 and 0 against the declared `:status`. |
