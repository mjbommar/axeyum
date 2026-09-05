# Solver Configuration

[`SolverConfig`](../../crates/axeyum-solver/src/backend.rs) is the per-query
configuration shared by solver backends and full-profile dispatch. Start from
`SolverConfig::default()` and enable only measured, required levers.

## Resource and admission controls

| Field | Meaning |
|---|---|
| `timeout` | Wall-clock budget for the complete check |
| `resource_limit` | Backend-specific deterministic search budget |
| `memory_limit_mb` | Backend memory budget where supported |
| `node_budget` | Maximum translated DAG nodes before submission |
| `cnf_variable_budget` | Maximum CNF variables submitted to SAT |
| `cnf_clause_budget` | Maximum CNF clauses submitted to SAT |

Budget exhaustion returns a classified `CheckResult::Unknown`; it is not
`Unsat` and normally not a `SolverError`. `resource_limit` units are backend-
specific, so artifacts must record both the value and backend/unit.

## Assurance and preprocessing controls

| Field | Meaning |
|---|---|
| `prove_unsat` | Require a DRAT-checked BV UNSAT verdict; the current native core checks its proof inline |
| `preprocess` | Run the full-profile denotation-preserving canonicalizer before dispatch |
| `cnf_inprocessing` | Enable model-reconstructing CNF subsumption/BVE pipeline |
| `cnf_vivify` | Add clause vivification when CNF inprocessing is enabled |

`preprocess` defaults on because the denotation-preserving canonicalizer is a
measured, replay-safe default. The other assurance/inprocessing levers in this
table default off.

`prove_unsat` is a high-assurance verdict mode for bounded instances. On the
current SAT-BV path the proof-producing native core is the primary SAT search
and checks its emitted DRAT proof inline in the same solve. A compatibility
fallback that receives an unchecked adapter result re-derives and verifies it;
inability to obtain a checked proof fails closed to `Unknown`.

This mode does not return or write the proof artifact, and it is not a guarantee
that every supported theory can produce an end-to-end proof. Use the
[UNSAT evidence exporter](../user-guide/unsat-evidence.md) when certificate
files are required, and check the [trust ledger](trust-ledger.md) for the
selected fragment and route.

## Lowering and search experiments

| Field | Meaning |
|---|---|
| `bit_lowering_mode` | Eager, demand-sliced, or admission-controlled range-sliced cold BV lowering |
| `incremental_positive_and_flattening` | Opt into the named incremental flattening policy |
| `xor_cdcl_fallback` | Enable the CDCL(XOR) fallback |
| `lazy_bv` | Enable the lazy/CEGAR BV experiment |
| `lazy_bv_abstract_ite` | Permit ITE abstraction within lazy BV |
| `native_cdcl` | **Retired no-op** (ADR-1703). The in-tree CDCL core is the primary SAT search unconditionally; nothing reads this field. Kept only because `axeyum-py`, `axeyum-bench` and `axeyum-verify` name it |

These levers are separate and mostly off by default. Do not combine them into
an undocumented “fast” profile; benchmark each configuration with an explicit
artifact policy.

## Diagnostic profiling

| Field | Meaning |
|---|---|
| `profile_bit_demand` | Collect observational bit-demand diagnostics |
| `profile_cnf_construction` | Collect detailed AIG-to-CNF construction attribution |

Profiling should not change the verdict or circuit, but it can add material
cost. Keep it off in ordinary production cells and label diagnostic artifacts.

## Example

```rust
use std::time::Duration;
use axeyum_solver::SolverConfig;

let config = SolverConfig::default()
    .with_timeout(Duration::from_secs(2))
    .with_node_budget(100_000)
    .with_cnf_variable_budget(1_000_000)
    .with_cnf_clause_budget(3_000_000);
```

Builder method names and available fields are checked by rustdoc; use:

```sh
cargo doc -p axeyum-solver --features full --no-deps --open
```

## Reproducibility rules

- Record the complete configuration, not only timeout.
- Distinguish wall-clock limits from deterministic resource limits.
- Record backend/version and feature profile.
- Treat `UnknownKind` classes separately in results.
- Do not compare benchmark cells with different admission or replay policies.
- Keep model replay and proof-check state beside the verdict.

See [Benchmark artifacts](../contributor-guide/benchmark-artifacts.md) for the
retained-artifact contract.
