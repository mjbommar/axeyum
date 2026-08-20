# ADR-0547: Shard connected extension-field class vectors before larger geometry probes

Status: accepted
Date: 2026-08-20
Index-summary: Make connected Adams extension-field diagnostics deterministically shardable and require exact class-vector conservation before merged moments receive finite evidence credit

## Context

`binary_extension_connected_adams_trace` tests the geometric connected trace
by enumerating all `q^n` monic polynomials and retaining all `q^ell` Mangoldt
class populations.  Unlike the older one-class long-cycle operation, it had no
shard artifact or checked merge path.  The next level-three field row has
`16^7=268435456` candidates, so monolithic execution would prevent safe fleet
distribution and make partial results difficult to audit.

## Decision

Add `BinaryExtensionConnectedAdamsTraceShardReport` with deterministic
contiguous candidate endpoints and the complete partial class-population
vector.  Add

```text
binary_extension_connected_adams_trace_shard,
combine_binary_extension_connected_adams_trace_shards.
```

The merge sorts by shard index and rejects missing, duplicate, noncontiguous,
reversed, differently parameterized, or wrong-length shards.  It adds every
class component with checked arithmetic and requires the merged Mangoldt total
to equal `q^n` before computing `M_2`, `M_4`, the Wick subtraction, or the
connected trace.  The monolithic API now runs through the same one-shard merge
path.

Extend `axeyum-gf2-extension-trace` with `--connected-shard` and
`--connected-merge`.  Shards use canonical Serde JSON; the final command emits
bignums as decimal strings.  Focused tests compare two-, three-, and
seven-shard merges with direct execution over both `GF(2)` and `GF(4)`, round
trip shard serialization, and require failures for missing, duplicate,
parameter-mutated, vector-truncated, population-mutated, and invalid-index
inputs.

## Consequences

- Larger extension-field cutoff probes can now use independent fleet workers
  without weakening the exact classwise contract.
- A completed merge remains bounded finite diagnostic evidence.  It cannot
  prove a cohomological cutoff or an asymptotic Betti bound.
- Sharding removes an execution bottleneck, not the mathematical endpoint
  obstruction.  Any pattern inferred from merged rows must still be promoted
  to a separately proved uniform theorem and replayed through the endpoint
  ledger.
