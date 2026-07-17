# ADR-0217: Glaurung small-driver performance regime

Status: accepted
Date: 2026-07-17

## Context

ADR-0215 retired the historical cold-Z3/warm-Axeyum headline and found that
topology-equivalent warm Z3 beat warm Axeyum on DptfDevGen. The reviewer
follow-up proposed a narrower hypothesis: Axeyum might win on small formulas
where boundary and construction costs dominate, while Z3 wins on harder,
solver-bound formulas.

One driver cannot establish either a general loss or that proposed boundary.
The named next control was the same N>=5 four-cell method on vwififlt, IntcSST,
and SurfacePen, with the result reported even if the hypothesis failed.

## Decision

Accept the repeated three-driver artifact as evidence that Axeyum has a real,
workload-dependent winning regime. Do not yet name formula size, FFI overhead,
or solver hardness as its causal boundary.

Keep the publication language at the level established by the data: under the
same fixed-work four-cell methodology, warm Axeyum wins on IntcSST and
SurfacePen, reaches parity on vwififlt, and loses to warm Z3 on DptfDevGen.
Any stronger regime description requires joined per-query feature attribution.

The next causal pass must correlate paired outcomes with at least formula/DAG
size, operator family, lowered AIG/CNF size, SAT share, and retained-state reuse
class. A neutral solver and timeout-sensitive marked workload remain separate
controls rather than post-hoc explanations of these four drivers.

## Evidence

The capture uses clean Glaurung `403a5c5`, Axeyum `4464dae2`, one worker, five
sequential fresh processes per driver, a 60-second per-function solver bound,
and the same 9-path/512-assertion warm envelope and replay-SAT cache policy as
the accepted control. Each driver preserves exact work across repetitions:

- vwififilt: 4,742 checks, 14 warm-created and 4,728 retained;
- IntcSST: 1,672 checks, 24 warm-created and 1,648 retained; and
- SurfacePen: 2,551 checks, 43 warm-created and 2,508 retained.

All four cells decide every occurrence. There are zero nondecisions,
operational results, decided disagreements, replay failures, or fallbacks.

The paired warm Z3/Axeyum geomeans are:

- vwififlt: 1.0030x [0.9731, 1.0350], statistical parity;
- IntcSST: 1.5315x [1.4512, 1.6167], favoring Axeyum; and
- SurfacePen: 1.5584x [1.5069, 1.6096], favoring Axeyum.

Per-run warm-ratio CV is 0.66%, 1.33%, and 1.61%, respectively. Cold results
also split: vwififlt is 0.6185x [0.6061, 0.6313], while IntcSST and SurfacePen
are 2.3703x [2.2719, 2.4744] and 2.4901x [2.4073, 2.5763]. That cold split is
direct evidence against attributing the observed warm map solely to saved FFI
entry cost.

The exact reports and CDFs are committed under
[`bench-results/glaurung-four-cell-small-drivers-20260717/`](../../../bench-results/glaurung-four-cell-small-drivers-20260717/README.md).

## Alternatives

- Generalize the Dptf loss to all workloads: rejected by the two decisive
  Axeyum wins.
- Claim Axeyum wins on small formulas: rejected because one named small driver
  is parity and the available artifact does not yet measure formula features.
- Attribute the wins to FFI overhead: rejected because IntcSST and SurfacePen
  also favor Axeyum in the cold topology, while vwififlt favors Z3 cold.
- Pool drivers into one aggregate: rejected because it hides the regime the
  experiment was designed to characterize.
- Treat parity as a win: rejected; the vwififlt interval crosses one.

## Consequences

The publication plan may now state that a measured Axeyum-winning regime
exists, with exact named workloads and confidence intervals. It must also show
the tie and loss and must not advertise a universal speedup.

The immediate performance task changes from collecting these three drivers to
explaining their boundary with query-feature attribution and adding neutral
and timeout-sensitive controls. Correctness fuzzing and authoritative finding
parity remain higher-level publication blockers, and product defaults do not
change from this diagnostic evidence.
