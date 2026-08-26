# ADR-0583: Weighted CNF composition precedes target-machine cost claims

Status: accepted
Date: 2026-08-26
Index-summary: Compose bounded integer costs as checked CNF, lift weighted SIMD models, and keep dependent-latency claims distinct from scheduling

## Context

ADR-0566 decides minimum instruction count in one exact unary AVX2 language.
Instruction count is not a target-machine objective: on Haswell, the modeled
register forms have dependent latencies of either one or three cycles. Axeyum
had no reusable way to conjoin a pseudo-Boolean weighted-at-most constraint
with an already constructed CNF, so a SIMD-only encoding would have duplicated
a generally useful capability.

Even a correct sum of documented instruction latencies is not a complete
performance model. Intel explicitly says added latency figures are useful for a
dependency chain, while throughput and out-of-order execution matter for
parallel code. The current language is a single-register chain, but it still
omits frontend, port, bypass, and memory effects.

## Decision

Add a deterministic, resource-bounded `encode_weighted_at_most` composition to
`axeyum-cnf`. It accepts signed CNF literals with nonnegative integer weights,
copies the source formula, and builds capped dynamic-program layers for sums
`0..bound` plus overflow. Every layer is exactly one state; true and false
transitions are explicit; the final overflow state is forbidden. Invalid source
variables, arithmetic/resource ceilings, and non-satisfying projected models
fail closed.

Use that generic constraint in unary AVX2 synthesis. Every real instruction
cost must be positive. The bounded query allocates `bound / minimum_cost` slots
and adds a zero-cost internal no-op solely to pad shorter programs. Lifted models
drop padding, sum the costs of real typed instructions, and replay the original
target. The ordinary instruction-count encoder does not enable the no-op and
remains byte-identical.

The first profile is named
`intel-haswell-dependent-latency-cycles`: `vpshufb=1`, `vpermd=3`,
`vpermq=3`, same-source `vpalignr=1`, and same-source `vperm2i128=3`.
It is a serial dependency-chain proxy, not a throughput or whole-machine cost.

## Evidence

- Exhaustive tests compare all eight assignments of a weighted formula,
  including a negated literal, with the mathematical inequality. A forced
  overweight assignment produces DRAT accepted by the backward checker;
  out-of-range variables fail.
- Global byte reversal at cost at most three yields 6,024 variables and 235,303
  clauses. CaDiCaL 3.0.1 returns UNSAT in 1.35 wall seconds and emits a
  12,554,825-byte textual DRAT proof. Axeyum's file-backed backward checker
  accepts the complete proof and rejects the same proof truncated by 64 bytes.
- At cost at most four, the 7,710-variable / 308,555-clause formula solves SAT.
  Its model lifts and replays as `vpermd` dword reversal followed by `vpshufb`
  within-dword byte reversal, with summed profile cost four.
- Regenerating ADR-0566's unweighted one-step query produces the identical
  1,391,517 bytes and SHA-256
  `7da5e2668087334e73d7415e89fadee2e977d2e2937d6b263d2d4ad456cc88ec`.
- Intel's optimization manual gives latency one for `VPALIGNR` and `VPSHUFB`
  and three for `VPERMD/PS` on the Haswell model column. uops.info's measured
  register-operand pages independently report the selected one/three-cycle
  values, including three for `VPERM2I128` and the qword permute form.

## Alternatives

Encoding costs inside the SIMD transition clauses was rejected because the
same bounded pseudo-Boolean constraint is useful to circuits, schedules, and
other synthesis consumers. Repeating a family selector according to its weight
was rejected because it obscures the mathematical contract and scales with
weight rather than the admitted bound. Calling the result “minimum Haswell
latency” was rejected because it would erase the exact instruction/operand
language and overstate a dependency-chain proxy as a complete scheduler model.

## Consequences

In the exact ADR-0566 language and stated profile, global byte reversal has
minimum weighted cost four. This does not strengthen the already known
two-instruction upper bound into an ISA-wide or performance-priority claim.
Multi-source operations require explicit live-register semantics; realistic
target costing requires at least operand-specific latency, throughput/port
resources, and a schedule objective. The generic CNF composition can be reused
for those later models without trusting the SIMD encoder to enforce arithmetic.
