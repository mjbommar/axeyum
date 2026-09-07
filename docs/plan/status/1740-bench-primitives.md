# Lane: bench-primitives — benches and a profile for the three shared primitives

<!-- plan-section: lane-status -->

**Measuring the primitives every division above them pays for: the `axeyum-ir`
arena/value/evaluator layer, `axeyum-bv` term-to-AIG lowering, and the
`axeyum-smtlib` parser and writer** (`WIP`, bench-primitives, 2026-09-07).

Two of the three crates (`axeyum-bv`, `axeyum-smtlib`) had **no benches at all**
before this lane; `axeyum-ir` had exactly one (`arena_intern`, added 2026-09-05
as the before/after instrument for the `FastMap` hasher swap, which has since
landed).

Running diary, including the places this lane's predictions were wrong:
[`docs/research/12-performance/bench-primitives-2026-09-07.md`](../../research/12-performance/bench-primitives-2026-09-07.md).

Standing constraint carried from the brief and honoured per bench: **a
microbenchmark that does not predict the real workload is worse than none.**
Every bench added here names, in its own module doc, the real workload it is a
proxy for — or says plainly that it has not been shown to predict anything.

<!-- plan-section: landed-changes -->

| 2026-09-07 | bench-primitives | lane status, performance diary, and the first `axeyum-smtlib` parse bench over committed corpus files |
