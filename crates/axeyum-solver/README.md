# axeyum-solver

Solver backend interface for the
[Axeyum](https://github.com/mjbommar/axeyum) automated reasoning stack: the
backend trait, results (`Sat`/`Unsat`/`Unknown` as first-class outcomes),
models keyed by Axeyum symbols, capability descriptions, and cooperative
cancellation.

The default build has no C/C++ dependency; native backends are feature-gated
(`z3` arrives with milestone M0 and follows the demotion path of
[ADR-0002](../../docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md):
backend → differential oracle → CI cross-check).
The default backend implementation is now `SatBvBackend`, which composes
Axeyum's query terms, AIG lowering, Tseitin CNF, the pure Rust BatSat adapter,
model reconstruction, and evaluator replay for the supported QF_BV subset.

Design rationale:

- [Backend model](../../docs/research/03-architecture/backend-model.md) —
  trait shape and capabilities.
- [Incrementality and lifecycle](../../docs/research/03-architecture/incrementality-and-solver-lifecycle.md)
  — assumptions-first incrementality, arena/instance lifetimes.
- [Evidence and checking](../../docs/research/07-verification/evidence-and-checking.md)
  — why every `sat` is checked by evaluation.

Status: Phase 5 first slice — trait, models, Z3 oracle backend, and the
native-free SAT-backed BV backend with conformance and Z3 differential tests;
every `sat` in the test harness is replayed through the trusted evaluator.

License: MIT OR Apache-2.0.
