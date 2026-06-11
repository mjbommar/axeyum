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

Design rationale:

- [Backend model](../../docs/research/03-architecture/backend-model.md) —
  trait shape and capabilities.
- [Incrementality and lifecycle](../../docs/research/03-architecture/incrementality-and-solver-lifecycle.md)
  — assumptions-first incrementality, arena/instance lifetimes.
- [Evidence and checking](../../docs/research/07-verification/evidence-and-checking.md)
  — why every `sat` is checked by evaluation.

Status: pre-M0 stub.

License: MIT OR Apache-2.0.
