# axeyum-scenarios

Self-checking consumer workloads for Axeyum. SAT scenarios carry
construction-known witnesses; UNSAT identity scenarios use bounded independent
checks. The crate supplies deterministic, oracle-free shapes for tests,
benchmarks, curriculum examples, and performance attribution.

The [crate documentation](src/lib.rs) contains a compile-tested example and
explains what each expectation establishes.

```sh
cargo test -p axeyum-scenarios
```
