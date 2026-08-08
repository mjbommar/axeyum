# axeyum-solver

Axeyum's solver contract and orchestration hub: `Sat`/`Unsat`/`Unknown`, typed
models, configuration and deadlines, cold and retained backends, multi-theory
dispatch, and evidence/checking APIs.

The default feature profile is the pure-Rust scalar Bool/BV surface. Feature
`full` enables multi-theory dispatch, SMT-LIB solving, and the broader
certificate/reconstruction namespaces. `z3` and `z3-static` are optional oracle
leaves; they are not default product dependencies.

The [crate documentation](src/lib.rs) has a compile-tested default-profile
example. Complete runnable programs include:

```sh
cargo run -p axeyum-solver --features full --example first_smtlib_query
cargo run -p axeyum-solver --features full --example geometry_portfolio
```

Read [Rust embedding](../../docs/user-guide/rust-embedding.md),
[Solver dispatch](../../docs/internals/solver-dispatch.md), and
[Proof and evidence routes](../../docs/internals/proof-stack.md). Exact fragment
and assurance claims remain in the generated
[support matrix](../../docs/reference/support-matrix.md) and
[trust ledger](../../docs/reference/trust-ledger.md).

License: MIT OR Apache-2.0.
