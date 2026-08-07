# Public API

Axeyum is a workspace of composable Rust crates, not one monolithic facade. The
right entry point depends on whether you have terms, SMT-LIB text, a corpus, or
a proof/evidence task.

## Common entry points

| Goal | Crate / API |
|---|---|
| Build typed terms and evaluate ground terms | [`axeyum-ir`](../../crates/axeyum-ir/src/lib.rs) |
| Build assertions, assumptions, scopes, and labels | [`axeyum-query`](../../crates/axeyum-query/src/lib.rs) |
| Parse or write SMT-LIB without solving | [`axeyum-smtlib`](../../crates/axeyum-smtlib/src/lib.rs) |
| Solve terms with the default scalar-BV backend | `axeyum_solver::SatBvBackend` and `SolverBackend` |
| Auto-dispatch the full pure-Rust theory surface | `axeyum_solver::solve` / `check_auto` with feature `full` |
| Solve one complete SMT-LIB script | `axeyum_solver::solve_smtlib` with feature `full` |
| Preserve multiple SMT-LIB query points | `axeyum_solver::solve_smtlib_incremental` |
| Produce or check proof/evidence artifacts | `axeyum_solver::proofs` and `certificates` |
| Run corpus comparisons and emit JSON | `axeyum-bench` binary |

Generate the exact API documentation for the selected features:

```sh
RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps
cargo doc -p axeyum-solver --features full --no-deps --open
```

## Core result contract

[`SolverBackend`](../../crates/axeyum-solver/src/backend.rs) returns:

- `CheckResult::Sat(Model)` for a source-level model;
- `CheckResult::Unsat` for a definitive refutation;
- `CheckResult::Unknown(UnknownReason)` for timeout, resource limits, or an
  incomplete procedure; and
- `SolverError` for malformed/unsupported input or an operational/internal
  failure.

`Unknown` is a successful solver response, not an error. A `Sat` model should be
checked against the original assertions; an `Unsat` result's independent
assurance depends on the selected route. See the [Trust ledger](trust-ledger.md).

## Feature profiles

| Feature selection | Surface |
|---|---|
| default | Pure-Rust scalar QF_BV backend and common result/model types |
| `full` | Pure-Rust multi-theory dispatch, SMT-LIB solving, proof/certificate namespaces, optimization/interpolation/verification modules |
| `z3` | `full` plus the system-linked Z3 differential oracle |
| `z3-static` | `z3` using a downloaded prebuilt static Z3 |

The `z3` profiles are oracle/integration leaves, not the default product
dependency. See [Installation and build profiles](../user-guide/installation.md#feature-profiles).

## Stable namespaces

The solver crate groups its broad full-profile surface by purpose:

- `constraints` — Boolean cardinality and pseudo-Boolean builders;
- `proofs` — proof export, checking, Alethe, and end-to-end proof APIs;
- `certificates` — checked theory- and fragment-specific certificates;
- `theories` — direct theory procedures;
- `verification` — transition-system and symbolic verification helpers;
- `optimization` — optimization entry points;
- `interpolation` — verified and certified interpolation APIs; and
- `fp` — floating-point formula builders.

Historical crate-root re-exports may remain source-compatible but hidden from
root rustdoc. New code should prefer the documented namespace.

## SMT-LIB Rust results are typed, not transcripts

`solve_smtlib` returns `SmtLibOutcome { result, logic, expected_status }`.
Model, value, assertion, info, option, core, proof, and incremental helpers
return Rust values or a canonical proof string. They do not implement a
drop-in interactive SMT-LIB stdout session. See [SMT-LIB support](smtlib-support.md)
for the exact command/API matrix.

## API design rules

- Public term handles are lifetime-free `Copy` IDs owned by an arena.
- Backend/FFI types and lifetimes do not leak into public APIs.
- Output ordering, seeds, and resource controls are deterministic.
- The default dependency graph remains pure Rust and `unsafe_code` is denied.
- New public operators, routes, or evidence formats follow the
  [foundational DAG](../research/08-planning/foundational-dag.md).
