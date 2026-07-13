# Rust embedding

Axeyum's Rust API keeps construction strict: operators never guess how to
reconcile different sorts. This catches lifter bugs at the point where they are
introduced instead of silently changing a formula before solving it.

For a scalar-QF_BV-only consumer, select the dependency-minimal profile:

```toml
[dependencies]
axeyum-solver = { version = "0.1", default-features = false, features = ["qfbv"] }
```

That profile retains the cold and warm pure-Rust QF_BV backends, models,
configuration, and DIMACS/DRAT proof APIs while excluding the e-graph,
floating-point, Lean-kernel, SMT-LIB, and string crates. The default `full`
profile preserves the complete existing API.

## Bit-vector width conventions

Binary bit-vector operators require identical widths. A mismatch such as
`BitVec(16)` plus `BitVec(64)` returns an `IrError::SortsDiffer` whose display
text names both sorts.

Use `TermArena::coerce_to(term, width)` when a machine-word consumer explicitly
wants unsigned coercion. It zero-extends a narrower value, keeps an equal-width
value unchanged, and truncates a wider value to its low bits:

```rust
use axeyum_ir::{Sort, TermArena};

let mut arena = TermArena::new();
let x16 = arena.bv_var("x", 16)?;
let x64 = arena.coerce_to(x16, 64)?; // ((_ zero_extend 48) x)
let low8 = arena.coerce_to(x16, 8)?; // ((_ extract 7 0) x)
assert_eq!(arena.sort_of(x64), Sort::BitVec(64));
assert_eq!(arena.sort_of(low8), Sort::BitVec(8));
# Ok::<(), axeyum_ir::IrError>(())
```

This helper is deliberately unsigned. Use `sign_ext` directly when widening a
signed machine value; narrowing is always low-bit truncation.

Two builder conventions mirror SMT-LIB exactly:

- `extract(hi, lo, value)` includes both endpoints, so its width is
  `hi - lo + 1`.
- `concat(high, low)` puts the first operand in the high bits and the second in
  the low bits.

Invalid bounds and sorts fail during construction with actionable messages such
as `extract [64:56] out of range for width 64` and
`operands must share a sort: BitVec(16) vs BitVec(64)`.

## Warm incremental solving

Build related terms in one arena, then reuse one solver. The solver retains the
bit-blast, CNF, learned clauses, and phases across checks. It stores stable
`TermId`s but does not borrow the arena; keep using the same arena for the
solver's lifetime.

```rust
use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, IncrementalBvSolver};

let mut arena = TermArena::new();
let x = arena.bv_var("x", 32)?;
let ten = arena.bv_const(32, 10)?;
let twenty = arena.bv_const(32, 20)?;
let below_twenty = arena.bv_ult(x, twenty)?;
let below_ten = arena.bv_ult(x, ten)?;

let mut solver = IncrementalBvSolver::new();
solver.assert_configured(&mut arena, below_twenty)?;
assert!(matches!(solver.check(&arena)?, CheckResult::Sat(_)));

solver.push()?;
solver.assert_configured(&mut arena, below_ten)?;
assert!(matches!(solver.check(&arena)?, CheckResult::Sat(_)));
assert!(solver.pop());
# Ok::<(), Box<dyn std::error::Error>>(())
```

`assert_configured` honors `SolverConfig::preprocess` (enabled by default) and
retains the original term for model replay. Use `assert_preprocessed` to request
that behavior explicitly, or `assert` when measuring the raw, un-preprocessed
path. Narrow extracts are pushed through wide bitwise operations and
bit-vector `ite`s, avoiding AIG construction for discarded register bits.

Use `with_config` to set a timeout. Budget exhaustion is
`CheckResult::Unknown`, never `Unsat` and never an operational error.

## Model access

`Value` is re-exported by `axeyum-solver`, so a solver-only consumer can inspect
models without naming `axeyum-ir` directly:

```rust
use axeyum_solver::Value;

let value = Value::Bv { width: 8, value: 42 };
assert!(matches!(value, Value::Bv { width: 8, value: 42 }));
```

The SMT-LIB helpers have two distinct contracts:

- `solve_smtlib_get_model` is command-faithful and returns a model only when the
  script contains `(get-model)`.
- `solve_smtlib_model` returns the declaration-ordered model of any satisfiable
  single-query script, including scripts that contain only `(get-value ...)` or
  no model-query command.

## Parallel workers

`IncrementalBvSolver: Send` and the pure-Rust path has no shared global solver
context. Give each worker its own arena and solver; no global lock serializes
independent scans:

```rust
use axeyum_solver::IncrementalBvSolver;

let workers: Vec<_> = (0..4)
    .map(|_| std::thread::spawn(IncrementalBvSolver::new))
    .collect();
for worker in workers {
    let _solver = worker.join().expect("worker constructs its solver");
}
```

Native oracle backends may have different threading constraints; the statement
above is specifically about `IncrementalBvSolver` and the pure-Rust QF_BV path.

## Result guarantees

The pure-Rust embedding boundary distinguishes logical outcomes from operational
failures:

- `Sat(model)` has been replayed by evaluating the original assertion against
  the lifted model, including when warm preprocessing lowered a different term.
- Resource or timeout exhaustion is `Unknown` with a classified reason, never
  `Unsat` and never an `Err` masquerading as a logical result.
- `Err` is reserved for construction, parsing, or backend failures and remains
  separate from the benchmark decided count.
- `UnsatProof::recheck()` validates the exported DRAT evidence without invoking
  the search solver.

These contracts are why `Unknown` and operational-error rates must remain
visible even when an integration reports perfect agreement on decided queries.
