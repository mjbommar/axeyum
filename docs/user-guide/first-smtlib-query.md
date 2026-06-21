# Your First SMT-LIB Query

Three ways to run a query, from least to most setup. They all solve the same
tiny bit-vector problem: *is there an 8-bit `x` with `x + 1 = 0`?*

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-model)
```

Expected: **`sat`**, with `x = #xff` (255 + 1 wraps to 0 in 8 bits).

## 1. In your browser (no install)

Open the [WASM playground](../playground/README.md), paste the query, press
**Solve**. Axeyum runs *client-side* (compiled to WebAssembly) — there is no
server and nothing to install. Best for a first look.

## 2. From Rust (the embedded library)

Axeyum is a library first. `solve_smtlib` parses a script and decides the
conjunction of its assertions:

```rust
use std::time::Duration;
use axeyum_solver::{solve_smtlib, CheckResult, SolverConfig};

fn main() {
    let query = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x00))
        (check-sat)
    "#;

    let config = SolverConfig::new().with_timeout(Duration::from_secs(5));
    let outcome = solve_smtlib(query, &config).expect("parse + solve");

    match outcome.result {
        CheckResult::Sat(model) => {
            println!("sat — model: {model:?}"); // already replay-verified
        }
        CheckResult::Unsat => println!("unsat"),
        CheckResult::Unknown(reason) => println!("unknown: {reason:?}"),
    }
}
```

`solve_smtlib(input, config) -> Result<SmtLibOutcome, SolverError>`, where
[`SmtLibOutcome`](../reference/public-api.md) carries the `result`, the declared
`logic`, and any `(set-info :status …)` (used only for cross-checking, never to
decide). The returned `Sat(model)` has **already** been replayed against the
original assertions — see [models & replay](models-and-replay.md).

> The contradictory variant — assert `x = #x00` *and* `x = #x01` — returns
> `Unsat`. With the proof-producing core enabled it also emits a DRAT proof you
> can independently re-check; see [unsat evidence](unsat-evidence.md).

## 3. A whole corpus (the benchmark harness)

To run many queries with budgets, replay checks, and JSON artifacts, use
`axeyum-bench`. The committed micro corpus is a good smoke test:

```sh
cargo run --release -p axeyum-bench -- corpus/micro --backend sat-bv --timeout-ms 1000
```

For the measured Z3 head-to-head and the full recipe list, see
[Benchmarks](benchmarks.md).

## What you just relied on

A returned `sat` is trustworthy because the model was **evaluated against your
original query** before you saw it (the [trust boundary](../learn/07-how-axeyum-solves-a-query.md)).
If Axeyum can't decide a query within its budget, it returns a first-class
[`unknown`](../learn/05-models-unsat-and-unknown.md) — check for it explicitly.
