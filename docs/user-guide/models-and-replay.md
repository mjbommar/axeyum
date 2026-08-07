# Models and Replay

A `sat` result means there is an interpretation of the declared symbols that
makes every active assertion true. That interpretation is the **model**.

Axeyum does not expose a candidate model as `sat` merely because an internal
search procedure produced it. Supported solving routes lift backend values back
to Axeyum values and check the applicable original assertions first. If replay
cannot establish that the candidate works, the result is not credited as
`sat`.

## Read a named SMT-LIB model

Use `solve_smtlib_get_model` when command fidelity matters: it returns a model
only if the script contains `(get-model)` and the query is satisfiable.
`solve_smtlib_model` is the embedding convenience form; it returns the named
model for any satisfiable single-query script, even without `(get-model)`.

```rust
use std::time::Duration;
use axeyum_solver::{SolverConfig, solve_smtlib_model};

let input = r#"
    (set-logic QF_BV)
    (declare-const x (_ BitVec 8))
    (assert (= (bvadd x #x01) #x00))
    (check-sat)
"#;

let config = SolverConfig::new().with_timeout(Duration::from_secs(5));
let model = solve_smtlib_model(input, &config)?
    .expect("this known-sat example has a model");

for (name, value) in model.constants {
    println!("{name} = {value}");
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

The complete runnable version is
[`first_smtlib_query.rs`](../../crates/axeyum-solver/examples/first_smtlib_query.rs):

```sh
cargo run -p axeyum-solver --features full --example first_smtlib_query
```

Named constants and uninterpreted functions are returned in declaration order.
Values are typed `axeyum_ir::Value` objects rather than strings pretending to be
canonical SMT-LIB output.

## Preserve the three-way result

The named-model helpers return `None` for both `unsat` and `unknown`. If your
integration must distinguish all outcomes—and most integrations should—inspect
`solve_smtlib(...).result`:

```rust
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

# let input = "(set-logic QF_BV) (assert true) (check-sat)";
match solve_smtlib(input, &SolverConfig::default())?.result {
    CheckResult::Sat(model) => println!("sat: {model:?}"),
    CheckResult::Unsat => println!("unsat"),
    CheckResult::Unknown(reason) => println!("unknown: {reason:?}"),
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

Do not use “no model returned” as a synonym for `unsat`. A timeout, resource
limit, incomplete procedure, or unsupported bounded route can all produce an
honest `unknown`.

## Typed Rust models

The typed solver API stores ground assignments in `Model`, keyed by stable
`SymbolId`s rather than names or backend handles. The important methods are:

| Method | Purpose |
|---|---|
| `model.get(symbol)` | read one ground value |
| `model.iter()` | iterate ground values in deterministic symbol order |
| `model.function(func)` | inspect one uninterpreted-function interpretation |
| `model.functions()` | iterate function interpretations deterministically |
| `model.to_assignment()` | obtain the assignment used by the ground evaluator |

Keep the `TermArena` that created the symbols: it defines their sorts and names.
Do not join models to terms by display strings.

## What replay checks

For a ground Bool/BV query, replay evaluates each original asserted term under
the lifted assignment and requires Boolean `true`. This catches bugs in SAT
model extraction, bit ordering, term-to-circuit maps, preprocessing lift maps,
and backend-to-IR conversion.

More expressive fragments need more than a flat ground assignment. Models may
also carry:

- finite interpretations for uninterpreted functions;
- array defaults and overrides;
- model-chosen values for underspecified real division by zero;
- finite carrier sizes for uninterpreted sorts;
- checked certificates for supported quantified models or witnesses.

For quantified results in the `full` profile, the canonical `check_model`
entry point validates the additional certificate rather than pretending that
ground evaluator replay alone proves a universal claim.

## What replay does not prove

Model replay establishes a concrete positive fact: this returned interpretation
satisfies the parsed assertions under Axeyum's IR semantics. It does not by
itself establish:

- that an informal requirement was encoded correctly;
- that every SMT-LIB command or operator is supported;
- that a bounded model represents an unbounded system;
- that an `unsat` result is correct (that requires refutation evidence);
- that parsing or the ground evaluator contains no defect.

For source-level assurance, keep the specification-to-formula step in review and
pair replay with independent or differential checks appropriate to the risk.

## Model completion and determinism

Backends may omit unconstrained values because any value would work. Axeyum's
model boundary completes supported declarations with deterministic,
well-founded defaults where required. This makes model iteration and artifacts
reproducible without claiming that the completed value was uniquely implied by
the formula.

Stable ordering is part of the API promise. It is safe to serialize a model in
iteration order; do not reorder it through an unordered map if byte-for-byte
reproducibility matters.

## Fail-closed behavior

Replay failure is never converted to `Unsat`. Depending on the route and cause,
Axeyum returns a classified `Unknown` or an operational `SolverError`. Preserve
that distinction in logs, metrics, and control flow.

Next, read [UNSAT evidence](unsat-evidence.md) for the opposite result's trust
boundary and [limitations](limitations.md) for fragment-specific coverage.
