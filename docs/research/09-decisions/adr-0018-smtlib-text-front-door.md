# ADR-0018: SMT-LIB Text Front Door in the Solver Crate

Status: accepted
Date: 2026-06-13

## Context

The library now has two complete programmatic front doors:
`axeyum_solver::solve` decides any supported query (quantifier-free or
quantified, any theory combination) given a `TermArena` and a slice of
assertion `TermId`s. But the **real-world entry point** for an SMT consumer is
not an arena — it is an SMT-LIB 2 script as *text* (a file, a string from
another tool, an editor buffer). The pieces to close that gap already exist and
are exercised, but only inside test helpers:

- `axeyum-smtlib` parses a script into `Script { arena, assertions, logic,
  status, check_sats }`, covering the full supported fragment (n-ary
  `declare-fun`, `define-fun`, `let`, `forall`/`exists` — ADR-0013, ADR-0016).
- `axeyum_solver::solve` decides `(arena, assertions)`.

Composing them is a one-liner, but until now there was no public function that
does it, and no integration test asserting the **whole path** — text in, a
checked `sat`/`unsat`/`unknown` out, cross-checked against the benchmark's own
declared `(set-info :status ...)`. Without that, "feed it an SMT-LIB file"
remained an unproven claim rather than tested API.

## Decision

Add a text front door, `axeyum_solver::solve_smtlib`, that parses an SMT-LIB
script and decides it with `solve`, returning the decision alongside the
script's declared logic and expected status:

```rust
pub struct SmtLibOutcome {
    pub result: CheckResult,
    pub logic: Option<String>,
    pub expected_status: Option<String>, // "sat" | "unsat" | "unknown", if declared
}

pub fn solve_smtlib(input: &str, config: &SolverConfig)
    -> Result<SmtLibOutcome, SolverError>;
```

- This promotes `axeyum-smtlib` from a **dev-dependency to a production
  dependency** of `axeyum-solver`. The edge is acyclic (`axeyum-smtlib` depends
  only on `axeyum-ir`) and pure Rust, so the no-native-dep Hard Rule and the
  wasm target (ADR-0017) are preserved — `axeyum-smtlib` already builds for
  `wasm32`.
- `axeyum-solver` is the correct home: it is the top of the library stack and
  already the single decision front door. A text front door belongs next to the
  programmatic one, not in a new crate (ADR-0001: no crate without a proven
  boundary) and not in the `axeyum-bench` binary (which is a native-only CLI
  harness, not a reusable library API).
- Parse failures surface as a new `SolverError::Parse(String)` variant, keeping
  the front door's error type uniform (one `Result<_, SolverError>` for the
  whole text-to-answer path) rather than leaking `SmtError`.
- The returned `expected_status` is **not** consulted when solving — it is
  passed through so a caller (a benchmark harness, a differential test) can
  cross-check the decision against the script's own ground truth. The trust
  anchor remains model replay inside `solve`, unchanged.

## Evidence

- Integration tests (`crates/axeyum-solver/tests/smtlib.rs`) drive real SMT-LIB
  2 text end to end: a `QF_BV` `sat` script (model replayed against the parsed
  term), a `QF_BV` `unsat` script, and a quantified script — each asserting the
  decision matches the declared `:status`.
- `cargo build --target wasm32-unknown-unknown -p axeyum-solver` still succeeds
  with `axeyum-smtlib` as a production dependency.

## Alternatives

- **Leave it as a test-only composition.** Keeps the dependency graph slightly
  smaller, but the most common real use case (solve this SMT-LIB file) stays
  unsupported API and untested as a whole. Rejected.
- **A new `axeyum-frontend`/`axeyum-cli` crate.** Premature (ADR-0001); the
  function is a thin composition with no boundary of its own yet.
- **Return `SmtError` or a `Box<dyn Error>` from `solve_smtlib`.** A single
  `SolverError` with a `Parse` variant gives callers one error type for the
  whole path and matches the rest of the solver API.

## Consequences

- `axeyum-solver` now depends on `axeyum-smtlib` in normal builds; the
  foundational dependency DAG is updated to record this edge.
- `SolverError` gains a `Parse(String)` variant (a public, additive API change).
- The library can be handed raw SMT-LIB text and return a checked answer — the
  end-to-end use case is now both supported and regression-tested.
