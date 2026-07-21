# ADR-0314: Make the cold bit-lowering mode a typed choice

Status: accepted
Date: 2026-07-20

## Context

The artifact-readiness review identifies one concrete invalid state in
`SolverConfig`. Two public fields select mutually exclusive cold bit-lowering
experiments:

- `demand_bit_slicing: bool`; and
- `range_demand_slicing: Option<RangeDemandPolicy>`.

They admit four combinations. Eager, dense demand-sliced, and range-sliced
lowering are valid; enabling both experiments is not. The field documentation
calls the fourth combination a configuration error, `SatBvBackend` rejects it
at runtime, and the benchmark CLI independently duplicates the same rejection.
This is policy encoded as loosely coupled storage rather than as a type.

The rest of the configuration census does not justify a broad redesign. Budgets
are independent limits. Assurance, preprocessing, profiling, incremental,
fallback, and primary-search controls are independently selectable opt-ins.
`cnf_vivify` without inprocessing and ITE abstraction without lazy BV are
documented harmless no-ops rather than rejected states. They may deserve later
ergonomic grouping, but they are not the explicit invalid-state bug addressed
here.

The compatibility census is bounded:

- Glaurung constructs `SolverConfig` through `new()` plus timeout/resource
  builders and does not name either lowering field;
- Axeyum tests use the two existing fluent selectors;
- only `axeyum-bench` directly initializes both fields; and
- benchmark CLI flags, artifact JSON, and configuration hashing deliberately
  expose the two historical identities and must remain stable for old/new
  artifact comparison.

## Proposed decision

**Replace the two `SolverConfig` fields with one public `BitLoweringMode` enum.**

```rust
pub enum BitLoweringMode {
    Eager,
    DemandSliced,
    RangeSliced(RangeDemandPolicy),
}
```

`Eager` is the default. `SatBvBackend` exhaustively matches the enum before the
existing observational-demand profile fallback. No mode changes its lowering
algorithm, replay contract, telemetry, or default.

`SolverConfig::with_bit_lowering_mode` is the direct typed selector. The
existing `with_demand_bit_slicing(bool)` and
`with_range_demand_slicing(policy)` builders remain as source-compatible
conveniences for callers that do not name fields; each selects one enum variant,
so chained selectors have ordinary last-call-wins builder semantics and can
never construct the old invalid state. Read-only compatibility helpers report
whether dense demand or range demand is selected.

`axeyum-bench` retains both CLI booleans and rejects their simultaneous use at
argument validation. After validation it maps exactly one selection into the
enum. Artifact JSON keys, policy payload, and configuration-hash byte sequence
stay unchanged so this API cleanup does not rewrite historical benchmark
identity.

## Acceptance gate

- Unit tests prove the default and all builder transitions select exactly one
  mode, including last-call-wins replacement of one experimental mode by the
  other.
- Existing dense-demand and range-demand SAT/UNSAT, telemetry, fallback,
  deadline, and replay tests remain green.
- The former runtime-invalid-state test becomes a construction test showing
  the state is unrepresentable.
- `axeyum-bench` CLI tests still reject both flags and preserve the existing
  configuration JSON/hash fixtures.
- Glaurung's current minimal `qfbv` construction sites compile unchanged.
- Full/minimal solver tests, workspace consumers, strict Clippy, and strict
  rustdoc pass under the bounded one-job configuration.

## Alternatives

- **Keep both fields and validate earlier.** Rejected: validation changes where
  the invalid state fails but leaves it representable to every public caller.
- **Add the enum while retaining legacy fields.** Rejected: precedence between
  three selectors creates more invalid states and defeats the type boundary.
- **Make all `SolverConfig` fields private.** Rejected for this increment: it
  would break every external struct-update literal and expand a two-field fix
  into a wholesale builder-only API migration.
- **Group every dependent-looking boolean now.** Rejected: the review found one
  explicit configuration error. Harmless no-op dependencies need separate
  consumer and behavior decisions rather than a name-based sweep.

## Consequences

- Simultaneous dense and range-demand lowering becomes unrepresentable.
- Callers that directly name either removed public field must migrate to the
  enum or retained fluent selectors. This is an intentional pre-1.0 source
  break recorded here; Glaurung is unaffected by the census.
- Benchmark artifacts preserve their historical external schema and identity.
- Default eager behavior and both deferred experimental implementations remain
  unchanged.

## Acceptance evidence

- The complete all-feature solver library remains 891/891 green, and the
  all-feature SAT/BV integration file is 34/34 green.
- The complete all-feature benchmark suite is green: 47 harness tests, 12
  ordered-trace tests, and three process/export integration tests. Its focused
  configuration test covers eager, dense-demand, range-demand, and the retained
  dual-flag CLI rejection.
- Full and minimal `qfbv` namespace compatibility tests pass. Warning-denied
  all-target Clippy for `axeyum-solver` plus `axeyum-bench` and warning-denied
  rustdoc for both solver profiles pass under the bounded one-job profile.
- The actual Glaurung production consumer compiles with
  `--no-default-features --features solver-axeyum` against the minimal `qfbv`
  path dependency without source changes.
- The benchmark artifact JSON fields and configuration-hash byte sequence were
  left byte-for-byte unchanged; only their validated internal mapping now
  selects the enum.
