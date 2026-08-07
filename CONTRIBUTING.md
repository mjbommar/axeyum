# Contributing

## Ground Rules

- Read [PLAN.md](PLAN.md) first; it carries current status and next actions.
- Architectural choices are made through decision records in
  [docs/research/09-decisions/](docs/research/09-decisions/README.md), not as
  silent code choices. If a change closes or contradicts an open question in
  [research-questions.md](docs/research/08-planning/research-questions.md),
  write or amend an ADR.
- New research notes start from
  [templates/research-note.md](docs/research/templates/research-note.md).

## Checks

Use the focused edit loop and pre-merge sequence in
[Testing and validation](docs/contributor-guide/testing-and-validation.md).
The repository-wide gates are:

```sh
just check       # all repository gates except cargo-deny
just deny        # dependency/license/advisory policy
```

While editing, prefer `cargo test -p <crate>` or `just check-scope origin/main`
instead of repeatedly running the whole workspace. Solver/dispatch changes also
need the serialized, nonzero `progress_frontier` gate documented in the guide.

MSRV is **1.88** and covers the default, pure Rust
build; CI runs `cargo check` on it. Optional native-oracle features (`z3`,
`z3-static`) track stable Rust instead.

## Code Conventions

- Arena- and ID-oriented: `u32` newtype IDs, `Vec` arenas, no `Rc`/`Box`
  term trees in hot paths
  (see [implementation principles](docs/research/06-rust-strategy/implementation-principles.md)).
- `unsafe_code` is denied workspace-wide; a future exception requires a
  narrow module, justification, and an ADR.
- `unknown` is a first-class solver result, never an error.
- Determinism is a public promise: no hash-map iteration order in output, no
  hidden randomness; seeds and resource limits are explicit.
- Every transformation layer ships with its check (evaluator equivalence,
  round trips, lift maps) and a differential test once an oracle exists.
- The default build must stay free of C/C++ dependencies; native backends are
  feature-gated.

## Commits

- Conventional prefixes: `feat:`, `fix:`, `docs:`, `chore:`, `test:`,
  `bench:`, `refactor:`.
- One logical change per commit; docs updates that motivated a code change
  belong with it.
