# Lane: creal-split — split `creal.rs`'s four fused concerns

<!-- plan-section: lane-status -->

**Started** (`WIP`, creal-split, 2026-09-01). Working the refactor named in
[2026-08-27-architecture-review.md](../../research/11-design-review/2026-08-27-architecture-review.md)
§1: `crates/axeyum-lean-kernel/src/creal.rs` fuses the name registry, the
`CRealPrelude` field struct, the build ORDER, and dispatch.

Starting state, measured on this lane's base commit `5c8eaf7b8` (the review's
2026-08-27 numbers in parentheses):

- `creal.rs`: **17,050** lines (9,284)
- `CRealPrelude`: **607** fields (441)
- `STEPS` build-order table: **211** entries (135 at the level-1 landing)

The level-1 fix already landed (lane `creal-steps`, `de853af65`): each
`BuildStep` names `requires`/`provides` as function pointers, and
`validate_step_order` checks the *hand-written* order is a valid topological
order. What has NOT happened is the review's actual recommendation — the
builder does not *sort*; it validates a linearization a human still maintains.
This lane's slices:

- **A** — measure the real dependency graph from the source and check the
  hand-written `requires`/`provides` table against it.
- **B** — make the build order *computed* (topological sort, stable tie-break
  by source order) rather than hand-maintained.
- **C** — per-module registries behind a facade (ADR-1512), one module moved.

Invariant instrument: `target/release/examples/kernel_declaration_projection`,
captured before any change. Before-snapshot SHA-256 recorded below once the
release build completes (`did not run` until then).

<!-- plan-section: landed-changes -->

| 2026-09-01 | `pending` | Lane opened; status stub and starting measurements recorded. |
