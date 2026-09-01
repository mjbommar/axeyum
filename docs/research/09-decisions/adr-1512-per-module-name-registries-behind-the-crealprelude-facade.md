# ADR-1512: per-module name registries behind the `CRealPrelude` facade

Date: 2026-09-01
Status: Accepted
Lane: `creal-split`

Index-summary: `CRealPrelude` becomes a facade over per-module registries, each
owned by the `creal/` module that declares its names, so two lanes working in
different modules stop editing one struct. `ivt_boundary` migrated first: 606
fields to 599, projection byte-identical.

- Supersedes: nothing. Extends the level-1/level-2 build-order work
  (`de853af65`, `b3b449dfc`).
- Context:
  [2026-08-27 architecture review](../11-design-review/2026-08-27-architecture-review.md) §1,
  [2026-09-01 dependency-graph measurement](../11-design-review/2026-09-01-creal-declare-deps-measured.md)

## Context

The architecture review names two halves of one fix. The build-order half is
done: the builder computes its order from the dependency graph rather than
running a hand-written array, so the phase-order failure class is repaired
rather than reported. The other half is untouched:

> Split the god-struct into per-module registries behind a facade, and the
> production-side collision goes away too.

Measured 2026-09-01 on this lane's base:

| signal | 2026-08-27 | 2026-09-01 |
| --- | --- | --- |
| `CRealPrelude` fields | 441 | **606** |
| `creal.rs` lines | 9,284 | **17,050** |
| `STEPS` entries | 135 | **211** |

The struct grew 37% in five days. A lane adding one declaration to
`creal/integral.rs` edits three places in `creal.rs` — the field, the
`intern_names` line, and the `STEPS` entry — plus its own module and its
inventory shard. Two lanes in *different* modules therefore still collide, in
the file with the highest edit rate in the repository. The test-side collision
was removed by sharding `creal_tests.rs` into 33 per-module inventory files;
this is the same fix applied to the production side, which is the half that
still hurts.

The general rule CLAUDE.md already states, arriving in a struct instead of a
document: **per-lane state belongs in per-lane paths, never in one file every
lane writes.**

## Decision

`CRealPrelude` becomes a **facade**. Each `creal/` module that declares names
owns a `Copy` registry struct in its own file, holding those names and knowing
how to intern them:

```rust
// crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IvtBoundaryNames {
    pub uniformly_continuous_max: NameId,
    // … the module's own names, with their documentation
}

impl IvtBoundaryNames {
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self { … }
}
```

and `CRealPrelude` holds one field per module:

```rust
pub struct CRealPrelude {
    pub rat: RatPrelude,
    …
    pub ivt_boundary: IvtBoundaryNames,
}
```

Consequences that follow from the shape, not from taste:

1. **Adding a declaration to a migrated module touches that module only** —
   the field, its documentation, and the interning all live beside the
   `declare_*` that uses them. `creal.rs` changes only when a module is
   *created*.
2. **`STEPS` accessors become `|p| p.ivt_boundary.ivt_plateau`.** The table
   stays in `creal.rs` for now; splitting it is a separate decision, and the
   review does not ask for it.
3. **The registry is `Copy` and by-value**, exactly like `CRealPrelude`, so no
   call site changes shape — only its path lengthens by one segment.
4. **Visibility.** `mod creal` is private at the crate root and
   `CRealPrelude` is re-exported from it. A `pub` field needs a publicly
   nameable type, so each registry is re-exported the same way
   (`pub use ivt_boundary::IvtBoundaryNames;` in `creal.rs`, then from
   `lib.rs`). Anything else trips `private_interfaces`.

### Migration order, measured rather than chosen

A module can move only if nothing outside it reads its names — otherwise the
move is a cross-module rename with no local benefit.
`scripts/creal-declare-deps.py` answers that from the graph. **Fifteen modules
are fully self-contained today, 76 fields between them:**

| module | fields | code sites | files |
| --- | --- | --- | --- |
| `sqrt` | 17 | 187 | 8 |
| `pi` | 14 | 582 | 63 |
| `polynomial` | 10 | 150 | 11 |
| `crossing` | 9 | 48 | 4 |
| `ivt_boundary` | 7 | 30 | 4 |
| `cos_sign` | 6 | 30 | 4 |
| `completeness` | 5 | 22 | 3 |
| `exp_fn`, `lub_boundary` | 4 each | 17, 22 | 3–4 |
| `extreme_value` | 3 | 17 | 4 |
| `inverse_fn`, `ratio_test` | 2 each | 7, 8 | 3–4 |
| `deriv_unique`, `evt_row1`, `mvt` | 1 each | — | — |

The other end of the distribution is where the value is and where the cost is:
`creal` itself owns 46 fields read by 45 other modules, `uniform_continuity`
29 read by 21, `lattice` 23 by 19. Those are genuinely shared vocabulary and
should move last, or stay.

`ivt_boundary` is migrated first: seven fields, 30 code sites, four files —
large enough that the mechanism is exercised (multi-field registry, interning
split, `STEPS` accessors, inventory shard, intra-doc links) and small enough
that the result is reviewable in one commit.

## Alternatives considered

- **Accessor methods on `CRealPrelude`** (`p.ivt_plateau()` delegating to the
  registry). Keeps every call site's spelling, but leaves 606 accessors in
  `creal.rs` — the collision is the *file*, not the syntax, so this buys
  nothing.
- **One registry per `STEPS` entry** rather than per module. 211 registries
  against 33, and it re-creates the collision one level down whenever a module
  has several steps (`integral` has 46).
- **A `HashMap<&str, NameId>`.** Loses the compile-time check that a field
  exists, which is the property that makes `STEPS`'s accessors a rename-safe
  table rather than a stale string list. Rejected on the same grounds the
  `BuildStep` design already records.
- **Do nothing until the whole split can land at once.** The review's own
  sequencing constraint asks for an empty board; the board is empty now and
  will not stay empty. A migration that can proceed one self-contained module
  at a time does not need one.

## Consequences

- The 15 self-contained modules can migrate independently, in any order, by
  different lanes, with no shared edit point between them.
- `creal.rs`'s field count falls by exactly the migrated module's count each
  time — a running metric, not a promise.
- **Every migration must show the projection is byte-identical.**
  `target/release/examples/kernel_declaration_projection` is the instrument;
  nothing about this changes a kernel name, a type, or an axiom footprint, so
  any difference at all is a defect.
- The shared vocabulary (`creal`, `uniform_continuity`, `lattice`, …) is not
  addressed here and may never be worth moving. This ADR does not claim the
  god-struct disappears; it claims the *growth* stops being concentrated in
  one file.

## First migration, landed and measured

`ivt_boundary` moved. `IvtBoundaryNames` lives in `creal/ivt_boundary.rs`,
re-exported through `creal.rs` and `lib.rs` so the `pub` field has a publicly
nameable type.

| | before | after |
| --- | --- | --- |
| `CRealPrelude` `NameId` fields | 606 | **599** |
| `creal.rs` lines | 17,243 | **17,171** (−72) |
| `creal/ivt_boundary.rs` lines | 1,012 | **1,138** (+126) |
| projection SHA-256 | `576296bf…1ecd0c87` | **unchanged** |

Line count is not the metric and the totals say so: the crate gained 54 lines
overall, because a registry costs a struct and an `intern`. What changed is
*where the edits land* — a lane adding an `ivt_boundary` declaration now
touches `creal/ivt_boundary.rs` and its inventory shard, and `creal.rs` not at
all.

Churn: 30 code sites, 10 intra-doc links, 7 files
(`creal.rs`, `creal/ivt_boundary.rs`, `creal/lub_boundary.rs`,
`creal/creal_tests.rs`, `creal/inventory/ivt_boundary.rs`, `lib.rs`,
`examples/ivt_evt_vacuity_probe.rs`). `cargo doc` reports no new unresolved
link; the crate's 24 pre-existing rustdoc errors (`nat_prelude.rs`,
`ipc_heyting.rs`, `ipc_provable.rs`) are untouched by this and were red
before it.

**`scripts/creal-declare-deps.py` follows the facade.** It had to: a scan
stopping at `p.<one segment>` reads every migrated name as required-by-many
and provided-by-none, which is a clean report and a false one. Migrated
fields keep the composite id `ivt_boundary.ivt_plateau`, the run prints
`registries=1|fields_in_registries=7`, and a new finding —
*every field the struct declares is provided by exactly one step*, derived
from `CRealPrelude` rather than a list — fails `--strict` if that ever stops
being true. Mutation-verified: deleting the registry branch of `resolve`
takes that finding from 0 to 2 and `--strict` to exit 2.
