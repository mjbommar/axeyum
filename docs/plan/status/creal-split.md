# Lane: creal-split — split `creal.rs`'s four fused concerns

<!-- plan-section: lane-status -->

**All three slices landed** (`WIP`, creal-split, 2026-09-01). The refactor
named in
[2026-08-27-architecture-review.md](../../research/11-design-review/2026-08-27-architecture-review.md)
§1: `crates/axeyum-lean-kernel/src/creal.rs` fuses the name registry, the
`CRealPrelude` field struct, the build ORDER, and dispatch.

Starting state on base commit `5c8eaf7b8` (the review's 2026-08-27 numbers in
parentheses): `creal.rs` **17,050** lines (9,284), `CRealPrelude` **606**
fields (441), `STEPS` **211** entries (135 at the level-1 landing).

**A — measured the real dependency graph.** `scripts/creal-declare-deps.py`
re-derives it from the source (1,916 functions across `creal.rs` and 49
modules) and checks it against the hand-maintained `STEPS` table.
Headline: the hand-written order really is topologically valid (0 violations,
independently confirmed), and every one of the 606 fields is provided by
exactly one step — but the table is missing **977 of the 4,831** measured
`requires` edges, and two `provides` entries named declarations their step
does not make, leaving a 48-step window where the preflight was silently
disarmed for `CReal.sharedIndexToCanonical`. Five defects in the analysis
produced clean, plausible, entirely false reports before the numbers meant
anything; they are tabulated in the note, and the script now carries controls
for each.

**B — the builder sorts.** `plan_step_order` computes the order (Kahn, array
index as tie-break) instead of validating a hand-written one. The tie-break
makes the plan the array order whenever the array order is valid, so the
kernel sees the identical call sequence. Order-inversion demonstration, with
`declare_projections`/`declare_carrier` swapped: level 1 refuses the build
(exit 101, naming the missing `CReal` and its provider); level 2 produces a
projection byte-identical to the unpermuted run. The two false `provides` are
deleted and a duplicate provider is now rejected outright.

**C — the god-struct split, one module.**
[ADR-1512](../../research/09-decisions/adr-1512-per-module-name-registries-behind-the-crealprelude-facade.md)
designs the facade and derives the migration order from the graph: **15
modules are fully self-contained** (76 fields), and they can migrate
independently in any order. `ivt_boundary` moved — `IvtBoundaryNames` lives in
`creal/ivt_boundary.rs`, `CRealPrelude` 606 → 599 fields, `creal.rs`
17,243 → 17,171 lines. The analyzer follows the facade (composite field ids,
`registries=1|fields_in_registries=7`) because a scan that stops at
`p.<one segment>` reads every migrated name as provided-by-none.

**The invariant, checked after every slice.**
`target/release/examples/kernel_declaration_projection` is **byte-identical**
across all three: SHA-256
`576296bf531513e04749c77fb2162f374e3006cb837355ee0f06c7721ecd0c87`, 14,673
rows, before and after. `creal` construction (release,
`AXEYUM_PRELUDE_CACHE=0`, three iterations) 20.196 / 20.272 / 20.215 s before
against 20.110 / 20.494 / 20.135 s after — no regression.

**Next, for whoever picks this up.** The 14 remaining self-contained modules
migrate the same way, one commit each, `sqrt` (17 fields) being the largest.
The 977 unnamed `requires` edges are the real remaining exposure: the planner
can only use the edges the table names, so the fix is to GENERATE
`requires`/`provides` rather than maintain them, which is what
`scripts/creal-declare-deps.py` already computes. Re-apply after any merge
touching `creal` with `python3 scripts/creal-declare-deps.py --self-check
--strict` (exit 2 today, by design — 175 steps' tables still disagree with
the code).

**Not this lane's, but observed:** `cargo doc -p axeyum-lean-kernel --no-deps`
with `RUSTDOCFLAGS=-D warnings` has **24 pre-existing unresolved-link errors**
in `nat_prelude.rs`, `ipc_heyting.rs` and `ipc_provable.rs`. None are in files
this lane touched, and they were red before it.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `c56868c75` | Lane opened; status stub and starting measurements recorded. |
| 2026-09-01 | `208104bd5` | Slice A: `scripts/creal-declare-deps.py` re-derives `creal.rs`'s dependency graph from source and checks the `STEPS` table against it. 0 order violations, but 977 of 4,831 `requires` edges unnamed and two false `provides` disarming the preflight over a 48-step window. `--self-check` permutes a step before its provider and requires the scan to fire; `--strict` exits 2 on a table/code disagreement. |
| 2026-09-01 | `b3b449dfc` | Slice B: `plan_step_order` computes the build order (Kahn, array-index tie-break) instead of validating a hand-written one; the two false `provides` deleted; duplicate providers rejected. Projection byte-identical (same SHA-256, 14,673 rows); build time unchanged. Inversion demo: level 1 exit 101, level 2 exit 0 with identical output. Six new tests, each a distinct failure mode. clippy `--all-targets -D warnings` exit 0. |
| 2026-09-01 | `3096c587c` | Slice C: ADR-1512 (per-module registries behind the `CRealPrelude` facade) plus the first migration, `ivt_boundary`. 606 → 599 fields; 15 self-contained modules identified as the migratable population. Analyzer extended to follow the facade, with a mutation-verified guard (every struct field provided by exactly one step). Projection byte-identical. clippy exit 0. |
