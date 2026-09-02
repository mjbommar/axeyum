# Lane: creal-split-2 — generate the `STEPS` table, migrate the self-contained modules

<!-- plan-section: lane-status -->

**Both slices landed** (`WIP`, creal-split-2, 2026-09-01). Continues
[creal-split](creal-split.md) and
[ADR-1512](../../research/09-decisions/adr-1512-per-module-name-registries-behind-the-crealprelude-facade.md);
the decisions are in
[ADR-1530](../../research/09-decisions/adr-1530-the-creal-build-table-is-generated-not-maintained.md).

**D — the build table is generated, not maintained.** `creal.rs`'s
hand-written `requires`/`provides` named **3,934 of the 4,831** `requires`
edges the code has: 977 missing across 175 of the 211 steps, so a planner that
can only constrain the edges it is told about was blind on most of its subject.
`creal.rs` now keeps only `STEP_DISPATCH` — the order and the dispatch, one
line per step — and `scripts/creal-declare-deps.py` generates
`crates/axeyum-lean-kernel/src/creal/steps_generated.rs`, the `STEPS` table the
prelude builds against.

**Why a generated Rust file rather than the planner reading the JSON artifact
at build time.** It keeps the trusted surface unchanged. The entries stay
`fn(CRealPrelude) -> NameId` accessors, so a renamed field is still a compile
error — the property the `BuildStep` design was chosen for over a
`HashMap<&str, NameId>` — `BuildStep` is untouched, and `plan_step_order` runs
on exactly the data it ran on before. Reading JSON would put a file read, a
parser and a new failure mode on the prelude build path, and make the build
depend on an artifact nothing type-checks.

**The unlisted-edge inversion, both outcomes.**
`integral::declare_riemann_sum_shared_accuracy_close_at` reads
`CReal.sharedIndexToCanonical`, declared two steps earlier by
`integral::declare_shared_index_to_canonical`; the hand-written table omitted
that edge. Lifting the consumer above its provider gives **0** violations
against `declared_requires` at `a503a9241` and **1** against
`measured_requires`, naming `CReal.sharedIndexToCanonical`. Pinned by
`creal_tests::an_edge_the_hand_written_table_never_named_is_now_enforced`,
which MOVES the consumer rather than swapping the pair — a swap also displaces
the sibling `..._close`, whose edge the old table *did* name, so it fires for a
reason unrelated to the omitted edge. That swap version was written first and
its failure named the sibling. Mutation-verified: deleting the one accessor
line from the generated table kills exactly this test.

**The build asserts the two halves agree.** `STEPS` and `STEP_DISPATCH` are the
same list written twice, so `build_creal_prelude_uncached` checks them
entry-for-entry (label and `run` pointer) before planning. `--check` catches a
stale file too, but that is a gate somebody has to run.

**Gates.** `--check --strict --self-check` (~1.1 s, pure Python) in
`scripts/check.sh`, the `justfile`, and `scripts/check-merge-hygiene.sh` — the
last because `creal.rs` has the highest edit rate in the repository, so its
generated table is the file most likely to be merged stale. New control
`test_stale_creal_steps_table_fails_the_gate`, mutation M7, measured to kill
exactly one test. **Not** an L0 gate; that needs `ci.yml`, `hooks/pre-push`,
`local-ci.sh` and `check-l0-gate-enforcement.py` together, and is the obvious
next step.

**E — 13 modules into per-module registries, 62 fields.** `pi` 14,
`polynomial` 10, `crossing` 9, `cos_sign` 6, `completeness` 5, `lub_boundary` 4,
`exp_fn` 4, `extreme_value` 3, `inverse_fn` 2, `ratio_test` 2, `deriv_unique` 1,
`mvt` 1, `evt_row1` 1. The migration is
`scripts/creal-migrate-registry.py`, promoted from a throwaway because the
remaining work is the same mechanism; it reads its field list from the
dependency graph, and `--list` answers "which module can move" from the tree.

**ADR-1512's migration table was wrong about `sqrt`, and that is the whole
difference between its 15 modules / 76 fields and this lane's 13 / 62.** That
table scanned `creal.rs` plus `creal/*.rs` and nothing else, so it could not
see `src/complex.rs` reading `creal.sqrt`, `creal.sqrt_approx`,
`creal.mul_self_sqrt`, `creal.le_of_sq_le`, `creal.nat_sqrt` and
`creal.sqrt_congr` at 19 sites. Moving `sqrt` — its largest entry, 17 fields —
is the cross-module rename ADR-1512's own criterion excludes. ADR-1512 now
carries a correction pointer. The new scan states its own limit in the other
direction too: it matches by NAME, not by receiver TYPE, so
`RatPrelude::poly_eval` reads as an external use of `CRealPrelude::poly_eval` —
a module it calls blocked may still be movable; a module it calls movable
really is.

**Counts, one method for before and after** (`pub <x>: <T>,` inside
`pub struct CRealPrelude`):

| | `a503a9241` | slice D | slice E |
| --- | --- | --- | --- |
| `creal.rs` lines | 17,172 | 12,004 | **11,439** |
| `NameId` fields | 599 | 599 | **537** |
| module registries | 1 | 1 | **14** |
| struct fields, all kinds | 601 | 601 | **552** |
| `creal/steps_generated.rs` lines | — | 6,843 | 6,843 |
| `--strict` exit | 2 | **0** | **0** |

**The invariant held at every step.**
`target/release/examples/kernel_declaration_projection` is byte-identical —
SHA-256 `576296bf531513e04749c77fb2162f374e3006cb837355ee0f06c7721ecd0c87`,
14,673 rows — on the base commit and after each slice. `creal::` suite 216
passed / 0 failed (release, `--test-threads=4`, 113 s). `cargo doc` back to the
crate's 24 pre-existing errors, none in a file this lane touched. clippy
`-p axeyum-lean-kernel --all-targets -D warnings` exit 0; `cargo fmt --check`
exit 0.

**A timing regression I nearly reported as fact.** `prelude_build_timing 3`
(release, `AXEYUM_PRELUDE_CACHE=0`) read **22.93 / 23.00 / 22.96 s** after
slice E against 20.34 s after slice D — a 13% regression with no mechanism I
could name, since a registry field is a compile-time offset. Interleaving the
two builds back to back in the same warm target dir instead:

| | run 1 | run 2 | run 3 |
| --- | --- | --- | --- |
| slice D | 20.328 | 20.306 | 20.296 |
| slice E | 20.334 | 20.348 | 20.254 |

Identical within noise. The 22.9 s window had another lane's `python3` at
99.9% CPU. This is `frontier-ratchet-reference-frame.md`'s hazard in a
different gate: **a before/after separated by an hour on a shared box measures
the box.** Interleave, or do not compare.

**Next.** The remaining `creal/` modules are not local moves — `--list` reports
32 blocked, led by `integral` (61 fields), `supremum` (36) and `trig_fn` (33) —
and the shared vocabulary (`lattice` 23 fields read by 27 modules,
`uniform_continuity` 29 by 17) should move last or not at all, exactly as
ADR-1512 says. The cheap next increments are wiring `creal-declare-deps.py`
into L0, and `sqrt` if `complex.rs`'s 19 sites are worth the rename.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `4fc6ba86e` | Lane opened; status stub with the before-snapshot digest. |
| 2026-09-01 | `b17d66d9e` | Slice D: the `STEPS` `requires`/`provides` are generated from a measurement of the source into `creal/steps_generated.rs`; `creal.rs` keeps `STEP_DISPATCH` (order + dispatch) and asserts the two agree. Unlisted-edge inversion demonstrated both ways (old table 0 violations, measured graph 1) and pinned by a test that dies when the edge is deleted. Gate registered in `check.sh`, the `justfile` and `check-merge-hygiene.sh` with a control and mutation M7. `--strict` 2 → 0; `creal.rs` 17,172 → 12,004 lines; projection byte-identical. |
| 2026-09-01 | `461a58573` | Slice E: 13 self-contained modules (62 fields) moved into per-module registries behind the `CRealPrelude` facade; `scripts/creal-migrate-registry.py` promoted, with `--list`. ADR-1530, plus a correction pointer on ADR-1512 — `sqrt` is NOT a local move (`complex.rs`, 19 sites). `NameId` fields 599 → 537, registries 1 → 14, `creal.rs` → 11,439 lines. Projection byte-identical; `creal::` 216 passed; clippy exit 0. |
