# Lane: doc-refactor — the engineering strand, corrected against what changed

<!-- plan-section: lane-status -->

**Done (`DONE`, doc-refactor, 2026-08-19).** `docs/refactor-2026-08/` corrected
against 2026-08-18/19, by amending specific claims and keeping the original
reasoning visible — no rewrites. Five files touched of 18; thirteen left alone
because dated lane diaries are records, not assertions about now.

Corrections, each re-measured here rather than taken from a brief: `04` G2 said
"Unfixed" (`check-clippy-complete.sh` is in both gates); ADR count 455 → `rows=523`;
G4–G8 added (ADR `--check` exiting 0 on duplicates, the mutation harness scoring
a non-building mutant as a kill, axiom-freedom run by no gate, `local-ci.sh`
never having run, `just check` aborting at #18 of 41 so 23 gates never ran).
`gate-divergence-2026-08-14.md`'s 112/61 → 203/278 and its completeness ordering
INVERTED — while `aggregate-scope` was red at #18 the no-`just` fallback was the
more complete gate. `00` gained the three new hygiene incident classes and a
closing open-items list; `06` gained the shared scratchpad.

**Open, and recorded as open in `00` and `04`:** `check-aggregate-scope`'s 32
unrecorded steps (fix by wiring, not re-pinning); ADR numbering's structural fix
(non-sequential allocation, unbuilt); no `axeyum-lean-kernel` suite registered
with the mutation harness (six are: five Python plus `fp-width-guard`).

**Found while writing, not in the brief:** the record
`check-local-ci-freshness.sh` enforces has five steps; `local-ci.sh` has had a
sixth (the frontier ratchet) since `69f2cffb8` the same morning. The gate reports
`PASS -- fresh, ancestor, all-pass` over a run in which that step did not exist.
Freshness of a record is not coverage by it. Owner: whoever owns `local-ci.sh`.

**Not touched, deliberately:** CLAUDE.md still says to treat `just check` as the
gate and `check.sh` as the fallback that may lag it. G8 inverted that for the
duration of the red-gate window. It is the repository's most contested file and
outside this lane's paths.

<!-- plan-section: landed-changes -->

