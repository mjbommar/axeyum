# Lane: curriculum-depth — re-measure the depth spine, fix the bucket bug it exposed

<!-- plan-section: lane-status -->

**Re-measured `curriculum.toml`'s `kernel_decls` axis and found a real bug, not
just drift** (`COMPLETE`, curriculum-depth, 2026-08-31). ADR-1120's general-`n`
determinant (`Rat.det`, `matSkip`, `matMinor`, `altSign`, `matInv2*`) landed
after ADR-1075's measurement was pinned, and
`measure-curriculum-kernel-coverage.py`'s `linear-algebra` bucket matched
`det2`/`det3` literally — so all 22 new declarations fell through to the
`rationals` catch-all and `linear-algebra`'s pinned value (59) stayed exactly
where it was by coincidence, invisible without diffing declaration-by-
declaration against the pattern. Fixed the pattern, re-measured (2,615
distinct declarations, 2,483 attributed, same 132 residual), and corrected six
drifted `kernel_decls` values: `naturals` 512→516, `integers` 186→193,
`rationals` 211→204, `divisibility-and-euclid` 151→153, `number-theory`
107→108, `linear-algebra` 59→81. The six drifts sum to exactly the +29 total
declaration growth, confirming the reconciliation.
[ADR-1140](../../research/09-decisions/adr-1140-the-depth-spine-stays-a-proposal-two-of-its-rungs-already-landed.md).

**Did not apply `DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`'s ~30-node
graph surgery, confirming ADR-1075's decision.** Checked all real consumers
(`grep -rl curriculum.toml scripts/ crates/`, docs-only hits excluded):
`graph_dispatcher.py` reads `status`/`layer`/`area`/`title` and never
`kernel_decls`; `validate-foundational-concepts.py` checks `title`/`layer`/
`area`/`status`/`family`/`prerequisites`/`unlocks`, never `summary` or
`kernel_decls` (137 rows, unaffected, ran clean); `mathtour.rs`'s `NODES`
mirror has no `kernel_decls` field at all (6/6 `mathtour::` tests pass, 53.46s,
unaffected by construction). Most proposed rungs (N7′, N9, N11, L3, L9) have no
self-checking scenario family, so landing them as `covered` would fail
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario` on sight —
the same mistake ADR-1075 rejected for `calculus`. The five-script-plus-Rust-
mirror consumer surface is real, separate work from a measurement fix and
belongs to a task that budgets it explicitly, ideally after a scenario family
exists for one of the open rungs to make `covered` honest.

**Two proposal rungs (N10 Euler's theorem, L7 the general-`n` determinant)
landed the same day the proposal was written, so it and two destination pages
were stale on exactly the frontier they each called live.** Corrected in
place: `DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` (a top correction
block, both table rows, the "live rungs"/keystone prose),
`03-destinations/number-theory.md` (added `Int.euler_totient_theorem` to the
"Proved in the kernel" table, removed the stale "absent" bullet),
`03-destinations/linear-algebra.md` (rewrote the determinant bullet and the
closing gap paragraph — itself only hours old — to the corrected 81-declaration
count). `graded-statement-families-number-theory-and-linear-algebra.md` (821
lines, dated 2026-08-30) got a top-of-file pointer rather than a line-by-line
rewrite — out of this task's budget for a document nothing mechanically
consumes.

**One pre-existing, unrelated gate failure found and left alone.**
`check-graph-dispatcher.py` fails on `G7 queue-below-floor` from
`check-dispatchable-frontier.py` — the mathlib-import dispatch queue, nothing
to do with curriculum nodes. Confirmed unrelated: no curriculum edge, status or
family value changed.

**Regenerated consumers, all clean.** `gen-foundational-concepts.py` (138
rows, picked up the `linear-algebra` summary edit),
`gen-foundational-dashboards.py` (4 dashboards, also caught a pre-existing,
never-applied drift from the `probability` node's addition — 23→24 curriculum
rows in `curriculum-status-audit.md`), `validate-foundational-concepts.py`,
`check-curriculum-coverage.py`, `gen-import-backlog.py --check`, `gen-adr-index.py
--check` (704 rows, no new duplicates) all exit 0.

<!-- plan-section: landed-changes -->

| 2026-08-31 | (pending) | ADR-1140: re-measured `curriculum.toml` post ADR-1110/ADR-1120, found and fixed a real bucket-attribution bug (not drift) that had silently mis-filed 22 `linear-algebra` declarations under `rationals`, corrected six `kernel_decls` values, and confirmed ADR-1075's decision not to apply the ~30-node depth-spine graph surgery this pass. |
| 2026-08-31 | (pending) | Corrected the two proposal rungs (N10, L7) that landed the same day the proposal and both destination pages were written, in `DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`, `03-destinations/number-theory.md`, `03-destinations/linear-algebra.md`, and a pointer note in `graded-statement-families-number-theory-and-linear-algebra.md`. |
