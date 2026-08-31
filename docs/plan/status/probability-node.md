# Lane: probability-node — give the kernel's probability spine a curriculum node

<!-- plan-section: lane-status -->

**Landed (`COMPLETE`, probability-node, 2026-08-31).** `docs/curriculum/curriculum.toml`
mentioned probability zero times while `crates/axeyum-lean-kernel/src/rat_prelude/probability.rs`
carries 47 axiom-free `Rat` declarations — distributions, expectation, variance
and covariance with Cauchy-Schwarz, Markov's and Chebyshev's inequalities, and
the weak law of large numbers — attributed to `rationals` only for want of a
better bucket. Added a single layer-3 `probability` node, on prerequisites
`rationals` + `counting` (what `probability.rs` actually imports: `Rat.sumRange`
and its monotonicity, nothing analytic), `status = "planned"` — the first node
in the file to use that value, since the content is bounded/computable but no
self-checking `Family` exists for it yet. Decision and full measurement in
[ADR-1082](../../research/09-decisions/adr-1082-add-a-probability-node-the-kernel-had-the-spine-the-map-did-not.md).

**One correction to the brief that mattered.** ADR-1075's own pinned totals
(2,562 declarations / 2,433 attributed, measured hours earlier the same day)
were already stale by the time this lane re-ran the measurement — 2,586 / 2,454
— from other lanes' commits landing in between, not from this change. Five
pre-existing nodes' `kernel_decls` had drifted the same way and are corrected
here as a direct byproduct of the same command (`naturals`, `integers`,
`rationals`, `number-theory`, `linear-algebra`); the other 18 matched exactly
and were left alone. `scripts/gen-import-backlog.py --check` is still red on
`main`, unrelated to this change (confirmed: the regenerated diff mentions
`probability` zero times) — the same pre-existing gate ADR-1075 found and
deliberately left alone.

**Also merged local `main` rather than `origin/main`.** ADR-1075 and the
`kernel_declaration_projection`/`measure-curriculum-kernel-coverage.py`
infrastructure this task depends on were 18 commits ahead of `origin/main` at
session start (pushed to the shared checkout's local `main` but not yet to
`origin`). `git merge --no-edit origin/main` alone would not have found them.

Checks run: `cargo test -p axeyum-scenarios --lib mathtour::` (6 passed),
`scripts/measure-curriculum-kernel-coverage.py --expect-attributed 2454
--require-node probability --require-node calculus --require-node
number-theory` (exit 0), `scripts/gen-foundational-concepts.py` (138 rows,
regenerated), `scripts/validate-foundational-concepts.py` (138 rows, 24
curriculum, 0 errors), `scripts/gen-adr-index.py --check` (696 rows, no new
duplicates), `scripts/check-links.sh` (all links ok). The full workspace gate
was **not** run (out of scope for a docs/data-graph change; the coordinator
re-verifies before merge per standing practice).

<!-- plan-section: landed-changes -->

| 2026-08-31 | (uncommitted at status-file write time) | ADR-1082 + `probability` curriculum node: `docs/curriculum/curriculum.toml` (new node, `rationals`/`counting` unlocks, corrected `kernel_decls` for 5 drifted nodes, updated header), `crates/axeyum-scenarios/src/mathtour.rs` mirror, `docs/curriculum/03-destinations/probability.md`, `scripts/measure-curriculum-kernel-coverage.py` (new bucket + NODES entry), `scripts/gen-foundational-concepts.py` (new `CURRICULUM_MAP` entry reusing `finite-probability-v0`), regenerated `artifacts/ontology/foundational-concepts.json`. |
