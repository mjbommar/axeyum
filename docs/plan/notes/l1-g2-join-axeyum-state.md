# Notes: l1-g2-join-axeyum-state

Detail moved out of [`../status/l1-g2-join-axeyum-state.md`](../status/l1-g2-join-axeyum-state.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **The prerequisite (ADR-0820, l1-g1-declaration-graph) was landed but not
  yet on `main`** when this lane started -- it existed only on a sibling
  worktree branch (`worktree-agent-aa31b64cb74260e6c`). Merged that branch
  into this one (clean merge, 17 files, no conflicts) to get
  `artifacts/declaration-graph/` and ADR-0820 into this tree.
- **The join** (`scripts/lib/graph_join.py`, `scripts/gen-graph-join.py`,
  `scripts/check-graph-join.py`): seven dimensions --
  `fact_ids`, `kernel_declarations`, `statement_vocabulary`,
  `destination_nodes`, `producers`, `declines`, `trust_footprints` -- each a
  `population`/`resolved`/`unresolved` triple with named unresolved members,
  written to `artifacts/graph-join/mathlib-group-defs-v1.join.json` and
  `artifacts/graph-join/dashboard.md`.
- **No theorem-name similarity silently creates an identity.**
  `fact_ids`/`kernel_declarations` resolve ONLY through an EXACT match on an
  existing ledger fact's `title` field (the `F:ml430-*` mirror family,
  whose own evidence already compared a rendered kernel type against the
  Mathlib statement) -- never a match on a fact `id`, never a substring.
  `name_coincidence_candidates` computes, as an explicit diagnostic, every
  declaration name that coincides with an UNRELATED fact's kernel subject
  elsewhere in the ledger and keeps every one unresolved: **27 found in the
  current population**, all correctly declined. See ADR-0835 for the full
  argument and the `Fin`/`Nat.Fin` non-match this join deliberately produces.
- **Measured, over the bounded 446-declaration population**:
  ```
  fact_ids:             9 / 446   (437 unresolved, named)
  kernel_declarations:  9 / 9     (population = fact_ids.resolved)
  statement_vocabulary: 161 / 446
  destination_nodes:    1 / 1     -> curriculum_groups (lean_status: planned)
  producers:            0 / 9
  declines:             0 / 9
  trust_footprints:     9 / 9     (all axiom_footprint = [])
  ```
  All 9 resolved facts are `kernel-lean`, `proved`, axiom-free, and none
  participates in an S2 duplicate-identity class
  (`artifacts/trust-closure/identity-map.tsv`).
- **No second duplicate-detection mechanism.** `trust_footprints.
  in_identity_class` reads `artifacts/trust-closure/identity-map.tsv`
  verbatim; nothing here recomputes `Kernel::render_lean` canonical-type
  equality. This join therefore inherits ADR-0790/S2's own stated limit
  (byte-identical canonical types only) exactly, stated in `join.json`'s
  own `notes.adr_0790_limit_inherited` field.
- **Absence fails loudly.** Emptying the declaration population (a scratch
  fixture with `declarations: []`) makes `check-graph-join.py` exit 1 with
  `EMPTY_POPULATION: declaration graph has zero declarations` -- confirmed
  by hand, not merely asserted.
- **Six guards, six distinct mutation classes, mutation-verified 1:1**
  (`scripts/tests/test-graph-join-mutations.sh`):
  ```
  EMPTY_POPULATION  -> bad_EMPTY_POPULATION
  EMPTY_FACTS       -> bad_EMPTY_FACTS
  ACCOUNTING        -> bad_ACCOUNTING
  STALE_ARTIFACT    -> bad_STALE_ARTIFACT
  POSITIVE_CONTROL  -> bad_POSITIVE_CONTROL
  BARE_NAME_BASIS   -> bad_BARE_NAME_BASIS
  ```
  Baseline: the good fixture passes every guard, all six bad fixtures fail;
  each guard's deletion flips exactly its own target and nothing else, and
  the good fixture stays green throughout the whole sweep (mutation-tested
  in this worktree only, in scratch copies -- never the shared checkout).
- 15 in-process unit tests (`scripts/tests/test-graph-join.py`), all
  passing: every guard's good/bad fixture, the no-name-similarity
  requirement directly (exact title match, name-coincidence recorded but
  not resolved, `Fin` vs `Nat.Fin` deliberately not equated), and a
  regression suite against the REAL 446-declaration population.
- Gate registered in both `justfile` (`graph-join` recipe, appended to the
  `check:` dependency line) and `scripts/check.sh` (three `step` lines:
  `graph-join`, `graph-join-tests`, `graph-join-mutations`). Verified:
  `just --justfile justfile --list` lists `graph-join`;
  `AXEYUM_CHECK_LIST=1 bash scripts/check.sh` lists all three new steps;
  neither edit touched the other lines in either dependency list.

## What this join does not capture

Bounded to `mathlib-group-defs-v1`'s 446 declarations, which are heavily
Lean/Mathlib-CORE arithmetic and abstract-algebra typeclass scaffolding
(`Add`, `Mul`, `Semigroup`, `Monoid`, `CommMagma`) -- 0 of which have a
representable Axeyum counterpart, since this kernel has no bundled-
structure/typeclass mechanism at all; the low 9/446 `fact_ids` resolution
rate is the honest, expected shape of THIS population, not a defect of the
join. `destination_nodes` operates at population granularity only (the
curriculum ledger carries no per-declaration join key).
`producers`/`declines` are checked only against the 9 already-resolved fact
ids; a producer targeting an unresolved declaration is invisible to this
join by construction, since that declaration has no fact yet. Trust
footprints are read from each fact's own committed `axiom_footprint`,
never re-derived by calling the kernel.

## Files

- `artifacts/graph-join/mathlib-group-defs-v1.join.json`
- `artifacts/graph-join/dashboard.md`
- `scripts/lib/graph_join.py` (join logic, identity-safety rules)
- `scripts/gen-graph-join.py` (generator, no toolchain needed)
- `scripts/check-graph-join.py` (gate, no toolchain needed)
- `scripts/tests/graph_join_mutations.py` (good/bad fixture builder)
- `scripts/tests/test-graph-join.py` (15 in-process tests)
- `scripts/tests/test-graph-join-mutations.sh` (guard-deletion kill table)
- `docs/research/09-decisions/adr-0835-the-graph-join-resolves-identity-only-through-an-existing-ledger-mirror.md`

## Next (not this lane's scope)

G3 (publish the infrastructure frontier) can read `join.json` for which
declarations in this bounded population already have ledger/kernel/producer
coverage. Extending the join to a wider or different declaration-graph
population needs only a new population, not a new identity mechanism.
