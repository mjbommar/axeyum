# Lane: l2-g3-infrastructure-frontier — ADR-0717 L2 phase G3, publish the infrastructure frontier

<!-- plan-section: lane-status -->

**Done, l2-g3-infrastructure-frontier, 2026-08-30.**
[ADR-0845](../../research/09-decisions/adr-0845-the-infrastructure-frontier-curates-candidates-and-validates-them-live.md)
records the design decisions.

## What landed

Executed G3 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`:
four frozen queues over the L1 phase G2 graph join
(`artifacts/graph-join/mathlib-group-defs-v1.join.json`, ADR-0835), each
row carrying a stable content-hash id, raw evidence, a stated gain kind,
current blockers, destination paths, an estimated cost, and a
preregistered, re-runnable metric.

- **Rank-by-degree was tried first and rejected in favor of hand-curated
  candidates re-validated live.** The population's top in-degree
  declarations (`Nat` 194, `OfNat.ofNat`/`instOfNatNat` 85, `LT.lt`/
  `instLTNat` 54, ...) are Lean/Mathlib-core notation plumbing with no
  independent content -- a pure-degree queue would violate the roadmap's
  own closing line ("raw degree never authorizes work"). Candidates instead
  live as source in `scripts/lib/infrastructure_frontier.py::
  ROW_CANDIDATES`, each with a written mechanism (`gain_explanation`), and
  are re-validated against the live join/graph at generation time
  (`validate_candidate` raises if a candidate's premise no longer holds).
- **Measured result over `mathlib-group-defs-v1` (446 declarations)**:
  ```
  language-infrastructure:   4 rows
  proof-producers:           0 rows (structural: 9/9 fact-linked already proved)
  theorem-dominators:        1 row
  dependency-ready-leaves:   0 rows (8 candidates, all excluded for a stated reason)
  ```
  Two of four queues are genuinely empty for this population, each for a
  data-backed, machine-checkable reason computed in `_empty_reason` (never
  asserted in prose alone) and re-derivable from the artifact's own
  `diagnostics` section.
- **Row rows, briefly:**
  - `language-infrastructure` (4): Semigroup+mul_assoc, CommMagma+mul_comm,
    Mul+IsLeftCancelMul+mul_left_cancel, and carrier-polymorphic congrArg.
    All four cite the same root cause ADR-0835 already measured -- this
    kernel has no bundled-structure/typeclass mechanism at all -- and the
    congrArg row separately cites CLAUDE.md's own documented per-carrier
    `congr_X_to_Y` hardcoding incidents (2026-08-29) as its cost evidence.
  - `theorem-dominators` (1): `of_decide_eq_true`. NOT a
    `name_coincidence_candidate` in the join (that scan only reads FACT
    evidence text), but a plain source grep finds a same-named kernel
    prelude primitive (`crates/axeyum-lean-kernel/src/prelude.rs`). Per
    ADR-0835's own refusal to treat name similarity as identity, this row's
    action is "verify the two statements match before doing anything
    else", not "go prove this" -- confidence `low`, gain kind
    `independent_assurance` pending that verification.
  - `proof-producers` (0): the join's `producers`/`declines` dimensions can
    only see the 9 declarations already resolved in `fact_ids`
    (ADR-0835's own stated limit), and all 9 are already
    `epistemic_status=proved` -- there is no open, fact-linked cluster in
    this population for a producer to serve.
  - `dependency-ready-leaves` (0): 8 Theorem-kind declarations have every
    direct TYPE dependency already available (computed from
    `direct_type_deps` only, never proof/value deps -- phase G1's own rule
    that proof-derived data is forbidden producer input). Each was excluded
    for a stated reason: built-in inductive projections needing no separate
    proof (`And.left`, `And.right`, `Or.elim`), Lean-generated auxiliary
    machinery with no independent content (`noConfusion_of_Nat` and its
    private aux, `Nat.le.brecOn`), or promoted to another queue because the
    real blocker is architectural (`congrArg`) or a naming question
    (`of_decide_eq_true`). Matches
    `scripts/check-dispatchable-frontier.py`'s own finding that the
    ledger-wide dispatchable set is nearly empty (1 of 139 open ml430
    mirrors) -- this population contributes 0 to that 1.
- **Row ids are content hashes of substance, not position.**
  `row_id(queue, population_id, subject, gain_kind)` hashes only those four
  fields -- explicitly excluding degree, resolved counts, and confidence --
  so an id survives a graph refresh that shifts degree by one but proposes
  the same increment. `ROW_ID_PURITY` re-derives every row's id from its
  own recorded fields and fails if it does not match.
- **Cross-checked against `scripts/check-dispatchable-frontier.py`**
  (read-only, out of this lane's edit scope). None of this population's 446
  names is a subject that script reports on -- its dispatchable/held-out/
  blocked sets are drawn from unrelated `ml430` number-theory mirror
  families -- so no direct disagreement is possible; the artifact records
  this explicitly (`cross_check.population_overlap_note`) rather than
  omitting the comparison, and notes the thematic agreement: both
  independently land on "almost nothing is immediately actionable", for
  different reasons.
- **Absence fails loudly, confirmed by hand, not merely asserted.**
  Pointing `--join-dir` at a nonexistent directory:
  `FAIL: MISSING_JOIN: .../mathlib-group-defs-v1.join.json does not exist`,
  exit 1. Pointing `--frontier-dir` at a nonexistent directory (no generated
  artifact yet): `FAIL: .../mathlib-group-defs-v1.frontier.json does not
  exist -- run scripts/gen-infrastructure-frontier.py`, exit 1.
- **Seven guards, seven distinct mutation classes, mutation-verified 1:1**
  (`scripts/tests/test-infrastructure-frontier-mutations.sh`):
  ```
  MISSING_JOIN           -> bad_MISSING_JOIN
  STALE_ARTIFACT         -> bad_STALE_ARTIFACT
  ROW_ID_UNIQUE          -> bad_ROW_ID_UNIQUE
  ROW_ID_PURITY          -> bad_ROW_ID_PURITY
  EMPTY_QUEUE_REASON     -> bad_EMPTY_QUEUE_REASON
  ROW_EVIDENCE_COMPLETE  -> bad_ROW_EVIDENCE_COMPLETE
  CROSS_CHECK_PRESENT    -> bad_CROSS_CHECK_PRESENT
  ```
  Baseline: the good fixture passes every guard, all seven bad fixtures
  fail; each guard's deletion flips exactly its own target and nothing
  else, and the good fixture stays green throughout the whole sweep
  (mutation-tested in this worktree only, in a scratch copy -- never the
  shared checkout).
- Gate registered in both `justfile` (`infrastructure-frontier` recipe,
  appended to the `check:` dependency line -- only that append, no
  restructuring) and `scripts/check.sh` (two `step` lines:
  `infrastructure-frontier`, `infrastructure-frontier-mutations`).
  Verified: `AXEYUM_CHECK_LIST=1 bash scripts/check.sh` lists both new
  steps; neither edit touched the other lines in either dependency list.

## What this queue set does not capture

Bounded to the same 446-declaration `mathlib-group-defs-v1` population
ADR-0835 joins -- a wider population needs its own join first (ADR-0835's
own consequence), which is out of this lane's scope. The `grep_presence`
heuristic backing the `of_decide_eq_true` row is explicitly
non-authoritative; a row built on it names verification as its first step,
never proof work. Rows never claim a downstream FACT count from the ledger
beyond what the join can see -- since the join resolves only 9/446 to
facts (all already proved), "top downstream facts" for the
language-infrastructure rows is reported as the in-population Mathlib
dependent count (a proxy, explicitly labeled as such), not a ledger count,
because no ledger fact currently depends on a construction this kernel
cannot yet represent.

## Files

- `artifacts/infrastructure-frontier/mathlib-group-defs-v1.frontier.json`
- `artifacts/infrastructure-frontier/mathlib-group-defs-v1.dashboard.md`
- `scripts/lib/infrastructure_frontier.py` (candidates, evidence computation, row_id)
- `scripts/gen-infrastructure-frontier.py` (generator, no toolchain needed)
- `scripts/check-infrastructure-frontier.py` (gate, no toolchain needed)
- `scripts/tests/infrastructure_frontier_mutations.py` (good/bad fixture builder)
- `scripts/tests/test-infrastructure-frontier-mutations.sh` (guard-deletion kill table)
- `docs/research/09-decisions/adr-0845-the-infrastructure-frontier-curates-candidates-and-validates-them-live.md`

## Next (not this lane's scope)

G4 (three pilot clusters) can cite a row's `row_id` in a lane brief and
re-run its `preregistered_metric.command` afterward to check whether it
moved. Widening beyond `mathlib-group-defs-v1` needs a new L1 G1/G2
population and join first; this generator takes a `--population-id` and
needs no other change to read one.

<!-- plan-section: landed-changes -->

| 2026-08-30 | (pending) | L2 phase G3: publish the infrastructure frontier -- four frozen queues over the group-defs population, content-hash row ids, seven mutation-verified guards (ADR-0845). |
