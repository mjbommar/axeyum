# Lane: l3-d0-effort-taxonomy -- where theorem effort actually goes

<!-- plan-section: lane-status -->

**Done (`l3-d0-effort-taxonomy`, 2026-08-30).**
[ADR-0870](../../research/09-decisions/adr-0870-d0-effort-measurement-refines-not-confirms-retrieval-as-bottleneck.md)
records the full decision.

## Headline

32 sampled completed/declined lane episodes classified into a 9-category
taxonomy (the D0 spec's 8, plus `infrastructure_maintenance`, added
deliberately). Trust-and-plumbing work (`safety_evidence` + `integration` +
`infrastructure_maintenance`) is **19/32 (59%)**, against `proof_assembly`'s
4/32 (12%). The "retrieval is the bottleneck" claim
(`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`)
is **refined, not confirmed or refuted**: retrieval is a major component in
4 of 7 mathematical-domain episodes in this sample, but it is not the
dominant cost once the full episode population -- mostly infrastructural --
is counted, because the original "thirteen instances" tally was never
measured against that larger population.

## What landed

- `artifacts/effort-taxonomy/taxonomy.json` -- 9 category definitions, each
  with a one-paragraph discriminating definition, plus a `category_additions`
  block justifying the one category the D0 spec did not name.
- `artifacts/effort-taxonomy/episodes.json` -- 32 episodes, each carrying
  `primary_category`/`secondary_categories`, `kind` (completed/partial/
  declined), `domain` (mathematical/infrastructural), `basis` (self-report/
  corroborated), and a `corroboration` object naming a commit SHA, an ADR
  number, or a source-file path.
- `scripts/gen-effort-taxonomy.py` -- derives `distribution.json` +
  `report.md` from the two JSON inputs (single implementation; this is a
  data-consistency computation, not a soundness-critical certificate, so it
  does not need the two-independent-readers pattern).
- `scripts/check-effort-taxonomy.py` -- 9 independent guards (G1-G9 below),
  each failing on absence with a named reason.
- `scripts/tests/test-effort-taxonomy.py` -- 24 unit tests, one guard's
  fixture fully isolated from another's (tests call guard functions
  directly), so a mutation to one guard can only ever kill that guard's own
  test(s).
- Registered in `justfile` (appended `effort-taxonomy` to the end of the
  existing `check:` dependency line, did not restructure it; added a new
  `effort-taxonomy` recipe) and `scripts/check.sh` (three new `step` lines
  after `infrastructure-frontier-mutations`). Verified: `just
  effort-taxonomy` runs clean; `AXEYUM_CHECK_LIST=1 bash scripts/check.sh`
  lists all three new steps.
- ADR-0870, ADR index and PLAN.md regenerated.

## Sampling method

Sampled from today's `git log --since="24 hours ago" --diff-filter=A
--name-only -- docs/plan/status/` (123 new files) and the equivalent for
`docs/research/09-decisions/` (52 new ADRs). Deliberately picked for
coverage, not at random: completed, partial, and declined; mathematical
proof-production and infrastructural/safety work; single-commit wins and
multi-step diagnoses. One episode (`nursery-draw-8-declined`) is drawn
directly from an ADR rather than a status file, because it is the cleanest
fully-declined episode in the window (zero rows moved, zero constructions
made) and status files alone did not have one as clean.

## Classification basis, and the one bug this caught before it shipped

28 of 32 episodes are `corroborated`: the checker independently re-verifies
each citation (`git cat-file -e` for a commit, a file-glob for an ADR, a path
existence check for a source file) rather than trusting the string in
`episodes.json`. This caught a real mistake during authoring: an episode's
first draft cited `5e93448c` as a commit SHA, copied from a hex-looking
string in its status file -- the checker reported `G5 DANGLING COMMIT`, and
reading the source file showed `5e93448c` was the first eight hex characters
of a **fact-id hash**, not a commit at all. Fixed to cite the gate script
the episode built instead
(`scripts/check-mirror-statement-fidelity.py`, file-corroborated).

4 of 32 episodes rest on self-report alone, named in
`artifacts/effort-taxonomy/report.md`: `control-registration-hyphen`,
`ivt-claim-correction`, `lean-attestation-s5`, `totient-mul`. None of the
four had a citable commit SHA, ADR number, or distinctive new file in the
portion of their status file read.

**"Corroborated" confirms the cited artifact is real, not that the taxonomy
LABEL is correct.** The category assignment is always drawn from reading the
episode's self-reported narrative; corroboration only rules out a fabricated
or misremembered citation, which is a real and (per the paragraph above)
non-hypothetical failure mode.

## Distribution

| category | count | share |
| --- | ---: | ---: |
| `safety_evidence` | 11 | 34% |
| `proof_assembly` | 4 | 12% |
| `integration` | 4 | 12% |
| `infrastructure_maintenance` | 4 | 12% |
| `retrieval` | 3 | 9% |
| `kernel_debugging` | 3 | 9% |
| `statement_repair` | 1 | 3% |
| `missing_definitions` | 1 | 3% |
| `semantic_falsification` | 1 | 3% |

`kind`: 26 completed, 5 partial, 1 declined. `domain`: 25 infrastructural, 7
mathematical. Full per-episode rows in `artifacts/effort-taxonomy/episodes.json`;
regenerable summary in `artifacts/effort-taxonomy/report.md`.

## D1-D4 ordering recommendation (ADR-0870 decision 2)

The roadmap's D1 (declarative spec) -> D2 (retrieval index) -> D3
(falsification) -> D4 (obstruction compiler) sequence is not overturned, but
near-term emphasis is re-weighted:

- **D3 first** -- already partially built (`l0-s3-semantic-controls`'s
  13-fixture pack, ADR-0752), and its per-instance leverage is high even
  though it is the rarest primary category in this sample (1/32): CLAUDE.md's
  own gotchas record several false/vacuous statements that would have cost
  an entire family's proof budget had they not been caught first.
- **D2 ahead of further D1 mathematical-spec work** -- retrieval friction,
  when it occurs in a proof-production episode, is decisive (4/7
  mathematical episodes here), while `missing_definitions` -- D1's target
  failure mode -- occurred once and was handled cleanly by hand.
- **D1's first pilot subsystem redirected** -- from a mathematical
  declaration subsystem to a repeatedly-decayed artifact/gate subsystem
  (candidates from this sample: the statable-vocabulary artifact, or a
  safety-matrix-shaped census), since 59% of measured effort is
  trust-and-plumbing and several episodes are exactly "a hand-maintained
  artifact's invariant broke because nothing re-derived it."
- **No new roadmap phase added.** The infrastructure_maintenance share may be
  a one-time cost of this week's ADR-0717 L0-L2 rollout rather than a
  standing rate; re-measure (extend `episodes.json`, do not replace it) after
  that program settles before deciding whether a dedicated phase is
  warranted.

## Absence check

```
$ python3 scripts/check-effort-taxonomy.py
CHECK_EFFORT_TAXONOMY|PASS|episodes=32|categories=9
```

Demonstrated failing on absence by dropping below the floor: truncating a
scratch copy of `episodes.json` to its first 5 entries and running the
checker against it (`--episodes <scratch>`, `--skip-generated-check` since a
scratch copy has no matching generated pair) gives:

```
$ python3 scripts/check-effort-taxonomy.py --episodes <scratch-5-entry-copy> --skip-generated-check
CHECK_EFFORT_TAXONOMY|FAIL|violations=2
  G1 FLOOR: 5 episodes < required floor 20 (D0's exit criterion is at least 20 representative episodes)
  G7 COVERAGE: no 'declined' episode in the sample
```

Exit code 1, two independent reasons named (the first 5 entries happen to
carry no `declined` episode either, which is itself a small demonstration
that G7's coverage requirement is not redundant with G1's floor -- a
20-episode sample of only successes would clear G1 and still fail G7). The
same technique (drop a category from `taxonomy.json`, blank an episode's
`basis` field, point a corroboration at a nonexistent commit/ADR/file)
exercises G2-G6 identically; the mutation table below exercises every guard
by deleting it instead.

## Guard -> test kill table

Mutated `scripts/check-effort-taxonomy.py` one guard function at a time (each
mutation: insert `return Violation()` as the function's first statement,
disabling exactly that guard), ran `scripts/tests/test-effort-taxonomy.py`
against the mutant, then restored the original file byte-for-byte and
verified the restore before moving to the next guard. Done in this worktree
only, via a scratch driver, never against the shared checkout. `__pycache__`
cleared between every mutation (CLAUDE.md's stale-bytecode trap: same-length
mutations written back-to-back within one second collide on the
`(mtime-in-whole-seconds, size)` cache key -- confirmed by reproducing the
trap first, seeing four unrelated guards all report the SAME "killed" test,
then re-running clean after adding the cache-clear).

| guard | tests killed | survived? |
| --- | --- | --- |
| G1 `guard_floor` | 1: `test_below_floor_is_flagged` | no |
| G2 `guard_categories_defined` | 2: `test_secondary_category_must_also_be_defined`, `test_used_but_undefined_category_is_flagged` | no |
| G3 `guard_required_fields` | 3: `test_bad_kind_enum_is_flagged`, `test_empty_field_is_flagged`, `test_missing_field_is_flagged` | no |
| G4 `guard_basis_corroboration_shape` | 2: `test_corroborated_with_empty_refs_is_flagged`, `test_self_report_with_corroboration_is_flagged` | no |
| G5 `guard_corroboration_reverified` | 1: `test_dangling_refs_of_every_type_are_flagged` | no |
| G6 `guard_source_exists` | 1: `test_dangling_source_is_flagged` | no |
| G7 `guard_coverage` | 2: `test_all_completed_is_flagged_for_missing_declined`, `test_all_mathematical_is_flagged_for_missing_infrastructural` | no |
| G8 `guard_no_duplicate_ids` | 1: `test_duplicate_id_is_flagged` | no |
| G9 `guard_generated_fresh` | 1: `test_stale_artifact_is_flagged` | no |

9/9 guards killed, 0 survivors. A guard killing more than one test is
legitimate here (not vacuous): each additional test exercises a distinct
sub-case of the same guard function (e.g. G3 covers missing/empty/bad-enum
fields separately), matching the standing rule that a guard may kill more
than one test as long as it never kills zero. After the sweep,
`git status --porcelain scripts/check-effort-taxonomy.py
scripts/tests/test-effort-taxonomy.py` is empty and `just effort-taxonomy`
is green.

## Largest bias in the sample

The sample is skewed toward `docs/research/09-decisions/adr-08*.md`-citing
episodes because I actively searched for citable artifacts to corroborate --
today's ADR-0717 L0-L2 safety-roadmap rollout produced a disproportionate
share of easily-corroborated (ADR-numbered) episodes compared to ordinary
`ml430` mirror lanes, which more often cite only a lane name or nothing at
all in their landed-changes table. That almost certainly inflates
`safety_evidence`'s measured share relative to its true share of the day's
total lane-hours, though by how much is not measurable from this sample
alone -- flagged explicitly in ADR-0870's "what would change this decision"
section as the reason to re-sample rather than to trust this single 59%
figure as a stable constant.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `0a067aa37` | taxonomy.json, episodes.json (32), gen/check scripts, 24-test suite (first commit). |
| 2026-08-30 | `10716c57d` | Registered `effort-taxonomy` in justfile (`check:` line appended, new recipe) and scripts/check.sh (three new steps). |
| 2026-08-30 | (this commit) | ADR-0870, status doc, mutation kill table, regenerated ADR index and PLAN.md. |
