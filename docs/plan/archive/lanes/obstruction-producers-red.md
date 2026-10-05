# Lane: obstruction-producers-red — retire settled obstruction producers instead of erroring

<!-- plan-section: lane-status -->

**obstruction-producers-red (`DONE`, obstruction-producers-red, 2026-09-02).**
`scripts/gen-obstruction-producers.py` was red on `main`, exiting 2 before
writing anything, because both hard-coded targets of the
`pointwise-bit-extensionality` contract had been proved. Fixed the ADR-1510
way — a claim sized against a population that empties RETIRES, it does not
error — and the three gates that depend on it are green again.

**The contract died of its own success.** The two targets were flipped in
`8822d5033` (2026-08-30) by exactly the four-step recipe the contract wrote
down (`Nat.eq_of_testBit_eq` extensionality, `testBit_land`/`testBit_lor`, an
8-leaf `{0,1}` case split), executed by hand in
`nat_prelude/and_or_distrib.rs`. The generator reported that as
`hypothesis is stale`. **The handoff's attribution was wrong**: `845fc8823`
only bound `formal.kernel_theorem` and changed no `epistemic_status`; the
flip is `8822d5033`, confirmed by reading the `epistemic_status` diff on
both fact files. `and_or_distrib.rs` also tripped the same function's SECOND
staleness trap — the "no machinery exists in the tree" grep, which is a
claim only while a target is live and is the evidence for HOW it closed once
they are not.

**Blast radius was the whole artifact, not one contract**, because the
writer runs after contract compilation. `obstructions.json` could not be
regenerated at all, so the `testbit-codomain` lane's corrected
`nat-testbit-bool-codomain` row sat at `removability: new-construction` in
the committed artifact a selector reads. It is `not-removable` there now,
for the first time.

**One partition, three labels, no policy invented.** P1 had grown a private
`fulfilled` path for exactly this; P2 never grew one, and neither had the
PARTIAL case — a producer losing some targets kept claiming them. Both now
route the live/settled split through one `partition_settled`, and
`contract_kind` picks the label mechanically from what
`check-obstruction-producers.py` already demands: `producer` (>= 2 live),
`capsule` (1 live — G6's own words), `fulfilled` (none live). A target
ABSENT from the ledger is still an error; a broken table is not an
exhausted population.

**A retirement that cannot say what closed it is unauditable**, so
`settlement_record` reads the settling commit and date from history. The
fact file cannot answer — `provenance.date` is when the mirror was created
(2026-08-29, a day before the flip) and `provenance.established_by` reads
"not established in this ledger". Where there is no `.git` it falls back to
the value in the committed contract, which is the SAME value because a
settling commit is immutable history. Verified drift-free both ways:
`--check` exits 0 in this tree and in a git-free copy where
`_git_settlement` returns `None` and `_committed_settlement` demonstrably
supplies `8822d5033`/`2026-08-30`.

**G3 had to be relaxed or the fix would have reproduced the bug in the
checker.** With both contracts retired there is no live producer, and the
old G3 would have failed — reporting success as a defect one layer up. It
now passes on an all-retired tree and prints an `EXHAUSTED` line naming the
policy question instead. New **G11** holds the partial case together for
every kind: `spent` names real, non-open facts each carrying a
`settled_commit`, and is disjoint from `applicability.fact_ids`, so `spent`
cannot become a place to park live work where G7 cannot see it.

| gate | before | after |
| --- | --- | --- |
| `gen-obstruction-producers.py` | 2 (`P2 target … is missing or not open`) | 0 |
| `gen-obstruction-producers.py --check` | 2 (same, dies first) | 0 |
| `check-obstruction-producers.py` | 1 (G1 + two G7) | 0 |
| `scripts/tests/test-obstruction-producers.sh` | 2 failures of 13 | 0 of 15 |
| `scripts/check-control-registration.sh` | 0 | 0 (`controls=51 orphans=0`) |

Retired and partial producers:

| contract | kind | live | settled | settling commit |
| --- | --- | --- | --- | --- |
| `pointwise-bit-extensionality` | `fulfilled` | 0 | 2 | `8822d5033` (2026-08-30) |
| `extensional-duplicate-close` | `fulfilled` | 0 | 8 | `79d9691c6`, `21fa9575c`, `ecbc1bab6` (all 2026-08-30) |

No contract is partial in the current ledger; the partial path is exercised
by its control, which puts one settled P1 hypothesis back to `open` and
requires `kind=capsule` with the live target kept and the other seven
recorded.

Mutation table — `mutation_controls.py obstruction-testbit-classification`,
6 mutations, **each `killed 1`, a different test each time**:

| mutation | test killed |
| --- | --- |
| the Bool-codomain row is not-removable | `test_bool_row_is_not_removable` |
| the row cites the ADR its removability rests on | `test_bool_row_cites_the_deciding_adr` |
| every path-shaped evidence entry names a real file | `test_every_path_shaped_evidence_entry_exists` |
| the List-Bool group is split out by what the statements say | `test_the_split_matches_what_the_statements_say` |
| **an exhausted population retires instead of erroring** | `test_exhausted_population_retires_rather_than_erroring` |
| **a partial settlement keeps its live targets live** | `test_partial_settlement_keeps_live_targets_and_records_settled` |

The two checker sub-guards cannot be registered there — `mutation_controls`
has only unittest and cargo runners, and this suite is bash — so they were
deleted one at a time in an isolated `rsync` copy outside the checkout.
Deleting the whole G11 block killed both G11 cases and left the other 13
green; deleting `spent-target-still-open` alone killed
`[G11-spent-target-still-open]` and nothing else; deleting `spent-and-live`
alone killed `[G11-spent-and-live-and-consequent-G7]` and nothing else.

**The retirement mutation raises `SystemExit` rather than calling `die()`,
and the reason is a measurement hazard worth carrying.** `die` prints
`ERROR: …` to stderr, `classify_unittest`'s death regex reads that line as a
SECOND dead test, and the harness returns `INCONSISTENT — the summary line
says 1 died but 2 were named`, which measures nothing. A mutation whose own
diagnostic output is parsed as a result is a mutation that cannot be scored.

## Next lane: what replaces the retired populations (NOT decided here)

This lane fixed the mechanism and deliberately did not re-point either
contract at new targets. Two questions are open, and the measurement that
sharpens them is:

| obstruction | removability | still open |
| --- | --- | --- |
| `nat-bitwise-cross-operator-proof-gap` | `producer` | **0 / 2** |
| `nat-bitwise-extensional-duplicate` | `producer` | **0 / 3** |
| `nat-fastfib-recursion-principle` | `not-removable` | 1 / 1 |
| `nat-minfac-algorithmic-divergence` | `not-removable` | 1 / 1 |
| `nat-multichoose-definitional-divergence` | `not-removable` | 3 / 3 |
| `nat-testbit-bool-codomain` | `not-removable` | 5 / 5 |
| `nat-testbit-list-bool-getI` | `not-removable` | 1 / 1 |

**Every fact this compiler still classifies as blocked sits under a
`not-removable` row. Its entire producer-removable frontier is closed.** So:

1. **Sizing.** ADR-1510 rule 1 is that a contract is sized by the frontier
   before it is written, never by what a producer already did — which is
   precisely how both of these came to describe exhausted families. A third
   producer therefore cannot be sized inside this compiler's current scope
   at all; it has to be sized against the live open population
   (`python3 scripts/fact-frontier.py --json`, and ADR-1510's own note that
   the 209-fact `proof-route-only` pool is dominated by `Iff`-headed,
   existential, `Decidable`-instance and higher-order induction-principle
   statements no producer in the current vocabulary addresses). Run the
   frontier FIRST; the shape follows from it.
2. **Lifecycle of a fully-closed obstruction row.** Both `producer` rows now
   have `blocked_fact_ids` that are hard-coded literals and 0/2 and 0/3
   open. Should such a row be dropped from the classification, kept as a
   closed historical record, or given its own `settled` marker the way a
   contract now has one? ADR-0618's precedent (a census dies when its
   subject closes) points one way and this lane's own "retirement preserves
   the record, deletion destroys it" points the other. **Not decided here**
   — the current behaviour is unchanged (the rows stay, with their
   literals), which is the status quo, not an answer.

Neither question is answerable from inside the gate, which is why
`check-obstruction-producers.py` now prints the `EXHAUSTED` line rather than
failing: a checker that fails on a true state manufactures the same
unfalsifiable claim from the other direction.

**Did not run.** No cargo (none expected; every change is Python, bash and
JSON artifacts). Not pushed, per the brief. `just check` / `check.sh` not
run in full — the four gates this change touches were each run by name,
before and after.

| landed | what |
| --- | --- |
| `03e693425` | status stub |
| `4b13f5eab` | the retirement policy, G11, the two controls, regenerated artifacts |
