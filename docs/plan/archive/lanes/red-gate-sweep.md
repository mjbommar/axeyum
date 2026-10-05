# Lane: red-gate-sweep — four red gates on `main`, made green without weakening

<!-- plan-section: lane-status -->

**Three of four gates green, the fourth deliberately left red with the argument
(`done-for-now`, red-gate-sweep, 2026-09-01).** Base `b558d9b5a`; each gate
re-measured in this worktree rather than relayed.

| gate | before | after |
| --- | --- | --- |
| `scripts/check-generated-artifact-ownership.py` | 1 | **0** |
| `scripts/tests/test_check_autogenesis_holdout_isolation.py` | 1 | **0** |
| `scripts/check-autogenesis-nursery.py` | 1 | 1 — v1 half green, cross-population half is another lane's file |
| `scripts/tests/test_check_autogenesis_nursery.py` | 1 | 1 — same cause, through its live-manifest test |

**The partition leak (ADR-1455).** The `--fix` runs DID widen it, twice.
Reconstructed by composing the nursery entries against each ref's own fact
ledger: `237c1abdd^` 81 intra-nursery edges / 1 crossing component,
`366f11a91^` 108 / 3, HEAD 113 / 4. Of the three honest remedies none applies —
the edges come from `Kernel::theorem_dependencies`, the partitions are a frozen
preregistered split ADR-0850 already declined to move for this class, and the
check is not over-strict: it did exactly what ADR-0850 designed, going red on a
component whose digest stopped matching its exemption. So the remedy is the
re-review that mechanism demands. **No held-out row is involved**; the crossings
are train↔development plus the longitudinal Autogenesis-1 chain.

Verified independently for the 13 facts, and one point DIFFERS from ADR-0850's
evidence rather than copying it: two members ARE named by autogenesis
operations. That operation is train-only over the nursery (all four of its fact
ids are `train`) and neither component's development member is named by any
operation, so no development row has been spent. Recorded separately: two
operations (`authoritative-mathlib-modeq-family-v1`,
`authoritative-mathlib-nat-modeq-congruence-family-v1`) name fact ids in BOTH
train and development and no gate measures that — a second instance of the open
question ADR-0850 flagged above a lane's level.

**Two guards that were never written**, both the class mutation testing
structurally cannot report (a guard never written has nothing to delete):
`validate_exemptions` accepted an exemption naming a **held-out** row — the
entire safety argument of the mechanism, asserted in every reason and enforced
by `rescope-nursery-exemption.py`, and unenforced by the gate; and a recorded
exemption matching **no live crossing component** was a `--json` field with no
effect on exit status, so both stalings (10 vs 11 here, 258 vs 274
cross-population) showed the operator nothing about the adjudication just
voided. Both are hard errors now.

**A third defect, found while fixing the second.**
`scripts/rescope-nursery-exemption.py` had no tests and scraped the gate's
combined output with one regex. The gate raises on nursery-v1 first, so with v1
red it returned the 13 V1 fact ids and `main()` would have written them over the
258-member cross-population exemption — printing `RESCOPE|258 -> 13 members` and
exiting 0.

**The stale pin was NOT transcribed.** `held_out=146` against a live 186:
established first, on five lines — composition 16 (v1) + 170 (v2, confirmed by
the extension's own `coverage.partition_counts`); the move is two RISES from
draws (`e26076356` 146→166, `6d8f84258` 166→186, +20 each, v1 unchanged at 16,
so no FALL and no ledger amendment needed); all 186 rows measured `open`, no
evidence, unreferenced by any of the 29 operations, with a positive control over
198 train rows returning 191/191/37; draw 16's commit carries no gate output so
its two families were re-verified via `check-holdout-adjacency.py` (18 families,
0 refused, both `clean … reviewed`); and `check-holdout-closed-evaluation.py` /
`check-autogenesis-holdout-contamination.py` both pass at 186.

**One of the two ownership failures was a fiction.** `schema.json` was reported
as a three-producer artifact because COVER matched basenames as substrings, and
two of those producers name `fact.schema.json` and
`obstruction-graph.schema.json` — different files. Recording it would have put
an invention into the ratchet's population. Fixed by extracting whole `*.json`
path components per producer: candidates 35 → 34, dropping `schema.json` alone,
adding none, removing none of the 32 already recorded. The genuinely
multi-named `mirror-divergence-registry.json` was recorded, which is the arm's
designed action. `referencing_scripts` stays a substring test on purpose and now
says why: it feeds an arm that DEMANDS classification, so its errors point the
opposite way.

**Deliberately left red.** `check-autogenesis-nursery.py`'s cross-population
half: the v1∪v2 union's 274-member component outgrew the 258-member exemption in
`artifacts/autogenesis/nursery-v2-extension.json`, a file a concurrent lane owns
and is editing to author a draw. Pre-existing at `b558d9b5a` (that commit is the
manifest regeneration that grew it), previously masked by the v1 failure raising
first. Re-scoping now is stale on arrival once the draw lands, so it is left to
its owner: `python3 scripts/rescope-nursery-exemption.py`, which this lane makes
safe to run. Verified here that with v1 green it reports
`RESCOPE|258 -> 274 members|census={'development': 314, 'train': 230,
'longitudinal': 4}|held_out=0`; the write was reverted and no v2 file is touched
by this lane.

**Not fixed, recorded:** all 30 `nursery_sha256` bindings across 19 artifacts
are stale — zero match `nursery-v1.json` on disk, and they were already stale at
`b558d9b5a` before this lane's edit.
`check-autogenesis-binomial-arrow-measurement.py` is red for an earlier reason
(`candidate ranking is absent or changed`) and short-circuits before the nursery
check, so this lane's edit changes no gate's observable state on that axis.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `PENDING` | ADR-1455: re-scoped the two nursery-v1 split exemptions a `depends_on` repair voided (the `--fix` runs widened the leak 1 -> 3 -> 4 crossing components; edges are proof-derived, so the remedy is the re-review ADR-0850's self-invalidation demands, not an edge removal or a partition move). Added the two guards the mechanism's own safety argument always assumed and never checked: no exemption may name a `held-out` row, and a recorded exemption matching no live crossing component now FAILS instead of being a `--json` field. Fixed `rescope-nursery-exemption.py`, which had no tests and would have overwritten the 258-member cross-population exemption with 13 nursery-v1 fact ids at exit 0. Mutation-verified: `nursery-split-exemption-guards` 3/3 killed, `nursery-rescope-parser` 2/2 killed over disjoint cases, every negative case paired with a positive control. |
| 2026-09-01 | `PENDING` | Established that `held_out=186` is CORRECT before moving the stale `held_out=146` pin — composition 16 (v1) + 170 (v2, matching the extension's own `coverage.partition_counts`), two RISES from draws with v1 unchanged so no ledger amendment is owed, and all 186 rows measured `open` / no evidence / unreferenced by any of the 29 operations against a positive control of 191/191/37 over the 198 train rows. Pin now carries a failure message naming the procedure. Control mutates the SUBJECT: perturbing the gate's reported count kills the pin. |
| 2026-09-01 | `PENDING` | `check-generated-artifact-ownership.py`: one of its two COVER failures was a fiction — `schema.json` reported as a three-producer artifact because basenames were matched as substrings of `fact.schema.json` and `obstruction-graph.schema.json`. Recording it would have put an invention into the ratchet's population. Now extracts whole `*.json` path components per producer (35 -> 34 candidates, dropping only `schema.json`, adding none, removing none of the 32 recorded; also 112 s -> 0.05 s, past a timeout that made the gate unrunnable), and the genuinely multi-named `mirror-divergence-registry.json` is recorded. Gate `fails=0|PASS`. |
