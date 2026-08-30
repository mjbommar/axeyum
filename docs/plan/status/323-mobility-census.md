# Lane: mobility-census — the gate failed because we succeeded, and it was hiding worse news

<!-- plan-section: lane-status -->

**Lane block (`DONE — 127 violations to 3, graduation audited against the
pinned commit, 49 mutants each killed by exactly one test; the census has NO
SUBJECT and the gate stays red for that reason, mobility-census,
2026-08-30`).**

Commits: `8e4f0c5d9`, `fda827c93`, `a3d790b7a`, `e61fcd288`. **Not pushed.**
ADR: [ADR-0618](../../research/09-decisions/adr-0618-graduation-is-lifecycle-a-census-dies-when-its-subject-closes.md).

## Headline

`python3 scripts/check-mobility-census.py` went from **127 violations to 3**,
and the three are distinct, actionable, and correct. The gate is **still red**,
and it should be: an entire documented capability measurement is currently void.

126 of the 127 were one sentence — `F:<id> is proved in the ledger; the census
is over OPEN facts`. That is the flywheel working. The census wrote 152 fact
rows; 126 of those facts have since been proved.

**Underneath that noise:**

| recomputed from the ledger / nursery / export index | |
|---|---:|
| census rows | 152 |
| … still open | 26 |
| … graduated (open at census time, settled now) | 126 |
| rows the census could EVALUATE | 3 |
| … of those, still open | **0** |
| zero-match clusters (the capability backlog) | 1 |
| … naming at least one still-open fact | **0** |
| entries in `agent-frozen-export-index-v1.json` | 4 |
| … whose fact is still open | **0** |

A frozen statement export is the **only** route to an evaluable goal — a
deliberate choice, argued in `docs/python-2026-08/07-mobility-census.md`: there
is no fallback that parses `formal.statement`, because that would make every
verdict rest on a goal nobody pinned. With zero open facts carrying one, the
census has no subject. **Regeneration cannot fix this**: `just
mobility-census-regen` would produce `evaluable = 0`, which the checker's rule 7
already refuses.

## Answers to the four questions in the brief

**1. What is the census FOR?** Well documented, not inferred.
`docs/python-2026-08/07-mobility-census.md` (slice A7) states it: take the model
out of the loop and ask a purely structural question — for each tactic and each
open fact, does the tactic's precondition hold at that fact's imported goal? It
exists because an earlier slice produced a false-negative rate nobody could
interpret. Its outputs are the tactic reach numbers, the zero-match clusters
(read as the capability backlog), and the headline evaluable/open ratio.

**2. Was the premise "no path to refresh it" right?** No — `just
mobility-census-regen` already existed and is documented in the justfile. The
real problem is worse than a missing refresh path: refreshing does not help.

**3. Is `evaluable=3 / unevaluable=186` a real capability finding or a narrow
definition?** **Real, and the narrowness is the finding.** "Evaluable" means "a
digest-pinned frozen Lean export exists that a producer can import into a real
kernel". The index holds **4 entries, ever** — the `Nat.ModEq` family from one
adapter run. 186 of 189 facts were never looked at, which is why the census is
three-valued: a two-valued one would have reported all 186 as zero-match and
produced a 186-deep capability backlog of pure fiction. The number is not an
artifact of a stingy predicate; it is the export pipeline's actual output.

And it moved in the wrong direction. On 2026-08-24 it was 4 exports over 191
open facts. Today it is the same 4 exports over 146 open facts, all four closed.
126 facts closed by other routes and the export index gained nothing: **the
bottleneck did not narrow, the ledger walked around it.**

**`zero_match_facts=1` and `clusters=1`:** of the 3 evaluable facts,
`F:ml430-nat-modeq-comm-24b71e7a` matched none of the 9 tactics, for three
reasons (`goal-head-is-not-eq-shaped`,
`goal-does-not-unfold-to-an-eq-shaped-head`, `no-hypothesis-binder-to-classify`)
which group into one cluster. The other two (`symm`, `trans`) each matched
`T:modeq-equivalence-combinators`, giving `matched_pairs=2`. So the entire
published capability backlog is one fact — and it is now proved, which is the
third violation the gate reports.

**4. Not green by going blind.** Measured, not asserted:
`python3 scripts/tests/mutation_controls.py mobility-census` → **49 mutants,
every one killed by exactly one test, zero survivors, zero ambiguous anchors,
exit 0**, over a 60-test suite. It was 44 tests with one failing before this
lane.

## What changed

* **Graduation is lifecycle**, counted (`graduated=` on the status line), never
  rejected.
* **Graduation is AUDITED**, not assumed: every row's status is re-read at the
  census's own pinned `git_commit` in one `git cat-file --batch` (0.01 s for
  152 rows). A row already settled there is population padding — `open_facts` is
  the denominator of the headline ratio. All 152 verify as `open` at
  `e2714027`; `audit=ok` says the audit ran. `no-git` (a `git archive` lane
  snapshot, or the mutation harness's `copytree`) prints the skip rather than
  swallowing it; `.git` present with the commit unreachable is a violation.
* **Three recomputed freshness rules** replace the 126 lines, each naming its
  own remedy. Held-out facts are excluded before anything is named, and that
  exclusion has its own control — deleting it would turn this gate into a
  held-out-id leak.
* **Status line carries both sides**: claimed `open`/`evaluable` beside
  recomputed `live`/`graduated`/`live_evaluable`/`live_exportable`/`audit`.

```
MOBILITY_CENSUS|open=189|evaluable=3|unevaluable=186|tactics=9|matched_pairs=2
|zero_match_facts=1|clusters=1|held_out_excluded=37|live=26|graduated=126
|live_evaluable=0|live_exportable=0|audit=ok|violations=3
```

## Three things the mutation harness caught that reading would not have

1. **The harness `copytree`s the tree, so the copy has no `.git`.** My first
   graduation-audit controls audited this repository's own history; under the
   harness all four failed on the BASELINE, and every git guard would then have
   survived its own mutant — coverage that was never measured. They now build a
   throwaway repo holding one fact committed `open` then `proved`.
2. **Two of my fail-closed guards were line-for-line identical to
   `held_out_ids`'s**, so the mutant anchor matched two functions: AMBIGUOUS
   ANCHOR on three mutants, including a **pre-existing one I had broken**.
   Renaming the locals in `exportable_fact_ids` restores 1:1.
3. **Matching violation SENTENCES made one mutant kill two tests** — deleting
   the `no subject` guard makes its sibling `elif` fire with a different
   sentence, so the blunt subprocess ratchet died too. It now matches violation
   KINDS, which keeps it blunt and keeps the ratchet.

## Why the gate is still red, and what clears it

Three violations remain and all three are true:

1. `nursery_sha256` pins a nursery that is no longer on disk (lane 319 landed
   an ADR-0542 amendment today). The census's `held_out_excluded=37` is
   therefore unverifiable. The **leakage scan is unaffected** — it recomputes
   against the current nursery on every run and passes.
2. No open fact carries a frozen export: the census has no subject.
3. The one zero-match cluster names only a proved fact: the published
   capability backlog names no capability.

**Only one action clears 2 and 3: a producer exporting a statement for a fact
that is still open.** Nothing in the checker can do that. Clearing 1 needs a
regeneration, which is worth doing only once 2 is fixed.

## Handoff notes

* **`docs/plan/generated/mobility-census.md` is stale in lockstep** and I did
  not hand-edit it — it is generated by `python -m axeyum.agent mobility`, the
  same command that writes the census, and nothing gates it with `--check`. A
  reader will take its `evaluable=3` as current. It refreshes with the census.
* Retiring the gate was considered and rejected in ADR-0618. It is the only
  instrument measuring the export bottleneck, and it is currently the thing
  reporting that the bottleneck got worse. Retire it only on a decision that
  the frozen-export route is abandoned.
* No new gate steps were added, so `scripts/check-aggregate-scope.sh` is
  unchanged and green (396 / 452 steps, all 66 differences recorded).
* `scripts/check-links.sh` green. `python3 scripts/gen-adr-index.py` run
  (612 rows).
