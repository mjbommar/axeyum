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

Detail moved to [`../notes/323-mobility-census.md`](../notes/323-mobility-census.md).

