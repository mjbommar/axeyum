# lia-warm-decider A/B, 2026-09-08

Raw data behind
[`docs/research/12-performance/lia-warm-decider-2026-09-08.md`](../../docs/research/12-performance/lia-warm-decider-2026-09-08.md).

## What is here

| file | what it is |
| --- | --- |
| `ab.py` | the runner. Three arms from ONE release binary, arm order alternating per repetition so machine drift is shared rather than landing on whichever arm ran second. |
| `score.py` | the scorer. Reports verdict changes first, excludes files the online theory never entered from the throughput figures (and says how many), and refuses to average a decided-verdict disagreement into a timing number. |
| `perfile.py` | every row, because a summary that cannot be checked against its own rows is a claim. |
| `mutate.py` | the five staleness/drift mutations applied to the warm decider, one at a time, in a `lane-snapshot.sh` scratch tree. |
| `mutation-results.txt` | baseline plus three mutants. |
| `mutation-results-2.txt` | the remaining two, under an external wall bound, because `no-tightening` does not fail — it grinds. |
| `stage1-8s.json` | every run: verdict, wall time, and the full `; lia-warm` counter set. |
| `stage1-8s.summary.txt` | `score.py` output. |
| `stage1-8s.perfile.txt` | `perfile.py` output. |
| `engaged.txt` | the 29 of 85 loss files where the online `LIA` theory is actually entered. |

## Reading the numbers

* **The population is budget-bound.** Every file here is one axeyum loses, so in
  every arm nearly every run spends its whole timeout. Wall time is pinned to
  the budget: it is reported and it is NOT the score.
* **The score is live-set decisions in the same budget**,
  `theory_offline_checks + theory_filter_answers`. Counting only the offline
  half scores the rational filter's contribution as zero work, which is how the
  hypothesis this lane was given came to be wrong.
* **56 of 85 files never enter the online theory at all** and are excluded from
  every throughput figure. They are reported, not dropped.

## Conditions

Host s4, load average 8-11 throughout (a second lane was running a 24 s parity
sweep on the same box). Release binary at `ca7717c5e`. 8,000 ms budget, one
repetition per arm per file. The alternating arm order is what keeps the
contention from landing on one arm; it does not make the absolute wall times
comparable to an idle run, and no claim here rests on them.
