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
| `verify-extraction.py` | the mechanical check on the merge's soundness-critical half: inlining `decide_int_constraints` back into `lia_simplex_capped` must reproduce `origin/main`'s function token for token. A one-shot check against `d0e06e8f9`; re-run it if that resolution is ever revisited. Reported IDENTICAL. |
| `mutation-results-merged.txt` | the whole battery re-run against the merged tree. `no-tightening`'s anchor named a function the merge renamed, so it matched zero places — the driver reported ANCHOR MISS rather than a pass, which is the only reason that was caught. |
| `mutation-run.sh` | the driver: every mutant under an external wall bound, because `no-tightening` does not fail — it grinds, and "the suite never returned" is a different kind of kill, not a pass. |
| `mutation-results.txt` | first pass, baseline plus three mutants. |
| `mutation-results-2.txt` | the remaining two from that pass. |
| `mutation-results-shipped.txt` | the whole battery re-run at the end against the code that SHIPS. The tests changed after the first pass (the theory differential was parameterized over the filter setting), so the earlier result was about a tree that no longer exists. |
| `stage1-8s.json` | every run: verdict, wall time, and the full `; lia-warm` counter set. All 85 loss files, 8,000 ms. |
| `stage1-8s.{summary,perfile}.txt` | `score.py` and `perfile.py` output for stage 1. |
| `stage2-24s.json` | the 29 engaged files at the 24,000 ms parity budget. |
| `stage2-24s.{summary,perfile}.txt` | the same two views for stage 2. |
| `xs2434-repeat.json` | `xs_24_34.smt2` alone, three repetitions per arm. Stage 2 showed it `unknown` in two arms and `sat` in a third, which would read as a coverage change; the repeat is `sat` in every arm every time, and in the arm that "won" the warm decider recorded ZERO checks. A host artefact, recorded rather than quoted. |
| `engaged.txt` | the 29 of 85 loss files where the online `LIA` theory is actually entered (pre-merge, 8 s). |
| `merge1-24s.json` | **the result that supersedes the rest**: the whole 85-file population at 24 s, three arms, on idle s5 at `39c493ba5`. |
| `merge1-24s.summary.txt` | `score.py` output for it. |
| `merge2-24s.{json,summary,attribution}` | the same sweep on a DIFFERENT host (s6) and a different tree (`1a01d335d`). Every figure the conclusion rests on reproduces, including the contested filter count to within 1 of 46,193. |
| `merge1-24s.attribution.txt` | `attribute.py` output: where the offline decider's entries actually come from. This is the file that explains the flat ratio — the warm decider serves 9.7% of them. |
| `attribute.py` | the attribution. Written because `offline_calls` is a denominator the warm path can only touch a tenth of, and a ratio over a denominator the change cannot move is not a measurement of the change. |
| `off-equivalence.{py,json}` | pristine `origin/main` vs this lane with `AXEYUM_LIA_WARM=off`, two binaries, 91 files: 0 verdict mismatches, 0 runs where the `off` arm entered the warm decider. Returns non-zero if nothing was decided, so it cannot pass vacuously. |

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
sweep on the same box). Release binary at `ca7717c5e` for both stages. Stage 1:
all 85 loss files, 8,000 ms, one repetition per arm. Stage 2: the 29 engaged
files, 24,000 ms, one repetition per arm. The `xs_24_34` repeat used the binary
at `68258cf23`, where the arm names changed (`filter` became the default and the
no-filter arm became `nofilter`). The alternating arm order is what keeps the
contention from landing on one arm; it does not make the absolute wall times
comparable to an idle run, and no claim here rests on them.
