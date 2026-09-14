# `inst-select` — are the instances a refutation needs reachable by e-matching?

**2026-09-13.** [ADR-1995] closed the budget question on `UFLIA`/`UFNIA` at 0 of
87 and handed over *"the vein is instance selection, not clock."* This lane
tested that, and specifically the named suspicion behind it — that a refutation
may need terms **pure e-matching structurally cannot generate**, making the
missing capability enumerative or model-based instantiation over small domains.

**It does not survive.** The full argument is [ADR-2005]; this directory holds
the artifacts and the scripts that regenerate every number from them. Nothing
below is transcribed.

## The headline

- **Of the 115 winnable files cvc5 decides, e-matching alone decides 111 the same
  way — 97 %, Wilson 95 % `[91 %, 99 %]`.** 0 of 115 need the combination of
  e-matching and the other strategies.
- On the brief's own exemplar the ground applications the refutation needs
  (`(pow2 0)` … `(pow2 3)`) are **written in the query as applications**, and
  **our own ground set already contains every one of them.**
- The defect is that we substitute the **first-inserted** member of a matched
  e-class rather than the smallest. Fixing it behind a lever more than halves
  the resulting term bloat and **decides nothing**: measured **+0**, and all
  three rows that moved in any single pass are **UNSTABLE**.

## Reproducing

    # M1 -- the reference ablation (this is the load-bearing measurement)
    python3 refabl-summarize.py --outdir refabl

    # M2 -- what cvc5 instantiated with, bucketed Q / G / N / S
    python3 bucket-summarize.py --json classify.json

    # M3 -- our baseline on this lane's base, ADR-1941 classification
    python3 ours-summarize.py --outdir ours

    # The A/B, and its three-pass stability re-check
    python3 ab-summarize.py --outdir ab --divisions UFNIA UFLIA --controls UF
    python3 stability-summarize.py --outdirs ab ab2 ab3 --division UFLIA

`classify.json` is rebuilt by `classify-instantiations.py`, which needs the cvc5
dumps and our ground dumps on `/nas3`; the committed JSON is the record.

## Layout

| path | what it is |
|---|---|
| `PREREGISTRATION.md` | method and decision rules, committed **before** the population was measured |
| `refabl/` | M1 — cvc5 in four arms over all 129 winnable rows, per shard |
| `ours/` | M3 — our verdict, route fields and give-up detail per row |
| `classify.json`, `BUCKETS.md` | M2 — every instantiating term bucketed |
| `ab/`, `ab2/`, `ab3/` | three independent interleaved A/B passes |
| `AB.md`, `STABILITY.md` | generated summaries of those |
| `*.sh`, `*.py` | the runners and summarizers |

## Reading the artifacts without being misled

Each of these cost a wrong number here before it was written down.

- **The four cvc5 arms are not a partition.** A file may refute in several, and
  only a *success* under `ematch` is load-bearing — a failure there says nothing
  about e-matching in general, because cvc5's is one implementation with its own
  trigger inference.
- **`NONE` is not `unknown`.** It means no verdict-shaped line: crash, OOM or
  watchdog, none of which is a solver opinion. All 7 in M1 were re-run
  individually and every one is cvc5's own `--tlimit` firing.
- **Bucket N is contaminated.** cvc5 prints `(+ -1 (typeof S))` where the source
  writes `(- (typeof S) 1)`; 28.6 % of N terms have an arithmetic head. `BUCKETS.md`
  publishes the bucket both ways and the classifier records the count as a field
  rather than reclassifying on its own judgement.
- **`--dump-instantiations` is a SUPERSET.** It prints what cvc5 *produced* on
  the winning run, not a minimised set it *needs*. A small N is strong evidence;
  a large one is weak.
- **One A/B pass is not a result on this division.** The base arm alone scores
  72 / 75 / 74 across three passes — a band of 3 files — so a single pass here
  reported `+1` and `−2` from identical code.
- **Lever polarity**: `AXEYUM_QINST_SMALLEST_WITNESS` **ships OFF**. The base arm
  runs with the variable *unset*; `ab-run.sh` says so in its header because
  copying the wrong polarity measures the shipped arm against itself.

[ADR-1995]: ../../docs/research/09-decisions/adr-1995-the-instantiation-loops-verdict-is-not-monotone-in-its-budget.md
[ADR-2005]: ../../docs/research/09-decisions/adr-2005-the-instances-are-e-matchable-and-we-already-build-them.md
