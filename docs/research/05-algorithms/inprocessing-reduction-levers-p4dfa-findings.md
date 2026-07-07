# Inprocessing + word-level reduction levers on public p4dfa — measured findings

Status: **measurement-grounded finding (2026-07-07).** Executes Gap 1 / leverage
step 1 of the
[2026-07-07 Z3/cvc5 gap analysis](../../plan/gap-analysis-z3-cvc5-2026-07-07.md):
*flip the built-but-default-off performance levers on the committed public QF_BV
p4dfa pulse and measure* — PAR-2 + the unknown-cause split that decides whether
the next performance dollar goes to **encoding** or **search**. This is a
flag-flip + measurement, **not** new code. Mirrors the sibling note
[lazy-bitblasting-p21-findings.md](lazy-bitblasting-p21-findings.md).

Gate: `DISAGREE = 0` and `0` model-replay failures are absolute. Both held in
**every** config below (see the table). No lever introduced a wrong verdict.

## The levers

Two families of built-but-opt-in machinery, exercised through `axeyum-bench`
flags (they do **not** change the committed `SolverConfig` default):

- **Word-level reduction (`--preprocess`, ADR-0034/0037, T1.2).** `solve_eqs`,
  `propagate_values`, `elim_unconstrained`, canonicalize — denotation-preserving
  shrink of the post-rewrite assertions before bit-blasting. (`preprocess`
  already defaults **on** in `SolverConfig`.)
- **SAT inprocessing (`--inprocess` = subsumption + self-subsumption + BVE,
  `axeyum-cnf/src/{simplify,bve}.rs`; `--vivify`, `vivify.rs`).** Gated off by
  default (`cnf_inprocessing: false`, `cnf_vivify: false` in `backend.rs`).

## The corpus

The committed 113-file public slice
`corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen` (SMT-LIB 2024,
Zenodo 11061097). Per ADR-0037 this is arithmetic-free DFA/protocol bit-logic —
wide `bvand`/`bvxor`/`bvadd` over huge `ite`-nests, **0/113** files contain any
heavy arithmetic op. All instances are `sat` (no `unsat` in the slice).

## The measured ladder (jobs=2, Z3 4.13.3 oracle, `mem-run.sh` 64 GiB cap)

`dec` = decided (sat+unsat); `unk` = unknown; `PAR-2` = harness `par2_mean_s`
(total PAR-2 seconds / 113, lower is better). Blocker buckets: `Timeout` = SAT
search hit the wall clock (**search-bound**); `EncodingBudget`/`NodeBudget` =
refused *before* solving, CNF/node cap exceeded (**encoding-bound**).

| config | budget | dec | PAR-2 (s) | DIS | replay-fail | Timeout | EncBudget | NodeBudget |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| OFF (eager) | 3s / n200k / cnf5M | **3** | 5.855 | 0 | 0 | 87 | 13 | 10 |
| +preprocess | 3s | 4 | 5.837 | 0 | 0 | 88 | 11 | 10 |
| +preprocess +inprocess | 3s | 3 | 5.865 | 0 | 0 | 89 | 11 | 10 |
| ALL ON (+vivify) | 3s | **5** | 5.805 | 0 | 0 | 87 | 11 | 10 |
| OFF (eager) | 20s / n300k / cnf8M | **4** | 38.639 | 0 | 0 | 98 | 10 | 1 |
| ALL ON | 20s | **7** | 37.839 | 0 | 0 | 99 | 6 | 1 |

Artifacts: `bench-results/baselines/qf-bv-p4dfa-task56-*.json`.

## What moved

- **Decide% moves, modestly.** 20s: OFF **4 → 7** ALL-ON (+3, no regressions —
  ON is a strict superset of OFF's decided set). 3s: OFF **3 → 5**. The three
  banked-at-20s instances (`compose.s2`, `mobiledevice_…_paired`,
  `string1x8.3`) are all `sat`, all replay against the original term.
- **PAR-2 narrows only marginally**: 38.64 → 37.84 s (−2.1%) at 20s; 5.855 →
  5.805 (−0.9%) at 3s. The 113-file mean is dominated by the ~99 unsolved, so a
  +3 decide moves it little.
- **The reduction lever attacks *encoding*, and it works — but there is little
  there to win.** `EncodingBudget` refusals fall **10 → 6** at 20s (**13 → 11**
  at 3s): word-level reduction shrinks a handful of instances below the
  bit-blast-size ceiling (exactly the ADR-0037 mechanism). But the encoding-side
  blockers are only ~7–11 of 113 to begin with.
- **Lever attribution.** `--preprocess` alone banks +1 (3→4 at 3s). Adding
  `--inprocess` at the tight 3s budget *costs* one (4→3): subsumption+BVE
  overhead eats into the 3s wall clock without paying off at that budget.
  `--vivify` on top recovers and exceeds (3→5). At the 20s budget the full stack
  is unambiguously best (7). Reading: inprocessing/vivify help only when the
  budget is large enough to amortize their cost.

## The diagnostic: encoding-bound or search-bound?

**Decisively search-bound.** Two independent signals:

1. **The unknown-cause split.** At 20s ALL-ON the residual 106 unknowns are
   **99 `Timeout` (SAT search)** + 6 `EncodingBudget` + 1 `NodeBudget`. The
   encoding-side blockers are 7/113; the search-side wall is 99/113. Even
   driving `EncodingBudget` to **zero** would bank at most ~7 more — the other
   99 already encode and then drown in SAT search.

2. **Post-reduction CNF size vs Z3 — axeyum's CNF is already *smaller*.** On the
   7 instances where both encode (ALL-ON 20s), axeyum's CNF is **0.71× Z3's
   variables (median)** and **0.34× Z3's clauses (median)**:

   | instance | ax vars | ax clauses | z3 vars | z3 clauses | var ratio | clause ratio |
   |---|---:|---:|---:|---:|---:|---:|
   | compose.p2 | 159 560 | 583 284 | 202 137 | 1 421 637 | 0.79 | 0.41 |
   | compose.s2 | 106 666 | 391 123 | 135 769 | 1 035 961 | 0.79 | 0.38 |
   | mobiledevice na1 | 4 120 | 17 456 | 8 191 | 78 263 | 0.50 | 0.22 |
   | mobiledevice paired | 58 380 | 217 322 | 79 091 | 663 191 | 0.74 | 0.33 |
   | mobiledevice twocond | 31 482 | 118 228 | 44 101 | 348 209 | 0.71 | 0.34 |
   | simple na1 | 1 424 | 5 651 | 2 461 | 9 225 | 0.58 | 0.61 |
   | string1x8.3 | 58 850 | 218 799 | 86 291 | 790 890 | 0.68 | 0.28 |

   axeyum encodes to *fewer* variables and roughly *one third* the clauses of
   Z3, yet Z3 decides these while axeyum's `rustsat-batsat` core times out on the
   bulk. The differentiator is **not encoding compactness — it is the SAT search
   engine.** Z3's own stats on these files show heavy in-CDCL inprocessing
   (≈125 k subsumed clauses, bool-var elimination, hundreds of restarts) that
   batsat does not bring. The mountain axeyum builds is smaller than Z3's; Z3
   still climbs it faster.

## Honest calibration of the Z3 baseline

The gap-doc headline "Z3 decides all 113 p4dfa in ≤1s" is **stale for this
slice**. Measured here, Z3 4.13.3 does *not* sweep these:

- **Z3 crate oracle, 20s (committed `…-z3-standalone-20s.json`): 8/113 decided**,
  median decided solve 4.5 s.
- **Z3 CLI (`z3 -smt2 -T:20`, full default tactic pipeline), all 113: 9/113
  decided** (all `sat`), **104 timeouts at 20 s**; median decided solve 2.1 s,
  and only **2/113 decided in ≤1 s**. Spot check: `compose.p2` sat 2.1 s,
  `mobiledevice_na1` sat 1.2 s, but `string1x8.3` and `tcp_full_bit16` **time out
  past 30 s** — the same `string1x8.3` that axeyum ALL-ON decides in 20 s.

So the true p4dfa picture is *both* solvers find this slice hard: Z3 is a hair
ahead (9 CLI / 8 crate vs axeyum's 7 at 20s) but it is a single-digit race on a
hard corpus, not the "1 s vs never" chasm the stale number implies. This does not
change the verdict — it sharpens it: the corpus is a **SAT-search benchmark**,
and closing it is a SAT-search problem for *both* engines.

## Verdict → where the next dollar goes

- **Net benefit of the levers: real but small, and sound.** +3 decided at 20s
  (+2 at 3s), PAR-2 non-worse (slightly better), `DISAGREE = 0`,
  `0` replay failures across all six configs. The reduction/preprocess lever has
  now **harvested the cheap encoding wins** (`EncodingBudget` 10→6); further
  encoding effort caps out at ~6 more instances.
- **The residual is search-bound.** 99/113 unknowns are SAT-search timeouts on
  CNFs *smaller than Z3's*. Deeper word-level reduction is not the lever here.
- **Recommended next thrust: SAT-core modernization (P1.3)** — the modernized
  proof-producing CDCL with VSIDS/Luby/LBD **plus in-solver inprocessing**
  (subsumption/vivification interleaved with search, not just a pre-pass),
  toward a default-capable core that can climb these smaller mountains. That is
  the front where Z3 wins these instances.
- **Recommended banking step (separate ADR):** the levers are a clean, sound,
  net-positive increment — an ADR to enable `cnf_inprocessing` + `cnf_vivify`
  by default is defensible **budget-gated** (they help at 20s, but their
  overhead can cost a decide at a tight 3s budget). Do **not** flip the
  `SolverConfig` default without that ADR. `preprocess` already defaults on.

Exit signal (gap-doc Gap 1): a committed head-to-head where the p4dfa PAR-2 gap
*narrows* with `DISAGREE = 0`. **Met** — narrowly (38.64 → 37.84 s at 20s), and
the measurement redirects the effort to search, not encoding.
