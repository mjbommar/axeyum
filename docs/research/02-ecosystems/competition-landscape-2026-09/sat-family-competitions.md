# The Propositional / Boolean-Optimization Competition Landscape, 2022–2026

A sourced catalog of every competitive arena adjacent to a proof-producing CDCL SAT
core, written for **axeyum** — a Rust stack whose SAT surface today is:

- `crates/axeyum-cnf/src/proof_sat.rs` — a proof-producing pure-Rust CDCL core
  (1-UIP, two-watched-literal), emitting DRAT (ADR-0012);
- `crates/axeyum-cnf/src/drat.rs` — an independent DRAT checker (RUP + RAT), with a
  streaming sink (ADR-0011, ADR-0381);
- `crates/axeyum-cnf/src/lrat.rs` — an independent LRAT checker **and** a DRAT→LRAT
  elaborator, currently **RUP-only** (RAT additions rejected);
- `crates/axeyum-cnf/src/{gf2,xor_*}.rs` — GF(2)/XOR reasoning with a per-query DRAT
  refutation for XOR-Gaussian UNSAT;
- `crates/axeyum-cnf/src/alethe.rs` — an Alethe (veriT/cvc5) proof checker;
- `crates/axeyum-bench/examples/cnf_core_bench.rs` — the **only** external comparison:
  byte-identical DIMACS across the native core, CaDiCaL, Kissat (and optionally
  BatSat / Z3), on one small CNF slice.

Section 9 is the gap analysis: what axeyum has not entered, and what entry would cost.

**Reading convention.** Lines marked **[C]** are confirmed against a primary source I
fetched (competition site, results slides, spec, or repo). Lines marked **[I]** are
inference or secondary reporting and should be re-checked before being quoted as fact.

---

## 1. SAT Competition

Home: <https://satcompetition.github.io/>. The series index lists 17 SAT Competitions
(2002–), 5 SAT Races (2006, 2008, 2010, 2015, 2019), 1 SAT Challenge (2012), and 3
events in the 1990s. **[C]** (SAT Competition 2025 results slides, slide 2.)

**As of 2026-09-06, SAT Competition 2026 has already run** — results were presented
2026-07-23 and revised 2026-08-10. **[C]**

### 1.1 Track structure by year

| Year | Tracks run | Notes |
|---|---|---|
| 2021 | Main (+ No-Limits, CaDiCaL-Hack sub-tracks), **Crypto**, **Incremental Library**, Parallel | Crypto track = 200 cryptography benchmarks, 100 SAT / 100 UNSAT, 5000 s **[C]** |
| 2022 | Main (+ CaDiCaL Hack, No-Limits), **Anniversary**, Parallel, Cloud | Anniversary = "20 Years of SAT Competition" **[C]** |
| 2023 | Main, No-Limits, Parallel, Cloud, **CaDiCaL 1.5.3 Hack** | First year of *multiple verified proof checkers* **[C]** |
| 2024 | Main, No-Limits, Parallel, Cloud, **CaDiCaL 1.9.4 Hack** | **[C]** |
| 2025 | **Main (sequential) and Parallel only** — Cloud skipped ("too demanding for AWS organizers") | New LMU BenchCloud host; parallel timeout cut 5000 s → 1000 s **[C]** |
| 2026 | Main, Parallel, **Experimental** (renamed from No-Limits), Cloud, plus **AI-Generated / AI-Tuned sub-tracks** in each | First year on NHR@KIT HoreKa **[C]** |

Standing rules across all years **[C]** (2022/2023/2024/2025/2026 results slides, "Key
rules" slide, identical wording):

- Certified UNSAT results by proof logging; **"instance is 'not solved' if the proof
  checker times out."**
- Disqualification for a buggy solver: an incorrect model, or (from 2024) an incorrect
  proof.
- Mandatory solver description **and open source**.
- Ranking is **PAR-2** — runtime, plus twice the timeout for every unsolved instance.
- **BYOB** (Bring Your Own Benchmarks): at most 20 instances per participant are used.

### 1.2 Resource limits

| Track | Timeout | Memory / hardware |
|---|---|---|
| Main 2023 | 5000 s CPU | 128 GB, StarExec **[C]** |
| Main 2024 | 5000 s | 128 GB **[C]** |
| Main 2025 | 5000 s | **30 GB** RAM, LMU BenchCloud (SoSy Lab Munich) **[C]** |
| Main 2026 | 5000 s | **32 GB**, HoreKa Blue @ NHR@KIT, 76-core Xeon Platinum 8368, 7 benchmarks in parallel per node **[C]** |
| Proof-checker tool chain (2023, 2025) | **45 000 s** | — **[C]** |
| Parallel 2023/2024 | 5000 s wall | AWS `m6i.16xlarge`, 64 vCPU / 256 GB **[C]** |
| Parallel 2025/2026 | **1000 s** wall | AWS `m6i.16xlarge` **[C]** |
| Cloud 2023/2024 | 1000 s wall | 100 × AWS `m6i.4xlarge` (16 vCPU, 64 GB each), MPI + SSH **[C]** |
| Cloud 2026 | **200 s** wall | 100 × `m6i.4xlarge` **[C]** |

Main track benchmark set size is stated as **300–600 problems** in the 2023–2026 rules
**[C]**; the actual sets were 400 (2022), 400 (2023), 400 (2024: 300 unused + 100 random
Anniversary-2022), 400 (2025). **[C]**

### 1.3 Proof requirements and checkers — the axis that matters most here

This is the single most important part of the landscape for axeyum, because SAT
Competition has done exactly what axeyum's identity statement claims: made the *checker*
the arbiter.

| Year | Proof regime |
|---|---|
| ≤2022 | **DRAT only.** "Certified results of unsatisfiability using DRAT proof logging." Checker timeouts (45 000 s) still counted as **solved**. **[C]** |
| 2023 | **Open call for proof checkers; checkers must be formally verified.** Participants *pick* their checker. Three offered: **cake_lpr** (verified LRAT + LPR, Tan/Heule/Myreen), **GRAT** (Lammich), **VeriPB + CakePB** (verified pseudo-Boolean). Checker timeout ⇒ **unsolved**. **[C]** |
| 2024 | Available checkers: **GRAT, DPR-trim, VeriPB**. Models verified with **GRAT in "sat mode"**. Correct result + *wrong* certificate ⇒ **disqualified** (tightened from "unsolved" in 2023). **[C]** |
| 2025 | Same three options presented as cake_lpr / GRAT / VeriPB+CakePB. Solver 5000 s, checker chain 45 000 s. **[C]** |
| 2026 | Available checkers: **GRAT, DPR-trim, VeriPB, SR**. **[C]** Proof-checker submissions were a first-class deadline (2026-03-20), separate from solvers. **[C]** |

The 2022→2023→2024 tightening of the certificate rules, verbatim from the slides **[C]**:

| Result | Certificate | SAT | UNSAT (2022) | UNSAT (2023) | UNSAT (2024) |
|---|---|---|---|---|---|
| Wrong | Wrong | Disq. | Disq. | Disq. | Disq. |
| Correct | Timeout | Disq. | **Solved** | Unsolved | Unsolved |
| Correct | Wrong | Disq. | Unsolved | Unsolved | **Disq.** |

2024 proof-checking statistics **[C]** (2024 slides, "Certificates"): *no wrong
certificates were found* — no buggy solvers. Checker timeouts: GRAT 2 (on the same
instance), DPR 17 (on ten instances), VeriPB 25 (on 25 instances).

2025 organizer note **[C]**: "Proof logging & checking matured over the last decade —
checking time is roughly similar to solving time. However, **LRAT checking is much
faster**. Should we have a track that combines solver and checker time?" — an open
design question that would directly favor a solver emitting LRAT with hints.

**The SR checker (new for 2026).** SR = *substitution redundancy*, a generalization of
PR and RAT that succinctly expresses symmetry breaking. Formats: **DSR** (no hints) and
**LSR** (with unit-propagation hints), both backwards compatible with the RAT/PR
formats. The competition's SR checker is **the first verified LSR checker, proved
correct in Lean 4** (Codel, Avigad, Heule — FMCAD 2024). The paper states plainly:
"Currently, no solver supports SR reasoning." **[C]**

Output format (unchanged since the 2000s) **[C]**: solution line `s SATISFIABLE` /
`s UNSATISFIABLE` / `s UNKNOWN`; model on `v ` lines, space-separated non-contradictory
literals, terminated by `0`, each line ≤ 4096 characters; UNSAT proof written to
`proof.out`. Exit codes 10 = SAT, 20 = UNSAT, anything else = error. **[C]** The 2025
organizers noted parallel/cloud solvers *do not* follow these conventions and proposed
adding MEMOUT/TIMEOUT codes. **[C]**

### 1.4 Winners

Only non-VBS entries are listed; "VBS" (Virtual Best Solver) tops every published table
and is an oracle, not a submission.

**2022** **[C]** — Main 400 benchmarks (300 new + 100 old), 52 sequential / 10 parallel
/ 2 cloud solvers; Anniversary 5355 benchmarks, 29 sequential / 6 parallel / 2 cloud.

| Track | 1st | 2nd |
|---|---|---|
| Main sequential | Kissat_MAB-HyWalk — PAR-2 3334.22, 290 solved | kissat_inc — 3351.93, 290 |
| Main parallel | parkissat-rs — 2105.19, 326 | nps — 2799.64, 303 |
| Main cloud | mallob-kicaliglu — 344.78, 341 | paracooba — 1025.51, 221 |
| Anniversary sequential | Kissat_MAB_ESA — 2806.15, 4029 | kissat-sc2022-bulky — 2810.70, 4038 |
| Anniversary parallel | mallob-ki — 1992.46, 4400 | mergesat-aws — 2689.75, 4076 |
| Anniversary cloud | mallob-kicaliglu — 279.27, 4687 | paracooba — 725.07, 3619 |
| No-Limits | kissat_pre — 3687.68, 206 | kissat_inc — 3965.90, 198 |

**2023** **[C]** — Main 400 benchmarks (306 new + 94 old), 49 sequential / 15 parallel /
3 cloud solvers.

| Track | 1st | 2nd |
|---|---|---|
| Main SAT+UNSAT | **SBVA-CaDiCaL** — 3274.01, 284 | KissatMabProp-PrNosym — 3596.73, 272 |
| Main SAT | SBVA-CaDiCaL — 2337.38, 122 | KissatMabProp-PrNosym — 3376.46, 108 |
| Main UNSAT | **SBVA-Kissat** — 3852.39, 146 | MapleCaDiCaL LBD-990-275 — 4147.84, 138 |
| Parallel | PRS — 2272.36, 320 | Mallob64 — 2746.30, 301 |
| Cloud | Mallob1600 — 426.10, 328 | PRS-Dist — 530.92, 305 |
| CaDiCaL Hack | **CaDiCaL-vivinst** (Biere, Fleury, Pollitt) | — |
| Special prize (ranking if checker timeouts counted as solved) | **BreakID-kissat** (Bogaerts, Nordström, Oertel, Yıldırımoğlu) | — |

**2024** **[C]** — Main 300 previously unused instances (195 from 2024, 31 from 2023, 74
from 2022) + 100 random Anniversary-2022 instances; 33 solvers/configurations: 14 Main
(+7 No-Limits), 8 parallel, 3 cloud.

| Track | 1st | 2nd |
|---|---|---|
| Main SAT+UNSAT | **kissat-sc2024** — 2788.13, 306 | Kissat_MAB-DC — 3435.23, 290 |
| Main SAT | kissat-sc2024 — 1270.53, 153 | Kissat_MAB-DC — 2104.59, 146 |
| Main UNSAT | kissat-sc2024 — 2077.11, 153 | Kissat_MAB-DC — 2740.35, 144 |
| Parallel | saoudi-painless-par2 — 1397.76, 353 | saoudi-painless-par1 — 1418.19, 353 |
| Cloud | **schreiber-mallobsat** — 278.87, 356 | qian-prs-distributed — 400.36, 330 |

Kissat swept all three gold medals in the main track. **[C]**

**2025** **[C]** — Main track 400 benchmarks (184 new submissions: 73 SAT / 89 UNSAT / 22
UNK; 116 unused old; 100 Anniversary-track submissions), **26 sequential** and **8
parallel** solvers. No Cloud track.

| Track | 1st | 2nd | 3rd |
|---|---|---|---|
| Main sequential (ALL) | **AE-Kissat-MAB** — 2264.73, 327 | Kissat-public — 2423.38, 321 | Kissat-VSA — 2478.45, 317 |
| Main SAT | AE-Kissat-MAB — 715.921, 173 | Kissat-public — 1397.09, 163 | Kissat-CURE — 1525.91, 159 |
| Main UNSAT | **CaDiCaL-SC2025** — 2327.00, 161 | Kissat-VSA — 2335.54, 160 | AE-Kissat-bump — 2358.10, 159 |
| Parallel (ALL) | **MallobSat** — 394.56, 337 | PL-PRS-Kissat — 406.87, 334 | PRS-SC25-SBVA — 457.19, 331 |
| Parallel SAT | PL-PRS-Kissat — 191.21, 171 | MallobSat — 201.04, 169 | PRS-SC25-SBVA — 214.26, 172 |
| Parallel UNSAT | MallobSat — 231.65, 168 | PL-PRS-GASPI-Kissat — 266.85, 164 | PRS-PaKisInc — 327.21, 161 |

2025 also produced a cautionary operational note: on the new 30 GB LMU host, "several
runs crashed at 20 GB allocation — parsing issues on some huge instances, **proof
checking issues on some big proofs**." **[C]**

**2026** **[C]** — 1028 benchmark submissions (855 from 15 participating teams, >600 from
a single team; 173 from four non-participant providers). 33 sequential solver
submissions: 17 in Main, 12 AI-generated/AI-tuned, 2 Experimental, 2 disqualified for
buggy models / wrong results. 12 parallel submissions (10 Parallel, 2 Cloud of which one
disqualified).

| Track | 1st | 2nd | 3rd |
|---|---|---|---|
| Main (ALL) | **satsuma-iter+kissat** (Anders, Codel) — 3647.02, 276 | Kissat-MAB-HyPre — 3996.29, 255 | EDA-Kissat-v2 — 4469.34, 240 |
| Main SAT | satsuma-iter+ae-kissat-mab — 3430.95, 136 | Kissat-MAB-HyPre — 3445.92, 134 | AE-kissat-HUCB — 3507.77, 133 |
| Main UNSAT | satsuma-iter+kissat — 1743.84, 149 | Kissat-MAB-HyPre-V2 — 3073.61, 121 | EDA-Kissat-v3 — 3843.30, 111 |
| Main SAT — **AI category** | **Lymphosat** (Harrison Green) — 2813.50, **146** (beats the human 1st place on solved count) | — | — |
| Parallel (ALL) | **mallob-quick** — 346.504, 300 | prs-mergesat — 401.118, 282 | prs-sc26 — 453.758, 263 |
| Parallel SAT | PL-Kissat — 342.003, 148 | hypre — 346.172, 146 | prs-mergesat — 347.677, 147 |
| Parallel SAT — AI category | hypre-evolve — 340.434, 145 | — | — |
| Parallel UNSAT | mallob-quick — 182.648, 156 | prs-mergesat — 319.434, 135 | prs-sc26 — 419.426, 119 |
| Cloud | mallob-quick (only real participant; one of two entrants disqualified) | — | — |

New in 2026 **[C]**: the benchmark selection script is published *before* the submission
deadline, with the seed derived from a hash of the submitted instances, so "even
organizers cannot predict which instances will be selected." A deterministic version was
re-released 2026-07-15 after two non-determinism sources (unsorted unique-value
iteration and Python's randomized `hash()`) were found. The FLoC 2026 Olympic Games
"Open Source Contribution Award" went to Armin Biere. Organizers flagged two discussion
points: whether AI-generated solvers memorizing benchmark families is a problem
(Lymphosat used **over 100 family-specific LLM-generated solvers, mostly specialized
preprocessing, including proofs**), and disqualifying solvers that crash.


---

## 2. Benchmark sources: where the CNFs actually live

| Source | What | URL |
|---|---|---|
| **GBD — Global Benchmark Database** | The canonical, annotated, queryable index. Contexts: **CNF, WCNF, OPB**. Tracks span `main_2006`…`main_2026`, `application_2009–2016`, `random_2002–2018`, `crafted_2005–2016`, `industrial_2002–2007`, `handmade_2002–2004`, `agile_2016–2017`, `planning_2020`, `crypto_2021`, `mus_2011`, `portfolio_2012`, `submissions_2022–2026`. **[C]** | <https://benchmark-database.de/> |
| Download mechanism | Each track page emits a `.uri` file: `wget --content-disposition -i track_main_2025.uri`. **[C]** | <https://benchmark-database.de/?track=main_2025&context=cnf> |
| SAT Comp 2024 main track | 400 CNF files, DIMACS, Zenodo, published 2025-03-27, DOI `10.5281/zenodo.15095752` **[C]** | <https://zenodo.org/records/15095752> |
| **SAT Competition Benchmarks 2002–2024** | **7330 normalized benchmarks** — application/industrial 2002–2019, main track 2020–2024, plus Anniversary-track 2022 instances. Published 2025-04-02, DOI `10.5281/zenodo.15125952` **[C]** | <https://zenodo.org/records/15125952> |
| SAT Comp 2022 Anniversary track | 5355 benchmarks: a non-isomorphic, normalized subset of all available instances from previous Application, Crafted and Main tracks **[C]** | <https://zenodo.org/records/11175170> |
| SAT Comp 2025 benchmarks + solvers | `track_main_2025.uri`; 25 main-track solver source archives as `.tar.xz` **[C]** | <https://satcompetition.github.io/2025/downloads.html> |
| SAT Comp 2026 benchmarks | `track_main_2026.uri`, tagged in GBD as of 2026-08-10 **[C]** | <https://satcompetition.github.io/2026/downloads.html> |
| Per-year proceedings | Solver, benchmark **and proof-checker** descriptions, published as a report (TU Wien repositum for 2025, Helsinki research portal for 2024) **[C]** | <https://repositum.tuwien.at/> · <https://researchportal.helsinki.fi/en/publications/proceedings-of-sat-competition-2024-solver-benchmark-and-proof-ch/> |

Practical note for axeyum: the 7330-instance 2002–2024 archive is the right corpus for a
*first honest* head-to-head, because it is exactly what the Anniversary track used and
the per-instance difficulty distribution is documented. The 400-instance current main
track is the wrong first target — it is deliberately selected to be hard for
state-of-the-art solvers.


---

## 3. MaxSAT Evaluation

**Fetching gotcha first:** since 2024 the MSE site is a jQuery `data-include` shell.
`https://maxsat-evaluations.github.io/2024/` returns a **blank page**; the real content is at
`.../<year>/contents/contents_<page>.html`. 2022 and 2023 are plain HTML at
`.../<year>/<page>.html`. **[C]**

### 3.1 Editions

| Year | Ran? | Edition |
|---|---|---|
| 2022 | Yes | 17th **[C]** |
| 2023 | Yes | 18th **[C]** |
| 2024 | Yes | 19th **[C]** |
| **2025** | **NO — cancelled** | Verbatim: *"We regret to inform you that the MaxSAT 2025 evaluation will not be held this year. We hope to resume the event in 2026."* **[C]** |
| 2026 | Yes | 20th, at SAT'26 July 2026, results published **[C]** |

The 2025 gap is corroborated three ways **[C]**: the 2025 page text; the MSE 2026
proceedings preface ("organized yearly starting from 2006, **with a pause in 2025**"); and
<https://github.com/maxsat-evaluations/data> whose `results/` directory jumps from
`2024-*.csv` straight to `2026-*.csv`.

### 3.2 Tracks — they never merged

**Direct answer to the "did weighted and unweighted merge?" question: no. They stayed two
separate tracks in every year.** What changed, in **2023**, was only the naming: *Complete →
Exact*, *Incomplete → Anytime*. **[C]** (2023 tracks page verbatim: "Main Tracks for Exact
Solvers (formerly 'Complete Solvers')".)

| Year | Exact / Complete | Anytime / Incomplete | Incremental | Certified |
|---|---|---|---|---|
| 2022 | Complete: unweighted, weighted | Incomplete: unweighted, weighted × {60 s, 300 s} | **New in 2022** (IPAMIR) | **No** |
| 2023 | **Exact** (renamed) | **Anytime** (renamed), same subtracks | Offered — **no solvers submitted** | **No** |
| 2024 | Exact: UW, W | Anytime: UW, W × {60 s, 300 s} | **Showcase only**, no new solvers | **No** |
| 2025 | cancelled | cancelled | cancelled | — |
| 2026 | Exact: UW, W | Anytime: UW, W × **{60 s, 300 s, 1707 s}** | Yes, 5 applications | **No — but announced for next year** |

**[C]** for all rows. The 2026 third timeout is **drawn at random after submissions close**
from the range 900–1800 s; it came out **1707 s**, solvers must handle all three, and the
timeout is passed as a command-line hint. **[C]** (A Top-k track existed in 2020 only.)

**On the certified track — the precise answer.** No certified / proof-logging track has ever
existed, 2022–2026. Every content fragment of the 2022/2023/2024/2026 sites (index, tracks,
rules, execution, calls, submission, guidelines, incremental, benchmarks, rankings) was
grepped for `proof|certif|VeriPB|DRAT`: zero hits relating to a track or requirement — the
only matches are incidental "verify/verified" about SIGTERM testing and solution checking.
**[C]**

**BUT**: slide 23 of the **MSE 2026 presentation**, under "Outlook for Next Year", reads
**"Introducing a certified track"**. **[C]** — read in
<https://zenodo.org/records/21358014/files/slides.pdf>. It is an announced intention with no
date, rules or call. *Note this is on the slides, not on any web page — a page-only grep
returns a clean negative and misses it.* Supporting signals: **Dieter Vandesande**
(co-author of *Certified Core-Guided MaxSAT Solving*) is now an MSE 2026 organizer **[C]**;
and MSE 2026 added an optional **`c LB <int>`** lower-bound output line, "New for 2026",
with organizers "considering reporting on the ability of exact solvers to produce lower
bounds" — self-reported, not a certificate, but the first bound-evidence step. **[C]**

### 3.3 Rules

| | 2022 | 2023 | 2024 | 2026 |
|---|---|---|---|---|
| **Exact timeout** | **3600 s** | 3600 s | 3600 s | 3600 s **[C]** |
| Exact memory | 32 GB | 32 GB | 32 GB | 32 GB **[C]** |
| Anytime timeouts | 60 s, 300 s | 60 s, 300 s | 60 s, 300 s | 60 s, 300 s, **1707 s** **[C]** |
| Incremental | 7200 s / 32 GB | (none) | 7200 s / 32 GB | 3600 s / 32 GB **[C]** |
| Exact hardware | StarExec, Xeon E5-2609 @2.40 GHz, 128 GB | StarExec, Xeon Gold 6334 @3.60 GHz, 264 GB | same as 2023 | **VSC/VUB HYDRA**, 2× 32-core **AMD EPYC 9384X @3.1 GHz**, 384 GB **[C]** |
| Anytime hardware | StarExec | Helsinki FCCI, Xeon E5-2670 | Helsinki FCCI, Xeon Gold 6148, 381 GB | VSC HYDRA **[C]** |
| Cores per solver | 1 (parallel ⇒ disqualified) | 1 | 1 | 1 **[C]** |

**2026 moved off StarExec entirely**, onto the Flemish Supercomputer Centre HYDRA cluster at
VUB. **[C]**

**Exact-track scoring is the number of solved instances — NOT PAR.** Rules verbatim:
"ranked based on the number of solved instances within predefined per-instance resource
limitations… solving an instance means finding an optimal solution." **[C]** PAR-2 *is*
published alongside the count in 2026, but the ranking follows the count, and they disagree:
`MaxCDCL2026S2O3` (415 solved, PAR-2 2467.9) ranks above `CASHWMaxSAT` (414, PAR-2 2587.5)
but also above `MaxCDCL2026S2` (407) whose PAR-2 2535.6 beats CASHWMaxSAT's. PAR-2 was not
published for the 2022–2024 exact tracks at all. **[C]**

**Anytime score formula** **[C]**:

```
score(s, i) = (1 + cost of best known solution for i) / (1 + cost of solution found by s on i)
```

0 if no solution found; always in [0, 1]; the ranking is the **mean over all instances**.
Critical baseline detail: "best known" means the best found by all anytime solvers **within
300 seconds**. Recomputing the 2024 60 s scores with a within-file baseline yields
systematically *higher* numbers (SPB-MaxSAT-c-Band 0.863 vs. the official 0.827); the gap is
exactly the tighter 300 s best-known cost. **Do not recompute these without that baseline.**
**[C]**

Other rules **[C]**: mandatory open source; **no closed-source third-party binaries** (which
is why MaxHS moved off CPLEX to SCIP by 2026); mandatory pass of the regression suite since
2024; buggy solvers flagged `*` rather than auto-disqualified. New for 2026: descriptions
must state "the nature and extent of changes introduced by generative AI tools, with those
tools identified by name."

### 3.4 The new WCNF format

**Introduced in 2022.** Rules page verbatim: "Note that the input format is changed for
2022." **[C]**

| | Old (pre-2022) | New (2022–) |
|---|---|---|
| Header | `p wcnf <vars> <clauses> <top>` | **removed entirely** |
| Hard clause | weight = `top` (= Σ soft weights + 1) | prefix **`h`** |
| Soft clause | `<weight> <lits> 0` | unchanged |

```
c comment                        c comment
p wcnf 7 4 12            ->      h 1 2 3 4 0
12 1 2 3 4 0                     1 -3 -5 6 7 0
1 -3 -5 6 7 0                    6 -1 -2 0
6 -1 -2 0                        4 1 6 -7 0
4 1 6 -7 0
```

Weights: `1 ≤ w < 2^63`, `Σw < 2^64 − 1`. The stated reason for dropping the `p` line is
that it is "a source of many problems when constructing benchmark files" and clause storage
must be dynamically reallocated anyway. **[C]** Conversion tools `std_wcnf` (old→new),
`to_old_fmt`, `verify_soln`, `to_cnf` at
<https://bitbucket.org/fbacchus/maxsat_benchmarks_code_base/> (C++, **no LICENSE file**).
**[C]**

Output: `s OPTIMUM FOUND` (exit 30) / `s UNSATISFIABLE` (20) / `s SATISFIABLE` (10) /
`s UNKNOWN` (0), plus `o <cost>` and `v <0/1 string>`; optional `c LB <int>` new in 2026.
**[C]**

**Instance counts** (each verified twice — webpage vs. row count of the official per-instance
CSV) **[C]**:

| Year | Exact UW | Exact W | Anytime UW | Anytime W |
|---|---|---|---|---|
| 2022 | 594 | 607 | 179 | 197 |
| 2023 | 572 | 558 | **179** | **160** |
| 2024 | 553 | 571 | 216 | 229 |
| 2026 | 607 | 609 | 175 | 211 |

**Warning: the 2023 benchmarks webpage has the anytime labels swapped** — it reads "Weighted
… (179) / Unweighted … (160)". The talk slides and the CSV row counts both say UW 179, W
160. Trust the slides and CSVs. **[C]** Anytime instances are always the hard subset of the
exact set — those not solved optimally within 60 s by *any* exact participant. **[C]**

**Where they live.** Zenodo DOIs exist only from 2026; earlier years used Google Drive plus a
Helsinki web directory. **[C]**

| Resource | URL / DOI |
|---|---|
| **Complete collection 2007–2026** | concept DOI **10.5281/zenodo.21283147** → version **10.5281/zenodo.21283148**. CC-BY-4.0, published 2026-07-09, 19 files split by submission year (`2020.zip` alone ≈18.7 GB); normalized with `std_wcnf`; metadata in a GBD SQLite (`meta.db`, `base.db`) |
| **MSE 2026 solvers + benchmarks + results** | **10.5281/zenodo.21358014**, CC-BY-4.0, 2026-07-14, 38 files including `slides.pdf` and `logs.zip` (1.8 GB) |
| Metadata + all results CSVs 2017–2026 | <https://github.com/maxsat-evaluations/data> — `results/<year>-<track>.csv`; **`results/2026-summary.md`** has the full 2026 rankings including PAR-2 |
| 2024 benchmarks | `https://www.cs.helsinki.fi/group/coreo/MSE2024-instances/mse24-{exact,anytime}-{unweighted,weighted}.zip` (verified 200) |
| 2023 anytime / 2022 incomplete | `.../MSE2023-anytime-instances/…`, `.../MSE2022-inc-instances/…` (live; exact sets on Google Drive) |

The 2026 `benchmark-metadata.csv` has exactly **1216 rows = 607 + 609**, **98 families**,
**952 optimal costs known / 264 unknown**; largest families logistics-routing (50),
asp-optimization (45), planning-hplus (33). **[C]**

### 3.5 Winners

**Exact / Complete** (solved counts) **[C]**

| Year | Track | 1st | 2nd | 3rd |
|---|---|---|---|---|
| 2022 | Complete UW (594) | **CASHWMaxSAT-CorePlus — 438** | CASHWMaxSAT-Plus — 433 | UWrMaxSat-SCIP — 432 |
| 2022 | Complete W (607) | **CASHWMaxSAT-CorePlus — 438** | CASHWMaxSAT-Plus — 435 | UWrMaxSat-SCIP — 427 |
| 2023 | Exact UW (572) | **EvalMaxSAT-SCIP — 433** | MaxCDCL-S6-HS9 — 430 | CASHWMaxSAT-CorePlus — 428 |
| 2023 | Exact W (558) | **WMaxCDCL-S6-HS12 — 446** | EvalMaxSAT-SCIP — 442 | CASHWMaxSAT-CorePlus — 432 |
| 2024 | Exact UW (553) | **WMaxCDCL-openwbo1200 — 421** | MaxCDCL-openwbo300 — 418 | UWrMaxSat-SCIP-MaxPre — 415 |
| 2024 | Exact W (571) | **CASHWMaxSAT-DisjCom-S6 — 448** | UWrMaxSat-SCIP — 442 | EvalMaxSAT — 435 |
| 2026 | Exact UW (607) | **UWrMaxSAT2026 — 424** (PAR-2 2409.1) | UWrMaxSat-MaxCDCL — 423 | WMaxCDCL2026S6O3 — 417 |
| 2026 | Exact W (609) | **UWrMaxSAT2026 — 456** (PAR-2 2122.8) | WMaxCDCL2026S6 — 436 | EvalMaxRes — 434 |

VBS: 2024 UW 458 / W 472; 2026 UW 477 / W 470. **[C]**

**Anytime / Incomplete** (mean anytime score) **[C]**

| Year | Track | 60 s | 300 s | 1707 s |
|---|---|---|---|---|
| 2022 | UW | **NuWLS-c 0.807** | **NuWLS-c 0.895** | — |
| 2022 | W | **NuWLS-c 0.759** | **NuWLS-c 0.846** | — |
| 2023 | UW | **NuWLS-c 2023 — 0.810** | **NuWLS-c 2023 — 0.883** | — |
| 2023 | W | **NuWLS-c 2023 — 0.787** | **NuWLS-c 2023 — 0.898** | — |
| 2024 | UW | **SPB-MaxSAT-c-Band 0.827** | **SPB-MaxSAT-c-Band 0.898** | — |
| 2024 | W | **SPB-MaxSAT-c-FPS 0.876** | **SPB-MaxSAT-c-FPS 0.926** | — |
| 2026 | UW | **PASMaxSAT-c 0.861** | **Aperture-KBG 0.907** | **PASMaxSAT-c 0.948** |
| 2026 | W | **Aperture-KBG 0.914** | **Aperture-KBG 0.942** | **Aperture-KBG 0.963** |

Two 2026 anomalies worth knowing **[C]**: rank order is **not stable across timeouts** in
unweighted (PASMaxSAT-c wins 60 s and 1707 s, Aperture-KBG wins 300 s); and `SPB-NIM-c`
collapses from 0.809 at 300 s to **0.259** at 1707 s in weighted — a failure to handle the
long timeout, exactly the risk the organizers flagged. `COGS` was **disqualified for
weighted**, and its own solver description says "the developers have found that weighted
instances are not always sound and the solver is not recommended to solve weighted problems."

**Incremental** **[C]**: 2022 (5 apps × 100) — EvalMaxSAT, iMaxHS and UWrMaxSat each ranked
1st on some application. 2023 — no submissions. 2024 — showcase of the 2022 solvers on one
new 72-instance set; EvalMaxSAT and UWrMaxSat both 68/72, PAR-2 810.11 vs 886.45. 2026
totals across 5 apps: **share-trail 337**, UWrMaxSAT 325, core-trail 324, UWrMaxSAT-scip
321, Aperture 220.

Participation notes **[C]**: **RC2 has not participated since 2020.** MaxHS skipped
2023–2024 and returned in 2026 (SCIP-based, 374 UW / 393 W). Open-WBO last appears in the
2024 submitted list. DT-HyWalk was 2022 only.

### 3.6 Solvers

`NOASSERTION` below means GitHub could not classify the license; in each case the LICENSE
body is hand-formatted MIT text carrying the MiniSat/Open-WBO copyright chain (bodies read
directly). **[C]**

| Solver | Repo | License | Lang | Family |
|---|---|---|---|---|
| **EvalMaxSAT** | <https://github.com/FlorentAvellaneda/EvalMaxSAT> | **GPL-3.0** | C++ | Core-guided OLL + totalizer, on CaDiCaL |
| **UWrMaxSat** | <https://github.com/marekpiotrow/UWrMaxSat> | MIT text (NOASSERTION) | C++ | Core-guided OLL over MiniSat+/kp-minisatp PB encoding; SCIP via IPAMIR; MaxPre built in |
| **MaxHS** | <https://github.com/fbacchus/MaxHS>; 2026 fork <https://github.com/ASchidler/MaxHS> | MIT text (NOASSERTION) | C++ | **Implicit hitting set**; was CPLEX, 2026 uses SCIP 10.0.2 |
| **RC2** | <https://github.com/pysathq/pysat> → `examples/rc2.py` | **MIT** | Python | Core-guided OLLITI |
| **CASHWMaxSAT** (all variants) | **no public VCS** — MSE zips only | MIT chain + bundled SCIP | C++ | UWrMaxSat OLL + disjoint core extraction + SCIP |
| **Pacose** | <https://github.com/tobipaxe/PacoseMaxSATSolver> | **no LICENSE file**; MIT in headers **[I]** | C++ | SAT-UNSAT solution-improving; DPW/binary-adder PB encodings |
| **NuWLS / NuWLS-c** | <https://github.com/shaowei-cai-group/NuWLS>, `.../NuWLS-c` | none / MIT chain | C / C++ | Local search (SATLike + Dist-weighting) hybridized with TT-Open-WBO-Inc |
| **MaxCDCL / WMaxCDCL** | MSE zips; <https://github.com/jordicollcaballero/WMaxCDCL_Paper> | MIT text | C++ | **Branch-and-bound + clause learning** |
| **Open-WBO** | <https://github.com/sat-group/open-wbo> | MIT text | C++ | Linear SAT-UNSAT + core-guided (MSU3/OLL/WBO) |
| **TT-Open-WBO-Inc** | <https://github.com/alexander-nadel-academic/tt-open-wbo-inc> | **MIT** | C++ | Anytime SAT-UNSAT (author **Alexander Nadel**, Intel/Technion) |
| **CGSS / CGSS2** | <https://bitbucket.org/coreo-group/cgss2> | **MIT** (v2); v1 no LICENSE | C++ | Core-guided OLL; **built on RC2/PySAT**, not CaDiCaL |
| **Scuttle** | <https://github.com/chrjabs/scuttle> | **MIT** | **Rust** | Multi-objective MaxSAT; certified Pareto-optimality |
| **MaxPre / MaxPre2** | <https://github.com/Laakeri/maxpre>; <https://bitbucket.org/coreo-group/maxpre2> | **MIT** | C++ | Preprocessor; v2.2 adds **certified preprocessing** |
| **Exact** | <https://gitlab.com/nonfiction-software/exact> | **AGPL-3.0** (GitLab's API wrongly reports MIT — read the LICENSE) | C++ | PB/ILP cutting-planes CDCL (RoundingSat fork); **emits VeriPB certificates** |
| **Loandra** | <https://github.com/jezberg/loandra> | MIT text | C++ | Core-boosted linear search |
| **SPB-MaxSAT-c** | <https://github.com/JHL-HUST/SPB-MaxSAT> | **Apache-2.0** | C | Local search + soft-conflict PB constraint |
| **IPAMIR** | <https://bitbucket.org/coreo-group/ipamir> | — | C header | **Incremental MaxSAT API — the IPASIR analogue, 10 functions** |

Two licensing traps verified by reading files rather than API fields **[C]**: **Exact is
AGPL-3.0** despite GitLab reporting MIT, and **EvalMaxSAT is GPL-3.0** — the most
restrictive of the widely-used solvers. Everything else is MIT-style except SPB-MaxSAT
(Apache-2.0), BandMaxSAT (GPL-2.0), and four with no license at all.

### 3.7 Certified MaxSAT — mature literature, zero competition pressure

Measured overhead from *Certified Core-Guided MaxSAT Solving* (CADE-29) **[C]**: solving
**+8.8% median**, ≤36.2% at p95; 803 vs 806 instances solved. Checking is the real cost —
VeriPB verified only **747 of 803** proofs (42 memory-outs, 14 time-outs at 14 GB /
36,000 s), on the full MSE **2022** complete-track sets. **Proof logging found two real bugs
present in both CGSS and RC2** (fixed in CGSS `5526d04`, RC2 `d0447c3`) — the strongest
available argument for the practice. Note the CADE'23 solver is **CGSS built on RC2/PySAT**,
not CaDiCaL; CaDiCaL enters later via Scuttle (TACAS'25, CaDiCaL 2.0.0 under VeriPB 2.2.2).
**[C]**

**VeriPB ingests WCNF natively** (2022 format), translating to OPB with unit softs folded
into the objective and multi-literal softs relaxed with blocking literals. IJCAR'24 built
**`CakePBwcnf`**, a *verified* WCNF frontend, so the verified theorem states the original
WCNF and the preprocessed output are **equioptimal** — the trust boundary includes the
MaxSAT-to-PB translation, not just the PB reasoning. **[C]**

**No paper instruments MaxHS itself** — confirmed against a DBLP full-text search plus
Vandesande's and Oertel's complete publication lists. IHS certification goes through PB
hitting-set computation (AAAI'26) and **HitPBO** (SAT 2026, 10.4230/LIPIcs.SAT.2026.34), not
MaxHS. **[C]**

The paradigm coverage is now complete — SIS 2022 → core-guided 2023 → preprocessing + WLOG
2024 → multi-objective 2025 → IHS + branch-and-bound 2026 — and the certified
branch-and-bound paper targets **MaxCDCL** specifically, the family that won MSE 2024
unweighted and placed 2nd–3rd in 2026. **The gap is not that the certifying solvers are
toys; it is that the evaluation does not ask.** **[C]**


---

## 4. Model Counting Competition

### 4.1 Tracks

Track ids: **1** = MC (unweighted); **2** = WMC (weighted); **2B** = WMC allowing **negative
weights** (motivated by quantum circuit simulation); **3** = PMC (projected); **4** = PWMC
(projected weighted); **1F** = MC on the same instances at a **120 s** timeout; **5B** = AMC,
algebraic model counting over the **complex field**; **6B** = bitvector counting, SMT input.
**[C]**

| Year | Iter | Tracks | Change |
|---|---|---|---|
| 2020 | 1st | MC, WMC, PMC | baseline **[C]** |
| 2021 | 2nd | 1, 2, 3, 4 = "harder model counting instances" | Track 4 added but **not** PWMC **[C]** |
| 2022 | 3rd | 1 MC, 2 WMC, 3 PMC, **4 PWMC** | PWMC added (Track 4 repurposed) **[C]** |
| 2023 | 4th | 1, 2, 3, 4 | unchanged **[C]** |
| 2024 | 5th | 1, 2, **2-Bonus (negative weights)**, 3, 4 | negative-weight bonus added **[C]** |
| 2025 | 6th | 1, 3, 4, **5B AMC-complex**, **6B Bitvector**; **Track 2 omitted** | 2 dropped, 5B+6B added **[C]** |
| **2026** | **7th** | 1, **1F**, 2B, 3, 4, 5B | 1F added; 6B not run; 2 returns as 2B **[C]** |

**MC 2026 has already run** — presented Thursday 23 July 2026 at FLoC / SAT 2026, Lisbon;
awards deck at <https://mccompetition.org/assets/files/2026/MC2026_awards.pdf>. **[C]** Any
planning document treating 2025 as the latest edition is out of date.

Notes **[C]**: 2025's stated reason for dropping Track 2 — "Since the results no Track 2
were quite similar to Track 4 in 2024, we omit weighted model counting unless requested by
solver developer who has not been participating." 2025 Track 5B was annotated "⇒ still
evaluating" and 6B "(only one submission)"; neither produced a ranking, and AMC first
produced a real ranking in 2026. **There is no ProjMC track, no #DNF track, and no
certified/proof track in any year.**

### 4.2 Rules

| Item | Value |
|---|---|
| Timeout | **3600 s** per instance **[C]** |
| Timeout, Track 1F (2026) | **120 s** **[C]** |
| Memory | **32 GB** per instance (2025 deck: "32 GB → 31 GB" on the SoSy cluster) **[C]** |
| Instances | **200 per track, split 100 public / 100 private — ranking is on the private 100 only** **[C]** |
| Execution | Competition phase runs solvers **exclusively** (one solver per whole node); `runsolver` for limits, `perf` for timing; BenchExec rejected for aborts/quota bugs **[C]** |

Hardware changed year to year **[C]**: StarExec 2021–2024; **SoSy(comp) cluster at LMU
Munich** in 2025 (the description page's "Tetralith" was the pre-competition plan, the deck
records what ran); 2026 warmup on the Barnard cluster at HPC Dresden, **final on the CRIL
cluster at Lens** — the same machines as the Pseudo-Boolean competition.

**Scoring is a plain count of accepted answers. No PAR-2, no time weighting, no
tie-breaking.** Verbatim **[C]**: "we define the scoring function … as the number of
acceptably solved instances together with the number of solutions for instances where no
count could be precomputed" and "If multiple solvers score in tie, we assign the same place
to all solvers and leave the subsequent place(s) vacant."

Error measure, with `c_o` observed and `c_e` expected **[C]**:

```
lpc(c_e, c_o) = 10^(log10(c_o) − log10(c_e))
eps(c_e, c_o) = 1 − lpc(c_e, c_o)
c_o is ACCEPTED           iff  eps <= eps_max
c_o is APPROX. ACCEPTED   iff  c_e/(1+alpha) <= c_o <= (1+alpha)*c_e
```

The A/B/C/D penalty scheme (2022 onward) **[C]**:

| Ranking | Solver class | `eps_max` | Penalty |
|---|---|---|---|
| **A** | Exact, arbitrary precision | **0.0** | **any single wrong solution ⇒ removed from the ranking** |
| **B** | Exact, small precision loss | 0.001 (0.1%) | >20 solutions outside margin ⇒ disqualification |
| **C** | Approximate (must state a guarantee) | `alpha` = 0.8 | >20 outside the factor ⇒ removed |
| **D** | Heuristic (e.g. anytime) | 20% | 1 point per correct answer, no disqualification |

Two mechanics worth knowing **[C]**: (a) **automatic demotion** — "If a solver outputs too
many counts that are not accepted in one category, we automatically move the solver into a
category that allows for lower precision", which is why one solver holds different places in
the A/B/C columns of one table; (b) 2021 used a *different* uniform scheme (per-track
`eps_max`: MC 0.1%, WMC 1.0%, PMC 1.0%, Track 4 20%), regardless of declared solver type.
Ranking D existed on paper since 2022 but only produced a placement column in **2026**, when
CoinCount entered as the "first ever heuristic counter".

Benchmark selection, verbatim 2022–2026 **[C]**: "We precompute instances and discard those
that can be solved by standard solvers within less than 10s and keep at most 40 instances
that cannot be solved by common existing solver." 2024 adds: remove instances solvable in
60 s by SharpSAT (2011); remove unsatisfiable instances (Track 1 only); stratified sample
over the collected sets.

### 4.3 Input format

Spec: <https://mccompetition.org/assets/files/mccomp_format_25.pdf> — "Model Counting
Competition Data Format (version 1.2)", Fichte, Hecher, Shaw. "The input format remains
compatible with the 2021 Competition format." **[C]**

```
c c this is a comment and will be ignored
c r originUrl/doi descUrl/doi [generatorUrl/doi]     <- reproducibility, mandatory for submissions
p cnf n m
c t mc|wmc|pmc|pwmc|amc-complex                      <- optional type line
c p weight  1 0.4 0
c p weight -1 0.6 0
c p show varid1 varid2 ... 0
-1 -2 0
2 3 -4 0
```

**[C]** on all of the following:

- **`c t` line.** "A line starting with character `c t` … will be followed by `mc`, `wmc`,
  `pmc`, or `pwmc`… The solver needs to support the line and either handle the problem or
  output an error." All four are valid; `c t wmc` appears literally in worked Examples 2 and
  3 even though the schematic at the head of §2 omits it — **[I]** the schematic is a typo,
  prose plus worked examples are authoritative. Since 2024: "Supporting the problem type only
  via commandline parameters is considered insufficient." The `c t` line is *optional on
  input*, but the corresponding output line `c s type [...]` is **mandatory**.
- **Weights**: `c p weight <literal> <weight> 0`. A decimal with ≤9 significant digits after
  the point, or 32-bit scientific notation (`1.23e+4`), or a fraction (`3/10`). If
  `0 < w_l < 1` is given and `-l` is not, `w_-l = 1 − w_l` is assumed (with a warning). If
  `w_l ≤ 0`, the weight for `-l` **must** also be given or the solver "must output a format
  error and abort". If neither `x` nor `-x` has a weight it is 1 — "this differs from the
  format used in Cachet." Since 2025, for PWMC "we enforce that weights are given only for
  projection variables". **`c p weight` lines may occur anywhere, including after clauses.**
- **Projection**: `c p show varid1 varid2 ... 0`, multiple lines allowed anywhere, the
  projection set is their union. "if all variables are stated using show, we consider model
  counting. if no variables are stated the problem is simply to decide satisfiability."
- **Complex weights** (2025+, Track 5B): `c t amc-complex` then `c p weight 1 0.4+0.2i 0`.
- **Mandatory output**: `s SATISFIABLE|UNSATISFIABLE|UNKNOWN`; `c s type [...]`;
  `c s [log10-estimate|neglog10-estimate] VALUE` (15 significant digits);
  `c s SOLVERTYPE PRECISION NOTATION VALUE`, with SOLVERTYPE ∈ {approx, exact, heuristic},
  NOTATION ∈ {log10, float, prec-sci, int, frac}. `VALUE = log10(|cnt|)`; `-inf` if the count
  is 0; `neglog10-estimate` if negative.

**Two spec defects to code around** **[I]**: the spec references a "return code section"
twice but v1.2 contains no such section (a leftover 2021 cross-reference); and Example 4
writes the header as `p cnf 6 4 2` — a third number the prose never defines. A strict DIMACS
parser rejects it. Be lenient.

### 4.4 Winners

Scores are instances solved out of the 100 **private** instances. Column labels follow the
awards decks: 0% = Ranking A, 0.1% = B, 0.8 = C, Heu. = D. **[C]** throughout.

**MC 2022** — Track 1 (A): SharpSAT-td+Arjun **79**, ExactMC 77, SharpSAT-TD 77, d4 76,
gpmc 69, MTMC 66, DPMC 61, c2d 50. Track 1 (C): SharpSAT-td-Arjun+ApproxMC 74. Track 2 (A):
**SharpSAT-TD 75**, c2d 60, DPMC 35. Track 3 (A): **gpmc 72**, d4 71, Ganak 56, DPMC 26;
(C) Ganak 83. Track 4 (B): **gpmc 79**, DPMC 35.

> **Naming discrepancy, unresolved.** The 2022 awards deck names the Track 3 third-place
> (Ranking A) entry — and the Ranking C winner — **"Ganak"**; the winners certificates name
> the same entries **"SharpSAT-td-Arjun"**. Both are Soos/Meel submissions. Two official
> documents disagree and I could not determine which name the scored binary carried.
> Everything else cross-checks. **[C]**

**MC 2023** — Track 1: **SharpSAT-TD 82** (1st in A, B and C), arjun-ganak-approxmc 79
(C 2nd), d4 75, ExactMC-Arjun 74, arjun-ganak 71, gpmc 64, Alt-DPMC 50, DPMC 43, MTMC 34.
Track 2: **SharpSAT-TD 75**, d4 67, gpmc 62, ExactMC-Arjun 59. Track 3 (C):
**arjun-ganak-approxmc 81**; (A+B) d4 71, gpmc 67, arjun-ganak 64, DPMC 36, **Alt-DPMC 12
marked "X X" — removed from both exact rankings**. Track 4: **gpmc 82**, d4 72, DPMC 39.

**MC 2024 — Ganak won every track.** Track 1 (C): Ganak-ApproxMC 63; (A/B) **Ganak 54**,
SharpSAT-TD 48, SharpSAT-TD-CH 48, ExactMC 44, d4 42, AS4MOCO 40, MTMC 37, gpmc 36, DPMC 27,
NumSat 13. Track 2: **Ganak 63**, SharpSAT-TD 52, d4 45. Track 2-Bonus (negative weights):
**Ganak 77**, SharpSAT-TD 73, SharpSAT-TD-CH 73. Track 3 (C): Ganak-ApproxMC 78; (A/B)
**Ganak 48**, d4 40, gpmc 35. Track 4: **Ganak 75**, d4 72, gpmc 64.

**MC 2025** — participation shrank (MC 7, −3; PMC 4; PWMC 3; AMC 3). Track 1 (C):
Ganak-ApproxMC 63; (A) **Ganak 60**, Cara 50 *(best newcomer)*, d4 50, sharpSAT-TD-CH 47,
sharpSAT-TD 47, MTMC 39, gpmc 38; vbest 69. Track 3 (C): Ganak-ApproxMC 79; (A) **Ganak
56**, d4 45, gpmc 45; vbest 89. Track 4 (C): Ganak-Approx 58; (A/B) **Ganak 57**, d4 46,
MTMC 36; vbest 60. Track 2 not run; 5B "still evaluating"; 6B one submission.

**MC 2026** — new entrants **CoinCount** (Yang, van Bremen, Meel; "first ever heuristic
counter") and **TiDiDi** (Van den Broeck, Capelli; "great newcomer").

| Track | Result |
|---|---|
| 1 MC | CoinCount **Heu 1st, 77**; Ganak-approx C 1st, 68; **d4 A/B 1st, 63**; Ganak 62; Cara 59; gpmc 57; TiDiDi 56 |
| 1F MC @120 s | CoinCount Heu 1st, 57; **Ganak A/B/C 1st, 48**; TiDiDi 46; d4 42; Cara 38; gpmc 38 |
| 2B WMC, negative weights | CoinCount Heu 1st, 82; Ganak-approx C 1st, 60; **d4 A/B 1st, 60**; Ganak 59; TiDiDi 56; gpmc 55 |
| 3 PMC | CoinCount Heu 1st, 83; Ganak-approx C 1st, 83; **Ganak A/B 1st, 61**; d4 52; TiDiDi 49; gpmc 45 |
| 4 PWMC (mixed) | CoinCount Heu 1st, 87; Ganak-approx C 1st, 84; **Ganak A/B 1st, 69**; d4 67; TiDiDi 64; gpmc 57 |
| 5B AMC complex | Ganak-approx C 1st, 49; **d4 A/B/Heu 1st, 49**; Ganak 44; vbest 50 |

Deck footnote: "CoinCount is an approximate anytime solver, ranked in the heuristic
category, due to missing guarantees." **FLoC 2026 medals**: "Most Competitive Solver over
the Last 6 Years" → **Ganak**; "Most Robust Solver over the Last 6 Years" → **D4**. **[C]**

### 4.5 Certification — an empty niche, described as such by the organizers

**There is no certified / proof-logging track in any edition 2020–2026.** Every year's
description page and awards deck was read; `grep -i "proof|certif|verif|trust"` over the
2024/2025/2026 decks returns only "Certificates" as an *award*-certificates slide title, plus
one benchmark family named "Debug Failing Proof Search". **[C]**

The organizers say why, verbatim **[C]** (<https://arxiv.org/pdf/2504.13842>):

> "Obviously, a majority decision is insufficient for model counting… Hence, a majority check
> is **only a necessary condition**. A sufficient condition would require to emit a
> correctness proof and verify the proof. Recent advances on proof systems for model counting
> seem to be a promising start. Unfortunately, only few solvers implement proof traces and
> these traces can be quite large, which is a notable issue with our available cluster
> resources. Still, we discovered erroneous solvers and had to remove them partially or
> entirely from rankings… For future editions, we suggest to introduce fuzzing and optional
> proof traces and checking thereof…"

| System | What | Status |
|---|---|---|
| **MICE** ("Model-counting Induction by Claim Extension") | Fichte, Hecher, Roland, SAT 2022, DOI 10.4230/LIPIcs.SAT.2022.30. Line-based/dynamic, five step kinds. **Unweighted, non-projected only.** | Checker `sharpCheck` = <https://github.com/vroland/sharptrace> — **Rust, NO LICENSE FILE, dormant since 2023-03-16**. Emitters: instrumented sharpSAT, DPDB, and `nnf2trace` (Rust) post-processing D4. **It found a real wrong-count bug in sharpSAT** — the code base Ganak and Dsharp descend from. **[C]** |
| **CPOG** (Certified Partitioned-Operation Graphs) | Bryant, Nawrocki, Avigad, Heule — SAT 2023 (10.4230/LIPIcs.SAT.2023.6), JAIR 82 (2025, 10.1613/jair.1.15958). <https://github.com/rebryant/cpog>, **MIT**. **The proof generator is untrusted by design.** Weighted counting via exact arithmetic over Q₂,₅ = {a·2^b·5^c}; one weighted result had **260,909 decimal digits**. **Lean 4** verifies the checker. | Trusted-but-unverified: CNF/CPOG parsing (mitigated by `--print-cnf`/`--print-cpog` + diff), Lean's extraction of Nat/Int arithmetic and arrays, and Lean's kernel. **There is no "partial-CPOG" repo**; the closest is a documented **one-sided** proof mode (reverse implication only) usable "even when full validation is impractical". **[C]** |
| **SCPOG** (projected) | Bryant, Tan, Heule, SAT 2025, 10.4230/LIPIcs.SAT.2025.8. Adds Skolem nodes for existentially quantified variables; the checker also verifies decomposability and determinism. <https://github.com/rebryant/scpog>, MIT; companion <https://github.com/rebryant/d4v2-proofgen> (LGPL-2.1, active to 2026-04). | **The proof assistant moved Lean 4 → HOL4/CakeML between 2023 and 2025.** **[C]** |
| **ApproxMCCert** | Tan, Yang, Soos, Myreen, Meel, CAV 2024, 10.1007/978-3-031-65627-9_8, arXiv 2406.11414. <https://github.com/meelgroup/approxmc-cert>. Split design: the PAC guarantee proved once-off in **Isabelle/HOL**; per-run CNF-XOR UNSAT checking in **CakeML** (`cake_xlrup`). | 1,896 instances; certificates for 1,202 of 1,211 ApproxMC-solvable (99.3%); fully certified 1,018 (84.7%); 46 timeouts, 138 OOM, **zero certificate errors**. **Found a bug in CryptoMiniSat's XOR system.** **[C]** |

**Proof-complexity ordering** **[C]**: CLIP p-simulates {kcps, MICE, CPOG} (Chede, Chew,
Shukla, FSTTCS 2024 — theoretical only, not a logging format); **CPOG p-simulates {MICE,
kcps}**, and MICE and kcps are **exponentially incomparable** (SAT 2024
10.4230/LIPIcs.SAT.2024.5; JAR 70(2):12, 2026). AAAI-26 (Beyersdorff, Hoffmann, Kasche): with
moderate adaptations MICE and annotated-Decision-DNNF are **equivalent** and both **tightly
characterise state-of-the-art #SAT solving**. MICE has an exponential proof-step lower bound
(SAT 2023).

**Measured cost** **[C]**:

| | Result |
|---|---|
| CPOG unweighted, MC-2022 public, 180 CNFs, 4000 s, M1 MacBook Pro 64 GB + SSD | D4 compiled 123; generator converted 122 (the 1 failure needed 2,761,457,765 defining clauses and **overflowed the 32-bit signed clause id**); **full validation completed for 111 of 123**. **Median validation/compile ratio 12.5×** (range 0.27×–177×). Proof files **"some over 150 GB"** — "using an SSD was critical". Verified Lean checker vs C prototype: 3.42× faster to 4.39× slower |
| SCPOG projected, MC-2024 set, 389 CNFs | modified D4 compiled 175 at ≤1.8× (median 1.11×) stock cost; **172 of 175 fully verified**; median Skolem-POG/POG size ratio 34×; **verification/compilation median 2.95×**, worst 191.7×. The CakeML verified checker verified 156 of 172, **exceeding a 48 GB heap** on the other 16 |
| CPOG vs MICE head to head, 90 problems, 1000 s | both finished 75; CPOG faster on 66, MICE on 9; **median 7.67× faster for CPOG**. Root cause: MICE "has no mechanism for reusing results, effectively expanding the graphs into trees" |

**Consequence** **[I]**: no competition-winning counter emits a proof in its competition
configuration — the format spec has no proof-output field at all, and Ganak's README mentions
no proof/certificate/CPOG/verification. Only **d4's output** can be certified externally, via
CPOG.

The **2026 Model Counting Workshop** (adjacent to the competition) carries "Proof Logging for
Projected Enumeration (and Counting?) Problems in VeriPB" — extending VeriPB to
enumeration/counting in both its checker and the verified **CakePB** backend — plus
Beyersdorff's "Tutorial: Proof Complexity and Model Counting". **[C]** So the direction of
travel is clear even though the competition has not moved.

### 4.6 Benchmarks and the Rust landscape

200 instances selected per track per year, 100 public / 100 private. The 2026 submitted pool
was **49,315 instances, ~19 GB**. **[C]**

| Year | Solvers | Competition instances | Submitted benchmarks |
|---|---|---|---|
| 2020 | zenodo 4292581 | zenodo 10031810 | zenodo 10004947 |
| 2021 | zenodo 10006718 | zenodo 13988776 | zenodo 10006441 |
| 2022 | zenodo 10012803 | zenodo 10012860 | zenodo 10014715 |
| 2023 | zenodo 10012811 | zenodo 10012864 | zenodo 10012822 |
| 2024 | zenodo 14249109 | zenodo 14249068 | zenodo 14969231 |
| 2025 / 2026 | Nextcloud (LiU) shares — **not fetched, contents unverified** **[I]** | | |

**No published competition report exists for 2024, 2025 or 2026** — the only official record
for those years is the awards deck plus winners certificates. The last full write-up covers
2021–2023 (<https://arxiv.org/abs/2504.13842>). **[C]**

**Rust landscape** — relevant to a no-C-dependency stack **[C]**:

| Crate | Repo | License | What |
|---|---|---|---|
| **schlandals** | <https://github.com/aia-uclouvain/schlandals> | **MIT** | **The only competitive pure-Rust model counter.** Projected *weighted* counter specialized to Horn / distribution-structured input (Bayesian nets, ProbLog). CP 2023 |
| decdnnf_rs | <https://github.com/crillab/decdnnf_rs> | **GPL-3.0** ⚠ | d-DNNF reasoner from the d4 group |
| ddnnife | <https://github.com/SoftVarE-Group/d-dnnf-reasoner> | LGPL-3.0 | d-DNNF reasoner |
| sddrs | <https://github.com/jsfpdn/sdd-rs> | BSD-3-Clause | Bottom-up SDD compiler library; small solo project |
| sharptrace / nnf2trace | <https://github.com/vroland/sharptrace>, `.../nnf2trace` | **no license file** ⚠ | The MICE checker and D4→MICE converter. Dormant since March 2023 |

`d4-oxide` (LGPL-3.0) wraps d4 but drags in Mt-KaHyPar, Boost, GMP and MPFR — exactly the
C/C++ leaf dependencies a default build forbids. **No Rust bindings exist at all** for Ganak,
ApproxMC, Arjun, SharpSAT-TD, GPMC, DPMC/ADDMC, c2d, miniC2D, ExactMC/KCBox, Cachet or
DSHARP; the meelgroup tools ship Python bindings only. **[C]**

Licensing read: safe MIT tier — Ganak (but its bundled BreakID is GPL), ApproxMC, Arjun,
SharpSAT, SharpSAT-TD, GPMC, DPMC, ADDMC, KCBox, Schlandals, `rebryant/cpog`,
`rebryant/scpog`. Copyleft throughout — the **entire d4 family** (d4 v1 LGPL-3.0, d4v2
LGPL-2.1, decdnnf_rs GPL-3.0). **Do not vendor** c2d, miniC2D or the UCLA SDD binaries
(registration-gated, no published license), or Cachet (no LICENSE file, bundles zChaff whose
header restricts to "internal, noncommercial, research purposes only"). **[C]**

---

## 5. QBF: QBFEVAL → QBFGallery

**Correct the name first.** The event is now called **QBFGallery**, not QBFEVAL, and it is
*not* dormant — but it skipped two years.

| Year | Event | Status |
|---|---|---|
| 2022 | **QBFEVAL'22** ("14th QBF Solvers Evaluation"), FLoC Olympic Games, 3 Aug 2022 | Ran **[C]** |
| 2023 | **QBFGallery 2023**, QBF Workshop @ SAT 2023 | Ran; results 4 Jul 2023 **[C]** |
| 2024 | — | **No evaluation event** (workshop only, "Quantify" @ IJCAR) **[C]** |
| 2025 | — | **No evaluation event** (workshop only @ SAT 2025) **[C]** |
| 2026 | **QBFGallery 2026**, FLoC 2026 Olympic Games / QBF Workshop @ SAT 2026, Lisbon | **Ran**; presented 19 Jul 2026; **results not published anywhere reachable as of 2026-09-06** **[C]** |

Evidence for the 2024/2025 gap: <https://qbf.pages.sai.jku.at/evaluations/> lists exactly
one row (2023) while the sibling workshops page lists 2023, 2024 and 2025 — the site
distinguishes the two. <https://www.qbflib.org/index_eval.php> has no 2024/2025/2026
entry. **[C]** Note also that `www.qbfeval.org` no longer resolves. **[C]**

Trap: the QBFGallery 2023 technical report (arXiv 2604.16153) calls 2023 "**the last** QBF
evaluation event." That means *most recent*, not *final* — the 2026 call for
participation was posted a week later by one of the same authors. **[C]**

### Tracks

| Track | '22 | Gallery '23 | Gallery '26 (announced) |
|---|---|---|---|
| Prenex CNF (PCNF, QDIMACS) | ✓ | ✓ | ✓ (main) |
| Prenex non-CNF (QCIR) | ✓ | ✓ | ✓ |
| DQBF (DQDIMACS) | ✓ | ✓ | ✓ |
| 2QBF | — | — | ✓ (returns, last seen 2018) |
| Random | — | — | ✓ (returns, last seen 2017) |
| Crafted / hard instances | ✓ (CIT) | ✓ | ✓ |
| Preprocessor | — | ✓ | — |
| **Certified** | — | — | **conditional only** — "might be organized if there are enough submissions" **[C]** |

DQBF is a *track*, not a separate competition — there is no standalone DQBF Evaluation. **[C]**

### Formats

| Format | Spec | Note |
|---|---|---|
| **QDIMACS** | <https://www.qbflib.org/qdimacs.html> | v1.1, 21 Dec 2005. Defines input **and** solver output, including *partial certificates* **[C]** |
| **QCIR-G14** | <https://www.qbflib.org/qcir.pdf> | Format id line `#QCIR-14`; the 2023 Gallery used the "cleansed" subset supported by all QCIR solvers **[C]** |
| **DQDIMACS** | **no canonical spec page found** | QDIMACS + a `d` line giving an existential variable and its explicit dependency set. A real ecosystem gap. **[I]** |
| **QRP** (proof/trace) | <https://fmv.jku.at/qbfcert/qrp.format> | Full EBNF, ASCII and binary; steps are `idx literals antecedents` (≤2 antecedents), terminated `r sat` / `r unsat` **[C]** |
| **AIGER** | <https://fmv.jku.at/aiger> | The certificate output format — Skolem/Herbrand functions as AIGs **[C]** |

### Rules

| | QBFEVAL'22 | QBFGallery 2023 |
|---|---|---|
| Timeout | 900 s | **900 s** **[C]** |
| Memory | 32 GB | **8 GB** **[C]** |
| Hardware | StarExec | JKU cluster, dual AMD EPYC 7313 @ 3.7 GHz, **one core per solver task** **[C]** |
| Scoring | # solved | **PAR-2**: `(Σ S + U × 900 × 2) / F` **[C]** |

Solver interface, unchanged 2023→2026 **[C]**: one file argument; **exit 10 = true, exit
20 = false, anything else = failure**; max three submissions per submitter per category;
Linux 64-bit. Benchmark selection rule (2023): any formula solved by *all* solvers in
under one second is disqualified from the final set. **[C]** Policy shift: 2023 said
submitted tools would *not* be made public; 2026 **requires** public source under a
research license, with Zenodo archiving recommended. **[C]**

### Winners

**QBFEVAL'22** **[C]**: PCNF+CIT — **CAQE**; PNCNF — **QuAbS**; DQBF — **Pedant**.

**QBFGallery 2023** **[C]** (the report gives both a *unique* ranking — best configuration
per solver family — and an *overall* ranking; they disagree, so quote which one):

| Track | 1st | 2nd | 3rd | VBS |
|---|---|---|---|---|
| PCNF (356 formulas) | **CAQE-pre** — PAR-2 842.36, 231 solved | DepQBF-v1 — 1301.56, 110 | dynQBF — 1493.93, 70 (but **16 uniquely** solved, highest in track) | 287 |
| PNCNF/QCIR (391) | **QuAbS-CAQE** — 548.48, **286** | CQESTO — **539.97** (better PAR-2), 283 | miniQU-dl — 748.63, 234 | 344 |
| DQBF (354, reused from 2022) | **Pedant** — 382.02, 284 (10 unique) | DQBDD — 433.04, 271 | HQS-2022 — 506.97, 259 | 290 |
| Crafted | **CAQE-Bloqqer** — the only solver to solve every formula in all 14 families | — | — | — |
| Preprocessor | No winner declared: "there is no specific preprocessor which is the best choice for all QBF solvers" | — | — | — |

One DQBF solver was **disqualified for producing differing results** — the report does not
name it. **[C]** In the PCNF track CAQE swept the top three overall places with three
different preprocessor pairings, which is exactly why the unique ranking exists. **[C]**

**QBFGallery 2026 winners are unknown** — presented, not published. **[C]**

### Solvers

| Solver | Repo | Language | License |
|---|---|---|---|
| **CAQE / dCAQE** | <https://github.com/ltentrup/caqe> | **Rust** | MIT |
| QuAbS | <https://github.com/ltentrup/quabs> | C | none stated |
| Qute | <https://github.com/fslivovsky/qute> | C++ | MIT (most actively maintained; last push 2026-03-31) |
| DepQBF | <https://github.com/lonsing/depqbf> | C | GPL-3.0 (the QRP-trace producer feeding QBFcert) |
| DQBDD | <https://github.com/jurajsic/DQBDD> | C/C++ | LGPL-3.0 |
| dynQBF | <https://github.com/gcharwat/dynqbf> | C++ | — (tree-decomposition expansion) |
| Pedant | <https://github.com/fxreichl/Pedant-QBFEVAL22> | wrapper only | — |
| QRATPre+ | <https://github.com/lonsing/qratpreplus> | C | GPL-3.0 |
| Bloqqer | <https://fmv.jku.at/bloqqer/> | C | — |
| HQS / HQSpre, GhostQ, QFUN, miniQU | not located on GitHub | — | — |

**CAQE is the only Rust QBF solver of consequence, and it won the PCNF track at both the
2022 and 2023 events.** **[C]**

### Proof and certification status — the honest picture

**No QBF track has ever mandated proofs.** **[C]** The only certification track in the
entire history is QBFEVAL'16's *"Evaluate & Certify (**non-competitive**) Track"*, and
2026's certified track was conditional on submissions. Correctness is enforced *post hoc*
by discrepancy analysis between solvers — which is how the 2023 DQBF disqualification
happened. Certification appears in the organizers' own "future work" slides in both 2019
("Certification for DQBF") and 2023 ("Certification"). **[C]**

| Artifact | What |
|---|---|
| **QRAT** | Quantified Resolution Asymmetric Tautology; simulates virtually all inference used in state-of-the-art QBF tools including universal expansion. Heule, Seidl, Biere, IJCAR 2014 **[C]** |
| **QRAT+** | Generalizes QRAT's redundancy check from propositional UP to QUP. Lonsing & Egly 2018, arXiv 1804.02908 **[C]** |
| **qrat-trim** | The checker. C, MIT header, **last source edit 2020-10-01, repo last push 2021-02-13, 6 commits, 0 stars**. Does checking *and* Skolem-certificate output (`cheskol.c`), with a hardcoded `TIMEOUT 900`. <https://github.com/marijnheule/qrat-trim> **[C]** |
| **QBFcert** | Solver-independent Skolem/Herbrand certificate pipeline: QBF solver (DepQBF) → QRPcheck → QRPcert → CertCheck → a SAT solver (Lingeling). Certificates are AIGs. GPLv3. <https://fmv.jku.at/qbfcert/> **[C]** |
| **DQRAT** | The DQBF analogue. Chew & Peitl, arXiv 2605.29763 (28 May 2026): **"DQRAT has only existed in theory"** until their prototype `DQRAT-check` (no public repo found); certification remains "an ongoing challenge" **[C]** |
| Expansion-based certification | Bhavnani, Hofstadler, Seidl, QBF Workshop 2026 — certifying **true** QBFs in expansion-based solving, the hard direction **[C]** |

**No verified QRAT checker exists in any proof assistant.** The mechanized-checker work in
this neighbourhood is all propositional (cake_lpr, GRAT, the Lean LSR checker) or model
counting (the Lean 4 CPOG checker). **[I]** — this is absence-of-evidence, but a
consistent absence across several searches.


---

## 6. Pseudo-Boolean Competition, and the certified / proof-logging movement

### 6.1 The PB competition: dead for eight years, revived *by the proof-logging community*

| Years | Status |
|---|---|
| 2005–2007, 2009–2012 | Competitions (first organized by Roussel + Manquinho) **[C]** |
| 2015 | PB *Evaluation* (not a full competition) **[C]** |
| 2016 | **PB16** — last of the old era **[C]** |
| **2017–2023** | **"8 years with no competition"** **[C]** |
| 2024 | **PB24 — "rebirth"**, at SAT 2024 **[C]** |
| 2025 | PB25, at SAT 2025 **[C]** |
| **2026** | **PB26** — submissions due 2026-05-18, results at SAT 2026 (20–23 Jul), FLoC 2026 Olympic Games **[C]** |

Why it stopped and restarted, verbatim from the PB24 deck **[C]**: it stopped from "lack of
interest (very few solvers submitted in 2016)"; it restarted "because **Jakob Nordström
has insisted for two years** to have a new competition!" Organizer throughout: Olivier
Roussel, CRIL, Université d'Artois. Steering committee (PB25/26): Ansótegui, Fichte,
Nordström, Roussel. **[C]** Sat4j is the only solver submitted to every edition since
2005. **[C]**

**Correcting two common beliefs.**

1. **"Small / big integers" tracks no longer exist.** PB24 removed the distinction
   ("decided in 2005, when most solvers still used 32-bit integers"). A solver now answers
   `s UNSUPPORTED` for itself, and two rankings are produced: over *all* instances, and
   over the subset supported by *all* solvers. Solvers are expected to handle ≥64-bit
   integers. **[C]**
2. **VeriPB proof logging is OPTIONAL, not required.** The rules say "certificates of
   unsatisfiability/optimality **must be generated in the VeriPB format**" — that is a
   *format* mandate conditional on entering a `-CERT` track, not a participation mandate.
   PB25 had **43 solvers in DEC-LIN but only 6 in DEC-LIN-CERT**. **[C]**

But the incentive worked. PB24 deck, slide 23 **[C]**: *"to our knowledge, before June
2024, **no PB solver generated a proof for VeriPB v2**. The competition has encouraged
(maybe forced?) 3 teams to implement proof generation."* **The competition bootstrapped
the entire PB proof-logging ecosystem from zero in one year.**

### 6.2 PB tracks, formats, rules

Track axes **[C]**: linearity (**LIN** / **NLC**, products of literals); objective (**DEC**
decision / **OPT** optimization); soft-hard (**SOFT** all violable / **PARTIAL** ≥1 hard —
the WBO family); certification (`-CERT` variants of DEC-LIN and OPT-LIN); parallelism
(sequential ranked on CPU, parallel on wall clock). PB26 opens PBS, PBS-CERT, PBO,
PBO-CERT unconditionally; WBO and non-linear open only if there is enough interest. **[C]**

| Track | PB24 solvers / instances | PB25 solvers / instances |
|---|---|---|
| OPT-LIN | 37 / 478 | 52 / 555 |
| DEC-LIN | 33 / 397 | 43 / 502 |
| PARTIAL-LIN (WBO) | 11 / 208 | 10 / 208 |
| SOFT-LIN (WBO) | 11 / 60 (too few, unranked) | 10 / 60 (unranked) |
| OPT-NLC / DEC-NLC | 9 / 54, 9 / 10 (unranked) | 14 / 57, 13 / 10 (unranked) |
| **DEC-LIN-CERT + OPT-LIN-CERT** | **4** | **6** |

**[C]** All of the above.

Formats **[C]**:

| Format | Spec |
|---|---|
| OPB, restricted competition subset | <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf> |
| OPB, general | <https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf> (the PB25 page's relative link to this 404s) |
| Competition requirements (solver output, runtime env) | <https://www.cril.univ-artois.fr/PB24/competitionRequirements.pdf> |
| Classic OPB + **WBO** (Roussel & Manquinho, 2016) | <http://www.cril.univ-artois.fr/PB16/format.pdf> — the spec VeriPB itself cites |

A clause `x1 ∨ x̄2 ∨ x3` in OPB is the inequality `+1 x1 +1 ~x2 +1 x3 >= 1 ;`. **[C]**

Rules:

| Rule | PB24 | PB25 | PB26 |
|---|---|---|---|
| Sequential | 1 h CPU, 31 GB | 1 h CPU, 31 GB | 1 h CPU, 31 GB **[C]** |
| Parallel | 20 cores, 1 h wall | 20 cores, 1 h wall | ≥8 cores, 1 h wall **[C]** |
| Proof size cap | 100 GB → raised to 400 GB | 100 GB | 100 GB **[C]** |
| Proof verification budget | 5 h CPU | 5 h → extended to 10 h | 5 h **[C]** |
| Scoring | # solved, ties by cumulative time | same | **PAR-2** (new), lexicographic secondary **[C]** |
| VeriPB version | v2 | v2 (+ optional unchecked deletion) | **v3** (back-compat with v2) **[C]** |

Hardware (PB24/25): bi-CPU Xeon E5-2637 v4 @ 3.5 GHz, 128 GB, 4 jobs/host, 2 cores/job.
**[C]**

**The soundness rules are unusually candid and worth reading in full** **[C]**:

- A **SATISFIABLE** answer is the only one checked unconditionally — the model is replayed
  against every constraint.
- **UNSAT / OPTIMUM in the non-CERT tracks are checked only by cross-solver consistency**:
  *"An UNSATISFIABLE answer is not reliable. Some solvers may wrongly indicate
  UNSATISFIABLE but unless another solver finds a model, this will remain undetected."*
- In the CERT tracks, an invalid VeriPB proof ⇒ "considered incorrect and not ranked". But
  a *verification timeout* is not a failure — the instance is counted as plain OPT/UNSAT
  instead of certified. Hence the `UNSC` / `OPTC` answer codes and two sub-rankings.

### 6.3 PB winners

**PB24** **[C]**

| Track | Winner | Solved / total |
|---|---|---|
| DEC-LIN | Hybrid-CASHWMaxSAT…CadSP+Exact | 312 / 397 (VBS 362) |
| OPT-LIN | **mixed-bag** (Jabs, Berg, Järvisalo) | 279 / 478 (VBS 339) |
| PARTIAL-LIN | FiberSCIP 20 cores | 160 / 208 |
| DEC-LIN-CERT | **Exact veripb2** — 291 (175 UNSC); RoundingSat log 288 (189 UNSC) | — |
| OPT-LIN-CERT | **RoundingSat log** — 254 (218 OPTC + 13 UNSC) | — |

**PB25** **[C]** — two rankings that disagree at the top:

| Track | Winner, *all* instances | Winner, *supported-by-all* subset |
|---|---|---|
| DEC-LIN | **SCIP-NaPS** — 406/502 (81%) | Hybrid-CASHWMaxSATDisjCadS+SynLSCD — 390/472 |
| OPT-LIN | **UWrMaxSat-SCIP** — 358/555 (65%) | Hybrid-CASHWMaxSATDisjCom+ExactPRS9 — 289/420 |
| PARTIAL-LIN | **OR-Tools CP-SAT** — 172/208 | — |
| DEC-LIN-CERT | **roundingsat+pbsuma-log** — 387 (128 SAT, 258 UNSC) | — |
| OPT-LIN-CERT | **roundingsat+pbsuma-opt-log** — 329 (310 OPTC, 18 UNSC) | — |

The whole PB25 certified field was six entries: three RoundingSat variants, `Exact proof`,
`Sat4j Res VeriPB`, `Sat4j CP VeriPB`. **[C]** **Open-WBO did not appear in PB24 or
PB25.** **[C]** PB26 results were not reachable at
<https://www.cril.univ-artois.fr/PB26/results/> when checked. **[C]**

### 6.4 The cost of certification — measured, not speculated

| Measurement | Value |
|---|---|
| PB25: proofs verified | 3320; **0.76% needed more than 5 h**; 53 timed out **[C]** |
| PB25: max verification/search ratio | **2387×** **[C]** |
| CP 2025 paper, RoundingSat: proof-generation overhead | 2.7% median / 21.1% p95 / 46.2% max **[C]** |
| CP 2025, RoundingSat: verification vs. solve time | 1.43× median / 9.22× p95 / 19.17× max **[C]** |
| CP 2025, Sat4j cutting planes: verification vs. solve | 0.54× median / 1.60× p95 / 3.83× max **[C]** |
| Rank cost: `Exact proof` in OPT-LIN | 285 solved → **234** when uncertified answers excluded **[C]** |

The CP 2025 authors' conclusion: proof logging + checking is "now quite close to the level
of SAT solving, and hence is clearly practically feasible." **[C]** These are the numbers
to cite against a "proofs are too expensive" objection.

### 6.5 VeriPB

<https://gitlab.com/MIAOresearch/software/VeriPB> · <https://veripb.org/>

| Property | Value |
|---|---|
| Language | **VeriPB 3.0 is written in Rust** (2.0 was Python/C++, on branch `version2`) **[C]** |
| License | **Dual Apache-2.0 / MIT** **[C]** |
| Distribution | `cargo install --path .`; also on **crates.io**, docs at docs.rs/veripb **[C]** |
| Spec | SAT Competition 2026 documentation, dated 2026-03-20 **[C]** |

**Proof system**: cutting planes over 0-1 integer linear inequalities plus strengthening.
Rule families **[C]**: `pol` (cutting-planes: addition, multiplication, division,
saturation, literal axioms), `rup`, **`red`** (redundance-based strengthening — the
generalization of RAT, written as a constraint *plus a witness substitution*: a DRAT RAT
step on pivot `x1` is exactly `x1 -> 1`), **`dom`** (dominance-based strengthening,
requires a loaded **order** — this certifies symmetry and dominance breaking in
*optimization* and **has no DRAT analogue at all**), orders as first-class objects,
subproofs with *autoproven* goals, checked vs. unchecked deletion, and Output / Conclusion
sections so one format covers decision, optimization, enumeration and reformulation.

**The architecture is the same idea as axeyum's identity statement, already built.** **[C]**
VeriPB reads a convenient **augmented format** (what solvers emit) and *elaborates* it into
a restricted **kernel format**, which the verified checker consumes:

```
veripb --cnf --proofOutput translated.pbp input.cnf input.pbp   # untrusted elaboration
cake_pb_cnf input.cnf translated.pbp                            # trusted checking
```

Honest scope statement from the same document **[C]**: *"if all the reasoning performed by
some particular SAT solver can efficiently be captured by standard DRAT proof logging,
then there is no real reason to use pseudo-Boolean proof logging for that solver."* PB
logging earns its keep for **cardinality reasoning, Gaussian elimination / parity, and
symmetry breaking** — all three of which axeyum has code for. Implementation gotcha:
VeriPB requires **all** learned clauses to be logged including units, and deletion of unit
clauses is meaningful (DRAT checkers ignore it); "no such patching of formally incorrect
proofs is offered by VeriPB." **[C]**

Paper lineage, in the README's own citation-priority order **[C]**:

1. Bogaerts, Gocht, McCreesh, Nordström — *Certified Dominance and Symmetry Breaking for
   Combinatorial Optimisation*, **JAIR 77:1539–1589** (2023; prelim. AAAI '22)
2. Gocht, Nordström — *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean
   Proofs*, AAAI '21
3. Gocht — PhD thesis, *Certifying Correctness for Combinatorial Algorithms by Using
   Pseudo-Boolean Reasoning*, Lund, 2022

**Who emits VeriPB proofs** **[C]** (roster on veripb.org): SAT — **CaDiCaL**, **BreakID**,
**satsuma**; PB — **RoundingSat**, **Exact**, **HitPBO**; MaxSAT — **CGSS**, **Pacose**,
**QMaxSATpb**, **MaxPre**; CP/graph — **Glasgow Constraint Solver**, **Glasgow Subgraph
Solver**, **ZykovColor**, **Scuttle**; MIP — **PaPILO**. Plus **Sat4j** (resolution and
cutting-planes modes) and **WMaxCDCL**. **SBVA is *not* on the roster** — the
symmetry-breaking entries are BreakID and satsuma. **[C]**

### 6.6 The verified checkers, as a family

| Tool | Checks | Verified in | Source |
|---|---|---|---|
| **cake_lpr** | CNF unsat via **LRAT / LPR**, text and binary; also transformation checking | CakeML / HOL4 | binaries <https://github.com/tanyongkiam/cake_lpr>, source `CakeML/cakeml/examples/lpr_checker` **[C]** |
| **cake_pb** family (`cake_pb`, `cake_pb_cnf`, graph/, cp/) | Pseudo-Boolean, decision **and** optimization; the third invocation mode checks **problem reformulation**, not just UNSAT | CakeML / HOL4 | binaries <https://gitlab.com/MIAOresearch/software/cakepb>, source `CakeML/cakeml/examples/pseudo_bool` **[C]** |
| **cake_xlrup** | **CNF-XOR** unsatisfiability | CakeML / HOL4 | <https://cakeml.org/checkers.html> **[C]** |
| **cake_vipr** | **Mixed-integer linear programming** results (VIPR certificates) | CakeML / HOL4 | <https://cakeml.org/checkers.html> **[C]** |
| **GRAT** (`gratgen` unverified generator + `gratchk` verified checker) | DRAT in, GRAT out, checked; also SAT-mode model checking | Isabelle/HOL | <https://www21.in.tum.de/~lammich/grat/> **[C]** |
| **Verified SR / LSR checker** | The **SR** system (generalizes PR and RAT); DSR unhinted, LSR hinted | **Lean 4** | Codel, Avigad, Heule, FMCAD 2024 **[C]** |
| **PBLean** | Imports **VeriPB** certificates into Lean 4 *by reflection*; the checker is a Boolean function proved sound in Lean and run as compiled native code | **Lean 4** | Szeider, arXiv 2602.08692 (Feb 2026) **[C]** |
| **CPOG checker + model counter** | Certified knowledge compilation → **formally verified model counting** | **Lean 4** | Bryant, Nawrocki, Avigad, Heule, JAIR 2025, DOI 10.1613/jair.1.15958 **[C]** |
| drat-trim / dpr-trim / lrat-trim | Unverified trimmers/elaborators that sit **outside** the trust base — they only add hints | C, MIT | <https://github.com/marijnheule/drat-trim>, <https://github.com/marijnheule/dpr-trim> **[C]** |

The `cake_pb_cnf` end-to-end theorem is the specification shape worth copying **[C]**:
assuming CakeML-compiled x64 machine code under the FFI model, the program never crashes,
fails gracefully on heap/stack exhaustion, and **whenever `s VERIFIED UNSAT` is printed,
the input CNF file parses in DIMACS and is unsatisfiable — and no other output is possible
on stdout.** That is "the output string implies the semantic property of the file the
program was given", which is a strictly stronger claim than "the checker exited 0".

LRAT line format, verbatim **[C]**: `<ID> <CLAUSE> 0 <IDs> [-<ID> <IDs>]* 0`. Input CNF
clauses take IDs 1..n; the first literal of a RAT clause is the pivot; the first `<IDs>`
block is unit propagation from the blocking assignment; each `-<ID> <IDs>` block gives
propagations for a RAT resolution partner. Deletion: `<ID> d <IDs> 0`. The deployed chain
is `DRAT (solver) → drat-trim -L → LRAT → cake_lpr → "s VERIFIED UNSAT"`. **[C]**

**Lean 4 has become the second verified-checker ecosystem alongside CakeML/HOL4**, in three
independent 2024–2026 efforts (SR checking, CPOG model counting, PBLean). **[C]** PBLean's
distinguishing claim is directly relevant to a project with a Lean kernel: *"Rather than
producing verdicts like external checkers, PBLean generates formal **theorems** composable
within larger Lean developments."*

### 6.7 Where proof logging is mandatory — the cross-competition table

| Competition | Status |
|---|---|
| **SAT Competition, Main track** | **MANDATORY** since ≤2022 (DRAT), with a *choice* of verified checkers since 2023 and four options in 2026. Solvers that cannot certify go to No-Limits (2024/25) / **Experimental** (2026). **[C]** |
| **PB Competition** | **OPTIONAL** — separate `-CERT` tracks; VeriPB format mandated within them; VeriPB+CakePB used to check. 4/33 (2024), 6/43 (2025) entered. **[C]** |
| **MaxSAT Evaluation** | **ABSENT.** No certified track in any edition. **[C]** |
| **Model Counting Competition** | **ABSENT.** Tracks graded on answer accuracy; no proof/certificate/CPOG requirement. **[C]** |
| **SMT-COMP** | **ABSENT — no proof track.** Tracks: Single Query, Incremental, Unsat Core, **Model Validation**, Parallel, Cloud. Model Validation checks *models* (the SAT side); Alethe/LFSC/Carcara are research tooling outside the competition. **[C]** |
| **QBFGallery** | **ABSENT** — only ever a non-competitive certification track (2016), conditional in 2026. **[C]** |

SAT is the only competition where proof logging is mandatory. PB is the only *other* one
with a certified track, and it was created in 2024 precisely to force the ecosystem into
existence — which it demonstrably did. MaxSAT, model counting, SMT and CP all have a
mature *research* literature on certification with **no competition pressure behind it.**


---

## 7. Adjacent Boolean arenas

Four widely-repeated beliefs turned out to be wrong. Corrections first, because they change
what is worth pursuing:

| Common belief | Reality |
|---|---|
| SAT Competition had a crypto track in 2024 or 2025 | It was **SAT Competition 2021 only**. `track_crypto.html` returns 200 for 2021 and **404 for 2022–2026**. **[C]** |
| The incremental track ran in 2015 and 2020 | SAT **Race 2015** (introduced), then SAT Comp **2016, 2017, 2020, 2021**. **Dead since 2021.** **[C]** |
| SMT-COMP has QF_BV / QF_ABV / QF_UFBV divisions | Divisions are **QF_Bitvec** (= QF_BV) and **QF_Equality+Bitvec** (= QF_ABV + QF_AUFBV + QF_UFBV + QF_UFBVDT). QF_ABV is not its own division. **[C]** |
| IPASIR-UP is by Fazekas/Niemetz/Preiner/**Pollitt**/Biere/**Nadel** | It is Fazekas, Niemetz, Preiner, **Kirchweger, Szeider**, Biere (SAT 2023). Pollitt is on the *different* paper *Certifying Incremental SAT Solving* (LPAR-24). **[C]** |

### 7.1 Incremental SAT / IPASIR

`ipasir.h` (<https://github.com/biotomas/ipasir>) exports `ipasir_signature`, `init`,
`release`, `add`, `assume`, `solve` (10 = SAT / 20 = UNSAT / 0 = interrupted), `val`,
`failed`, `set_terminate`, `set_learn`. The track pages say "9 functions"; the header
declares 10 (`set_learn` is the optional extra). **[C]**

| Year | Incremental Library Track |
|---|---|
| SAT Race 2015 | **Introduced** **[C]** |
| SAT Comp 2016, 2017 | Ran **[C]** |
| SAT Comp 2018, SAT Race 2019 | No **[C]** |
| SAT Comp 2020 | **Ran, with results** **[C]** |
| SAT Comp 2021 | Track page published; **results absent from the results page** **[I]** |
| 2022–2026 | **Gone.** `track_incremental.html` is 404 for 2022, and present-but-orphaned for 2023 (stale template) **[C]** |

2020 harness **[C]**: six IPASIR *applications* (`bones`, `essentials`, `lsp`, `max`,
`ijtihad`, `pasar`), 50 selected inputs each; ranking is by (application + input) pairs
solved. Per-application winners: CryptoMiniSat5 (bones, essentials, lsp), abcdsat-i20
(max), CaDiCaL-sc2020 (ijtihad), Riss-7.1.2 (pasar).

**IPASIR-2** (<https://github.com/ipasir2/ipasir2>) is still a draft, and its README states
the goal outright: *"reviving the incremental library track of the SAT competition"* — a
first-party confirmation the track is defunct. **[C]** Four changes over IPASIR-1: error
codes on every function (data via out-params, `ipasir2_` prefix, breaking); an
*automatable* configuration interface (tuners can enumerate options with min/max); a
**clause-import** callback the solver pulls from while SOLVING, carrying a *pledge*
(equivalence-preserving / satisfiability-preserving / none) so lazy theory encodings and
parallel clause sharing both work; and fixed-variable notification. **[C]**

**IPASIR-UP** (SAT 2023, DOI 10.4230/LIPIcs.SAT.2023.8; journal version *Satisfiability
Modulo User Propagators*, JAIR 81, 2024) adds callbacks to observe assignments and
backtracking, propagate externally, add clauses lazily during search, and check final
models — CDCL(T)-style interaction that cannot be expressed clausally. Implemented by
**CaDiCaL** (reference), used by **cvc5** as its main CDCL(T) engine, by **SAT Modulo
Symmetries**, and exposed through **PySAT**. **[C]** Note CaDiCaL is now at **3.0.1**, and
3.0.0 was a *breaking* change for incremental users (explicit `declare_more_variables`)
driven by proof checking with BVA extension variables. **[C]**

### 7.2 Local search

**There is no local-search track anywhere in SAT Competition and has not been since 2018.**
**[C]** Random Track: 2016, 2017 (YalSAT won), 2018 ("Random Satisfiable Track" — the
last). SAT Race 2019 had a single track; 2020–2026 have none. Where SLS lives now:

1. **Inside Main-track CDCL hybrids.** Kissat ships `src/walk.c`, CaDiCaL `src/walk.cpp`;
   the JAIR paper *Better Decision Heuristics in CDCL through Local Search* says "Kissat
   sat already includes a simple local search procedure inspired by ProbSAT and
   particularly YalSAT." **[C]**
2. **SAT Comp 2026's Experimental Track** — no proof checking required, so structurally the
   only SAT-Comp home for an incomplete solver. 2 sequential solvers entered in 2026. **[C]**
3. **MaxSAT Evaluation anytime tracks** — the recognized competitive venue today. **[C]**
4. **MiniZinc Challenge Local Search category** — live and medalled. **[C]**
5. **Sparkle SAT Challenge 2018** (FLoC Olympic Games) was an *algorithm-selection*
   challenge, single edition, never repeated for SAT. **[C]** for 2018, **[I]** for the
   non-repetition.

### 7.3 Cryptographic / XOR SAT

The crypto track was **SAT Competition 2021** and nowhere else: 200 benchmarks all from
cryptography (100 SAT, 100 UNSAT), 5000 s, automatically including everyone registered for
Main or CaDiCaL-Hack, and reported as "Score Crypto"/"Solved Crypto" *columns inside the
Main track*, not a separate medal table. Top crypto scorers: Cadical_SCAVEL01, hKis_psids,
hCaD. **[C]**

**CryptoMiniSat** (<https://github.com/msoos/cryptominisat>) **[C]**: Gauss-Jordan
elimination compiled in by default since 5.8 and *auto-disabled if it underperforms*
(`--maxmatrixrows` 2000, `--maxmatrixcols` 1000, `--maxnummatrices` 5,
`--gaussusefulcutoff` 0.2, `--autodisablegauss` 1). Input is "a CNF with xors in it (either
in CNF or XOR+CNF form)". **Bosphorus** (<https://github.com/meelgroup/bosphorus>, DATE
2019, arXiv 1812.04580) iterates ANF and CNF techniques, feeding facts learned in each to
the other. **[C]**

**Is XOR reasoning DRAT-expressible? Yes — but plain DRAT is the wrong shape in practice.**
This is the most actionable finding in this section for axeyum, which already has
`gf2.rs`, `xor_cdcl.rs` and `xor_drat.rs`.

| Work | Claim |
|---|---|
| Philipp & Rebola-Pardo, **JELIA 2016**, *DRAT Proofs for XOR Reasoning* | **Yes, expressible** — two methods, one a direct translation of every XOR **[C]** |
| Soos & Bryant, POS'22 / arXiv **2304.04292** | CryptoMiniSat + **TBUDDY** (proof-generating BDD library) → proofs in the standard clausal framework; "CDCL … fare poorly on formulas involving large numbers of parity constraints" **[C]** |
| Bryant & Heule, **TACAS 2021**, arXiv 2105.00885 | BDD-based solver emits **LRAT**, with arbitrary existential quantification **[C]** |
| **The current CryptoMiniSat pipeline** | `cryptominisat5 input.cnf proof.frat` → `frat-xor elab` → **`.xlrup`** → **`cake_xlrup`** (CakeML-verified) prints `s VERIFIED`. <https://github.com/meelgroup/frat-xor> **[C]** |

**XLRUP** is the operative format: "RUP proofs, extended with both XOR- and BNN-specific
steps" (arXiv 2507.02916), also used by *Formally Certified Approximate Model Counting*
(arXiv 2406.11414). **`frat-xor` is a Rust fork of FRAT-rs**, so the elaborator side of
that pipeline is already in Rust. **[C]**

### 7.4 SAT-based planning (IPC)

**IPC 2023** (<https://ipc2023.github.io/>) ran five track families (Classical, Learning,
Probabilistic, Numeric, HTN). **No IPC edition in 2024 or 2025** **[I]**. **IPC 2026 ran** —
numeric tracks at <https://ipc2026-numeric.github.io/> (Optimal / Satisficing / Agile,
results Jun–Jul 2026, a subset of PDDL 2.1, fragments SNP and LNP), plus a new **Epistemic
Planning** track announced at ICAPS 2026. **[C]**

Classical 2023 rules **[C]**: a subset of PDDL 3.1; Optimal and Satisficing 1 core / 8 GB /
30 min, Agile 5 min; Optimal counts solved and marks *the whole domain* unsolved if a
suboptimal or invalid plan is returned; Satisficing scores C*/C against a reference plan;
Agile scores `1 − log(T)/log(300)`. 2023 winners: **Ragnarok** (optimal, 77), **Scorpion
Maidu / Levitron** (satisficing, 71.86 / 71.79), **DecStar-2023** (agile, 40.25).

**SAT-based planners have effectively left.** The IPC 2023 classical roster (30+ entrants)
is portfolios, abstraction and decoupled search; **Madagascar / Mp does not appear** and is
described in secondary sources as no longer actively maintained. **[C]** for the roster,
**[I]** for the conclusion.

**No proof requirement in IPC** — plans are *validated* (VAL-style), with domain-level
disqualification for invalid plans. The certified-unsolvability line is real but separate:
the **Unsolvability IPC 2016** (<http://unsolve-ipc.eng.unimelb.edu.au/>, Muise &
Lipovetzky) was a **single edition, never repeated** **[C]**/**[I]**; Eriksson, Röger,
Helmert, *Inductive Certificates of Unsolvability for Domain-Independent Planning* (IJCAI
2018); Eriksson & Helmert (2020), *Certified Unsolvability for SAT Planning with Property
Directed Reachability*. Most recent and most Boolean-adjacent: **Pseudo-Boolean Proof
Logging for Optimal Classical Planning** (arXiv 2504.18443) — cutting-planes proofs checked
by **VeriPB**, i.e. planning adopting the SAT community's stack. **[C]**

### 7.5 Constraint programming — where a CNF engine can actually medal

**MiniZinc Challenge** (<https://www.minizinc.org/challenge/>), editions through **2026**.
Five categories: FD Search (fixed), Free Search, Parallel (≤8 cores), Open (portfolios),
Local Search. **20 min process time per instance, including MiniZinc→FlatZinc translation.**
1 core / 16 GB for FD and Free; 8 cores / 64 GB for Parallel and Open. Scoring is a
Borda count. Submission is a **Docker image**; the entry must be a FlatZinc solver
accepting `-i`/`-a`, `-f`, `-p <n>`, or a MiniZinc solver accepting `--output-mode dzn`,
`--output-objective`, `-f`, `-p <n>`. **Nothing prohibits translation-based solvers.** **[C]**

| Category | 2025 gold / silver / bronze | 2026 gold / silver / bronze |
|---|---|---|
| Fixed | OR-Tools CP-SAT / Choco CP-SAT / SICStus, Pumpkin (tie) | OR-Tools CP-SAT / Pumpkin / Choco (CP+LCG) |
| Free | OR-Tools CP-SAT / **PicatSAT** / Choco CP-SAT | OR-Tools CP-SAT / **PicatSAT** / Pumpkin |
| Parallel | OR-Tools CP-SAT / **PicatSAT** / iZplus | OR-Tools CP-SAT / **PicatSAT** / Choco (CP) |
| Local Search | OR-Tools CP-SAT LS / Yuck / Atlantis | QiuQi-MIXSolver / OR-Tools CP-SAT LS / Yuck |
| Open | no medals (no portfolio entrants) | OR-Tools CP-SAT / Parasol / CUFE |

**[C]** **PicatSAT, a pure CP-to-SAT compiler, took silver in Free and Parallel two years
running.** That is the clearest existing proof that a bit-level engine can medal in a CP
arena through a front end alone.

**XCSP3 Competition** (<https://xcsp.org/competitions/>) — annual since 2022, editions
XCSP22…XCSP26, tracks Main CSP, Main COP, Fast COP, Parallel COP, Mini CSP, Mini COP.
**SAT-based solvers compete and place: "Fun-sCOP (kissat)" took silver in Main CSP in
2025.** Fun-sCOP is literally an XCSP3-core → CNF encoder around Kissat. Proceedings: arXiv
2312.05877 (2023), 2412.00117 (2024), 2511.06918 (2025). **[C]** This is the
lowest-friction CP arena for a CNF engine.

### 7.6 SMT-COMP

<https://smt-comp.github.io/>

| Edition | Tracks with results |
|---|---|
| 2023 | Single Query, Incremental, Unsat Core, Model Validation, **Proof Exhibition**, Parallel, Cloud **[C]** |
| 2024 | Single Query, Incremental, Unsat Core, Model Validation, Parallel, Cloud **[C]** |
| 2025 | as 2024 but **no Cloud** ("due to the lack of suitable infrastructure") **[C]** |
| 2026 | Single Query, Incremental, Unsat Core, Model Validation, Parallel — 21st edition, IJCAR-26 / SMT Workshop 2026; results generated 2026-07-25 **[C]** |

**The Proof Exhibition track existed in 2022 and 2023 only, and was never a real ranking.**
From the 2023 slides verbatim: *"Solver submitted together with a checker for
unsatisfiability proofs / No predefined format or checker / **No ranking** / Qualitative
assessment."* Scale in 2023: 4 solvers, 19 experimental divisions, 59,114 benchmarks. It
does not appear in 2024, 2025 or 2026. **[C]** Rules: 20-minute wall clock in every track;
error score `e=1` for any wrong sat/unsat; unsat cores validated by *other* sound solvers
from the Single Query track. **No track in 2024–2026 requires a proof.** **[C]**

| Division | Logics | SMT-LIB benchmarks |
|---|---|---|
| **QF_Bitvec** | QF_BV | **10,703** (2024, 2025) **[C]** |
| **QF_Equality+Bitvec** | QF_ABV (7,574), QF_AUFBV (75), QF_UFBV (764), QF_UFBVDT (76) | **8,489** **[C]** |

The 2026 QF_Bitvec Single Query run used only **2,540** benchmarks — division caps are
`min(n, max(300, 50n/100))` plus removal of everything solved by all solvers in <1 s during
2018–2024, so **do not quote 10,703 as a stable denominator.** **[C]**

| Year | Division | Winner | Solved |
|---|---|---|---|
| 2024 | QF_Bitvec | **Bitwuzla** | 10,489 / 10,703 (STP 10,488 — one behind) |
| 2025 | QF_Bitvec | **Bitwuzla-MachBV** | 10,523 (Bitwuzla 10,498, Yices2 10,491) |
| 2025 | QF_Equality+Bitvec | **Bitwuzla** | 8,279 / 8,489 (Yices2 8,230, Z3-Owl 8,056) |
| 2026 | QF_Bitvec | **Bitwuzla-MachBV** | 2,495 / 2,540 (Bitwuzla 2,475, bitwuzla-dandelion 2,472) |

**[C]** Bitwuzla wins QF_BV sequentially and in parallel every year 2024–2026. Note
**`bv_decide`**, the Lean-integrated bit-blaster, is now a competitive entrant (2025:
`bv_decide` and `bv_decide-nokernel`; 2026: `bv_decide-nokernel` at 2,404). **[C]**

### 7.7 HWMCC — the arena whose rules already match axeyum's thesis

<https://hwmcc.github.io/>

| Edition | Tracks | Certificates |
|---|---|---|
| **HWMCC'24** (FMCAD'24 Prague), 12th event | Bit-level (**AIGER**), Word-level BV (**BTOR2**), Word-level BV+Arrays (BTOR2) — all safety | **Mandatory safety certificates on the bit-level track**, validated with **Certifaiger**; counterexamples with `aigsim`. 319 benchmarks/track (321 arrays), 9 medals, 9 model checkers **[C]** |
| **HWMCC'25** (FMCAD'25 Menlo Park, Oct 2025) | 4 tracks: word-level safety w/o arrays, word-level safety with arrays, bit-level safety (AIGER 1.9), **bit-level liveness — new** | BTOR2 counterexamples mandatory (BtorSim); bit-level requires **both** counterexamples and safety certificates. ~400+ benchmarks, 10 medals, artifacts on Zenodo **[C]** |

Winners: HWMCC'24 — **rIC3** gold on bit-level (248) *and* word-level BV (249); avr led
BV+Arrays (200); pavy silver bit-level (217). HWMCC'25 — rIC3 two golds, plus nuXmv and
pono golds. **[C]**

**Certifaiger** (<https://github.com/Froleyks/certifaiger>) checks witness circuits in a
modified **AIGER 1.9** with reset functions, by **emitting SAT checks for simulation,
inductiveness and ranking obligations**. It uses **Kissat** by default; built with
`make lrat-trim` it uses **CaDiCaL streaming LRAT into lrat-trim** for higher assurance.
Papers: *Introducing Certificates to the Hardware Model Checking Competition* (CAV'25,
10.1007/978-3-031-98668-0_14) and *Hardware Model Checking Certification with Certifaiger
and Cerbtora* (IJCAR'26) — **Cerbtora** is the emerging BTOR2 counterpart. **[C]**

**This is the single best strategic fit in the survey.** It is bit-level, the input is
AIGER (which `axeyum-aig` already exports in ASCII form), the certificate is *checked by a
SAT solver emitting LRAT* — literally "untrusted fast search, trusted small checking" — and
the certificate requirement is a differentiator rather than an obstacle. HWMCC'26 at
FMCAD'26 (Oct 2026) is not yet posted. **[I]**

### 7.8 The rest, briefly

| Arena | Status |
|---|---|
| **CHC-COMP** <https://chc-comp.github.io/> | Live, 2020–**2026** (2026 results out). Nine tracks including **BV-Lin and BV-Nonlin**. SMT-LIB-shaped Horn clauses. No certificate requirement. **[C]** |
| **SV-COMP** <https://sv-comp.sosy-lab.org/2026/> | Live, 15th edition at TACAS 2026: 61 verifiers + **16 validators** for C. Not Boolean, but it is the field's most mature example of **separately medalling the checkers** — a design precedent for "a checker that cannot fail is worse than no checker". **[C]** |
| **termCOMP** | Ran in 2026 (raw results 2026-08-21, Zenodo 22042846). Rewriting/complexity, not Boolean. Not a fit. **[C]**/**[I]** |
| **ARCH-COMP** | Live (ARCH-COMP25 category reports). Hybrid/continuous systems. Not a fit. **[C]** |
| **SyGuS-Comp** <https://sygus.org/> | **Dead.** Most recent edition listed is **2019**. **[C]** for the listing, **[I]** for "discontinued". |


---

## 8. State of the art: CDCL SAT solvers and what they can prove

The solvers for each non-SAT arena are catalogued in that arena's own section above.

| Solver | Repo | Lang / license | Proof output | Incremental |
|---|---|---|---|---|
| **CaDiCaL** | <https://github.com/arminbiere/cadical> | C++ | **DRAT, LRAT, FRAT, VeriPB** (with or without antecedents), plus **IDRUP / LIDRUP** for *incremental* proofs; a `connect_proof_tracer` API streams clausal proofs on the fly **[C]** | Yes; **IPASIR** and **IPASIR-UP** (user propagators) **[C]** |
| **Kissat** | <https://github.com/arminbiere/kissat> | C, MIT | **DRAT only** — ASCII to stdout, binary to file unless `--no-binary`; `src/proof.h` has no clause IDs or hints, so no LRAT **[C]** | No (one-shot bare-metal core) **[C]** |
| **SBVA-CaDiCaL / SBVA-Kissat** | <https://github.com/hgarrereyn/SBVA> | — | Structured Bounded Variable Addition as a *preprocessor* in front of CaDiCaL/Kissat; won Main SAT+UNSAT and Main UNSAT in 2023 **[C]** | — |
| **satsuma** (+ kissat) | (Anders & Codel) | — | Symmetry-detection preprocessor; **won all three Main-track categories in 2026** **[C]** | — |
| **MallobSat** | <https://github.com/domschrei/mallob> | C++ | Distributed/parallel; won Cloud 2024, Parallel 2025, Parallel + Cloud 2026 **[C]** | — |
| **CryptoMiniSat** | <https://github.com/msoos/cryptominisat> | C++, MIT core | **FRAT** proofs ("can be independently verified"); XOR reasoning is covered by FRAT-XOR verification tooling rather than plain DRAT **[C]**. XOR clauses + Gauss-Jordan elimination on by default since 5.8, auto-disabled if it underperforms **[C]** | Yes ("an advanced incremental SAT solver"); has Rust bindings **[C]** |
| **IsaSAT** | <https://m-fleury.github.io/isasat/isasat-release/> | Isabelle/HOL → LLVM | The most advanced *verified* SAT solver; competes in the main track (it appears in the 2023 special-track plot) **[C]** | — |
| **RustSAT** | <https://github.com/chrjabs/rustsat>, paper SAT 2025 / arXiv 2505.15221 | Rust | A Rust library wrapping state-of-the-art solvers under one API, with cardinality and PB encodings, plus C and Python APIs; all but one wrapped solver are incremental **[C]** | Yes (`SolveIncremental` trait) |

Key asymmetry for axeyum: **the competition-winning sequential solver family (Kissat)
emits only DRAT**, while the checker side has moved to hint-carrying formats (LRAT/LPR,
LSR) because those check far faster. The 2025 organizers said as much and floated a
combined solve+check-time track. axeyum already emits DRAT *and* has a DRAT→LRAT
elaborator, which is precisely the pipeline shape the competition rewards — the gap is
RAT support in the elaborator, not the architecture.

### The checker / proof-format toolchain

| Tool | What it does | Verified in | URL |
|---|---|---|---|
| **drat-trim** | Checks DRAT (text and binary) against a DIMACS formula; emits UNSAT cores (`-c`), core lemmas (`-l`), TraceCheck resolution graphs (`-r`); `lrat-check.c` ships alongside **[C]** | Not verified (C) | <https://github.com/marijnheule/drat-trim> |
| **dpr-trim** | Same role for the **DPR** (propagation-redundancy) system; a 2024 and 2026 competition checker **[C]** | Not verified | (in the drat-trim family) |
| **cake_lpr** | Verified **LRAT and LPR** checker; LPR is backwards compatible with LRAT and adds PR clauses. Verified **down to x64 machine code**, eliminating compiler/extraction bugs. DRAT and DPR are supported by preprocessing through drat-trim / dpr-trim. **[C]** | CakeML / HOL4 | <https://satcompetition.github.io/2025/downloads/checkers/cakelpr.pdf> |
| **GRAT** | Formally verified (UN)SAT checker (Peter Lammich); also used in "sat mode" to verify *models* in 2024. Fewest checker timeouts of the three in 2024 (2). **[C]** | Isabelle/HOL | (competition checker docs) |
| **VeriPB + CakePB** | Verified pseudo-Boolean (cutting-planes) proof checking; a competition option since 2023. Most checker timeouts in 2024 (25). **[C]** | CakeML (CakePB) | see §6 |
| **SR / LSR checker** | Checks the **substitution-redundancy** system via the **LSR** (hinted) format; **DSR** is the unhinted form. Tools convert DSR→DRAT and DSR→LSR (adds hints). "The strongest clausal proof system to date." **[C]** | **Lean 4** | <http://www.cs.cmu.edu/~mheule/publications/SRcheck.pdf> |
| **lrat-trim** | Trims and checks LRAT in ASCII and binary and produces clausal cores; built to shrink proofs so cake_lpr checks faster **[C]** | Not verified | (Biere group) |
| **idrup-check** | Checker for the **IDRUP / LIDRUP** *incremental* proof formats, which capture solver reasoning **and user interaction**, including IPASIR-UP use cases **[C]** | Not verified | Fazekas, Pollitt, Fleury, Biere, LPAR-25 (2024) |


---

## 9. What axeyum has not touched

### 9.1 What it *has* touched

Two arenas are already well charted and should not be listed as gaps:

- **SMT-COMP.** `crates/axeyum-bench/examples/smtcomp_cli.rs` is a competition-shaped
  Single-Query CLI written against SMT-COMP 2026 §5 and §7.1.2; `support_matrix.rs`
  enumerates 15+ QF fragments; `docs/plan/smtcomp-2025-parity-targets-2026-07-28.md` carries
  per-division "not entered" columns. The project knows this arena's shape.
- **The SAT engine itself.** `proof_sat.rs` (a DRAT-emitting CDCL core), `drat.rs` (an
  independent RUP+RAT checker with a streaming sink), `lrat.rs` (an LRAT checker, a
  DRAT→LRAT elaborator, and `write_lrat`), `cube.rs` (cube-and-conquer with certificate
  composition), `gf2.rs`/`xor_cdcl.rs`/`xor_drat.rs` (XOR reasoning with per-query DRAT
  refutations), `alethe.rs` (an Alethe checker). This is more machinery than the framing
  "one small CNF slice" suggests.

The gap is not capability. It is that **none of it has ever been pointed at an external
arena**, and the one external comparison that exists — `cnf_core_bench.rs`, CaDiCaL and
Kissat on byte-identical DIMACS — is explicitly labelled "a mechanism diagnostic, not an
end-to-end SMT benchmark".

### 9.2 The arenas, ranked by fit

| Arena | Live? | Fit | Proof required? | What entry costs |
|---|---|---|---|---|
| **HWMCC bit-level** | ✅ '24, '25; '26 expected | **Highest** | ✅ **Yes** — Certifaiger | An IC3/BMC engine on the SAT core + binary AIGER + reset-function witness circuits |
| **SAT Competition Main** | ✅ 2026 | Direct | ✅ Yes | Binary DRAT + a competition CLI; the field is the hardest in the survey |
| **SAT Competition Experimental** | ✅ 2026 | Direct | ❌ **No proof checking** | Almost nothing — but you must beat the top three Main solvers to win |
| **PB Competition PBS/PBO-CERT** | ✅ 2026 | Adjacent | ✅ VeriPB | An OPB front end + cutting-planes logging |
| **XCSP3** | ✅ 2026 | Via encoding | ❌ No | An XCSP3-core → CNF encoder (Fun-sCOP+Kissat took silver in 2025) |
| **MiniZinc Challenge** | ✅ 2026 | Via encoding | ❌ No | A FlatZinc solver in a Docker image (PicatSAT took silver twice) |
| **MaxSAT Evaluation** | ✅ 2026 | Adjacent | ❌ No (announced for next year) | A WCNF front end + a real MaxSAT algorithm |
| **Model Counting Competition** | ✅ 2026 | Adjacent | ❌ No | A counter — axeyum has **none** |
| **QBFGallery** | ✅ 2026 | Adjacent | ❌ No | A QDIMACS/QCIR front end + a QBF solver |
| **CHC-COMP BV-Lin / BV-Nonlin** | ✅ 2026 | BV tracks exist | ❌ No | Horn solving, not just SAT |
| SAT Comp Incremental | ❌ dead since 2021 | — | — | IPASIR-2 aims to revive it |
| SAT Comp Random / local search | ❌ dead since 2018 | — | — | — |
| SAT Comp Crypto | ❌ 2021 only | — | — | — |
| SMT-COMP Proof Exhibition | ❌ 2022–23 only, never ranked | — | — | — |
| SyGuS-Comp | ❌ dead since 2019 | — | — | — |
| Unsolvability IPC | ❌ 2016 only | — | — | — |

### 9.3 Per-arena entry requirements, concretely

**SAT Competition (Main).** The closest arena, and the gaps are small and specific:

1. **A competition CLI.** No binary in the workspace reads a `.cnf` and prints
   `s SATISFIABLE` / `s UNSATISFIABLE` with `v` lines and exit codes 10/20. `dump_dimacs.rs`
   writes CNF; `parse_dimacs` reads it; nothing wires them to the competition contract.
2. **Binary DRAT.** `crates/axeyum-cnf/src/drat.rs` contains **zero occurrences of
   "binary"** — `write_drat` and `parse_drat` are text-only. Kissat writes binary by default
   for real files; drat-trim, dpr-trim and GRAT all expect it. This is a bounded change.
3. **RAT in the LRAT elaborator.** `lrat.rs` says plainly: "This slice supports **RUP-only**
   proofs (positive hints). RAT additions (negative hints) are out of scope, both in the
   checker and the elaborator." A CDCL core with inprocessing produces RAT steps; without
   them the DRAT→LRAT path cannot elaborate a competition-grade proof.
4. **Choose a checker.** GRAT and dpr-trim both take DRAT directly, so the pipeline
   `axeyum → binary DRAT → gratgen → gratchk` requires no new proof format at all. The
   cake_lpr route needs `drat-trim -L` in between — or, since axeyum already has
   `write_lrat`, **going straight to LRAT and skipping the trimmer entirely**, which is
   exactly the pipeline the 2025 organizers said is "much faster" to check.
5. **Scale.** The 2026 main track ran at 5000 s and **32 GB**; 2025's 30 GB caused several
   runs to crash at 20 GB allocation, specifically on "parsing issues on some huge instances"
   and "**proof checking issues on some big proofs**".

The realistic first step is *not* the current 400-instance main track — that set is selected
to be hard for Kissat. It is the **7330-instance 2002–2024 Zenodo archive**
(10.5281/zenodo.15125952), which is what the Anniversary track used and where a
per-instance difficulty distribution exists.

**HWMCC** — the best strategic fit in the survey, and the only competition whose *rules*
encode axeyum's thesis. Requirements: (a) **binary AIGER**, not just the ASCII `aag` export
`axeyum-aig` has today, and **sequential** AIGER with latches, not the combinational graph;
(b) an IC3/BMC engine — `pdr.rs` exists in `axeyum-solver`, which is the right starting
point; (c) **witness circuits in modified AIGER 1.9 with reset functions** — Certifaiger then
discharges simulation, inductiveness and ranking obligations *by calling a SAT solver*, and
when built with `make lrat-trim` that solver streams LRAT. A stack that both produces the
witness and can check the resulting SAT obligations with its own verified-style checker is a
genuinely differentiated position.

**Pseudo-Boolean.** Needs an **OPB** front end (spec:
<https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf>) — axeyum has cardinality
constraints (`axeyum-solver/src/cardinality.rs`) and weighted-at-most encodings
(`axeyum-cnf/src/weighted.rs`) but **no OPB parser or writer**. Then **VeriPB proof logging**:
the `red` rule generalizes RAT (a DRAT step on pivot `x1` is exactly `red … ; x1 -> 1`), so
existing DRAT machinery maps onto it, but `dom` (dominance/symmetry in optimization) has no
DRAT analogue. Practical notes: VeriPB requires *all* learned clauses logged including units,
and unit deletion is meaningful (DRAT checkers ignore it). **VeriPB 3.0.2 is Rust, dual
MIT/Apache-2.0, on crates.io — but its MSRV is 1.92.0, above axeyum's 1.88.** That is the
detail most likely to bite anyone scoping a "check our proofs with VeriPB" task.

**MaxSAT.** Needs the **new WCNF format** (hard clauses prefixed `h`, no `p wcnf` header) —
axeyum has **zero occurrences of `wcnf` anywhere in `crates/`**. `axeyum-solver/src/maxsat.rs`
is an internal API that reduces MaxSAT to bit-vector optimization; it is not a
core-guided/IHS/branch-and-bound algorithm and would not be competitive against
UWrMaxSat/WMaxCDCL/CASHWMaxSAT. Note the certified track is *announced for the edition after
2026*, and that CGSS/RC2 proof logging costs **+8.8% median** solving time and **found two
real bugs** — a certified entrant arriving as the track opens would be well timed. IPAMIR
(<https://bitbucket.org/coreo-group/ipamir>) is the incremental-MaxSAT analogue of IPASIR.

**Model counting.** axeyum has **no model counting of any kind** — no `count_models`, no
knowledge compilation, no d-DNNF. Entry needs a counter plus the `c t mc` / `c p weight` /
`c p show` format. The strategic observation is the empty niche: **no competition-winning
counter emits a proof, and the competition neither requires nor accepts one**, while
**CPOG** p-simulates MICE and kcps, keeps its generator **untrusted by design**, and has
verified checkers in **Lean 4** and CakeML/HOL4. The price is a median 3–12× overhead and
proof files reaching 150 GB. Note also that the only pure-Rust counter is **Schlandals**
(MIT, but domain-specialized), and the sole Rust proof checker in the space (`sharptrace`)
has **no license file** and has been dormant since March 2023.

**QBF.** axeyum has 37 `quant_*` modules in `axeyum-solver` — skolemization, certificates,
counterexample search — but **zero occurrences of "QBF"**, and no QDIMACS or QCIR support.
The quantifier work is SMT-side (BV / integer / UF), not propositional QBF. Entry needs a
QDIMACS front end and the `exit 10 = true / exit 20 = false` contract. Two things make this
arena unusually approachable: **CAQE, the PCNF-track winner in both 2022 and 2023, is
written in Rust**; and **no verified QRAT checker exists in any proof assistant**, while
`qrat-trim` has 6 commits, 0 stars and has not been edited since October 2020. A verified
QRAT or LSR-style checker would be a first.

**CP (XCSP3, MiniZinc).** The lowest-effort podium in the survey, and it is not speculative:
**PicatSAT (a pure CP-to-SAT compiler) took MiniZinc silver in Free and Parallel in both 2025
and 2026**, and **Fun-sCOP, an XCSP3-core → CNF encoder around Kissat, took Main CSP silver
in 2025**. Entry cost is a front end plus a Docker image (MiniZinc) or an XCSP3-core parser
(XCSP3), with no proof obligation at all — but also no way to differentiate on proofs.

### 9.4 Three observations worth carrying into planning

1. **The proof-format frontier has moved past DRAT, and it moved toward hints and toward
   Lean.** SAT Competition 2026 offers GRAT, DPR-trim, VeriPB and **SR**; the SR checker is
   **verified in Lean 4** and its authors state "currently, no solver supports SR reasoning"
   — they shipped the checker first, deliberately, to bootstrap adoption, exactly as happened
   with PR. **PBLean** (arXiv 2602.08692) imports VeriPB proofs into Lean 4 by reflection and
   produces *composable Lean theorems* rather than a verdict. For a project that already has
   a Lean kernel and a reconstruction arrow, that is the same architectural move.
2. **Where proof logging is mandatory, one competition made it happen deliberately.** SAT
   inverted the default (certification is the main track, uncertified solving is the
   handicapped Experimental exception). PB created a `-CERT` track in 2024 and went from
   *zero* VeriPB-emitting PB solvers to six certified entrants in one year. MaxSAT, model
   counting, SMT and CP all have mature certification research and **no competition pressure
   behind it** — four open niches, each of which the corresponding organizers have said in
   print they want filled.
3. **The cost of certification is now a measured number, not a worry.** RoundingSat: 2.7%
   median proof-generation overhead, 1.43× median verification. MaxSAT core-guided: +8.8%
   median solving. PB25: 3320 proofs verified, only 0.76% needing more than 5 hours. CPOG:
   median 12.5× validation/compile, worst case 150 GB proof files. These are the numbers to
   cite, in either direction, rather than asserting that proofs are cheap or expensive.

---

## Sources

Every URL below was either fetched directly during this research or appeared in a primary
result relied on above.

### SAT Competition
- <https://satcompetition.github.io/> · <https://satcompetition.github.io/2022/> · <https://satcompetition.github.io/2023/> · <https://satcompetition.github.io/2024/> · <https://satcompetition.github.io/2025/> · <https://satcompetition.github.io/2026/>
- Tracks: <https://satcompetition.github.io/2023/tracks.html> · <https://satcompetition.github.io/2024/tracks.html> · <https://satcompetition.github.io/2025/tracks.html> · <https://satcompetition.github.io/2026/tracks.html>
- Results: <https://satcompetition.github.io/2022/results.html> · <https://satcompetition.github.io/2023/results.html> · <https://satcompetition.github.io/2024/results.html>
- Results slides: <https://satcompetition.github.io/2022/slides/satcomp22slides.pdf> · <https://satcompetition.github.io/2023/downloads/satcomp23slides.pdf> · <https://satcompetition.github.io/2024/downloads/satcomp24slides.pdf> · <https://satcompetition.github.io/2025/satcomp25slides.pdf> · <https://satcompetition.github.io/2026/downloads/satcomp26slides.pdf>
- Output / certificate rules: <https://satcompetition.github.io/2024/output.html> · <https://satcompetition.github.io/2025/output.html> · <https://satcompetition.github.io/2026/output.html>
- Checker documentation: <https://satcompetition.github.io/2025/downloads/checkers/cakelpr.pdf> · <https://satcompetition.github.io/2026/downloads/checkers/cakelpr.pdf> · <https://satcompetition.github.io/2026/downloads/checkers/grat.pdf> · <https://satcompetition.github.io/2026/downloads/checkers/veripb.pdf> · <https://satcompetition.github.io/2026/downloads/checkers/verified_sr.pdf> · <https://satcompetition.github.io/2023/downloads/proposals/drat_dpr.pdf>
- Downloads: <https://satcompetition.github.io/2025/downloads.html> · <https://satcompetition.github.io/2026/downloads.html>
- Historical tracks: <https://satcompetition.github.io/2021/track_crypto.html> · <https://satcompetition.github.io/2021/track_incremental.html> · <https://satcompetition.github.io/2020/track_incremental.html> · <https://satcompetition.github.io/2020/results.html> · <https://satcompetition.github.io/2021/results.html> · <https://satcompetition.github.io/2019/>
- Repos: <https://github.com/satcompetition/2025> · <https://github.com/satcompetition/2026> · <https://github.com/satcompetition/template>
- Medals / proceedings: <https://cca.informatik.uni-freiburg.de/sat24medals/> · <https://researchportal.helsinki.fi/en/publications/proceedings-of-sat-competition-2024-solver-benchmark-and-proof-ch/> · <https://repositum.tuwien.at/bitstream/20.500.12708/218424/2/Codel-2025-Proceedings%20of%20SAT%20Competition%202025%20%20Solver%20and%20Benchmark%20Desc...-vor.pdf>
- Solver descriptions: <https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf> · <https://cca.informatik.uni-freiburg.de/papers/BiereFallerFleuryFroleyksPollitt-SAT-Competition-2025-solvers.pdf> · <https://cca.informatik.uni-freiburg.de/papers/BiereFleuryPollitt-SAT-Competition-2023-solvers.pdf>
- Parallel/cloud: <https://satres.kikit.kit.edu/news/2025-08-15-satcomp/> · <https://satres.kikit.kit.edu/papers/2025-mallob-naps.pdf>

### Benchmarks
- <https://benchmark-database.de/> (GBD) · <https://benchmark-database.de/?track=main_2025&context=cnf> · <https://github.com/Udopia/gbd>
- <https://zenodo.org/records/15095752> (SAT Comp 2024 main track, 400 CNFs, DOI 10.5281/zenodo.15095752)
- <https://zenodo.org/records/15125952> (SAT Competition Benchmarks 2002–2024, 7330 instances, DOI 10.5281/zenodo.15125952)
- <https://zenodo.org/records/11175170> (SAT Comp 2022 Anniversary track, 5355 benchmarks)
- <https://zenodo.org/records/16887742> (SMT-COMP 2025 benchmarks)

### Proof systems and verified checkers
- <https://github.com/marijnheule/drat-trim> · <https://github.com/marijnheule/dpr-trim> · <https://github.com/marijnheule/qrat-trim>
- <https://github.com/tanyongkiam/cake_lpr> · <https://cakeml.org/checkers.html> · <https://github.com/CakeML/cakeml/tree/master/examples/pseudo_bool> · <https://github.com/CakeML/cakeml/tree/master/examples/lpr_checker>
- <https://dl.acm.org/doi/10.1007/978-3-030-72013-1_12> (cake_lpr, TACAS 2021) · <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7984575/> · <https://link.springer.com/article/10.1007/s10009-022-00690-y>
- <https://www21.in.tum.de/~lammich/grat/> (GRAT)
- <https://gitlab.com/MIAOresearch/software/VeriPB> · <https://veripb.org/> · <https://gitlab.com/MIAOresearch/software/cakepb>
- <http://www.cs.cmu.edu/~mheule/publications/SRcheck.pdf> · <https://crcodel.com/research/verified_sr.pdf> (Verified Substitution Redundancy Checking, FMCAD 2024, Lean 4)
- <https://arxiv.org/abs/2602.08692> (PBLean — VeriPB certificates in Lean 4)
- <https://drops.dagstuhl.de/storage/00lipics/lipics-vol271-sat2023/LIPIcs.SAT.2023.21/LIPIcs.SAT.2023.21.pdf> (Faster LRAT checking than solving with CaDiCaL)
- <https://cca.informatik.uni-freiburg.de/papers/PollittFleuryBiere-MBMV23.pdf>
- <https://cca.informatik.uni-freiburg.de/papers/FazekasPollittFleuryBiere-LPAR24.pdf> (Certifying Incremental SAT Solving — IDRUP / LIDRUP / idrup-check)
- <https://www.cs.cmu.edu/~mheule/publications/LPR-TACAS.pdf>
- <https://drops.dagstuhl.de/storage/00lipics/lipics-vol340-cp2025/html/LIPIcs.CP.2025.21/LIPIcs.CP.2025.21.html> · <https://aoertel.de/pdf/paper/PracticallyFeasibleProofLoggingPB.pdf> (Practically Feasible Proof Logging for PB Optimization, CP 2025)
- <https://cakeml.org/aaai24-verified-subgraphs.pdf>
- <https://jakobnordstrom.se/docs/publications/CertifiedCoreGuidedMaxSAT_CADE.pdf> · <https://arxiv.org/pdf/2404.17316> (Certified MaxSAT Preprocessing, IJCAR'24) · <https://ojs.aaai.org/index.php/AAAI/article/view/38449/42411> (Certified Branch-and-Bound MaxSAT, AAAI 2026) · <https://arxiv.org/pdf/2511.10273> · <https://conf.researchr.org/details/ase-2025/ase-2025-papers/49/> · <https://cris.vub.be/ws/portalfiles/portal/105714406/thesis_DieterVandesande.pdf>
- <https://arxiv.org/html/2504.18443> (PB proof logging for optimal classical planning)

### MaxSAT Evaluation
- <https://maxsat-evaluations.github.io/> · <https://maxsat-evaluations.github.io/2022/> · <https://maxsat-evaluations.github.io/2023/> · <https://maxsat-evaluations.github.io/2024/contents/contents_history.html> · <https://maxsat-evaluations.github.io/2025/contents/contents_index.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_index.html>
- Tracks/rules: <https://maxsat-evaluations.github.io/2023/tracks.html> · <https://maxsat-evaluations.github.io/2022/rules.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_tracks.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_rules.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_execution.html> · <https://maxsat-evaluations.github.io/2024/contents/contents_execution.html> · <https://maxsat-evaluations.github.io/2020/tracks.html>
- Talks: <https://maxsat-evaluations.github.io/2022/mse22-talk.pdf> · <https://maxsat-evaluations.github.io/2023/mse23-talk.pdf> · <https://maxsat-evaluations.github.io/2024/mse24-talk.pdf> · <https://zenodo.org/records/21358014/files/slides.pdf> · <https://maxsat-evaluations.github.io/2026/mse26proc_draft.pdf>
- Results: <https://maxsat-evaluations.github.io/2022/results/complete/unweighted/summary.html> · <https://maxsat-evaluations.github.io/2023/results/exact/unweighted/summary.html> · <https://maxsat-evaluations.github.io/2024/contents/contents_rankings.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_exact_unweighted_ranking.html> · <https://maxsat-evaluations.github.io/2026/contents/contents_incremental_results.html>
- Data/benchmarks: <https://github.com/maxsat-evaluations/data> · DOI 10.5281/zenodo.21283147 · DOI 10.5281/zenodo.21358014 · <https://bitbucket.org/fbacchus/maxsat_benchmarks_code_base/> · <https://bitbucket.org/coreo-group/ipamir>
- Solvers: <https://github.com/FlorentAvellaneda/EvalMaxSAT> · <https://github.com/marekpiotrow/UWrMaxSat> · <https://github.com/fbacchus/MaxHS> · <https://github.com/ASchidler/MaxHS> · <https://github.com/pysathq/pysat> · <https://github.com/tobipaxe/PacoseMaxSATSolver> · <https://github.com/shaowei-cai-group/NuWLS-c> · <https://github.com/jordicollcaballero/WMaxCDCL_Paper> · <https://github.com/sat-group/open-wbo> · <https://github.com/alexander-nadel-academic/tt-open-wbo-inc> · <https://bitbucket.org/coreo-group/cgss2> · <https://github.com/chrjabs/scuttle> · <https://github.com/Laakeri/maxpre> · <https://bitbucket.org/coreo-group/maxpre2> · <https://github.com/jezberg/loandra> · <https://github.com/JHL-HUST/SPB-MaxSAT> · <https://github.com/tobipaxe/MaxSATRegressionSuite> · <https://github.com/tobipaxe/MaxSAT-Fuzzer>

### Model Counting Competition
- <https://mccompetition.org/> · <https://mccompetition.org/past_iterations.html> · <https://mccompetition.org/2024/mc_description.html> · <https://mccompetition.org/2025/mc_description.html> · <https://mccompetition.org/2026/mc_description.html> · <https://mccompetition.org/2026/mcw_description.html>
- Format spec: <https://mccompetition.org/assets/files/mccomp_format_25.pdf>
- Awards/winners: <https://mccompetition.org/assets/files/2022/MC2022_winners.pdf> · <https://mccompetition.org/assets/files/2022/MC2022_awards.pdf> · <https://mccompetition.org/assets/files/2023/MC2023_awards.pdf> · <https://mccompetition.org/assets/files/2024/MC2024_awards.pdf> · <https://mccompetition.org/assets/files/2025/MC2025_awards.pdf> · <https://mccompetition.org/assets/files/2026/MC2026_awards.pdf>
- Report: <https://arxiv.org/abs/2504.13842> · <https://arxiv.org/pdf/2504.13842> · <https://www.sciencedirect.com/science/article/pii/S0004370226001311> (AIJ, DOI 10.1016/j.artint.2026.104605)
- Certification: <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2022.30> (MICE) · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.6> (CPOG) · <https://arxiv.org/abs/2501.12906> · <https://www.jair.org/index.php/jair/article/view/15958> · <https://dl.acm.org/doi/pdf/10.1613/jair.1.15958> · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2025.8> (SCPOG) · <https://arxiv.org/abs/2406.11414> (ApproxMCCert) · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2024.18> (CLIP) · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.5> · <https://ojs.aaai.org/index.php/AAAI/article/download/38431/42393> · <https://arxiv.org/abs/2508.06264>
- Solvers: <https://github.com/crillab/d4> · <https://github.com/crillab/d4v2> · <https://github.com/khashimoto-lab/GPMC> · <https://github.com/meelgroup/KCBox> · <https://github.com/vroland/sharptrace> · <https://github.com/vroland/nnf2trace> · <https://github.com/rebryant/cpog> · <https://github.com/rebryant/scpog> · <https://github.com/rebryant/d4v2-proofgen> · <https://github.com/meelgroup/approxmc-cert> · <https://github.com/aia-uclouvain/schlandals> · <https://github.com/crillab/decdnnf_rs> · <https://github.com/SoftVarE-Group/d-dnnf-reasoner> · <https://github.com/SoftVarE-Group/d4-oxide> · <https://github.com/jsfpdn/sdd-rs> · <https://github.com/SoftVarE-Group/as4moco> · <https://github.com/arijitsh/mccomp-test-instances>
- Benchmarks: zenodo 4292581, 10031810, 10004947, 10006718, 13988776, 10006441, 10012803, 10012860, 10014715, 10012811, 10012864, 10012822, 14249109, 14249068, 14969231, 14249095, 10671987, 10866053

### QBF
- <http://www.qbflib.org/> · <https://www.qbflib.org/index_eval.php> · <https://www.qbflib.org/qbfeval2022_results.php> · <https://www.qbflib.org/QBFEVAL22_PRES.pdf> · <https://www.qbflib.org/qbfeval19_results.pdf> · <https://www.qbflib.org/solvers_list.php>
- Formats: <https://www.qbflib.org/qdimacs.html> · <https://www.qbflib.org/qcir.pdf> · <https://qbf.pages.sai.jku.at/qdimacs/> · <https://fmv.jku.at/papers/JKS-BNP.pdf>
- Gallery: <https://qbf.pages.sai.jku.at/> · <https://qbf.pages.sai.jku.at/evaluations/> · <https://qbf.pages.sai.jku.at/workshops/> · <https://qbf.pages.sai.jku.at/gallery26/> · <https://qbf23.pages.sai.jku.at/gallery/> · <https://qbf23.pages.sai.jku.at/gallery/slides.pdf> · <https://arxiv.org/abs/2604.16153> · <http://www.satlive.org/2026/04/24/qbfgallery.html> · <https://qbf-workshop.github.io/> · <https://qbf-workshop.github.io/programme/>
- Proofs: <https://fmv.jku.at/qbfcert/> · <https://fmv.jku.at/qbfcert/qrp.format> · <https://link.springer.com/chapter/10.1007/978-3-319-08587-6_7> (QRAT, IJCAR 2014) · <https://www.cs.utexas.edu/~marijn/publications/FMCAD14.pdf> · <https://www.cs.cmu.edu/~mheule/talks/QRAT-Dagstuhl.pdf> · <https://arxiv.org/pdf/1804.02908> (QRAT+) · <https://link.springer.com/chapter/10.1007/978-3-030-24258-9_7> · <https://link.springer.com/chapter/10.1007/978-3-642-31612-8_33> · <https://arxiv.org/abs/2605.29763> (DQRAT) · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.1> · <https://research.jku.at/en/activities/certification-of-true-qbf-formulas-in-expansion-based-solving/>
- Solvers: <https://github.com/ltentrup/caqe> · <https://github.com/ltentrup/quabs> · <https://github.com/fslivovsky/qute> · <https://github.com/lonsing/depqbf> · <https://github.com/lonsing/qratpreplus> · <https://github.com/jurajsic/DQBDD> · <https://github.com/MikolasJanota/qesto> · <https://github.com/gcharwat/dynqbf> · <https://github.com/fxreichl/Pedant-QBFEVAL22> · <https://fmv.jku.at/bloqqer/>

### Pseudo-Boolean
- <http://www.cril.univ-artois.fr/PB16/> · <http://www.cril.univ-artois.fr/PB24/> · <https://www.cril.univ-artois.fr/PB24/details.html> · <https://www.cril.univ-artois.fr/PB24/slides.pdf> · <http://www.cril.univ-artois.fr/PB25/> · <https://www.cril.univ-artois.fr/PB25/slides/PB25.pdf> · <https://www.cril.univ-artois.fr/PB25/results/results.php?idev=115> · <https://www.cril.univ-artois.fr/PB26/>
- Formats: <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf> · <https://www.cril.univ-artois.fr/PB24/OPBgeneral.pdf> · <https://www.cril.univ-artois.fr/PB24/competitionRequirements.pdf> · <http://www.cril.univ-artois.fr/PB16/format.pdf>
- Solvers: <https://gitlab.com/nonfiction-software/exact> · <https://gitlab.com/MIAOresearch/roundingsat> · <https://bitbucket.org/krr/breakid/src/veriPB/> · <https://gitlab.com/MIAOresearch/tools-and-utilities/kissat_fork> · <https://scipopt.org/> · <https://arxiv.org/abs/2501.03390>

### Adjacent arenas
- IPASIR: <https://github.com/biotomas/ipasir> · <https://github.com/ipasir2/ipasir2> · <https://arxiv.org/pdf/1810.04311> · <https://www.sciencedirect.com/science/article/pii/S0004370216300984> · <https://www.sciencedirect.com/science/article/pii/S0004370221001235>
- IPASIR-UP: <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.8> · <https://dl.acm.org/doi/pdf/10.1613/jair.1.16163> · <https://cs.stanford.edu/~niemetz/talks/Niemetz-CENTAUR23.pdf>
- Local search: <https://fmv.jku.at/yalsat/> · <https://dl.acm.org/doi/pdf/10.1613/jair.1.13666> · <https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/balint/SAT2012.pdf> · <https://cs.uwaterloo.ca/~dtompkin/papers/satcomp11-sparrow.pdf> · <https://ada.liacs.nl/projects/sparkle/>
- Crypto/XOR: <https://github.com/msoos/cryptominisat> · <https://github.com/meelgroup/bosphorus> · <https://arxiv.org/abs/1812.04580> · <https://repositum.tuwien.at/handle/20.500.12708/355> · <https://arxiv.org/abs/2304.04292> · <https://www.cs.cmu.edu/~bryant/pubdir/pos22.pdf> · <https://arxiv.org/abs/2105.00885> · <https://github.com/meelgroup/frat-xor> · <https://arxiv.org/html/2507.02916v1>
- Planning: <https://www.icaps-conference.org/competitions/> · <https://ipc2023.github.io/> · <https://ipc2023-classical.github.io/> · <https://ipc2026-numeric.github.io/> · <http://unsolve-ipc.eng.unimelb.edu.au/> · <https://researchr.org/publication/ijcai-2018>
- CP: <https://www.minizinc.org/challenge/> · <https://www.minizinc.org/challenge/2025/results/> · <https://www.minizinc.org/challenge/2026/results/> · <https://xcsp.org/competitions/> · <https://www.cril.univ-artois.fr/XCSP25/> · <https://arxiv.org/abs/2511.06918> · <https://arxiv.org/abs/2412.00117> · <https://arxiv.org/abs/2312.05877> · <https://www.cril.univ-artois.fr/~lecoutre/compets/proceedingsXCSP22.pdf>
- SMT-COMP: <https://smt-comp.github.io/> · <https://smt-comp.github.io/2024/results/qf_bitvec-single-query> · <https://smt-comp.github.io/2025/> · <https://smt-comp.github.io/2025/rules.pdf> · <https://smt-comp.github.io/2026/results/qf_bitvec-single-query> · <https://smt-workshop.cs.uiowa.edu/2023/slides/smtcomp.pdf> · <https://smt-comp.github.io/2022/results/qf-fp-proof-exhibition>
- HWMCC: <https://hwmcc.github.io/> · <https://hwmcc.github.io/2024/> · <https://hwmcc.github.io/2025/> · <https://cca.informatik.uni-freiburg.de/papers/BiereFroleyksPreiner-FMCAD24.pdf> · <https://link.springer.com/chapter/10.1007/978-3-031-98668-0_14> · <https://github.com/Froleyks/certifaiger> · <https://arxiv.org/html/2502.13605v1> (rIC3) · <https://fmv.jku.at/aiger>
- Others: <https://chc-comp.github.io/> · <https://sygus.org/> · <https://sv-comp.sosy-lab.org/2026/> · <https://termination-portal.org/wiki/Termination_Competition_2026>

### Solvers and libraries
- <https://github.com/arminbiere/cadical> · <https://github.com/arminbiere/kissat> · <https://github.com/domschrei/mallob> · <https://github.com/hgarrereyn/SBVA> · <https://m-fleury.github.io/isasat/isasat-release/> · <https://github.com/chrjabs/rustsat> · <https://arxiv.org/abs/2505.15221> · <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2025.15> · <https://link.springer.com/chapter/10.1007/978-3-031-65627-9_7> (CaDiCaL 2.0, CAV'24)
