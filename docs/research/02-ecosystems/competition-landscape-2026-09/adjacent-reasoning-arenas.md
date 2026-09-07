# Automated-reasoning arenas adjacent to SAT/SMT — a catalog for axeyum

Compiled 2026-09-06. Every factual row carries a URL in the Sources section.
Claims are marked **[C]** confirmed against a primary source read during this
research, or **[I]** inferred from a search snippet / secondary source that was
not re-read at the primary. Where a finding is a *negative* ("no such arena
exists"), that is stated as a finding, not as silence.

Axeyum's current measured position, for reference: an SMT-LIB head-to-head
parity ledger over **eleven divisions** — QF_SLIA, QF_BV, UF, QF_ABV, QF_LIA,
QF_UF, QF_RDL, QF_UFLIA, QF_LRA, QF_IDL, QF_NIA
(`docs/research/11-design-review/2026-09-05-parity-loss-census.md`). Everything
below is an arena it has not entered.

---

## 0. The map at a glance

| # | Arena | Cadence / latest | Format | What it would test in axeyum |
|---|---|---|---|---|
| 1 | **CHC-COMP** | annual, 9th ed. 2026 (results out) | SMT-LIB2 `(set-logic HORN)` | SMT front door + fixed-point/invariant engine |
| 2 | **SyGuS-Comp** | **dead since 2019** | SyGuS-IF 2.1 | (benchmarks live; no competition) |
| 3 | **CASC / TPTP** | annual, CASC-30 (2025), CASC-J13 announced 27 Jul 2026 | TPTP FOF/TFF/THF/TXF | first-order + higher-order proving, TSTP proof output |
| 4 | **miniF2F / PutnamBench / ProofNet / …** | continuous, leaderboards | Lean 4 / Isabelle / Rocq | the proof kernel + proof library |
| 5 | **termCOMP / CoCo** | annual | TPDB / COPS + **CPF certificates** | the rewriting layer, with a certificate story |
| 6 | **SV-COMP / VNN-COMP / HWMCC / MCC** | annual | C+witness YAML / ONNX+VNN-LIB / AIGER+BTOR2 / PNML | SMT as a backend; **AIG layer**; certificates |
| 7 | **CAS test suites** | rolling, no competition | Mathematica/Maple/Sympy syntax | the CAS, against Mathematica/Maple/Sympy |
| 8 | **OMT / MaxSAT / PB / strings** | MaxSAT+PB annual; **OMT has no competition** | WCNF / OPB+VeriPB / SMT-LIB | optimization and string routes |

---

## 1. CHC-COMP — Constrained Horn Clauses

**What it is [C].** An annual, community-run evaluation of CHC solvers, running
since 2018, with results presented at the HCVS workshop. Nine editions through
2026.

| Year | Ed. | Co-located with |
|---|---|---|
| 2018–2021 | 1st–4th | HCVS |
| 2022 | 5th | HCVS 2022, Munich (3 Apr 2022) |
| 2023 | 6th | HCVS 2023 Paris (23 Apr); also TOOLympics @ TACAS |
| 2024 | 7th | HCVS 2024 Luxembourg (7 Apr), ETAPS 2024 |
| 2025 | 8th | SPIN 2025, Hamilton CA (8 May), ETAPS 2025 |
| 2026 | 9th | HCVS @ CAV 2026 @ FLoC 2026; results posted |

**[C]** 2026 timeline: benchmark/solver submission 25 Apr 2026, resubmission
2 May 2026, results 25 Jul 2026.

### Tracks

Track names were renamed in 2024: a plain name means *nonlinear*, a `-Lin`
suffix means linear (at most one uninterpreted predicate atom in the premise).

| Edition | Tracks |
|---|---|
| 2022 (5th) | LIA-lin, LIA-nonlin, LIA-lin-Arrays, LIA-nonlin-Arrays, LRA-TS, LRA-TS-par, ADT-nonlin, LIA-nonlin-Arrays-nonrecADT |
| 2023 (6th) | LIA-lin, LIA-nonlin, LIA-lin-Arrays, LIA-nonlin-Arrays, LIA-nonlin-Arrays-nonrecADT, **ADT-LIA-nonlin** (new). LRA-TS dropped for lack of entrants |
| 2024 (7th) | LIA, LIA-Lin, LIA-Lin-Arrays, LIA-Arrays, ADT-LIA, ADT-LIA-Arrays |
| 2025 (8th) | the 2024 six **plus BV and LRA-Lin** |
| 2026 (9th) | nine tracks: LIA-Lin, LIA, LIA-Lin-Arrays, LIA-Arrays, ADT-LIA, ADT-LIA-Arrays, LRA-Lin, **BV-Lin, BV** (BV split) |

**Benchmark sizes [C]**, 2025 edition, per track: LIA-Lin 1312, LIA 1266,
LIA-Lin-Arrays 139, LIA-Arrays 1728, ADT-LIA 3585, ADT-LIA-Arrays 1045, BV 559,
LRA-Lin 274. In 2024 the 22 source repositories held 21,656 tasks total and 300
were sampled per track (20% easy / 40% medium / 40% hard).

**Format [C].** A syntactic fragment of SMT-LIB 2.6 with `(set-logic HORN)`.
Predicates are uninterpreted Boolean `declare-fun`s; three clause classes —
facts, rules, and queries `(forall (vars) (=> tail false))`. Predicate heads
must take distinct variables. Spec last revised 2023-03-31. Benchmarks and
tooling live under the `chc-comp` GitHub org (per-year `chc-compNN-benchmarks`
and `-scripts` repos, plus `chc-tools`); 2026 solver submission is by PR against
`chc-comp/chc-comp-2026`.

### Winners

| Track | 2023 | 2024 | 2025 | 2026 |
|---|---|---|---|---|
| LIA-Lin | Golem | Eldarica | Golem | Golem |
| LIA (nonlin) | Eldarica | Eldarica & Golem (tie) | Golem | Golem |
| LIA-Lin-Arrays | Eldarica | Theta | Eldarica | Eldarica |
| LIA-Arrays | Eldarica | Eldarica | Eldarica | Eldarica |
| ADT-LIA | Eldarica | Cata (newcomer) | Catalia | ChocoCatalia |
| ADT-LIA-Arrays | — | Eldarica | Eldarica | Eldarica |
| BV | — | — | Eldarica | Eldarica |
| BV-Lin | — | — | — | Eldarica |
| LRA-Lin | — | — | Golem | Golem |
| **Overall 2026** | | | | **Eldarica** (7892/10193 correct, 0 wrong) |

**The Spacer asterisk [C].** Z3/Spacer enters **hors concours** — excluded from
medals because a Spacer co-developer co-organizes the competition. In 2023 it
placed first in LIA-lin, LIA-nonlin, LIA-lin-Arrays and LIA-nonlin-Arrays; in
2026 it scored highest overall (8441/10193). It was **not submitted at all** in
2024 or 2025. So the credited winner is the top *eligible* solver, and the real
state of the art in LIA tracks is Z3/Spacer.

### How SMT solvers participate [C]

- **Eldarica** is built on **Princess** (same lead developer, Philipp Rümmer).
- **Golem** is built on **OpenSMT**, an interpolating SMT solver, and
  re-implements IMPACT (`lawi`), Spacer, a doubling-abstraction/TPA engine, BMC
  and k-induction as engines over it.
- **Ultimate TreeAutomizer / Unihorn** use SMTInterpol and Z3; **Theta** uses Z3.
- **cvc5 does not participate** — absent from every participant list 2022–2026.

So a CHC solver here *is* an SMT solver plus a fixed-point engine. That is the
entry cost for axeyum: no new front-end language, a new engine.

### Scoring, resources, validation

**[C]** Scoring is the count of `sat`/`unsat`, time as tiebreak. The 2026 page
formalizes three modes: "ignore wrong" (default, score = correct), "punish
wrong" (correct − 64×wrong), "assume all correct". Medals only to score > 0,
never to hors-concours entrants.

**[C]** Resource limits: through 2024 on **StarExec** (600 s test / 1800 s
competition, 64 GB). **2025 moved off StarExec** to LMU Munich's SV-COMP compute
cluster (8-core Xeon E3-1230 v5, 30 GB, 1800 s); the report notes the whole
evaluation cost roughly half a year of aggregate CPU time.

**Validation — the interesting part for axeyum [C].** Through 2023 there was
**no witness validation at all**; the 2023 report calls a common witness format
"still a work in progress", and soundness bugs were caught only when two solvers
disagreed. The 2025 slides admit results were "accepted as correct even though
there are definitely inconsistencies". The **2026 results page now carries a
separate "Model Track (check-sat with model generation)" alongside the Solver
Track, and states the results "have been certified by all participants"** — i.e.
certification became operational in this cycle. Independently, **ATHENA**
validates CHC SAT models by discharging the resulting SMT verification
conditions (LIA/ALIA), and validates UNSAT proofs through Carcara, LFSC and
SMTInterpol; it has been run over CHC-COMP 2022 and 2024 results. A sibling
project `pychc` is billed as "a library for certified CHC solving".

---

## 2. SyGuS-Comp — syntax-guided synthesis

**Status: discontinued. [C]** The last edition was **SyGuS-Comp 2019**
(satellite of CAV / SYNT 2019, New York, 13–14 July 2019; four entrants: CVC4,
DryadSynth, LoopInvGen, OASIS). It was not organized in 2020 because no
significant new solvers were ready **[I]**, and no edition has run since.

**[C]** The canonical `sygus.org` domain has lapsed: its substantive content is
frozen at a 2019 statement ("Planning for the 6th SyGuS-Comp will commence
around January 2019") and the live page now serves unrelated SEO spam dated as
recently as September 2026. The legitimate historical content survives on the
`sygus-org.github.io` mirror, which shows no activity 2020–2026.

### Tracks by year [C]

| Year | Tracks |
|---|---|
| 2014 | single unnamed track |
| 2015 | General, CLIA, Inv |
| 2016 | General, PBE, CLIA, Inv |
| 2017–2019 | General, CLIA, Inv, PBE-Strings, PBE-BV |

### Winners [C]

| Year | General | CLIA | Inv | PBE-Strings | PBE-BV |
|---|---|---|---|---|---|
| 2014 | Enumerative CEGIS | — | — | — | — |
| 2015 | CVC4 | CVC4 | ICE-DT | — | — |
| 2016 | EUSolver | CVC4 1.5.1 | ICE-DT | EUSolver | — |
| 2017 | EUSolver | CVC4 | ICE-DT / LoopInvGen | CVC4 | ESolver |
| 2018 | CVC4 | CVC4 & DryadSynth | LoopInvGen | CVC4 | CVC4 |
| 2019 | CVC4 | DryadSynth | CVC4 | CVC4 | CVC4 |

### Format and what remains [C]

- SyGuS-IF **1.0** (deprecated), **2.0** (Raghothaman & Reynolds),
  **2.1** (2021, Padhi & Polgreen). 2.1 added oracle specification, weighted
  SyGuS, a theory of tables, and **a logic for constrained Horn clauses** — a
  direct textual bridge to CHC-COMP's subject matter.
- Benchmarks: `github.com/SyGuS-Org/benchmarks`, split into `comp/` (per-year
  official sets, 2017+), `lib/` (latest per track) and `lib-nonconforming/`.
  The README concedes known errors and duplicates; the repo shows ~22 commits
  and no post-2019 competition-year additions.
- **cvc5 retains a built-in SyGuS engine** as a solving mode, not a competition
  entrant.
- **No successor competition was found.** SMT-COMP 2024/2025 do not run a
  synthesis track **[I — absence of evidence, track lists not fully enumerated]**.
  A 2025 arXiv paper, "Synthesis Benchmarks for Automated Reasoning"
  (2507.19827), presents a dynamically growing dataset complementing the SyGuS
  benchmarks — a lead, not a confirmed successor arena.

**Read for axeyum:** the benchmarks are free and unclaimed; the leaderboard is
gone. Entering here buys capability evidence, not a ranking.

---

## 3. CASC and the TPTP world

### Editions [C]

CASC alternates `CASC-<n>` at CADE (odd years) with `CASC-J<n>` at IJCAR (even
years); both count the same series.

| Edition | Year | Host | Date | Location |
|---|---|---|---|---|
| CASC-29 | 2023 | CADE-29 | 3 Jul 2023 | — |
| CASC-J12 | 2024 | IJCAR 2024 | 4 Jul 2024 | Nancy, France |
| CASC-30 | 2025 | CADE-30 | 30 Jul 2025 | Stuttgart, Germany |
| CASC-J13 | 2026 | IJCAR 2026 | **27 Jul 2026** | Lisbon (FLoC 2026 Olympics) |

Organizer throughout: Geoff Sutcliffe (Martin Desharnais assisting on SLH in
2023–24).

### Divisions [C]

| Division | Meaning | Status 2023 → 2025 |
|---|---|---|
| **THF** | typed higher-order theorems | every year |
| **THN** | typed higher-order non-theorems | in design docs; not separately reported J12/CASC-30 |
| **TFA** | typed first-order **with arithmetic** | every year |
| **TFN** | typed first-order non-theorems | returned from hiatus for CASC-29; run since |
| **FOF** | first-order theorems (FEQ/FNE categories) | every year |
| **FNT** | first-order non-theorems / model finding | run 2023; **"gone on hiatus"** for 2024; absent 2024 and 2025 |
| **EPR** | effectively propositional | absent from J12 results; **run in CASC-30** (6 systems, 200 problems) |
| **UEQ** | unit equality | every year |
| **SLH** | **Sledgehammer** — problems generated by Isabelle's Sledgehammer, unmodified | run 2023, 2024, 2025 |
| **LTB** | large theory batch | **"gone on hiatus"** as of CASC-29; absent 2024, 2025. Created 2008 |
| **ICU** | "I Challenge yoU" — half from the prior CASC's set, half submitted by each entrant (~10–20 FOF theorems each) | **new in CASC-J12 (2024)**; run again 2025 |

Systems / problems / time limit actually run [C]:

| Division | CASC-J12 (2024) | CASC-30 (2025) |
|---|---|---|
| THF | 7 / 500 / 180 s wall | 6 / 500 / 240 s wall |
| TFA | 4 / 200 / 180 s | 4 / 150 / 120 s |
| TFN | 4 / 150 / 180 s | 4 / 150 / 120 s |
| FOF | 14 / 500 / 180 s | 14 / 500 / 240 s |
| EPR | not run | 6 / 200 / 120 s |
| UEQ | 7 / 300 / 180 s | 9 / 300 / 240 s |
| SLH | 4 / 1000 / 30 s CPU | 5 / 1000 / 15 s CPU |
| ICU | 8 / 80 / 600 s | 8 / 101 / 480 s |

### Winners [C]

| Division | CASC-29 (2023) | CASC-J12 (2024) | CASC-30 (2025) |
|---|---|---|---|
| THF | Vampire 4.8 (452/500) | Vampire 4.9 (463/500) | Vampire 5.0 (449/500) |
| TFA | Vampire 4.8 (154/200) | Vampire 4.9 (164/200) | Vampire 5.0 (131/150) |
| TFN | Vampire 4.8 (108/150) | **iProver 3.9** (85/150) | Vampire 5.0 (110/150) |
| FOF | Vampire 4.8 (451/500) | Vampire 4.9 (471/500) | Vampire 5.0 (455/500) |
| FNT | Vampire 4.7 (142/150) | not run | not run |
| EPR | — | not run | Vampire 5.0 (186/200) |
| UEQ | **Twee 2.4.1** (260/300) | Vampire 4.9 (265/300) | Vampire 5.0 (263/300) |
| SLH | **E 3.0 / 3.1** (467/1000) | Vampire 4.9 (463/1000) | Vampire 5.0 (434/1000) |
| ICU | n/a | Vampire 4.9 (59/80) | Vampire 5.0 (69/101) |

**Vampire wins nearly everything.** The confirmed exceptions in this window are
Twee (UEQ 2023), E (SLH 2023) and iProver (TFN 2024).

**cvc5's position [C].** cvc5 competes but **won no CASC division in 2023–2025**.
Its best placings are in the arithmetic-heavy typed divisions: 2nd in TFA in
2023 (148/200) and 2024 (151/200), 2nd in TFN 2023 (58/150) and 2024 (48/150).
In 2025 (cvc5 1.3.0): THF 296/500, TFA 108/150, TFN 56/150, FOF 290/500,
SLH 294/1000. Pre-2023 wins were not checked.

Also seen in the tables: E, Zipperpin, iProver, Leo-III, LEO-II, Twee, Lash,
Duper, Satallax, Prover9, Princess, Beagle, the CSE/CSG contradiction-separation
family, Drodi, GKC, ConnectPP, SPASS-SCL, hopCoP, LisaTT.

### The TPTP library [C unless noted]

- **Languages**: CNF, FOF, TFF/TFX (typed first-order, extended), THF (typed
  higher-order), TCF (typed CNF), and the non-classical **NXF/NHF** dialects
  added with v9.0.0. A **DHF** (dependently typed higher-order) extension is
  documented in a 2025 paper.
- **Releases**: v9.0.0 on 1 Jun 2024 (first with non-classical problems);
  v9.1.0 ~30 Jul 2025; v9.3.0 on 20 Jun 2026; v9.3.1 on 21 Aug 2026, ~893 MB
  compressed / ~10.5 GB expanded **[I]**.
- **Size [I]**: v9.1.0-era figures, consistent across several snippets but not
  read off one authoritative table: **25,775 ATP problems** derived from 15,888
  abstract problems across **55 domains**, roughly 8,345 CNF / 9,091 FOF /
  3,297 TFF / 5,042 THF, with ~78% (20,172) containing equality.
- **Rating scheme [C]**: difficulty 0.0 (every state-of-the-art system solves
  it) to 1.0 (none does), re-assigned per release.
- **SZS ontology [C]**: `Theorem`, `ContradictoryAxioms`, `CounterSatisfiable`,
  `Unsatisfiable`, `Satisfiable`, `Unknown`, `Open`, `GaveUp`; CNF-only problems
  use the shorter `Unsatisfiable`/`Satisfiable`/`Unknown`/`Open` subset.
- **History [C]**: TPTP first released 1993; CASC conceived after CADE-12
  (1994); difficulty ratings 1997; current language 2003; SZS ontologies 2004;
  TSTP from ~2005; SPCs since 2010; SystemOnTPTP since 2011; StarExec since 2013.

**TSTP [C].** "Thousands of Solutions from Theorem Provers" — the companion
library of standardized-syntax derivations and models for TPTP problems, now at
`tstp.tptp.org` (the old `tptp.org/TSTP/` redirects). **A current numeric size
could not be confirmed.**

### Proofs and verification — the part that matters most here [C]

- CASC ranks by problems solved **with an acceptable solution output**, not by
  bare verdict. Proofs must be in TPTP derivation format, are checked with
  **TPTP4X** and **GDV**, must have TPTP problem formulae as leaves, and must
  show "reasonably fine-grained" inference steps — except SLH, which accepts
  proof-sketch-level single steps.
- **EPR is the sole exception**: ranked purely on solve count, no proof
  obligation. That is CASC's explicit *proof vs. assurance* line.
- **GDV** ("Geoff's Derivation Verifier") is the semantic derivation verifier;
  **IDV** is the interactive viewer; **SystemOnTPTP** is the web/API front end.
- A 2025 FLAIRS paper, *Proof Verification with GDV and LambdaPi — It's a Matter
  of Trust* (Sutcliffe, Blanqui, Burel), describes TPTP proof → GDV →
  **Dedukti/LambdaPi (λΠ-calculus modulo)** as a much smaller trusted kernel,
  and reports that **Vampire was extended to emit proofs in Dedukti concrete
  syntax** for exactly this purpose. This is the closest existing analogue to
  axeyum's "reconstruct into a small kernel" bet, in the first-order world.
- No routine Isabelle-reconstruction pipeline for CASC proof *output* was
  confirmed; SLH uses Isabelle-derived *inputs*.

### How to enter [C]

Package the system as a **StarExec installation package** (`.tgz`, runnable
contents only, source not required in that package) and email it to the
organizer by the delivery deadline; the organizer installs and runs it. Systems
enter per division and may enter several. Near-identical variants and
value-free wrappers are deprecated and can be pushed to the unranked
**Demonstration division**, which also auto-enters the previous year's division
winners and Prover9 1109a as fixed benchmarks. `SystemOnTPTP` is the natural
first step before StarExec packaging.

---

## 4. Theorem-proving and formalization benchmarks

### 4.1 The competition-math benchmarks

| Benchmark | Size | Systems | Notes |
|---|---|---|---|
| **miniF2F** | 488 problems (244 valid + 244 test) | Lean (3→4), Isabelle, HOL Light, Metamath | ICLR 2022; AIME/AMC/IMO + course material. **[I]** a 2025/2026 audit reports ~40% of formal statements across test+validation contain an error; "miniF2F-v2" corrects these and raises achievable end-to-end accuracy from ~40% to ~70% |
| **PutnamBench** | **1,724 formalizations** of 672 Putnam problems (1962–2025): Lean 4 = 672, Isabelle = 640, Rocq = 412 | Lean 4 / Isabelle / Rocq | NeurIPS 2024 D&B |
| **ProofNet** | 371 examples (Lean 3 statement + NL statement + NL proof) | Lean | undergrad analysis/algebra/topology; the standard autoformalization benchmark |
| **ProofNet#** | 2×185 = 370 statements **[I]** | Lean | 2025 re-annotation fixing ProofNet's evaluation reliability |
| **FIMO** | 149 formal statements (some sources 148) | Lean | IMO Shortlist 2006–2021, algebra + number theory |
| **FormalMATH** | 5,560 verified Lean 4 statements | Lean 4 | |
| **CombiBench** | 100 combinatorics problems | Lean 4 | |
| **NuminaMath-LEAN** | ~104,000 problems **[I]** | Lean | 19.3% human-annotated, 80.7% autoformalizer-generated (Aug 2025) |

**miniF2F-test SOTA (Lean 4) [C per paper, but budgets differ by 2–3 orders of
magnitude — always cite pass@k alongside the number]:**

| Model | Result | Date |
|---|---|---|
| Kimina-Prover-Preview-72B | 68.85% pass@32 (80.7% pass@8192) | 2025 |
| DeepSeek-Prover-V2-671B | 82.4% ± 0.6% pass@32 | 30 Apr 2025 |
| Goedel-Prover-V2-8B | 84.6% pass@32 | Aug 2025 |
| Goedel-Prover-V2-32B | 88.0% pass@32; 90.4% w/ self-correction; 92.2% pass@8192 | Aug 2025 |
| Pythagoras-Prover | 93.03% pass@2048 | 2026 |

**PutnamBench [I, second-hand]:** a Jan 2026 survey table reports "Aleph Prover"
at 668/672 Lean problems, with Seed-Prover 1.5 and "Hilbert" also cited. This
was **not** confirmed against the live leaderboard and should be re-verified
before being quoted.

### 4.2 Mathlib-derived and long-context benchmarks

| Benchmark | Size | Notes |
|---|---|---|
| **LeanDojo Benchmark / Benchmark 4** | ~98,734 theorem/proof pairs from Mathlib; Lean 4 test set 1,659 theorems | two splits: `random` and `novel_premises` |
| **ReProver** result | 51.2% pass@1 on `random` vs **26.3% on `novel_premises`** | the split exists precisely to expose this generalization gap |
| **miniCTX / miniCTX-v2** | long-context proving over real evolving Lean projects (PNT, PFR), cutoff 28 Nov 2024 | |
| LeanWorkbook, Herald, RealMath, HardMath | named in the literature; **sizes not pinned down** | treat as leads |

### 4.3 The Olympiad prizes — and a distinction that matters

- **IMO Grand Challenge [C]**: the rigorous formal-to-formal variant requires
  the system to receive a **Lean-formalized statement** and emit a
  **kernel-checkable Lean proof** within ~10 minutes, no partial credit.
- **AlphaProof / AlphaGeometry 2 [C]**, 2024: 4/6 IMO 2024 problems, 28/42
  points, silver-medal level, producing formal Lean proofs (statements
  hand-formalized by experts).
- **IMO 2025 gold [C]**: Google DeepMind's Gemini Deep Think (35/42, officially
  IMO-coordinator-certified) and OpenAI's experimental model (35/42,
  self-reported, **not** IMO-certified) both worked **entirely in natural
  language**. That is a different track from the F2F Grand Challenge. Harmonic's
  "Aristotle" is also reported at IMO 2025 gold **[I]**; formalization method
  unconfirmed.
- **AIMO (XTX Markets) [C]**: $10M challenge fund, $5M grand prize for the first
  open model to win IMO gold. **Critically, AIMO is answer-only** — Kaggle
  submissions are a single integer (mod 1000 in PP1/PP2, 5-digit in PP3), and no
  proof of any kind is graded. Progress Prize 1 (2024): $1.048M pool, won by
  **Numina**. Progress Prize 2: won by NVIDIA's **NemoSkills** (34/50) **[I]**.
  Progress Prize 3: launched 19 Nov 2025, $2.2M pool.

**Read for axeyum:** AIMO is not a proving arena. The Grand Challenge and
miniF2F/PutnamBench are.

### 4.4 Library sizes

| Library | Size | Confidence |
|---|---|---|
| **Isabelle AFP** | 1,025 entries, 607 authors, ~325,500 lemmas, ~5,422,400 lines | [I] live-page fetch, not line-verified |
| **Lean Mathlib** | 287,092 theorems, 136,466 definitions, 772 contributors | [I] stats page fetch |
| **Rocq** (ex-Coq) | renamed at **Rocq Prover 9.0**, 12 Mar 2025; current stable 9.1.0, 15 Sep 2025 | [C] |
| Rocq MathComp | ~150,000 LOC | [I] |
| **Mizar MML** | ~3.7M LOC; a 2012 figure gives >1,100 articles, >50,000 theorems | [I] / [C-dated] |
| **Metamath set.mm** | **exact current count not found** | gap |
| **HOL Light** | **exact current count not found** | gap |

**Freek Wiedijk's "Formalizing 100 Theorems" [C, live-fetched]** — the canonical
cross-system scoreboard, and all 100 are now formalized somewhere:

| System | Count | System | Count |
|---|---|---|---|
| HOL Light | 95 | Metamath | 74 |
| Isabelle | 92 | Mizar | 71 |
| Lean | 83 | ACL2/nqthm | 48 |
| Rocq | 80 | ProofPower | 43 |
| | | PVS 26, Imandra 20, Megalodon 12, Naproche 10, NuPRL/MetaPRL 8 | |

An older secondary summary quoted "HOL Light 69, Lean 85" — the live numbers
above supersede it, and the discrepancy is itself evidence the list moves. Date
any citation.

### 4.5 Cross-system ATP benchmarks

| Benchmark | What it is | Size |
|---|---|---|
| **GRUNGE** | HOL4 standard-library theorems translated into multiple logics (HOL with/without type vars, FOL typed/untyped) so HO and FO provers compete on matched problems | count not found |
| **Judgement Day** (2010) | the original Sledgehammer evaluation of E/SPASS/Vampire; found they discharge about half of typical user goals | methodology |
| **Mirabelle** | Isabelle's built-in tactic-evaluation harness | tool |
| **"Seventeen Provers Under the Hammer"** | every Sledgehammer problem from building 179 Isabelle sessions (75 distribution + 80 AFP + 24 IsaFoR) across 17 ATP configurations | 179 sessions |
| **HolyHammer** | hammer for HOL Light | — |
| **CoqHammer** | hammer for Rocq; translates goal + premises to FOL, dispatches to E/Vampire/Z3 | — |
| **MPTP2078** | Mizar theorems translated to FOL for premise selection | 2,078 |
| **Mizar40 / MizAR40** | larger Mizar-to-FOL set | 32,524 **[I]** |
| **M2K** | related Mizar set | 2,003 **[I]** |
| **HolStep** | HOL Light ML dataset | 2,209,076 conjecture–statement pairs; 11,410 conjectures |
| **HOList / DeepHOL** | HOL Light tactic/argument-prediction environment | ~30,000 proofs **[I]** |
| **IsarStep** | predicting missing intermediate propositions in Isar proofs | ~1.2M data points **[I]** |
| **PISA** | AFP proof extraction for Isabelle step prediction | 183K theorems, 2.16M steps; 1,000-problem eval subset **[I]** |

**Autoformalization metrics [I].** The field has largely abandoned BLEU/exact
match in favour of **typecheck rate** and **bidirectional proof-based
equivalence checking** against a reference — the direction ProofNet# and the
2026 "Proxy-Judge" paper push. No standard benchmark named "MathQual" was found.

---

## 5. Rewriting: termCOMP and the Confluence Competition

This is the arena with the closest structural match to axeyum's stated identity
("untrusted fast search, trusted small checking") — because it already works
that way.

### 5.1 termCOMP — Termination Competition

**[C] Editions:** ran in 2024, 2025 and **2026**. 2024/2025 were affiliated with
**WST** (Workshop on Termination); **2026 is at WST 2026 inside FLoC 2026**,
Lisbon — competition days 17–18 July, results at WST on 25 July, full run on the
RWTH Aachen HPC cluster. Organizer since 2024: Florian Frohn.

**[C] 2026 awards:** Long-Standing Contribution to **AProVE**; Test-of-Time to
**Matchbox**.

**[C] Category survival rule:** a category runs only "if there are at least 2
participants and at least 40 examples for this category in the underlying
termination problem data base." This is why the category list shrinks.

**[C] Categories, 2025:**

| Group | Categories |
|---|---|
| Termination of rewriting | TRS Standard (1,528 problems), TRS Relative, TRS Equational, TRS Conditional–Termination, TRS Conditional–Operational Termination, TRS Context Sensitive, TRS Innermost, TRS Outermost, SRS Standard, SRS Relative, Integer TRS Innermost, HRS Union Beta (higher-order) |
| Probabilistic | PTRS Standard, PTRS Innermost |
| Termination of programs | Integer Transition Systems, C, Java Bytecode, Java Bytecode Recursive, Logic Programming, Logic Programming with Cut, Prolog |
| Complexity | Complexity: C, Complexity: ITS |

**[C] A change worth knowing:** the classic **TRS Runtime Complexity** and
**TRS Derivational Complexity** categories **no longer run** — 2025's only
complexity categories are Complexity: C and Complexity: ITS. LoAT's own changelog
confirms several older input formats "have been discontinued at TermComp".

**[C] 2025 winners:**

| Category | 1st | 2nd |
|---|---|---|
| TRS Standard | AProVE25 (uncert 1302 / cert 1208) | NaTT (1046) |
| TRS Innermost | AProVE25 | MU-TERM 2025 |
| TRS Conditional–Termination | MU-TERM 2025 | — |
| SRS Standard | matchbox-tc25.0 (1674) | MnM-3.24 (1621) |
| Integer Transition Systems | T2 (1040) | VeryMax (994) |
| Java Bytecode | AProVE25 | — |
| Logic Programming | NTI+cTI25 | AProVE25 |
| Complexity: C | KoAT | CoFloCo |
| Complexity: ITS | KoAT & LoAT | CoFloCo |

### The certified track — read this part twice

**[C] Every tool submits two configurations per category:** an uncertified one
(`AProVE25_uncert`, scores every YES/NO it finds) and a certified one
(`AProVE25_cert`, which reports **only `CERTIFIED YES`**). In TRS Standard 2025:

| Config | score | YES | CERTIFIED YES |
|---|---|---|---|
| AProVE25_uncert | 1302 | 1030 | 0 |
| AProVE25_cert | 1208 | 0 | **946** |
| NaTT_uncert | 1046 | 877 | 0 |
| MU-TERM 2025_uncert | 789 | 693 | 0 |
| NTI25_uncert | 560 | 291 | 0 |

**Every "CERTIFIED YES" was independently re-verified by CeTA before being
counted** — not self-reported. AProVE's certified config recovers 946 of its own
1030 uncertified YES answers, i.e. **~92% of its proofs are machine-checkable and
~8% use techniques CeTA cannot check [I, computed from the table]**. Certification
has been part of this competition **since 2007**.

**[C] The pieces:**

| Piece | What it is |
|---|---|
| **CPF** (Certification Problem Format) | An XML format for termination (later confluence and complexity) proofs. Sternagel & Thiemann, UITP 2014. |
| **IsaFoR** | "Isabelle Formalization of Rewriting" — an Isabelle/HOL library of abstract rewriting theory plus concrete termination/confluence/complexity techniques. |
| **CeTA** | **Version 3.9, released 2026-06-16.** The checker, **extracted from IsaFoR by Isabelle's code generator** — so the checker is a byproduct of a machine-checked proof, not a hand-written verifier that trusts the formalization. Verifies: termination proofs (dependency pairs, reduction pairs, polynomial interpretations, path orderings, size-change), nontermination (loops/infinite sequences), complexity (weak dependency pairs, matrix interpretations), confluence/non-confluence (critical pairs, orthogonality, Newman's Lemma), and completion proofs. Home: `isafor-ceta.uibk.ac.at`. |

**[I] What CeTA cannot verify:** anything without a CPF encoding path from the
producing tool — coverage is capped by which techniques exist in IsaFoR. IsaFoR's
current size in lines was **not confirmed**; do not quote a number.

**[C] TPDB** (Termination Problem Data Base) lives at
`github.com/TermCOMP/TPDB`, organized by category directory (TRS
standard/innermost/outermost/conditional/equational/context-sensitive/relative,
SRS standard/cycle/relative, Java bytecode, Haskell, Prolog/LP, higher-order,
integer transition systems, plus complexity subdirectories) with an **XML**
subdirectory alongside native `.trs`/`.srs` text. New benchmark families go in
`Your-family-name_YY` directories via pull request; corrections use `file_REV2`.
The competition front end is a separate StarExec-presenter repo,
`github.com/TermCOMP/starexec-master`.

### 5.2 CoCo — Confluence Competition

**[C] Editions:** 2024 (13th, IWC 2024), 2025 (14th, IWC 2025, Leipzig, 2–3 Sep),
**2026 (15th, IWC 2026 on 24 July 2026, inside FLoC 2026 Lisbon)**.

**[C] Platform 2026:** StarExec Miami, 60 s wall-clock / 128 GB per problem;
registration by EasyChair, problems via the **ARI** submission interface;
problem deadline 9 June 2026.

**[C] Categories:** 2024 and 2026 run eleven — **COM** (commutation), **CSR**
(context-sensitive), **CTRS** (conditional), **GCR** (ground confluence),
**INF** (infeasibility), **LCTRS** (logically constrained), **NFP** (normal form
property), **SRS**, **TRS**, **UNC**/**UNR** (unique normal forms w.r.t.
conversion / reduction). 2025 was a reduced year: CSR, CTRS, INF, LCTRS, TRS,
plus the Certification and Reliability tracks. Per-category problem counts live
in COPS/ARI, not on the front page.

**[C] Winners:**

| Category | 2024 (1st/2nd/3rd) | 2025 (1st/2nd/3rd) |
|---|---|---|
| TRS | CSI / ACP / CONFident | CSI / Grackle-CSI / ACP |
| SRS | CSI / ACP / Hakusan | not run |
| CTRS | CONFident / CO3 / ACP | CONFident / CO3 / ACP |
| CSR | CONFident / — | CONFident / — |
| COM | ACP / FORT-h | not run |
| GCR | AGCP / FORT-h | not run |
| INF | infChecker / Moca / NaTT | infChecker / CO3 / Natto |
| **LCTRS** | **crest** / CRaris | **crest** / CRaris |
| NFP | CSI / FORT-h | not run |
| UNC | CSI / ACP / FORT-h | not run |
| UNR | CSI / FORT-h | not run |
| **Certification** | **CeTA** / FORTify | **CeTA** / FORTify |
| **Reliability** | FORT-h / CSI / ACP | CSI / Hakusan / ACP |

**[C] The two certificate categories are scored from opposite ends** — CoCo's own
results page: "In the CERTIFICATION category, certifiers are ranked based on the
number of certificates that are validated. In the RELIABILITY category, tools are
ranked based on the number of generated certified proofs." So CERTIFICATION scores
the **checker** (CeTA won both years) and RELIABILITY scores which **prover**
produces the most certificates that actually pass. That is a two-sided design
axeyum's evidence discipline should study directly.

**[C] COPS → ARI.** COPS ("Confluence Problems") was created in 2012 to support
CoCo, each problem with a persistent number (Hirokawa/Nagele/Middeldorp, IJCAR
2018). **The COPS format has been superseded by ARI** — "the ARI format replaces
the COPS format", with a conversion tool — and the combined infrastructure is
**ARI-COPS** at `ari-cops.uibk.ac.at`, with a web interface **ARIWeb**. The exact
current problem count was **not found**.

### 5.3 LCTRS — the rewriting↔SMT bridge

**[C]** An **LCTRS** (logically constrained TRS) is a rewrite system whose rules
carry a **logical constraint over a background theory** (e.g. LIA) with theory
terms and values interleaved into the rewriting signature — so program semantics
are encoded directly with built-in int/bool operations rather than as
constructors.

**[C] crest** is the current leading LCTRS tool: it proves **(non-)confluence and
(non-)termination of LCTRSs**, won the LCTRS category at CoCo 2024 *and* 2025,
and its documentation states plainly: **"As default SMT solver currently Z3 is
used."**

**[C] The mechanism:** critical pairs between LCTRS rules are computed as ordinary
TRS critical pairs over the left-hand sides, but **joinability/confluence checks
on the resulting pair require discharging the accompanying logical constraints as
SMT queries** — satisfiability of the constraint conjunction, and validity of
implications between constraints. An SMT call literally gates a rewriting
confluence conclusion.

**[C] Not yet certified.** CeTA/CPF certification applies to the TRS/CTRS-family
categories; crest's LCTRS results do **not** appear in the
CERTIFICATION/RELIABILITY tables for 2024 or 2025. **Treat "LCTRS is certified in
CoCo" as false / not yet supported.** That is an open slot.

**[I] Ctrl**, the earlier LCTRS tool, appears in secondary literature but was not
confirmed as an active participant; treat it as superseded by crest.

### 5.4 Equality saturation — an arena that does not exist

**[C]** **egg** ("egg: Fast and Extensible Equality Saturation", POPL 2021,
`github.com/egraphs-good/egg`) ships only a small illustrative test suite —
`prop.rs` (propositional logic), `math.rs` (real arithmetic + symbolic
differentiation), `lambda.rs` (lambda-calculus partial evaluator), timed via
`EGG_BENCH_CSV`. **egglog** ("Better Together: Unifying Datalog and Equality
Saturation", PLDI 2023) has CodSpeed micro-benchmarks against egg as a baseline.
**Tensat**, **SPORES** and **Herbie** are downstream *applications* of e-graphs
(tensor-graph superoptimization, SQL query optimization, floating-point
rewriting), not a shared benchmark suite. `awesome-egraphs` is the community
catalog.

**[C] There is no competition, bake-off, or standardized shared benchmark suite
for equality saturation**, comparable to termCOMP or CoCo. Given axeyum has an
`axeyum-egraph` crate with explanation forests, this is an open field rather than
a scoreboard to enter.

### 5.5 Unit equality and Knuth–Bendix completion

**[C]** **UEQ** in CASC (from TPTP) is effectively the standardized
Knuth–Bendix-completion arena; no separate KB-completion benchmark suite was
found **[I]**. **Waldmeister** dominated UEQ historically; **Twee** held it for
several years after; **at IJCAR 2024 Vampire won UEQ, deposing Twee** — so older
references citing Twee as champion are stale.

### 5.6 Verified rewrite rules — for SMT, no arena exists

**[C]** **RARE** is cvc5's DSL for declaratively specifying rewrite rules so cvc5
can emit fine-grained, machine-checkable proofs of its own simplification steps
instead of opaque "trust me" rewrites. The option `proof-granularity=dsl-rewrite`
controls how much is elaborated via RARE vs. left as a coarse `ProofRewriteRule`
step; **`dsl-rewrite` is now the default proof granularity**.

**[C]** **IsaRare** ("IsaRare: Automatic Verification of SMT Rewrites in
Isabelle/HOL", TACAS 2024) automatically proves cvc5's RARE rules sound in
Isabelle/HOL — retroactively discharging exactly the obligations RARE leaves open.

**[C] But there is no standardized shared "verified rewrite rule" benchmark or
competition** analogous to termCOMP/CoCo for SMT rewrite rules. What exists is
(a) cvc5's own in-repo RARE rule set, growing organically, and (b) one-off
academic verification against it. **[I]** No comparable effort to verify Z3's
simplifier was found.

**So: if axeyum wants a rewriting-certificate arena, CPF/CeTA is the pattern to
copy, not RARE/IsaRare** — and "verified rewrite rules as a benchmarked artifact"
is a genuine gap.

### 5.7 Proof obligations across competitions — is evidence mandatory?

| Arena / track | Proof required? | Format | Checker |
|---|---|---|---|
| **SAT Competition 2025, Main track** | **[C] MANDATORY for UNSAT** — "All participants in the Main track of this competition must output proofs of unsatisfiability", to `proof.out` | **DRAT** (text or binary, same as 2014), back-compatible with RUP/DRUP; also DPR and VeriPB | **drat-trim** (classical, unverified), **cake_lpr** (formally verified LRAT/LPR checker), **GRAT/gratgen** (formally verified), **VeriPB/CakePB** |
| **HWMCC 2024/2025** | **[C] MANDATORY** — bit-level tracks require counterexamples *and* safety certificates; word-level tracks require BTOR2 counterexamples | AIGER witness circuit / BTOR2 | **Certifaiger** (+ Cerbtora), **aigsim** |
| **CASC** (all but EPR) | **[C] MANDATORY** — ranked by problems solved *with acceptable solution output* | TPTP derivation | **TPTP4X + GDV**; optional Dedukti/LambdaPi |
| **termCOMP certified configs** | **[C] Opt-in per configuration**, but a certified config scores *only* CERTIFIED YES | **CPF** (XML) | **CeTA** (extracted from IsaFoR) |
| **CoCo Certification/Reliability** | **[C] Opt-in categories**, scored from both sides | CPF | CeTA, FORTify |
| **CHC-COMP 2026** | **[C] New Model Track**; main Solver Track results "certified by all participants" | model / SMT VCs | ATHENA (external), Carcara / LFSC / SMTInterpol for UNSAT |
| **SV-COMP** | **[C] Witnesses expected and separately scored**; 229,118 validated in 2026 | witness format 2.1 (YAML) | 16 C validators |
| **SMT-COMP** | **[C] Model Validation Track exists**; a **Proof Exhibition Track** is listed in the 2023 slides. **[I] not confirmed to still run in 2024/2025, and not confirmed mandatory anywhere.** Do **not** assert SMT-COMP mandates proofs — read the current `rules.pdf` if this is load-bearing | Alethe / LFSC / cpc | Carcara (fast, **explicitly not itself formally verified**), LFSC checker |

**[C] The asymmetry to notice:** SAT's checker (`cake_lpr`, GRAT) and rewriting's
checker (CeTA) are *themselves* machine-checked artifacts. SMT's fastest Alethe
checker, Carcara, is documented as "not currently formally verified". That is
precisely the gap axeyum's kernel sits in.



---

## 6. Verification consumers that stress SMT

### 6.1 SV-COMP — Competition on Software Verification

The largest comparative evaluation in formal methods, at TACAS/ETAPS.

| | SV-COMP 2025 (14th) | SV-COMP 2026 (15th) |
|---|---|---|
| Verifiers evaluated | 62 (C) | **61 (C) + 11 (Java) + 3 (SV-LIB)** |
| Validators evaluated | 18 | **16 (C) + 3 (Java) + 1 (SV-LIB)** |
| Actively supported | 35 verifiers, 13 validators; 33 reps, 12 countries | 43 verifiers, 13 validators; **44 reps, 12 countries** |
| C tasks | 33,353 (6 specifications) | **36,402** (6 specifications) |
| Java tasks | 674 assertion + 673 runtime-exception (demo) | **1,731** (2 specifications) |
| SV-LIB tasks | — | **254** (new demo format) |
| Witnesses validated | — | **229,118** generated + 135 handcrafted |

All **[C]** (2025 numbers from the TACAS 2025 report abstract; 2026 numbers read
directly from the TACAS 2026 report PDF).

**Specifications [C]:** reachability, memory safety, memory cleanup, overflows,
termination, data races.

**Category naming changed in 2026 [C]:** every category now begins with the
language — `C.*`, `Java.*`, `SV-LIB.*`. `FalsificationOverall` was renamed
**`C.FalseOverall`** and now includes termination; a dual **`C.TrueOverall`**
was introduced for the first time. There was a Huawei-sponsored demo category
`C.Huawei-Concurrency-Challenges` (€3,000 / €1,500 / €500 prizes). Java's
`assert_java` and `runtime-exception` properties were renamed `valid-assert` and
`no-runtime-exception`.

**Witness formats [C].** 2026 supports **witness format 2.1** and
**discontinued correctness witnesses in format 1.0** (except Java and
team-unsupported verifiers). A new category **`C.termination.ViolationWitnesses`**
holds 17 handcrafted non-termination witness validation tasks. The CPU limit for
validating a correctness witness was cut from 15 min to 5 min.

**2026 winners [C, read from the report's ranking tables]:**

| Category | 1st | 2nd | 3rd |
|---|---|---|---|
| C.Overall (max 60,609) | **UAutomizer** 31,472 | CPAchecker 27,979 | Symbiotic 25,471 |
| C.FalseOverall (max 12,195) | **Symbiotic** 7,833 | CPAchecker 7,389 | UAutomizer 5,835 |
| C.TrueOverall (max 48,413) | **UAutomizer** 25,637 | Goblint 22,673 | Mopsa 20,637 |
| Java.Overall (max 2,821) | **JBMC** 1,561 | GDart 1,470 | JLiSA 1,311 |

**Which solvers back the verifiers [C].** The 2026 report's Table 9 lists solver
libraries and frameworks used as components **by at least two participating
tools**: Apron, **Bitwuzla, Boolector, CVC, MathSAT, SMTInterpol, Z3**, MiniSAT,
Glucose, **JavaSMT** (the uniform Java SMT façade), CPAchecker, CProver,
ESBMC, Frama-C, JPF, Klee, Symbiotic, Ultimate — **and Eldarica and Golem**, the
two CHC solvers from §1. That last pair is the concrete link between CHC-COMP
and SV-COMP: winning CHC engines are shipped as components inside
software verifiers.

**Test-Comp [C].** Still alive and paired with SV-COMP: the report cites
"SV-COMP 2026, Test-Comp 2026" Zenodo artifacts, and a joint **SV-COMP/Test-Comp
Workshop** ran in April 2025 (Frauenchiemsee) and again on 17 March 2026
(Munich). SV-COMP's own report names RERS, VerifyThis, Test-Comp and TermCOMP as
its most related competitions.

### 6.2 VNN-COMP — neural network verification

**[C]** VNN-COMP 2025 was the **6th** edition, held as part of the 8th
International Symposium on AI Verification (SAIV), co-located with CAV 2025:
**8 teams**, **16 regular + 9 extended benchmarks**.

**[C] Formats:** networks in **ONNX**, specifications in **VNN-LIB**
(vnnlib.org). Tools are evaluated on equal-cost hardware via an automatic
AWS-based pipeline, and parameters are fixed by participants before the final
test sets are public.

**[C] Winner:** **α,β-CROWN** won VNN-COMP **2021, 2022, 2023, 2024 and 2025** —
five consecutive years — and in 2025 was ranked top-1 in *every* scored
benchmark. Other tools in the field: MN-BaB, VeriNet, Marabou, NeuralSAT, PyRAT,
nnenum.

**The SMT angle [I, needs confirmation].** Marabou descends from Reluplex, a
simplex-based SMT-style procedure, and is documented as combining SMT
techniques with abstract interpretation **and proof production**. There is also
a 2025-era "Soundness Benchmark for Neural Network Verifiers". But the winning
tools are bound-propagation + branch-and-bound on GPUs, not off-the-shelf SMT —
this is an arena where the SMT formulation lost to a specialized method, which
is itself the useful finding.

### 6.3 HWMCC — Hardware Model Checking Competition

**[C] Editions:** 2007, 2008, 2010–2015, 2017, 2019, 2020, **2024**, **2025**.
Note the four-year gap 2020→2024.

**HWMCC 2024 (12th) [C]:** affiliated with FMCAD 2024, Prague, 14–18 Oct 2024.
The organizers reintroduced a bit-level track **and made certificates
mandatory**. Participation went from **three entrants in the previous edition to
a record nine**. Winner: **rIC3**, on both safe and unsafe benchmarks, beating
the 2020 winner ABC *even with all certificates verified* — the headline result
that certification and performance are not in tension. Of **1,536 certificates
produced, 44 were incorrect**, from four model checkers (supercar 20,
ncip-minicraig 9, ncip-portfolio 8, fric3 7).

**HWMCC 2025 [C]:** affiliated with FMCAD 2025, Menlo Park CA, 6–10 Oct 2025.
Organizers: Armin Biere (Freiburg), Nils Froleyks (JKU Linz), Mathias Preiner
(Stanford). **Four tracks**, 10 medals:

| Track | Format |
|---|---|
| 1. Word-level safety **without** arrays | BTOR2 |
| 2. Word-level safety **with** arrays | BTOR2 |
| 3. Bit-level safety | **AIGER 1.9 including reset functions** (track-1 benchmarks translated down from word level) |
| 4. Bit-level **liveness** (new) | AIGER 1.9 |

**Mandatory evidence [C]:** word-level tracks require **BTOR2 counterexamples**;
bit-level tracks require **both counterexamples and safety certificates**,
validated by **Certifaiger** (certificates) and **aigsim** (counterexamples).

**2025 medals [C]:** rIC3 2 gold; nuXmv 1 gold; Pono 1 gold; supercar,
rIC3-multi, avr 1 silver each; btor2-select 2 bronze.

**Certifaiger [C]:** a C++ tool taking a model circuit `M` and a witness circuit
`M'` in AIGER, emitting **five CNF files** — if all five are UNSAT the witness
is valid. So the certificate check is *a SAT problem*, and the certificate
format is *an AIG*. There is a companion **Cerbtora** for the word-level side,
and the SAT Competition 2025 benchmark pool includes a "Challenging Certificates
from Model Checking" family generated from exactly these checks.

**This is the single most directly-connected arena to axeyum's existing AIG
layer.** The input format is AIGER 1.9, the certificate is an AIG, and checking
it is five SAT calls.

### 6.4 Adjacent model-checking arenas

- **Model Checking Contest (MCC) [C]** — Petri nets, annual, results at
  `mcc.lip6.fr`; the **2025 edition results** are published
  (`mcc.lip6.fr/2025/results.php`), and 2024 was held as part of Petri Nets.
  Tools include TAPAAL, TINA/tedd/SMPT.
- **RERS Challenge [C, existence]** — named by SV-COMP as one of its most
  related competitions.
- **SAT Competition [C]** — 2025 edition with Main and Parallel tracks;
  registration Apr 15–30, results announced 15 Aug 2025 at SAT 2025. A **2026**
  edition exists (its `downloads/checkers/veripb.pdf` is live). Proof logging is
  the norm in the main track and the checker documentation for **VeriPB and
  CakePB** is distributed with the competition; the exact mandatory-vs-optional
  status per track was **not confirmed** in this pass.

---

## 7. Computer algebra benchmarks

### 7.1 Integration: the one place a CAS is measured hard

**Rubi's test suite [C].** Built contemporaneously with Rubi, "currently
consisting of over 72,000 integration problems", organized by integrand form,
and translated into **Axiom, Maple, Mathematica and Maxima syntax** — freely
downloadable. Each problem stores the integrand, the variable, the number of
Rubi steps, and **the optimal antiderivative**. Results are graded by a "type
number" of the highest function class involved:

| Level | Class | Level | Class |
|---|---|---|---|
| 1 | rational | 6 | Appell |
| 2 | algebraic | 7 | nonclosed-form (e.g. RootSum) |
| 3 | elementary | 8 | Integrate |
| 4 | special | 9 | unrecognized |
| 5 | hypergeometric | | |

A result is **deficient** if its type number exceeds the optimal
antiderivative's. Reported per-file as pie charts over: optimal, valid but
suboptimal, unnecessarily higher-level/complex, not integrated, timed out
(120 s), and **not a valid antiderivative**. Note that Rubi's own site still
compares against **Mathematica 11.3 and Maple 2018.2**, and Maple was run on
only a random quarter of the suite to avoid crashing it.

**Nasser Abbasi's "Computer Algebra Independent Integration Tests"** is the live,
independent re-run — and it is far larger than 72k.

**[C] Summer 2024 edition (compiled 23 May 2024): 106,812 problems**, nine CAS:

| CAS | Version |
|---|---|
| Mathematica | 14 (9 Jan 2024) |
| Rubi | 4.17.3 (25 Sep 2023) on Mathematica 14 |
| Maple | 2024 (1 Mar 2024) |
| Maxima | 5.47 via SageMath 10.3 |
| FriCAS | 1.3.10 via SageMath 10.3 |
| Giac/Xcas | 1.9.0-99 via SageMath 10.3 |
| Sympy | 1.12 on Python 3.11.6 |
| Mupad | Matlab 2021a, Symbolic Math Toolbox 8.7 |
| Reduce | CSL rev 6687 (9 Jan 2024) |

**[C] Results, Summer 2024 (n = 106,812):**

| System | Solved % (count) | A grade | B | C | F |
|---|---|---|---|---|---|
| Mathematica | **97.367%** (104,000) | 73.46 | 5.21 | 15.02 | 2.63 |
| Rubi | 93.136% (99,480) | **84.74** | 2.50 | 2.12 | 6.86 |
| Maple | 83.761% (89,467) | 58.11 | 14.06 | 7.21 | 16.24 |
| FriCAS | 77.213% (82,473) | 50.54 | 18.94 | 4.54 | 22.79 |
| Giac | 57.511% (61,429) | 37.65 | 14.92 | 1.14 | 42.49 |
| Reduce | 54.340% (58,042) | n/a | 49.91 | n/a | 45.66 |
| Mupad | 52.841% (56,440) | n/a | 48.44 | n/a | 47.16 |
| Maxima | 52.537% (56,116) | 36.59 | 10.61 | 1.54 | 47.46 |
| Sympy | 42.166% (45,038) | 24.09 | 9.76 | 4.80 | 57.83 |

Grades: **A** optimal in quality and leaf size; **B** optimal quality but leaf
size > 2× optimal; **C** solved but non-optimal (introduces a hypergeometric,
a special function, or the imaginary unit where the optimal answer has none);
**F** unsolved, timed out, hung, crashed or raised. A CAS that *correctly
returns an integral unevaluated* within the time limit scores **A**; one that
times out on the same integral scores **F**.

**This is the sharpest CAS scoreboard that exists, and it is fully open.** The
suite has an index at `12000.org/my_notes/CAS_integration_tests/index.htm`
(compiled 31 Aug 2025) with FULL / Specialized / LITE sections; the Summer 2024
report is the most recent one whose URL resolved (`summer_2025` and
`summer_2026` are 404).

**Sibling suites by the same author [C]:** "Solved Differential Equations From
Selected Books" (`12000.org/my_notes/solving_ODE/`), **compiled 15 Aug 2026** —
i.e. actively maintained and newer than the integration report — comparing
Maple, Mathematica and Sympy per-problem with timings and leaf sizes. The classic
ODE benchmark it draws on is **Kamke's *Differentialgleichungen*, 1,429 linear
and non-linear ODEs [C]**, which Maplesoft itself used for a published
Maple-vs-Mathematica comparison. A PDE comparison by the same author is
referenced (700+ pages) **[I]**.

### 7.2 The Wester suite

**[C]** Michael Wester's "A Review of CAS Mathematical Capabilities" reviews six
general-purpose CAS on **123 short problems** across a broad range of symbolic
capability. It is ported into **Sage** as
`sage.calculus.wester`, so it is directly runnable today. There is also an older
"Computer Algebra Benchmark Initiative" page at Mannheim carrying it.

### 7.3 What does *not* exist

**There is no computer-algebra competition.** No CAS equivalent of SMT-COMP or
CASC was found: no annual event, no jury, no medals, no standardized rules. What
exists instead is (a) one person's very large, very good, independently re-run
integration/ODE scoreboard, (b) vendor-published comparisons (Maplesoft vs.
Mathematica on Kamke), and (c) per-paper ad-hoc benchmarking. **[C — this is a
negative finding from targeted search, and the absence of any competition site,
rules page, or results archive in the searches run.]**

The nearest thing to a *community* is **SC-Square** (Satisfiability Checking and
Symbolic Computation), whose **10th International Workshop was held in Stuttgart
on 2 August 2025, co-located with CADE-30 [C]** — precisely the community that
sits between a CAS and an SMT solver.

---

### 7.4 Polynomial and algebra benchmark collections

**SymbolicData — dead [C].** Started 1998 out of a benchmarking initiative in
computer algebra; the project's own site says "The SymbolicData Project started
in 1998 with several ambitious goals is over", with an end-of-project
announcement by Hans-Gert Gräbe dated **2020-11-04**. The GitHub org's six repos
were last updated 2016–2021. Its INTPS records were meant to unify the different
benchmark collections of polynomial systems. **[C] Sage still ships a wrapper
with 372 ideals**, retrievable by name (`sd.Katsura_3`) with configurable base
field and term order — so the data survived the project.

**[C] Canonical Gröbner-basis families:** Katsura-n, Cyclic-n, Eco-n, Noon-n,
Reimer-n, Henrion-n, Chandra-n. Instances live in:

| Source | Contents |
|---|---|
| `msolve.lip6.fr/examples/` | `.ms` files: eco10–eco15, katsura6–15, henrion5–9, noon3–9 (mod-31 and rational), plus critical-points, minrank, KLYZ, f633, gametwo7, phuoc1, sot1, vor1 |
| Groebner.jl | Chandra-n, Cyclic-n, Eco-n, Henrion-n, Katsura-n, Noon-n, Reimer-n, Hexapod, IPP, SIAN-Julia |
| Sage's SymbolicData wrapper | Katsura ideals by name |

**msolve [C].** Open-source C library (GPL-2.0, 2,743 commits on master) for
0-dimensional polynomial systems — Gröbner bases, lex conversion, real root
isolation, AVX2-accelerated linear algebra. Integrated into OSCAR, SageMath,
Macaulay2, AlgebraicSolving.jl. The ISSAC 2021 paper benchmarks it against
**Magma, Maple and Singular** "on a wide range of systems with finitely many
complex solutions", claiming systems "out of reach" for prior CAS. The specific
instance families in the comparison tables were **not extractable** (paywalls).

**[C, negative finding] No standard factorization/GCD suite exists.** Every
FLINT/NTL/Singular/Magma comparison found is a one-off table built for a specific
paper or talk — FLINT's own ICMS 2020 slides, a multivariate-factorization paper
running Singular 3-1-6 / FLINT 2.3 / NTL 5.5 on one machine, a `flint-devel`
mailing-list thread. `flintlib.org/links.html` has an "Applications & benchmarks"
section that points at scattered comparisons rather than a maintained suite.
**OSCAR** publishes no benchmark claims on its homepage at all (current version
1.8.2, 2026-09-02).

**SymPy's own suite [C].** `sympy/sympy_benchmarks` uses **airspeed velocity
(asv)**, mirrors SymPy's module layout, actively maintained (280 commits).
Results published at `hera.physchem.kth.se/~sympy_asv` and
`moorepants.info/misc/sympy-asv/`. **[I]** No citable SymPy-vs-Mathematica/Maple
comparison beyond claims in ML-for-math papers.

### 7.5 Certified computer algebra — what exists, and what does not

| Tool | What it does | Kernel-checked certificate? |
|---|---|---|
| **CoqEAL** | Refinement framework: change data representation mid-proof (dense→sparse, ℤ→machine ints) while preserving correctness | **Yes** — refinements are proof terms; the concrete algorithm's correctness is derived from the abstract spec via the `refines` relation |
| **MathComp** | SSReflect algebra library underlying CoqEAL | n/a (library) |
| **`ring` / `field_simp`** | Reflective (semi)ring/field equality decision | **Yes** — reflection; normal forms computed by a verified function, kernel checks by computation (`vm_compute`/`native_compute`) |
| **`nsatz`** | Polynomial equalities via Hilbert's Nullstellensatz | **Yes** — computes a Gröbner basis *externally* to find witnesses (Sᵢ, r, c) with c(P−Q)^r = Σ Sᵢ(Pᵢ−Qᵢ), then discharges that identity with `ring`. **Untrusted search, trusted check** |
| **`linear_combination`** (Mathlib) | Proves an equality is a stated linear combination of hypotheses | **Yes** — documented explicitly as "a certificate checker" |
| **`polyrith`** (Mathlib) | Finds the coefficients `linear_combination` needs, by calling an external CAS/service | Search is untrusted and external; the result is re-checked by `linear_combination`. Same trust boundary as `nsatz` |
| **`positivity`** (Mathlib) | `0 ≤ e` / `0 < e` / `e ≠ 0` by structural recursion | Ordinary kernel-checked proof term **[I]** |
| **Flocq** | Unified Coq formalization of floating point (binary/decimal, fixed/floating) | library; underlies CoqInterval |
| **CoqInterval** | Interval arithmetic with bisection and Taylor models, to prove numeric bounds | **Yes**, reflective |
| **Gappa** | Certifies numerical programs' FP/interval properties; has a Coq-checkable proof mode | **Yes**, via Coq |
| **ValidSDP** | Reflexive Coq tactics for multivariate inequalities: rounds a numerical SDP/SOS solution to a small-denominator **rational certificate**, checked reflexively by the kernel | **Yes** |
| **SOSTOOLS / YALMIP / SparsePOP** | Numerical SOS/SDP front ends | **No [I]** — they are the untrusted search step; rationalization/certification is bolted on afterward by ValidSDP or Monniaux–Corbineau |
| **HOL Light real arithmetic** | Harrison's proof-producing decision procedure for real closed fields; extended to SOS certificates | **Yes** — Coq's `psatz`/`nra`/`nia` are documented as based on it |
| **AFP `Groebner_Bases`** (Immler & Maletzky, 2016) | Gröbner basis theory for multivariate polynomial rings over fields in Isabelle/HOL, on top of AFP `Polynomials` | **Yes**, formalized; follow-ons cover modules, F4, and signature-based algorithms |
| **AFP `Berlekamp_Zassenhaus`** (Divasón, Joosten, Thiemann, Yamada) | Verified factorization of square-free integer polynomials; factors degree-100 (one source says up to degree 500) polynomials in seconds; underlies AFP `Algebraic_Numbers` | **Yes**, verified implementation |

**[C, negative finding] There is no benchmark arena for "CAS results carrying
kernel-checkable certificates."** No competition, no leaderboard, no standing
suite scoring computer-algebra systems on the fraction of results they can back
with a machine-checked certificate. What exists is a scattered set of point
solutions, each evaluated on its own hand-picked examples, with no shared corpus
and no comparison protocol across them. Even the *idea* of scoring
"CAS + certificate" systems against each other does not appear to have a named
venue. This is stronger than the §7.3 negative: there, the competition is
missing but a de-facto scoreboard exists; here neither does.

### 7.6 Real quantifier elimination, CAD, and nonlinear real arithmetic

| Tool | Status | Certificate? |
|---|---|---|
| **QEPCAD B** | Actively hosted; **now distributed as part of the Tarski system** per its own maintainer page | CAD/formula output, not an independently checkable certificate |
| **Tarski** | Chris Brown's successor/umbrella system (C/C++), open source: simplification, QE, CAD operations | No independent certificate found |
| **Redlog** (in REDUCE) | Long-running; still appearing in SMT-COMP system descriptions as late as 2018 | Formula output, not certificate-based |
| **SMT-RAT** | Active at RWTH Aachen; CAD / virtual substitution / Gröbner modules for SMT | Some proof-generation work exists (Kremer's coverings paper); primary output is sat/unsat |
| **Z3 `nlsat`** | Actively maintained; model-based CAD-like NLSAT is Z3's nonlinear real core | **[I]** no standard certificate beyond Z3's internal proof logging |
| **cvc5 CDCAC** | cvc5's nonlinear subsolver is **cylindrical algebraic coverings**, following Ábrahám et al. 2021 | The coverings line explicitly targets **simplifying proof generation** for NRA — the most certificate-oriented of these |
| **Maple RegularChains** | Exists; used in QE and polynomial-system SMT research | No certificate mechanism found **[I]** |

**[C] SMT-COMP 2025 results in these divisions — note that neither is in axeyum's
eleven:**

| Division | Benchmarks | Winner |
|---|---|---|
| **QF_NRA** (single query) | **3,104** | **Z3-alpha** — 2,872 solved (1,452 SAT / 1,420 UNSAT), zero incorrect, won every performance category |
| **NRA** (single query) | **99** | **SMT-RAT** — 96/99 correct, CPU-time score 26.55; SAT category tied with YicesQS |

QF_NRA corpus growth: 2,908 (2022) → 2,795 (2023) → 3,104 (2025) **[C]**.
2024 winners for these two divisions were **not confirmed**.

**[I, negative]** No dedicated standing QE/CAD benchmark repository independent
of SMT-LIB was found — only individual papers' ad hoc example sets.

**[C] SC-Square**, the community sitting exactly between CAS and SMT, held its
**10th workshop on 2 August 2025 in Stuttgart, co-located with CADE-30**,
proceedings at CEUR-WS Vol-4116. **Its own workshop page contains no mention of a
shared CAS/SMT benchmark library** — checked directly and confirmed absent. The
predecessor EU project SC² produced integration work (SMT-RAT's CAD/Gröbner/VS
modules) but no artifact named as a standing benchmark library.

---

## 8. Optimization Modulo Theories, and string-solver suites

### 8.1 OMT — a capability with no arena

**[C] The solvers.** **OptiMathSAT** (Sebastiani & Trentin, FBK + DISI Trento)
extends MathSAT 5: it supports equality and uninterpreted functions, linear
arithmetic, bit-vectors and arrays, and does **incremental multi-objective
optimization** over linear objective functions, including partial weighted
MaxSMT. Multiple heterogeneous objectives can be combined independently,
lexicographically, or in linear / min-max / max-min combinations. It has an
incremental interface, accepts an extended SMT-LIB v2 language and a FlatZinc
subset, and has an API. **νZ** is Z3's optimization layer (Bjørner, Phan,
Fleckenstein), offering Pareto fronts, lexicographic, or independent objectives.
**Symba** is the other Z3-based ancestor. Z3's `(maximize)` / `(minimize)` /
`(assert-soft)` are the de facto surface syntax.

**[C] There is no OMT standard and no OMT competition.** The SMT 2025 workshop
carried a paper, *A Proposal for an OMT Extension to SMT-LIB*, whose own framing
is the finding: **"no official SMT-LIB extension standard has yet been adopted
for OMT. As a result, OMT benchmarks lack standardization, which hinders broader
adoption."** The proposal's stated goal is "to foster the development of OMT
solvers and applications, to enable more robust, reusable, and comparable OMT
solutions." SMT-COMP has no optimization track (its five 2025 tracks are Single
Query, Incremental, Model Validation, Parallel, Unsat Core).

**[I] Benchmarks** for OMT therefore live inside the OptiMathSAT/νZ papers
(LGDP, SAL bounded model checking, LRA/LIA scheduling, MiniZinc-derived sets from
the "From MiniZinc to Optimization Modulo Theories, and Back" line of work). The
OptiMathSAT site's fetched pages surface no benchmark archive link.

**Read for axeyum: OMT is a capability gap with no scoreboard.** Entering it
buys nothing measurable today, but the SMT-LIB extension proposal is the moment
to be present at if the project wants a say in the format.

### 8.2 The adjacent optimization arenas that *do* exist

**MaxSAT Evaluation [C].** Alive and current — editions are published back to
2017 and **a 2026 edition is listed**. The 2024 evaluation ran **five tracks**:
two exact and two inexact/anytime (60 s and 300 s budgets) **[I, from the
solver-and-benchmark-descriptions booklet]**. Anytime tracks rank by average
anytime score. Recurring solvers: EvalMaxSAT, CASHWMaxSAT, UWrMaxSat, Pacose,
NuWLS.

**Certified MaxSAT [C].** "Certified MaxSAT Preprocessing" (IJCAR 2024) shows,
for the first time, how to use **pseudo-Boolean proof logging with VeriPB** to
produce correctness proofs for a wide range of MaxSAT preprocessing. "Practically
Feasible Proof Logging for Pseudo-Boolean Optimization" (CP 2025) presents a
**fully formally verified toolchain based on VeriPB and CakePB** for certified
pseudo-Boolean solving and optimization.

**Pseudo-Boolean Competition [C].** Live at CRIL Artois — **PB'24 and PB'25**
both have public execution traces; PB'25 traces show a **"VERIPB proof format"**
line, i.e. proof logging is integrated into the competition run. Format is
**OPB**. **VeriPB** itself (`veripb.org`, GitLab MIAOresearch) is a
general-purpose proof format supporting decision, enumeration, **and
optimization**, and the SAT Competition 2026 ships VeriPB/CakePB checker
documentation.

**This is the strongest adjacent precedent for optimization with certificates**,
and it is on the Boolean side — which is exactly where axeyum's CNF/AIG layer
already lives.

### 8.3 String and regex solver suites

**[C] ZaligVinder** (Kulczynski et al., "A generic test framework for string
solvers", JSEP 2023) is the aggregator: it exists because the field had no
standardized comparison. A benchmark-setup Python 3 script selects which sets and
which solvers to run under a common timeout. Its aggregated corpus, with counts
read from the project's own table:

| Set | Instances | Origin |
|---|---:|---|
| **Kaluza** | **47,284** | symbolic execution of JavaScript |
| **PyEx** | 8,414 | symbolic execution of Python |
| **LeetCode** | 2,666 | competitive-programming derived |
| **Sloth** | 1,065 | theory-driven, artificial |
| **StringFuzz** | 1,065 | fuzzer-generated |
| **Norn** | 1,027 | software verification |
| **Woorpje** | 809 | word equations |
| **Kausler** | 120 | |
| **JOACO** | 94 | vulnerability detection |
| **PISA** | 12 | sanitization |
| **IBM AppScan** | 8 | vulnerability detection |
| **Stranger** | 4 | vulnerability detection |

Distributed from `git.zs.informatik.uni-kiel.de/dbp/wordbenchmarks`.
**BanditFuzz** appears in the literature as another fuzz-generated family but is
not in ZaligVinder's table.

**[C] SMTQuery** (`smtquery.github.io`) is an information-extraction /
analysis system over SMT-LIB string benchmarks, with a 2026 journal paper. It is
the tool for asking *what is actually in* the string corpus rather than just
running it.

**[C] SMT-LIB theories:** **QF_S** (quantifier-free strings) is a strict subset
of **QF_SLIA** (strings + linear integer arithmetic). Both are SMT-COMP
divisions. **Z3-Noodler**, an automata-based fork of Z3 that replaces its string
theory with a stabilization-based solver, **won the string division of
SMT-COMP'24**. **OSTRICH2** (2025) supports QF_S and QF_SLIA for complex
constraints. Recent evaluations draw "2,000 formulas randomly selected from the
QF_S and QF_SLIA divisions of SMT-LIB 2024".

**[C] Proof-carrying strings — nearly empty.** **CertiStr** (arXiv:2112.06039)
is a *certified* string solver with an Isabelle/HOL correctness proof — the only
one found. cvc5 produces proofs for strings within its general proof
infrastructure **[I]**. There is no string-solver proof-checking competition.

**Read for axeyum:** the project already has an `axeyum-strings` crate and
QF_SLIA is one of its eleven measured divisions — but ZaligVinder's ~62,500
aggregated instances are far larger than the SMT-LIB string divisions alone, and
Kaluza at 47k is a single unclaimed target.

---

## What axeyum has not touched

Ranked by how *directly* the arena exercises something the project already
built — an AIG layer, a certificate-bearing CAS, a rewriting/e-graph layer, a
proof kernel, an SMT front door — not by prestige, and not by how easy it is.
Where an arena is dead or nonexistent, that is stated instead of ranked.

The reference point: the parity ledger measures eleven SMT-LIB divisions
(QF_SLIA, QF_BV, UF, QF_ABV, QF_LIA, QF_UF, QF_RDL, QF_UFLIA, QF_LRA, QF_IDL,
QF_NIA). Nothing below is in it.

**One arena is not even adjacent — it is inside SMT-COMP and simply unentered.**
**QF_NRA** (3,104 benchmarks in SMT-COMP 2025, won by Z3-alpha with 2,872 solved
and zero incorrect) and **NRA** (99 benchmarks, won by SMT-RAT at 96/99) are
divisions of the same competition the parity ledger already tracks. They are
where the CAS and the SMT solver meet — cylindrical algebraic decomposition,
coverings, Positivstellensatz — and axeyum measures neither. If the project
wants one place where its CAS and its solver would be graded together on
somebody else's corpus, this is the cheapest one, because the format is SMT-LIB
and the harness already exists.

### Tier 1 — the artefact already exists; only the harness is missing

**1. HWMCC bit-level track (AIGER 1.9 + mandatory AIG certificate).**
Input is AIGER 1.9 with reset functions; output must be a counterexample *and* a
safety certificate as a **witness circuit in AIGER**; checking it is
**five CNF files that must all be UNSAT**. Axeyum has `axeyum-aig` (deterministic
structural hashing, AIGER ASCII export), `axeyum-cnf` (Tseitin, DIMACS,
independent DRAT checker, proof-producing CDCL) and its own SAT core. The
certificate format is an AIG and the certificate check is a SAT problem — both
things the project already produces and consumes. HWMCC 2024's headline was that
mandatory certification *raised* participation from three entrants to nine and
the winner still beat the uncertified 2020 champion. This is the closest fit of
any arena in this document, and it is the one where the project's identity claim
would be tested on someone else's benchmarks rather than its own.
*Gap to close: model checking itself (IC3/PDR or BMC over the AIG), not the
plumbing.*

**2. SAT Competition main track (DRAT mandatory).**
Proof of UNSAT is mandatory and has been since 2014; the trend is toward
formally verified checkers (`cake_lpr`, GRAT) over the classical unverified
`drat-trim`. Axeyum has `solve_with_drat_proof` (1-UIP + two-watched-literal,
emits DRAT) and an *independent* `check_drat` (RUP+RAT). The pieces are there;
what is missing is the competitive CDCL and the willingness to be ranked on raw
speed against Kissat and CaDiCaL — which per the standing decision are yardsticks,
not candidates. Worth noting the SAT Competition 2025 benchmark pool includes a
**"Challenging Certificates from Model Checking"** family generated from
Certifaiger's checks — i.e. the two Tier-1 arenas feed each other.

### Tier 2 — the trust story is the same shape as axeyum's

**3. termCOMP certified categories and CoCo Certification/Reliability
(CPF + CeTA).**
This is the same architecture as axeyum's, already running for nearly twenty
years: an *untrusted* prover emits a CPF proof, a *trusted small checker* (CeTA,
**extracted by Isabelle's code generator from the IsaFoR formalization** — so the
checker is a byproduct of a machine-checked proof, not a hand-written verifier)
independently re-verifies it, and only re-verified answers score. AProVE's
certified config recovers ~92% of its own uncertified YES answers; the remaining
~8% is a *measured* trusted-base gap of exactly the kind axeyum reports.
CoCo goes one step further by scoring the checker and the prover in **separate
categories** — CERTIFICATION ranks certifiers by certificates validated,
RELIABILITY ranks provers by certified proofs generated. Axeyum has
`axeyum-rewrite` (manifest contracts, denotation-preserving canonicalizer) and
`axeyum-lean-kernel`. It has no CPF reader, no CPF writer, and no position in
either scoreboard.
*This is the arena whose design the project should study before designing its
own evidence gates — including the two-sided scoring, which is a direct answer to
"a checker that cannot fail is worse than no checker".*

**4. CHC-COMP (SMT-LIB `HORN`, nine tracks, new Model Track).**
The input format is a syntactic fragment of SMT-LIB 2.6 — the parser is largely
already written. What is missing is a fixed-point / invariant engine. The
competitors are literally SMT solvers plus an engine: Eldarica on Princess,
Golem on OpenSMT re-implementing IMPACT / Spacer / TPA / BMC / k-induction. The
BV tracks (BV-Lin and BV added 2025/2026) sit on top of exactly the bit-blasting
route axeyum already ships. And the 2026 edition just made model certification
operational, which is the project's home ground. cvc5 does not compete here at
all — the field is small.
*Also note that Eldarica and Golem appear in SV-COMP 2026's Table 9 as
components used by at least two software verifiers, so a CHC engine is
downstream-consumed, not a dead end.*

### Tier 3 — the kernel and the library have a scoreboard

**5. CASC / TPTP (TFA, FOF, UEQ, THF, SLH) and the TSTP proof world.**
CASC ranks by problems solved **with an acceptable, GDV-checkable solution
output** in every division but EPR — proof, not assurance. The 2025 GDV+LambdaPi
work (Vampire extended to emit Dedukti concrete syntax so a λΠ kernel can check
it) is the first-order world's version of axeyum's reconstruct-into-a-small-kernel
bet, and it is recent enough to still be moving. Entry is mechanical: package for
StarExec, email the organizer; `SystemOnTPTP` is the practice ground. cvc5
competes and has won nothing in 2023–2025, placing second in TFA/TFN — so the
SMT-shaped entrant's ceiling in this arena is known and modest.
*TFA (typed first-order with arithmetic) is the natural first division: 150–200
problems, 4 entrants, and it is arithmetic, which axeyum has.*

**6. miniF2F / PutnamBench / ProofNet / the Wiedijk 100.**
These test the kernel and the proof library, which is the north star. Two
different entry costs:
- The *ML leaderboards* (miniF2F 488, PutnamBench 672 problems / 1,724
  formalizations, ProofNet 371) are Lean-4-shaped; axeyum has
  `axeyum-lean-import`, so the statements are reachable, but the leaderboards are
  contested by very large models at pass@2048–8192 budgets. Also note the
  measured **~40% statement-error rate in miniF2F [I]** — entering a benchmark
  whose labels are 40% wrong is a trap the project's own evidence discipline
  should catch before anyone quotes a number from it.
- **Freek Wiedijk's "Formalizing 100 Theorems"** is the low-entry, high-legibility
  scoreboard: HOL Light 95, Isabelle 92, Lean 83, Rocq 80, Metamath 74, Mizar 71,
  ACL2 48, ProofPower 43, PVS 26, Imandra 20, Megalodon 12, Naproche 10, NuPRL 8.
  A system with a kernel and a growing axiom-free library has a visible, countable
  position on that list from its first entry, and the axis it competes on
  (axiom-freedom, and results the system established without anyone writing the
  proof) is one no other entrant reports.
- **LeanDojo's `novel_premises` split** (ReProver: 51.2% → **26.3%** pass@1) is
  the single most useful published number for anyone building retrieval into a
  proving loop, and directly relevant to the concept-DAG / fact-ledger design.
- **AIMO is not a proving arena** — it is answer-only, a single integer per
  problem, no proof graded. Do not treat its prize money as evidence about formal
  proving. The **IMO Grand Challenge** formal-to-formal variant is.

### Tier 4 — an uncontested axis, if the project wants one

**7. The CAS integration and ODE suites (106,812 and Kamke's 1,429).**
There is **no computer-algebra competition** — no jury, no medals, no rules page.
What exists is one open, independently re-run scoreboard of 106,812 integration
problems across nine CAS with a four-grade quality scale, and a companion ODE
suite still being recompiled as of August 2026. Mathematica solves 97.4%; Sympy
solves 42.2%. Nobody in that table emits a certificate. Axeyum's `axeyum-cas`
already refuses to treat a successful algebraic search as proof by itself and
checks route-specific exact obligations (canonical difference witnesses,
re-multiplication, substitution, differentiate-and-check) — which for
*integration specifically* is the natural check: differentiate the answer and
compare. **A per-problem "solved and the answer is kernel-checked" column on a
106,812-problem suite is a number nobody currently reports**, and it is the
per-statement-dominance claim the cost-model note describes, not a coverage-parity
claim.
*Caveat before anyone quotes a rate: the grading semantics are subtle — a CAS
that correctly returns an integral unevaluated scores **A**, one that times out on
the same integral scores **F**. Any axeyum column has to adopt the same
convention or it is not comparable.*

**8. SV-COMP (36,402 C tasks, witness format 2.1).**
Axeyum has `axeyum-verify` (a `#[axeyum::verify]` proc-macro that symbolically
checks Rust functions for panics and emits a runnable failing test) and
`axeyum-evm` (EVM symbolic bug hunting with replayable calldata witnesses). The
shape is right — bounded verification producing a replayable witness — but the
language is not: SV-COMP is C, Java and now SV-LIB. The relevant lesson is the
**witness ecosystem**: 229,118 witnesses validated by 16 independent validators
in one edition, with correctness-witness format 1.0 *deprecated* in favour of
2.1. That is what a mature evidence format looks like at scale.

### Tier 5 — real arenas, weaker fit

**9. String suites (ZaligVinder ≈ 62,500 instances; Kaluza alone 47,284).**
QF_SLIA is already one of the eleven measured divisions, and `axeyum-strings`
exists, but the SMT-LIB string divisions are a fraction of what the string
community actually benchmarks on. Z3-Noodler won SMT-COMP'24's string division;
OSTRICH2 is the 2025 entrant. **CertiStr** (Isabelle-verified) is the only
certified string solver found — a nearly empty field.

**10. MaxSAT Evaluation and the Pseudo-Boolean Competition (VeriPB / CakePB).**
Live, annual, and the **strongest existing precedent for optimization with
machine-checked certificates**: PB'25 traces carry a "VERIPB proof format" line,
and CP 2025 published a *fully formally verified* VeriPB+CakePB toolchain. This
sits on the Boolean layer axeyum already owns. It is ranked below the CAS suite
only because it tests the SAT core rather than anything distinctive.

**11. VNN-COMP (ONNX + VNN-LIB).** α,β-CROWN has won five consecutive years
(2021–2025) with GPU bound propagation and branch-and-bound. The useful finding
is negative: **this is an arena where the SMT/simplex formulation lost to a
specialized method**. Marabou keeps the SMT lineage and proof production, but not
the podium. Low priority.

**12. Model Checking Contest (Petri nets).** Live, annual, results at
`mcc.lip6.fr/2025`. Weakest fit of the live arenas.

### Arenas that do not exist (findings, not gaps in the research)

| Would-be arena | Status |
|---|---|
| **SyGuS-Comp** | **Dead since 2019.** `sygus.org` has lapsed to SEO spam; the GitHub mirror is frozen. Benchmarks (SyGuS-IF 2.1, `SyGuS-Org/benchmarks`) are live and unclaimed; no leaderboard exists. cvc5 keeps a SyGuS engine as a mode, not an entrant. |
| **Computer algebra competition** | **Does not exist.** No jury, no medals, no rules. Only Abbasi's independent scoreboard, vendor comparisons, and per-paper ad-hoc benchmarks. |
| **Optimization Modulo Theories** | **No standard and no competition.** SMT 2025 carried *A Proposal for an OMT Extension to SMT-LIB* whose own abstract says no official extension has been adopted and "OMT benchmarks lack standardization". SMT-COMP has no optimization track. |
| **Equality saturation** | **No competition, no shared benchmark suite.** egg ships an illustrative test suite; egglog has micro-benchmarks; Tensat/SPORES/Herbie are applications, not a corpus. Relevant because `axeyum-egraph` exists. |
| **Verified SMT rewrite rules** | **No competition, no shared corpus.** cvc5's RARE + IsaRare (TACAS 2024) is one solver's private rule set plus one academic verification effort. No comparable effort for Z3's simplifier was found. **CPF/CeTA is the pattern to copy here, not RARE.** |
| **String-solver proof checking** | **No arena.** CertiStr is the only certified string solver found. |

### The one asymmetry worth acting on

SAT's proof checkers (`cake_lpr`, GRAT) and rewriting's proof checker (CeTA) are
*themselves* machine-checked artifacts, extracted from formalizations. SMT's
fastest Alethe checker, **Carcara, is documented as "not currently formally
verified"** — and SMT-COMP does not mandate proofs at all (a Proof Exhibition
Track is listed in the 2023 slides; **whether it still runs in 2024/2025 was not
confirmed, and it was not confirmed to be mandatory anywhere — read the current
`rules.pdf` before acting on this**). So the position "SMT results carrying
evidence checked by a small kernel that is itself checked" is not a crowded one.
The two communities that already work that way — SAT/DRAT and rewriting/CPF —
are precisely the two arenas ranked first and third above.

### Recommended reading order, if only three things get read

1. **CoCo's CERTIFICATION vs RELIABILITY split** — two categories, one scoring
   the checker and one scoring the prover, on the same problems
   (`project-coco.uibk.ac.at/2025/results.php`). This is a working answer to
   "make the exit status depend on the finding".
2. **HWMCC 2024's certificate result** — mandatory certification tripled
   participation and the winner still beat the uncertified predecessor
   (`cca.informatik.uni-freiburg.de/papers/FroleyksYuPreinerBiereHeljanko-CAV25.pdf`).
3. **The Summer 2024 CAS integration report's grading table** — 106,812 problems,
   nine systems, and a four-grade quality scale that already distinguishes
   "solved" from "solved well"
   (`12000.org/my_notes/CAS_integration_tests/reports/summer_2024/index.pdf`).

---

## Sources

Every URL consulted, grouped by section. Where a page was read directly it
backs a **[C]** claim; search-snippet-only sources back **[I]** claims.

### CHC-COMP
- https://chc-comp.github.io/
- https://chc-comp.github.io/format.html
- https://chc-comp.github.io/2018/rules.html
- https://chc-comp.github.io/2019/
- https://chc-comp.github.io/2020/
- https://chc-comp.github.io/2021/
- https://chc-comp.github.io/2021/report.pdf
- https://chc-comp.github.io/2022/
- https://chc-comp.github.io/2022/CHC-COMP2022_presentation.pdf
- https://chc-comp.github.io/2023/
- https://chc-comp.github.io/CHC_COMP_2023_Competition_Report.pdf
- https://chc-comp.github.io/2024/
- https://chc-comp.github.io/2024/CHC-COMP%202024%20Report%20-%20HCSV.pdf
- https://chc-comp.github.io/2025/
- https://chc-comp.github.io/2025/CHC-COMP%202025%20Report%20-%20SPIN.pdf
- https://chc-comp.github.io/chc-comp-2026/
- https://chc-comp.github.io/chc-comp-2026/tables/index.html
- https://github.com/chc-comp
- https://github.com/orgs/chc-comp/repositories
- https://github.com/chc-comp/chc-comp26-benchmarks
- https://github.com/chc-comp/chc-comp-2026
- https://github.com/chc-comp/scripts/tree/master/format
- https://github.com/usi-verification-and-security/athena
- https://github.com/usi-verification-and-security/pychc
- https://github.com/usi-verification-and-security/golem
- https://github.com/uuverifiers/eldarica
- https://loat-developers.github.io/LoAT/
- https://github.com/hiroshi-unno/coar
- https://github.com/ftsrg/theta
- https://www.ultimate-pa.org/
- https://arxiv.org/abs/2404.14923 · https://arxiv.org/pdf/2404.14923 (CHC-COMP 2023 report)
- https://arxiv.org/abs/2211.12231 · https://arxiv.org/pdf/2211.12231 (CHC-COMP 2022 report)
- https://arxiv.org/pdf/2109.04635 (CHC-COMP-21)
- https://arxiv.org/pdf/2008.02939 (CHC-COMP-20)
- https://www.sci.unich.it/hcvs24/ · https://www.sci.unich.it/hcvs25/
- https://spin-web.github.io/SPIN2025/ · https://etaps.org/2025/
- https://conferences.i-cav.org/2026/ · https://www.floc26.org/
- https://verify.inf.usi.ch/sites/default/files/CHC_Model_Validation_with_Proof_Guarantees-iFM23.pdf

### SyGuS-Comp
- https://sygus.org/ · https://sygus.org/comp/2019/
- https://sygus-org.github.io/ · https://sygus-org.github.io/comp/ · https://sygus-org.github.io/comp/2019/
- https://sygus-org.github.io/language_1.0/ · https://sygus-org.github.io/language/
- https://sygus-org.github.io/artifacts/
- https://sygus-org.github.io/assets/pdf/SyGuS-IF_2.0.pdf
- https://sygus-org.github.io/assets/pdf/SyGuS-IF_2.1.pdf
- https://github.com/SyGuS-Org/benchmarks · https://github.com/SyGuS-Org/benchmarks/blob/master/README.md
- https://github.com/purdue-cap/DryadSynth
- https://arxiv.org/pdf/1907.10175 (CVC4SY at SyGuS-COMP 2019)
- https://arxiv.org/pdf/1711.11438 (SyGuS-Comp 2017 results and analysis)
- https://arxiv.org/abs/2507.19827 (Synthesis Benchmarks for Automated Reasoning, 2025)
- https://cvc5.github.io/

### CASC and TPTP
- https://tptp.org/CASC/
- https://tptp.org/CASC/29/ · /Design.html · /WWWFiles/DivisionSummary1.html
- https://tptp.org/CASC/J12/ · /Design.html · /WWWFiles/DivisionSummary1.html · /Proceedings.pdf
- https://tptp.org/CASC/30/ · /Design.html · /WWWFiles/DivisionSummary1.html
- https://tptp.org/CASC/J13/
- https://dl.acm.org/doi/10.3233/AIC-230325 (CASC-29 paper)
- https://journals.sagepub.com/doi/10.1177/30504554241305110 (CASC-J12 paper)
- https://www.researchgate.net/publication/379328850_The_CADE-29_Automated_Theorem_Proving_System_Competition_-_CASC-29
- https://en.wikipedia.org/wiki/CADE_ATP_System_Competition
- https://www.tptp.org/ · https://tptp.org/TPTP/
- https://tptp.org/UserDocs/ProblemLibraryManual/TPTPTR.shtml
- https://tptp.org/UserDocs/TPTPLanguage/TPTPLanguage.shtml
- https://tptp.org/UserDocs/QuickGuide/
- https://tptp.org/TSTP/ · https://tstp.tptp.org/
- https://arxiv.org/pdf/2507.03208 (Dependently Typed Higher-Order Form)
- https://groups.google.com/g/tptp-world/c/bllz1Zqj0qM (TPTP v9.0.0)
- https://groups.google.com/g/tptp-world/c/PNjDWZctAwE (TPTP v9.1.0)
- http://www.mail-archive.com/math.logic@mailman.rrz.uni-hamburg.de/msg01402.html (TPTP v9.3.0)
- https://journals.sagepub.com/doi/10.3233/AIC-2010-0466 (LTB / SUMO)
- https://link.springer.com/chapter/10.1007/978-3-031-63498-7_3 (Stepping Stones in the TPTP World)
- https://www.researchgate.net/publication/381849919_Stepping_Stones_in_the_TPTP_World
- https://journals.flvc.org/FLAIRS/article/view/138642 (Proof Verification with GDV and LambdaPi)
- https://dblp.org/rec/conf/flairs/SutcliffeBB25.html
- https://www.researchgate.net/publication/220160054_Semantic_Derivation_Verification_Techniques_and_Implementation (GDV)
- https://www.researchgate.net/publication/266984900_StarExec_A_Cross-Community_Infrastructure_for_Logic_Solving

### Theorem proving and formalization benchmarks
- https://arxiv.org/abs/2109.00110 (miniF2F)
- https://github.com/openai/miniF2F · https://github.com/facebookresearch/minif2f
- https://arxiv.org/html/2511.03108v1 (miniF2F-Lean Revisited)
- https://arxiv.org/html/2606.29493v1 (Faults in Our Formal Benchmarking)
- https://arxiv.org/pdf/2504.11354 (Kimina-Prover)
- https://arxiv.org/abs/2504.21801 (DeepSeek-Prover-V2)
- https://arxiv.org/pdf/2508.03613 · https://github.com/Goedel-LM/Goedel-Prover-V2 · https://blog.goedel-prover.com/
- https://arxiv.org/pdf/2606.12594 (Pythagoras-Prover)
- https://github.com/trishullab/PutnamBench · https://trishullab.github.io/PutnamBench/leaderboard.html
- https://arxiv.org/pdf/2407.11214 · https://openreview.net/forum?id=vqW1VRFeVP (PutnamBench)
- https://github.com/trishullab/PutnamBench/actions/runs/28620494934
- https://arxiv.org/pdf/2602.24273 (secondary leaderboard survey)
- https://arxiv.org/abs/2302.12433 · https://github.com/zhangir-azerbayev/ProofNet · https://huggingface.co/datasets/hoskinson-center/proofnet
- https://arxiv.org/pdf/2406.07222 · https://aclanthology.org/2025.emnlp-main.907.pdf (ProofNet#)
- https://arxiv.org/abs/2309.04295 · https://github.com/liuchengwucn/FIMO
- https://arxiv.org/pdf/2306.15626 · https://leandojo.org/leandojo.html (LeanDojo)
- https://arxiv.org/pdf/2408.03350 · https://cmu-l3.github.io/minictx/ (miniCTX)
- https://arxiv.org/pdf/2505.02735 (FormalMATH)
- https://arxiv.org/pdf/2505.03171 · https://github.com/MoonshotAI/CombiBench/
- https://imo-grand-challenge.github.io/
- https://leanprover-community.github.io/archive/stream/113488-general/topic/IMO.20Grand.20Challenge.html
- https://www.quantamagazine.org/at-the-international-mathematical-olympiad-artificial-intelligence-prepares-to-go-for-the-gold-20200921/
- https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/
- https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/
- https://www.axios.com/2025/07/21/openai-deepmind-math-olympiad-ai
- https://arxiv.org/pdf/2604.03789 (Aristotle / Harmonic)
- https://aimoprize.com/updates/ · https://aimoprize.com/updates/2025-11-19-third-progress-prize-launched
- https://www.kaggle.com/competitions/ai-mathematical-olympiad-progress-prize-3
- https://www.kaggle.com/competitions/ai-mathematical-olympiad-progress-prize-2/leaderboard
- https://www.prnewswire.com/news-releases/first-ai-mathematical-olympiad-progress-prize-won-by-team-numina-302202583.html
- https://mathstodon.xyz/@tao/112202296143187441
- https://isa-afp.org/
- https://leanprover-community.github.io/mathlib_stats.html · https://lean-lang.org/use-cases/mathlib/
- https://arxiv.org/pdf/2508.21593 (Growing Mathlib)
- https://leanprover-community.github.io/100.html · https://leanprover-community.github.io/100-missing.html
- https://us.metamath.org/mm_100.html · https://www.cs.ru.nl/~freek/100/ · https://madiot.fr/coq100/
- https://rocq-prover.org/releases/9.0.0 · https://rocq-prover.org/releases · https://en.wikipedia.org/wiki/Rocq
- https://github.com/Deducteam/coq-hol-light
- https://arxiv.org/abs/1903.02539 (GRUNGE)
- https://www21.in.tum.de/~nipkow/pubs/ijcar10.html (Judgement Day)
- https://matryoshka-project.github.io/pubs/seventeen.pdf
- https://arxiv.org/abs/1509.03534 (HolyHammer-related)
- https://link.springer.com/article/10.1007/s10817-018-9458-4 (CoqHammer)
- https://www.researchgate.net/publication/220532191_MPTP_02_Design_Implementation_and_Initial_Experiments
- https://www.researchgate.net/publication/257592519_MizAR_40_for_Mizar_40
- https://arxiv.org/abs/1703.00426 (HolStep)
- https://www.researchgate.net/publication/332300675_HOList_An_Environment_for_Machine_Learning_of_Higher-Order_Theorem_Proving_extended_version
- https://arxiv.org/abs/2006.09265 (IsarStep)
- https://arxiv.org/pdf/2606.09449 (Proxy-Judge autoformalization)

### Termination, confluence, rewriting
- https://termination-portal.org/wiki/Termination_Competition
- https://termination-portal.org/wiki/Termination_Competition_2024 · _2025 · _2026
- https://termination-portal.org/wiki/Tools:CeTA
- https://isafor-ceta.uibk.ac.at/
- http://cl-informatik.uibk.ac.at/users/thiemann/paper/UITP14CPF.pdf (CPF)
- https://termcomp.github.io/Y2024/ · https://termcomp.github.io/Y2025/
- https://github.com/TermCOMP · https://github.com/TermCOMP/TPDB · https://github.com/TermCOMP/starexec-master
- https://www.floc26.org/olympics · https://www.floc26.org/program
- https://project-coco.uibk.ac.at/2024/ · /2024/results.php
- https://project-coco.uibk.ac.at/2025/ · /2025/results.php
- https://project-coco.uibk.ac.at/2026/
- https://project-coco.uibk.ac.at/problems/ · /ARI/ · /results/ · /organization/
- https://ari-informatik.uibk.ac.at/
- https://jnagele.net/publications/Hirokawa-Nagele-Middeldorp-IJCAR18.pdf (COPS / CoCoWeb)
- https://link.springer.com/chapter/10.1007/978-3-032-32592-1_21 (ARI infrastructure)
- https://jonas.schoepf.me/crest/index.html · https://project-coco.uibk.ac.at/2024/participants/slides/crest.pdf
- https://arxiv.org/abs/2501.05240 · https://www.alphaxiv.org/abs/2501.05240 (crest)
- https://www.alphaxiv.org/abs/2309.12112 (confluence criteria for LCTRS)
- https://link.springer.com/chapter/10.1007/978-3-031-90643-5_7
- https://www.fwf.ac.at/en/research-radar/10.55776/I5943
- https://github.com/egraphs-good/egg · https://egraphs-good.github.io/
- https://github.com/egraphs-good/egglog · https://effect.systems/doc/pldi-2023-egglog/paper.pdf
- https://github.com/philzook58/awesome-egraphs · https://www.mwillsey.com/thesis/thesis.pdf
- https://arxiv.org/pdf/2112.14714 (Automated Code Optimization with E-Graphs)
- https://hanielbarbosa.com/papers/tacas2024.pdf (IsaRare)
- https://repositum.tuwien.at/bitstream/20.500.12708/81324/1/Noetzli-2022-Reconstructing%20Fine-Grained%20Proofs%20of%20Rewrites%20Using%20a%20Domai...-vor.pdf (RARE)
- https://cvc5.github.io/docs/cvc5-1.2.0/proofs/output_cpc.html · https://cvc5.github.io/docs/cvc5-1.2.1/api/cpp/enums/proofrule.html
- https://cvc5.github.io/blog/2024/03/15/isabelle-reconstruction.html
- https://github.com/cvc5/cvc5/releases/
- https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19 (Carcara)
- https://team.inria.fr/carma/software/
- https://cs.stanford.edu/~niemetz/publications/2023/BarbosaBCDKLNNOPRTZ-CACM23.pdf (cvc5, CACM)
- https://inria.hal.science/hal-04861898/document (SMT proofs in Lambdapi)
- https://cacm.acm.org/article/generating-and-exploiting-automated-reasoning-proof-certificates/
- https://schurr.io/pubs/talks/2024-grinnell.pdf

### Verification consumers: SV-COMP, VNN-COMP, HWMCC, MCC, SAT
- https://sv-comp.sosy-lab.org/2025/
- https://www.sosy-lab.org/research/pub/2025-TACAS.Improvements_in_Software_Verification_and_Witness_Validation_SV-COMP_2025.pdf
- https://www.sosy-lab.org/research/pub/2026-TACAS.Evaluating_Software_Verifiers_for_C_Java_and_SV-LIB_Report_on_SV-COMP_2026.pdf
- https://zenodo.org/records/15012085 · https://zenodo.org/records/19823904 (SV-COMP 2025 results)
- https://arxiv.org/abs/2512.19007 · https://arxiv.org/pdf/2512.19007 (VNN-COMP 2025)
- https://arxiv.org/abs/2412.19985 (VNN-COMP 2024)
- https://sites.google.com/view/vnn2025
- https://github.com/Verified-Intelligence/alpha-beta-CROWN · .../alpha-beta-CROWN_vnncomp2025 · .../alpha-beta-CROWN_vnncomp2024
- https://www.vnnlib.org
- https://openreview.net/pdf?id=UuYYldVLH3 (A Soundness Benchmark for Neural Network Verifiers)
- https://link.springer.com/content/pdf/10.1007/978-3-031-99991-8_14.pdf (NeuralSAT)
- https://github.com/ai-ar-research/luna
- https://hwmcc.github.io/ · https://hwmcc.github.io/2025/ · https://hwmcc.github.io/2024/hwmcc24slides.pdf
- https://ieeexplore.ieee.org/document/10918503/ (HWMCC 2024)
- https://github.com/gipsyh/rIC3-HWMCC24
- https://link.springer.com/chapter/10.1007/978-3-031-98668-0_14 (Introducing Certificates to HWMCC)
- https://cca.informatik.uni-freiburg.de/papers/FroleyksYuPreinerBiereHeljanko-CAV25.pdf
- https://froleyks.de/assets/pdf/Froleyks%20et%20al.%20-%202025%20-%20Introducing%20certificates%20to%20the%20hardware%20model%20checking%20competition.pdf
- https://github.com/Froleyks/certifaiger
- https://link.springer.com/chapter/10.1007/978-3-032-32589-1_17 · https://froleyks.de/assets/pdf/Froleyks%20et%20al.%20-%202026%20-%20Hardware%20Model%20Checking%20Certification%20with%20Certifaiger%20and%20Cerbtora.pdf
- https://cca.informatik.uni-freiburg.de/papers/FroleyksYuBiere-SAT-Competition-2025-benchmarks.pdf
- https://cse.engin.umich.edu/stories/hardware-model-checker-takes-gold-at-international-competition
- https://mcc.lip6.fr/results.php · https://mcc.lip6.fr/2025/results.php
- https://satcompetition.github.io/2025/ · /output.html · /downloads/checkers/cakelpr.pdf
- https://satcompetition.github.io/2026/downloads/checkers/veripb.pdf
- https://github.com/marijnheule/drat-trim · https://www.cs.cmu.edu/~mheule/publications/drat-trim.pdf
- https://cca.informatik.uni-freiburg.de/papers/PollittFleuryBiere-MBMV23.pdf
- https://jix.github.io/varisat/manual/0.2.0/formats/drat-proofs.html

### Computer algebra
- https://rulebasedintegration.org/ · /testProblems.html · /testResults.html
- https://www.12000.org/my_notes/CAS_integration_tests/index.htm
- https://www.12000.org/my_notes/CAS_integration_tests/reports/summer_2024/index.htm · .../index.pdf
- https://www.12000.org/my_notes/CAS_integration_tests/reports/summer_2021/index.htm
- https://www.12000.org/my_notes/CAS_integration_tests/reports/summer_2023/DATA_BASE/index.pdf
- https://www.12000.org/my_notes/solving_ODE/current_version/index.htm
- https://www.maplesoft.com/compare/mathematica_analysis/comparison_maple_mathmatica_des_kamke.pdf (Kamke's 1,429 ODEs)
- https://doc.sagemath.org/html/en/reference/calculus/sage/calculus/wester.html
- https://krum.rz.uni-mannheim.de/cabench/diractiv.html · https://krum.rz.uni-mannheim.de/cabench/cafgbench.html (Wester / CA Benchmark Initiative)
- https://www.researchgate.net/publication/2552349_A_Review_of_CAS_Mathematical_Capabilities
- https://symbolicdata.github.io/ · https://symbolicdata.github.io/Papers/karlsruhe-02.pdf · https://github.com/symbolicdata
- https://dl.acm.org/doi/pdf/10.1145/3313880.3313881 (20 Years SymbolicData — paywalled, not read)
- http://doc.sagemath.org/html/en/reference/databases/sage/databases/symbolic_data.html
- https://msolve.lip6.fr/ · https://msolve.lip6.fr/examples/index.html · https://github.com/algebraic-solving/msolve
- https://arxiv.org/abs/2104.03572 · https://dl.acm.org/doi/10.1145/3452143.3465545 · https://hal.sorbonne-universite.fr/hal-03191666v1/document (msolve, ISSAC'21)
- https://arxiv.org/pdf/2304.06935 (Groebner.jl)
- https://polsys.team.lip6.fr/software/software.html
- https://fredrikj.net/math/icms2020flint.pdf · https://flintlib.org/links.html
- https://d-nb.info/1036637972/34 · https://groups.google.com/g/flint-devel/c/h7krRDjydpA
- https://www.oscar-system.org/
- https://github.com/sympy/sympy_benchmarks · http://hera.physchem.kth.se/~sympy_asv · http://www.moorepants.info/misc/sympy-asv/
- https://arxiv.org/pdf/1710.00077 (Efficient Pattern Matching in Python / MatchPy, Rubi port)
- https://github.com/sympy/sympy/issues/12233 (Rubi integrator in SymPy)

### Certified algebra, SOS, verified numerics
- https://github.com/coq-community/coqeal · https://github.com/CohenCyril/CoqEAL · https://github.com/math-comp/math-comp
- https://rocq-prover.org/doc/V8.19.0/refman/addendum/nsatz.html
- https://rocq-prover.org/doc/V8.5pl3/refman/Reference-Manual025.html (psatz/nra/nia)
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Core.html
- https://radar.inria.fr/rapportsactivite/RA2023/toccata/TOCCATA-RA-2023.pdf (Flocq, CoqInterval)
- https://www.ens-lyon.fr/LIP/Pascaline/seminar.en.html (Gappa)
- https://www.cl.cam.ac.uk/~lp15/papers/Reports/Verif-Transcendental-Algs.pdf
- https://www.cl.cam.ac.uk/~jrh13/papers/sos.pdf (Harrison, SOS in HOL Light)
- https://www.researchgate.net/publication/220805687_A_Proof-Producing_Decision_Procedure_for_Real_Arithmetic
- https://hal.science/hal-01737737/document (Monniaux & Corbineau, Positivstellensatz witnesses)
- https://rocq-prover.org/p/coq-validsdp/1.0.3 · https://hal.science/hal-01510979v1/document (ValidSDP)
- http://www.mmrc.iss.ac.cn/~lzhi/Publications/KLYZ09.pdf (rationalizing SOS)
- https://isa-afp.org/entries/Groebner_Bases.html · https://isa-afp.org/entries/Polynomials.html
- https://arxiv.org/html/1805.00304v1 · https://www3.risc.jku.at/publications/download/risc_5815/Paper.pdf
- https://isa-afp.org/entries/Berlekamp_Zassenhaus.html · https://pmc.ncbi.nlm.nih.gov/articles/PMC7115093/ · https://zenodo.org/record/2539422
- https://isa-afp.org/entries/Algebraic_Numbers.html

### Quantifier elimination, CAD, NRA
- https://www.usna.edu/Users/cs/wcbrown/qepcad/B/QEPCAD.html · https://github.com/chriswestbrown/qepcad · https://github.com/PetterS/qepcad
- https://github.com/chriswestbrown/tarski
- https://dl.acm.org/doi/10.1145/261320.261324 (Redlog)
- https://smt-comp.github.io/2018/system-descriptions/veriT+raSAT+Reduce.pdf
- https://github.com/ths-rwth/smtrat/releases · https://gereon-kremer.de/static/2021-synasc-coverings.pdf
- https://gereon-kremer.de/static/2022-ijcar-nonlinear.pdf (cvc5 NRA)
- https://par.nsf.gov/servlets/purl/10388056 (cvc5)
- https://arxiv.org/html/2406.02122v4 (Improving NLSAT)
- https://www.sc-square.org/CSA/workshop10.html · https://ceur-ws.org/Vol-4116/ · https://www.dhbw-stuttgart.de/cade-30/
- https://inria.hal.science/hal-01377655v1/document (SC² project)

### OMT, MaxSAT, pseudo-Boolean
- https://optimathsat.disi.unitn.it/
- https://disi.unitn.it/rseba/papers/cav15_extended.pdf (OptiMathSAT, CAV'15)
- https://link.springer.com/article/10.1007/s10817-018-09508-6 (OptiMathSAT, JAR)
- https://arxiv.org/abs/1702.02385 · https://disi.unitn.it/rseba/papers/tacas17_maxsmt.pdf (OMT, MaxSMT, sorting networks)
- https://arxiv.org/pdf/1905.02838 (OMT over signed BV and FP)
- https://arxiv.org/html/1912.01476v2 (From MiniZinc to OMT, and Back)
- https://www.mdpi.com/2227-7390/14/8/1381 (hybrid OMT for FP)
- https://ceur-ws.org/Vol-4008/SMT_paper25.pdf (**A Proposal for an OMT Extension to SMT-LIB**)
- https://easychair.org/smart-program/SMT2025/2025-08-11.html (SMT 2025 programme)
- https://ceur-ws.org/Vol-4008/SMT_paper19.pdf (Instability Track proposal for SMT-COMP)
- https://maxsat-evaluations.github.io/ · /2024/index.html · /2026/ · /2023/rules.html
- https://helda.helsinki.fi/bitstreams/5066b1c4-72e6-465e-b5c4-c52a5d7d6837/download (MaxSAT Evaluation 2024 descriptions)
- https://link.springer.com/chapter/10.1007/978-3-031-63498-7_24 (Certified MaxSAT Preprocessing)
- https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2025.21 · https://aoertel.de/pdf/paper/PracticallyFeasibleProofLoggingPB.pdf
- https://veripb.org/ · https://gitlab.com/MIAOresearch/VeriPB · https://github.com/StephanGocht/VeriPB
- https://jakobnordstrom.se/docs/presentations/WHOOPS25_Tutorial_1_Intro.pdf
- https://www.cril.univ-artois.fr/PB24/ · https://www.cril.univ-artois.fr/PB25/

### Strings
- https://zaligvinder.github.io/
- https://onlinelibrary.wiley.com/doi/10.1002/smr.2400 (ZaligVinder, JSEP 2023)
- https://git.zs.informatik.uni-kiel.de/dbp/wordbenchmarks
- https://smtquery.github.io/ · https://www.sciencedirect.com/science/article/pii/S0167642326000924 (SMTQuery)
- https://sites.google.com/site/z3strsolver/benchmarks (Z3str3 benchmarks)
- https://link.springer.com/chapter/10.1007/978-3-319-96142-2_6 (StringFuzz)
- https://link.springer.com/chapter/10.1007/978-3-031-57246-3_2 (Z3-Noodler)
- https://arxiv.org/html/2508.19888v1 · https://dl.acm.org/doi/10.1145/3763165 (Regular Constraint Propagation)
- https://arxiv.org/pdf/2506.14363 (OSTRICH2)
- https://arxiv.org/pdf/1704.07935 (Z3str3)
- https://link.springer.com/chapter/10.1007/978-3-030-81688-9_14
- https://arxiv.org/pdf/2112.06039 (**CertiStr**, certified string solver)

### SMT-COMP itself (the baseline axeyum already measures)
- https://smt-comp.github.io/2023/ · /2023/results.html · /2023/rules.pdf · /2023/slides.html
- https://smt-comp.github.io/2023/results/results-model-validation
- https://smt-comp.github.io/2024/ · /2024/results/results-single-query/
- https://smt-comp.github.io/2025/ · /2025/results/
- https://smt-comp.github.io/2025/results/qf_nra-single-query/ · /2025/results/nra-single-query/
- https://smt-comp.github.io/2022/results/qf-nra-single-query · https://smt-comp.github.io/2023/results/qf-nra-single-query
- https://zenodo.org/records/16875980 (SMT-COMP 2025 raw execution data)
- https://zenodo.org/records/16887742 (SMT-COMP 2025 benchmarks)
- https://smt-lib.org/ · https://smt-lib.org/news.shtml · https://smt-lib.org/about.shtml
- https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r10.12.21.pdf
- https://schurr.io/pubs/smt2025-slides.pdf (A Catalog of SMT-LIB Benchmarks)
- https://smt-workshop.cs.uiowa.edu/2023/slides/smtcomp.pdf
- https://cs.stanford.edu/~niemetz/publications/2023/ScottNPNG-STTT23.pdf (MachSMT)
- https://zenodo.org/records/11581520/files/cvc5.pdf (cvc5 at SMT-COMP 2024)

---

## Known gaps in this research

These were looked for and not confirmed. Do not fill them in from memory.

| Gap | Notes |
|---|---|
| TSTP's current size | The library exists; no numeric size found. |
| Metamath `set.mm` current theorem count | Not found. |
| HOL Light core library size | Not found. |
| IsaFoR's current line count | Not found; one secondary "1500 lines" figure is historical and untrustworthy. |
| COPS/ARI current problem count | Not on the fetched pages; requires querying `ari-cops.uibk.ac.at`. |
| termCOMP 2026 category winners | Live run was 24–25 July 2026; results expected at `termcomp.github.io/Y2026/` **[I, by URL analogy]**. |
| SMT-COMP Proof Exhibition Track's current status | Listed in 2023 slides; **not confirmed to run in 2024/2025, not confirmed mandatory**. Read the current `rules.pdf`. |
| PutnamBench live leaderboard numbers | The 668/672 "Aleph Prover" figure is second-hand from a survey table. |
| CASC-J13 (2026) division list | The J13 page had no finalized `Design.html` at time of research. |
| SMT-COMP 2024 QF_NRA/NRA winners | Result index exists; the specific rows were not opened. |
| GRUNGE problem count | Description and authors confirmed; size not found. |
| 12000.org reports newer than Summer 2024 | `summer_2025` and `summer_2026` both 404; the index page is dated 31 Aug 2025, so a newer edition may exist under a different path. |
| OMT benchmark archive locations | The OptiMathSAT site surfaces no benchmark links; benchmark families are named only inside papers. |
| Exact TPTP v9.3.1 size/date, and the 25,775-problem / 55-domain figure | Consistent across snippets but not read off one authoritative table. |
