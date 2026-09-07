# The SMT-LIB / SMT-COMP Landscape, 2025–2026

A sourced catalog for the **axeyum** project. Every factual claim below carries a URL in
the [Sources](#sources) section. Claims are marked **[C]** when read directly off a primary
source (smt-lib.org, smt-comp.github.io, the SMT-COMP rules PDF, Zenodo API, cvc5 docs) and
**[I]** when inferred by me from those sources.

Data cutoff: fetched 2026-09-06. **The most recent completed competition is SMT-COMP 2026**
(results generated 2026-07-25); SMT-COMP 2025 results were generated 2025-08-11. The most
recent benchmark release is SMT-LIB 2025 (non-incremental, published 2025-08-04) — there is
no 2026 benchmark release on Zenodo, which is consistent with the 2026 rule that benchmarks
are drawn from the *preceding* year's library.

---

## 0. Executive summary — the six things that matter most

1. **There is no such thing as "the ~90 official SMT-LIB logics."** smt-lib.org publishes
   formal `(logic …)` declarations for exactly **25** logics. The 2025 benchmark release has
   **89 non-incremental + 41 incremental = 94 distinct logic directories**. **70 of those 94
   have no official declaration anywhere.** They are conventional names assembled from the
   letter-group naming scheme, defined only by the directory they live in. **[C]**
2. **SMT-COMP 2025 and 2026 each ran exactly five tracks**: Single Query, Incremental,
   Unsat Core, Model Validation, Parallel. **The Proof Exhibition track ran only in 2022 and
   2023 and was explicitly discontinued in 2024** — there is no competitive venue for SMT
   proof production today. **The Cloud track ran 2021–2024 and was dropped from 2025**
   ("due to the lack of suitable infrastructure"). **[C]**
3. **Divisions are not logics.** SMT-COMP scores over ~19–22 *divisions*, each a bundle of
   logics (e.g. `Equality+MachineArith` = 19 logics). axeyum's 11 target logics touch
   **9 of the 19** single-query divisions, and reach ~100 % coverage in only **4** of them
   (`qf_bitvec`, `qf_linearintarith`, `qf_linearrealarith`, `qf_nonlinearintarith`).
   Ten divisions are at 0 %. **[C/I]**
4. **The reference to beat is not one solver.** 2026 per-division winners were split across
   **Bitwuzla / Bitwuzla-MachBV, cvc5, Yices2, OpenSMT, SMTInterpol, Z3-alpha2, Z3-Noodler,
   SMT-RAT, QiuQi, Bitwuzllob, z3-parallel, OpenSMT-SMTS**. cvc5 won Best Overall in four of
   five tracks in both years — but **Largest Contribution 2026 went to Amaya**, a
   single-division automata solver, which is the far more realistic target shape. Note that
   **plain Z3 has not competed under its own name in either year.** **[C]**
5. **SMT-LIB is moving.** Version **2.7** is current (adds rank-1 polymorphism and a
   higher-order `HO-Core` map theory); **`QF_EIA` (integer exponentiation) was added
   2026-03-18**; and the standard states **Version 3 "will be based on higher-order
   logic."** **[C]**
6. **axeyum's 11 logics are 11.7 % of the logic directories but 45.5 % of the benchmarks.**
   83 logics and 245 676 non-incremental benchmarks are untouched; the whole quantified half
   of the library (48 logics) is untouched; four of five tracks are untouched. Full analysis
   in §7. **[C/I]**

---

## 1. The SMT-LIB logic landscape

### 1.1 The nine official theories

smt-lib.org lists exactly nine theory declarations. **[C]**

| Theory | Description |
|---|---|
| `Core` | Basic Boolean operators |
| `ArraysEx` | Functional arrays with extensionality |
| `FixedSizeBitVectors` | Bit vectors of arbitrary (fixed) size |
| `FloatingPoint` | IEEE-754 floating point numbers |
| `Ints` | Integer numbers (extended 2026-03-18 with an exponentiation operator) |
| `Reals` | Real numbers |
| `Reals_Ints` | Mixed real and integer numbers |
| `Strings` | Unicode character strings and regular expressions (added 2020-02-11) |
| `HO-Core` | Higher-order maps (new in 2.7; `@` is map application since 2025-04-09) |

Note what is **absent**: there is no `Datatypes` theory. SMT-LIB 2.6 added algebraic
datatypes to the **language** (`declare-datatype`, `declare-datatypes`, `match`), not as a
theory — which is why dozens of `…DT…` logic names exist with no theory behind them. **[C]**

### 1.2 The 25 logics with official `(logic …)` declarations

All are stamped `:smt-lib-version 2.7`, `:smt-lib-release "2024-07-21"` (except `QF_EIA`,
added 2026-03-18). **[C]**

`AUFLIA` `AUFLIRA` `AUFNIRA` `LIA` `LRA` `QF_ABV` `QF_AUFBV` `QF_AUFLIA` `QF_AX` `QF_BV`
`QF_EIA` `QF_IDL` `QF_LIA` `QF_LRA` `QF_NIA` `QF_NRA` `QF_RDL` `QF_UF` `QF_UFBV` `QF_UFIDL`
`QF_UFLIA` `QF_UFLRA` `QF_UFNRA` `UFLRA` `UFNIA`

Each declaration carries `:theories`, `:language` (the syntactic restriction), `:extensions`
(e.g. what counts as a "linear" term with concrete coefficients), and `:notes`. The
`:extensions` fields matter for a parser: `LRA` for instance explicitly permits `c`,
`(* c x)` and `(* x c)` with rational `c` written as `d`, `(- d)` or `(/ c n)`. **[C]**

### 1.3 The naming scheme

Documented on the logics page itself. **[C]**

| Token | Meaning |
|---|---|
| `QF_` prefix | restriction to quantifier-free formulas |
| `A` or `AX` | theory `ArraysEx` |
| `BV` | theory `FixedSizeBitVectors` |
| `FP` | theory `FloatingPoint` (listed as "forthcoming" on the page — stale text) |
| `UF` | free (uninterpreted) sort and function symbols |
| `IA` | theory `Ints` (Integer Arithmetic) |
| `RA` | theory `Reals` (Real Arithmetic) |
| `IRA` | theory `Reals_Ints` (mixed Integer/Real Arithmetic) |
| `IDL` | Integer Difference Logic |
| `RDL` | Rational Difference Logic |
| `L` before `IA`/`RA`/`IRA` | linear fragment |
| `N` before `IA`/`RA`/`IRA` | non-linear fragment |
| `DT` | algebraic datatypes (language feature, no theory) — **not documented on that page** |
| `S` | strings / regular expressions — **not documented on that page** |
| `E` before `IA` | Ints with exponentiation (`QF_EIA`, 2026) |

**[I]** `DT` and `S` follow the same convention but are not in the published convention
list; they are only attested by benchmark directory names.

### 1.4 The gap: official vs. benchmark-only

Computed by set difference between the 25 official declarations and the 94 logic directories
in the 2025 Zenodo release. **[C]**

- **94** distinct logic directories across both releases (89 non-incremental, 41 incremental,
  overlapping).
- **5 incremental-only** logics: `QF_AUFBVLIA` `QF_AUFBVNIA` `QF_BVLRA` `QF_UFBVLIA` `UFNRA`
- **1 official logic with no benchmarks yet**: `QF_EIA` (declared 2026-03, after the 2025 release)
- **70 logic names in the benchmark library with NO official declaration:**

```
ABV ABVFP ABVFPLRA ALIA ANIA AUFBV AUFBVDTLIA AUFBVDTNIA AUFBVDTNIRA AUFBVFP
AUFBVFPDTNIRA AUFDTLIA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA AUFNIA BV BVFP BVFPLRA FP
FPLRA NIA NRA QF_ABVFP QF_ABVFPLRA QF_ALIA QF_ANIA QF_AUFBVFP QF_AUFBVLIA QF_AUFBVNIA
QF_AUFNIA QF_BVFP QF_BVFPLRA QF_BVLRA QF_DT QF_FP QF_FPLRA QF_LIRA QF_NIRA QF_S
QF_SLIA QF_SNIA QF_UFBVDT QF_UFBVLIA QF_UFDT QF_UFDTLIA QF_UFDTLIRA QF_UFDTNIA
QF_UFFP QF_UFFPDTNIRA QF_UFNIA UF UFBV UFBVDT UFBVDTLIA UFBVDTNIA UFBVDTNIRA UFBVFP
UFBVFPDTNIRA UFBVLIA UFDT UFDTLIA UFDTLIRA UFDTNIA UFDTNIRA UFFPDTNIRA UFIDL UFLIA
UFNIRA UFNRA
```

**Practical consequence for axeyum [I]:** `set-logic QF_ABVFP` is legal SMT-LIB input that a
solver must accept, but there is no normative document saying what it means. The only
authority is the naming convention plus the benchmarks themselves. A front end should treat
the logic string as *advisory* (a hint for strategy selection) and derive actual capability
from the terms it parses.

### 1.5 Logics grouped by theory family

Grouping of the 94 benchmark logics. **[I]** (grouping is mine; the names are **[C]**)

| Family | Quantifier-free | Quantified |
|---|---|---|
| **Pure Boolean/UF** | `QF_UF`, `QF_UFDT` | `UF`, `UFDT` |
| **Arrays only** | `QF_AX` | — |
| **Bit-vectors** | `QF_BV` | `BV` |
| **BV + arrays / UF** | `QF_ABV`, `QF_AUFBV`, `QF_UFBV`, `QF_UFBVDT` | `ABV`, `AUFBV`, `UFBV`, `UFBVDT` |
| **Linear int arith** | `QF_LIA`, `QF_IDL`, `QF_ALIA`, `QF_AUFLIA`, `QF_UFLIA`, `QF_UFIDL`, `QF_UFDTLIA` | `LIA`, `ALIA`, `AUFLIA`, `UFLIA`, `UFIDL`, `UFDTLIA`, `AUFDTLIA` |
| **Linear real arith** | `QF_LRA`, `QF_RDL`, `QF_UFLRA` | `LRA`, `UFLRA` |
| **Mixed linear (IRA)** | `QF_LIRA`, `QF_UFDTLIRA` | `AUFLIRA`, `AUFDTLIRA`, `UFDTLIRA` |
| **Nonlinear int** | `QF_NIA`, `QF_ANIA`, `QF_AUFNIA`, `QF_UFNIA`, `QF_UFDTNIA` | `NIA`, `ANIA`, `AUFNIA`, `UFNIA`, `UFDTNIA`, `AUFBVDTNIA`, `UFBVDTNIA` |
| **Nonlinear real** | `QF_NRA`, `QF_UFNRA` | `NRA`, `UFNRA` |
| **Mixed nonlinear (NIRA)** | `QF_NIRA` | `AUFNIRA`, `UFNIRA`, `AUFDTNIRA`, `UFDTNIRA`, `AUFBVDTNIRA`, `UFBVDTNIRA`, `AUFBVFPDTNIRA`, `UFBVFPDTNIRA`, `AUFFPDTNIRA`, `UFFPDTNIRA` |
| **Floating point** | `QF_FP`, `QF_FPLRA`, `QF_BVFP`, `QF_BVFPLRA`, `QF_ABVFP`, `QF_ABVFPLRA`, `QF_AUFBVFP`, `QF_UFFP`, `QF_UFFPDTNIRA` | `FP`, `FPLRA`, `BVFP`, `BVFPLRA`, `ABVFP`, `ABVFPLRA`, `AUFBVFP` |
| **Datatypes** | `QF_DT`, `QF_UFDT`, `QF_UFBVDT`, `QF_UFDTLIA`, `QF_UFDTLIRA`, `QF_UFDTNIA` | `UFDT`, `UFBVDT`, and the whole `…DT…` family above |
| **Strings** | `QF_S`, `QF_SLIA`, `QF_SNIA` | — (no quantified string logic exists) |
| **BV + arithmetic** | `QF_BVLRA`, `QF_UFBVLIA`, `QF_AUFBVLIA`, `QF_AUFBVNIA` | `UFBVLIA`, `AUFBVDTLIA` |

**[C]** Notable: **there is no quantified strings logic in the library at all**, and there is
no `QF_UFNIRA`-style mixed QF logic beyond `QF_NIRA` (3 benchmarks) and `QF_LIRA` (7).


---

## 2. SMT-COMP tracks, rules, limits, scoring

### 2.1 Tracks by year

| Track | 2023 | 2024 | 2025 | 2026 |
|---|---|---|---|---|
| Single Query | ✓ | ✓ | ✓ | ✓ |
| Incremental | ✓ | ✓ | ✓ | ✓ |
| Unsat Core | ✓ | ✓ | ✓ | ✓ |
| Model Validation | ✓ | ✓ | ✓ | ✓ |
| Parallel | ✓ (AWS) | ✓ (AWS) | ✓ (on-prem) | ✓ (on-prem, 20 min) |
| Cloud | ✓ (AWS) | ✓ (AWS) | ✗ **not held** | ✗ not a scored track (AWS side event only) |
| Proof Exhibition | ✓ (non-competitive) | ✗ **discontinued** | ✗ | ✗ |

**[C]** For 2025 the rules say verbatim: *"Due to the lack of suitable infrastructure, Cloud
track is not taking place for SMT-COMP 2025. Parallel track is going to be executed on the
same BenchExec-based infrastructure as the other tracks, only on machines with a higher
numbers of CPU cores."* The 2025 results index lists exactly five tracks, and no proof track.
The 2025 participants table still carries a (now vestigial) "Cloud Track" column.

### 2.2 SMT-COMP 2025 execution environment **[C]**

| Item | Value |
|---|---|
| Runner | **BenchExec** on the SoSy-Lab cluster (168 `apollon` nodes) |
| Parallel track machine | one 256-processor, 2 TB RAM machine |
| Cores per solver/benchmark | 4 |
| Memory limit | ~30 GB per solver/benchmark pair (results pages report `30720` MB) |
| Filesystem | read-only with a writeable RAM-disk overlay; **RAM disk counts against the memory limit** |
| Network | forbidden |
| Reference image | `registry.gitlab.com/sosy-lab/benchmarking/competition-scripts/user:latest` |
| Random seed | sum of entrants' magic numbers + 100× NYSE Composite opening value (2025 scrambler seed: **757067271**) |

### 2.3 Time limits per track (2025) **[C]**

| Track | Wall-clock limit | Notes |
|---|---|---|
| Single Query | **20 min (1200 s)** | |
| Incremental | **20 min** | driven by the SMT-COMP trace executor over stdin |
| Unsat Core | **20 min** | *and* 20 min for validation; 2025 change: validation budget raised to the generation time |
| Model Validation | **20 min** | model-checking budget "yet to be determined, anticipated ~15 min" |
| Parallel | **2 min (120 s)** | deliberately short; 400 hand-selected long-running instances |

### 2.4 Benchmark scoring **[C]**

The **parallel benchmark score** is a 6-tuple `⟨e, n, aw, w, ac, c⟩`:

- `e ∈ {0,1}` — erroneous results
- `n` — correct results (for Unsat Core: the **reduction**, `N` minus core size)
- `aw`, `w` — actual and scored wall-clock seconds (`w = 0` unless correctly solved in time)
- `ac`, `c` — actual and scored CPU seconds across all `m` cores (limit `mT`)

Per-track `e`/`n`:

| Track | `e=0, n=0` | `e=1, n=0` | success |
|---|---|---|---|
| Single Query / Parallel | abort without response, or `unknown` | result disagrees with expected status | `n=1` if `sat`/`unsat` agrees **or** benchmark status is `unknown` |
| Incremental | — | any incorrect `check-sat` answer | `n` = number of correct `check-sat` answers before timeout |
| Unsat Core | abort, `unknown`, or malformed core | core is not actually unsatisfiable | `n = N − (size of core)` |
| Model Validation | validator says `UNKNOWN` | validator says `INVALID` | `n=1` on `VALID` |

**Critical detail [C]:** *"a (correct or incorrect) response is taken into consideration even
when the solver process terminates abnormally, or does not terminate within the time limit.
Solvers should take care not to accidentally produce output that contains `sat` or `unsat`."*
A stray `sat` in a debug log is a scored wrong answer.

**Sequential score [C]:** derived from the parallel score by imposing a *virtual CPU-time
limit equal to the wall-clock limit T*. Formally `⟨eˢ,nˢ,cˢ⟩` where all three are 0 if `c > T`,
else equal to `⟨e,n,c⟩`. This is how a single-threaded solver is compared fairly against a
4-core one. **Not computed for the Incremental or Parallel tracks.**

**Division score ordering [C]:** parallel division scores are compared lexicographically —
*fewer errors* ≻ *more correct* ≻ *less wall-clock* ≻ *less CPU*. Sequential uses
*fewer errors* ≻ *more correct* ≻ *less CPU*.

**Extra single-query scores [C]:** the **24-seconds score** is just the parallel division
score recomputed with `T = 24 s`; the **sat score** and **unsat score** are the parallel
division score restricted to satisfiable / unsatisfiable instances.

**Soundness handling [C]:** a solver is *sound in a division* if `e = 0` on every benchmark
with known status. Before scoring, benchmarks with `unknown` status where two solvers that
are sound-on-known-status **disagree** are **removed** from the results.

**Sequential vs parallel — the standing position [C]:** the rules state explicitly *"We will
not make any comparisons between parallel and sequential performances, as these are intended
to measure fundamentally different performance characteristics."* The sequential score exists
precisely because *"the parallel score as defined above favors parallel solvers."* Both are
reported side by side for every division, and the 2025 results show them diverging in real
cases (e.g. `qf_bitvec`: Z3-alpha ranks 6th sequentially with 8970 but 5th in parallel with
9370, because its CPU time score of 544 609 s exceeds the virtual limit on many instances).

### 2.5 Competition-wide rankings (2025 rules; identical in 2026) **[C]**

| Ranking | Definition |
|---|---|
| **Best Overall** | Reintroduced in 2025 (used 2014–2018, dropped 2019–2024). Normalized score `nnᴰ = (nᴰ/Nᴰ)²` if `eᴰ=0`, else `−2`. Overall = `Σ nnᴰ · log₁₀ Nᴰ` over entered competitive divisions. The square rewards near-complete divisions; the `−2` penalty equals two fully-solved divisions; the `log₁₀` compensates for division size. |
| **Biggest Lead** | For each division, `(n₁+1)/(n₂+1)`; winner is the division winner with the largest ratio. |
| **Largest Contribution** | Contribution to the virtual best solver: `1 − vbsₙ(D, S−s)/vbsₙ(D, S)`, normalized by division share. Unsound solvers excluded; divisions with ≤2 sound competitive solvers excluded. |

Also recognized: **new entrants** that beat an existing solver, and **benchmark contributors**.

### 2.6 Benchmark selection (2025) **[C]**

1. Organizers may remove inappropriate benchmarks or cap over-represented families.
2. **Single Query: remove everything solved by all solvers in < 1 s in 2018–2024.**
   Unsat Core: remove single-`assert` benchmarks.
3. Unsat Core keeps only `unsat`; Model Validation keeps only `sat` (status plus prior
   single-query evidence decides `unknown` cases).
4. **Per-logic cap:** with `n` benchmarks in a logic, select `min(n, max(300, 50n/100))` —
   i.e. all if `n ≤ 300`; 300 if `300 < n ≤ 600`; 50% if `n > 600`. One benchmark from each
   *new* family is guaranteed inclusion first.
5. Benchmarks are **scrambled** before the run (github.com/SMT-COMP/scrambler); relying on
   syntactic fingerprints is defined as cheating.

**Families [C]:** within a logic, benchmarks are partitioned into *families* by the
bottom-level directory imposed by each submitter. Families drive new-benchmark guarantees
and the Largest Contribution normalization — they are **not** the same thing as divisions.

### 2.7 Divisions and how logics group into them

**[C]** *"Within each track there are multiple divisions, and each division selects benchmarks
from a specific group of SMT-LIB logics."* A division is *competitive* only if at least two
solvers from two different teams entered it; non-competitive divisions are not run.

The 2025 division set (from the results index):

| Quantifier-free divisions | Quantified divisions |
|---|---|
| `QF_Bitvec`, `QF_Equality`, `QF_Equality+Bitvec`, `QF_Equality+Bitvec+Arith` (incr. only), `QF_Equality+LinearArith`, `QF_Equality+NonLinearArith`, `QF_LinearIntArith`, `QF_LinearRealArith`, `QF_NonLinearIntArith`, `QF_NonLinearRealArith`, `QF_Strings`, `QF_Datatypes`, `QF_FPArith`, plus model-validation-only `QF_ADT+BitVec` and `QF_ADT+LinArith` | `Arith`, `Bitvec`, `Equality`, `Equality+LinearArith`, `Equality+MachineArith`, `Equality+NonLinearArith`, `FPArith` |

The exact logic membership of every division is in the tables of §3.


### 2.8 Year over year: hardware, limits, and rule changes

#### Execution platform **[C]**

| Year | Platform | Machine | Memory cap |
|---|---|---|---|
| 2023 | **StarExec** (Univ. of Iowa) | Xeon E5-2609 @ 2.40 GHz, 2 sockets × 4 cores, 129 GB; two job-pairs per machine | **~60 GB** (61 440 MB) |
| 2024 | **BenchExec** — SoSy-Lab *VerifierCloud*, 168 `apollon` nodes | Xeon E3-1230 v5 @ 3.40 GHz, 33 GB RAM, 4 cores | rules say **30 GB**; results pages print `20480` |
| 2025 | **BenchExec** — SoSy-Lab, 168 `apollon` nodes; Parallel on a 256-proc / 2 TB machine | same nodes | **~30 GB** (`30720`) |
| 2026 | **BenchExec** — SoSy-Lab *BenchCloud*, 168 `apollon` nodes; Parallel on 256 vcores / 2 TB | same nodes | **~30 GB** (`30720`) |

The 2024 move off StarExec is the reason memory dropped: *"The reasons are hardware limits of
the new execution platform."* Note the **2024 discrepancy**: the rules say 30 GB but every
2024 results page prints `Memory Limit: 20480 GB` (a units bug; 20 480 MB = 20 GB).
**[I]** The enforced 2024 limit was most likely 20 GB.

#### Time limits **[C]**

| Track | 2023 | 2024 | 2025 | 2026 |
|---|---|---|---|---|
| Single Query | 1200 s | 1200 s | 1200 s | 1200 s |
| Incremental | 1200 s | 1200 s | 1200 s | 1200 s |
| Unsat Core | 1200 s + ~5 min check | 1200 s + ~5 min check | 1200 s + **generation-time** check | 1200 s + **1200 s** check |
| Model Validation | 1200 s + ~15 min check | 1200 s + ~15 min check | same | same |
| Parallel | 1200 s (AWS `m4.16xlarge`, 64 vCPU, 256 GB) | **120 s** per rules | **120 s** per rules | **1200 s**, 256 vcores / 2 TB |
| Cloud | 1200 s (100 × AWS `m4.4xlarge`) | **120 s** per rules | — | — (side event: 200 s recommended) |

**The Single Query wall-clock limit has been 1200 s (20 min) throughout.** **[C]**
The CPU-time budget is defined structurally as `mT` with `m = 4` cores — the rules never
print "4800 s". **[I]**

**[I] A caution on the 2024 parallel numbers:** the 2024 rules say 120 s, but the 2024
parallel/cloud web page still says 20 minutes, the results pages report `Time Limit: 1200
seconds`, and the published wall-time sums (e.g. SMTS with 86 solved and 22 751 s of wall
time in `qf_linearintarith-parallel`) are arithmetically impossible under a 120 s cap. Treat
the 2-minute figure as stated intent that the published results do not support.

#### Division structure over time **[C]**

- **19 single-query divisions in every year 2023–2026**, with the same names.
- 2023 → 2024: `UFNIRA` added to `Equality+NonLinearArith`.
- 2024 → 2026: `Equality+MachineArith` grew by five logics — `AUFBVFPDTNIRA`, `UFBVDTLIA`,
  `UFBVDTNIA`, `UFBVDTNIRA`, `UFBVFPDTNIRA` — reaching 19 logics.
- `QF_Datatypes` was **split out of `QF_Equality` in 2022**, because *"datatypes were too
  dissimilar from QF_UF and QF_AX to be organized in the same division."*
- `QF_Equality+Bitvec+Arith` (`QF_AUFBVLIA`, `QF_AUFBVNIA`, `QF_UFBVLIA`, `QF_BVLRA`) exists
  **only in the Incremental track**.
- Model Validation dropped two 2023 experimental divisions (`QF_Array+Bitvec+LinArith`,
  `QF_Datatypes+BitVec+LinArith`) for 2024.
- **2026 makes individual *logics* competitive units**, not just divisions: *"A division **or
  a logic** is competitive … We will not run non-competitive divisions and logics."*

#### The rule changes that matter **[C]**

| Year | Change |
|---|---|
| **2023** | Wall/CPU time scores set to **zero unless the benchmark was correctly solved** — because previously *"timeouts were scored worse than aborts and could overshadow the times of correctly solved problems."* Model Validation gains experimental array / non-linear / datatype divisions. Proof track continues with a reduced cap. |
| **2024** | **StarExec → BenchExec.** Submission moves to a **GitHub PR + Zenodo upload with a Dockerfile**. Memory 60 → 30 GB. Parallel/Cloud nominally → 2 min. **Proof Exhibition Track discontinued.** Tooling consolidated into a single `smtcomp` tool. |
| **2025** | Derived tools **must also submit their base solver**. Unsat cores: **no point for a core no solver can verify**; validation budget raised to generation time. **Best Overall ranking reintroduced** (last used 2018). **Cloud track dropped**; Parallel moved off AWS onto BenchExec. |
| **2026** | Derived solvers **must publish source code**, and **can only win if they beat their base by ≥10 % PAR-2** — which is why **PAR-2 scoring was added** and why results carry the `ne` marker. Benchmarks drawn from the **preceding year's** SMT-LIB release. **Fourth benchmark-cap tier** added. Parallel restored to 20 min. Portfolio solvers re-allowed in Parallel only. Communication moved to Google Groups + the `#smtcomp` **SMT-LIB Zulip** channel. |

**[I]** The 2026 derived-solver rule is the most consequential change for a newcomer: the
competition has moved to actively discount thin wrappers around Z3/cvc5/Bitwuzla. A
from-scratch solver like axeyum is structurally favoured by it.

#### Abstentions **[C]**

Identical wording in every year: *"A solver enters a division in a track if it supports at
least one logic in this division. A solver not supporting all logics in a division **will not
be run** on the benchmarks from the unsupported logics and **will be scored as if it returned
the result `unknown` within zero time**."*

**[I] This is the single most important rule for axeyum's competition strategy.** Partial
logic support inside a division is *permitted* — you simply forfeit the benchmarks you do not
support (they show in the `Abstained` column). So axeyum can enter e.g. `QF_Equality+Bitvec`
supporting only `QF_ABV` and `QF_UFBV`, scoring zero on `QF_AUFBV`, without any penalty
beyond the lost benchmarks. There is no all-or-nothing barrier to entry.

---

## 3. SMT-COMP results — who to beat, per division

> **Read this first.** The most recent completed edition is **SMT-COMP 2026** (21st edition,
> results generated **2026-07-25**, presented at the SMT Workshop in Lisbon, 24–25 July 2026,
> affiliated with IJCAR-26 / FLoC'26). SMT-COMP 2025 is included below because 2026 shrank
> every division sharply (see §3.4), so 2025 is the better picture of *breadth* while 2026 is
> the current *ranking*. **[C]**

Scores are the **sequential correct score**. Solvers flagged `n` (non-competing) or `ne`
(**new in 2026**: derived solver not eligible to win because it does not improve its base
solver's PAR-2 score by ≥10 %) are excluded from the top-3 columns; the "winner" columns are
the site's own awarded winners. **[C]**

### 3.1 Single Query Track — SMT-COMP 2026 (current reference)

| Division | Logics | Benchmarks | 1st (sequential) | 2nd | 3rd | SAT winner | UNSAT winner | 24s winner |
|---|---|---:|---|---|---|---|---|---|
| **qf_bitvec** | QF_BV | 2540 | Bitwuzla-MachBV (2495) | Bitwuzla (2475) | bv_decide-nokernel (2404) | Bitwuzla-MachBV | Bitwuzla-MachBV | Bitwuzla |
| **qf_equality_bitvec** | QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT | 2617 | Bitwuzla (2479) | Yices2 (2423) | cvc5 (2371) | Bitwuzla | Bitwuzla | Bitwuzla |
| **qf_equality** | QF_AX, QF_UF | 1404 | Yices2 (1404) | OpenSMT (1404) | cvc5 (1404) | Yices2 | Yices2 | Yices2 |
| **qf_linearintarith** | QF_IDL, QF_LIA, QF_LIRA | 1965 | QiuQi (1807) | OpenSMT (1710) | Yices2 (1701) | QiuQi | QiuQi | Yices2 |
| **qf_linearrealarith** | QF_LRA, QF_RDL | 766 | Yices2 (700) | OpenSMT (700) | cvc5 (691) | OpenSMT | Yices2 | Yices2 |
| **qf_nonlinearintarith** | QF_NIA, QF_NIRA | 2857 | Z3-alpha2 (2408) | Z3-Z3++ (2408) | Z3-GEX (2327) | Z3-Z3++ | Z3-alpha2 | Z3-alpha2 |
| **qf_nonlinearrealarith** | QF_NRA | 1020 | Z3-alpha2 (946) | cvc5 (913) | Yices2 (909) | Z3-GEX | Z3-GEX | Yices2 |
| **qf_equality_lineararith** | QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 1874 | SMTInterpol (1746) | cvc5 (1735) | OpenSMT (1728) | SMTInterpol | OpenSMT | SMTInterpol |
| **qf_equality_nonlineararith** | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 631 | Yices2 (473) | cvc5 (420) | SMTInterpol (292) | Yices2 | Z3-alpha2 | Yices2 |
| **qf_strings** | QF_S, QF_SLIA, QF_SNIA | 7633 | Z3-Noodler (7225) | OSTRICH (6951) | cvc5 (5299) | Z3-Noodler | Z3-Noodler | Z3-Noodler |
| **qf_datatypes** | QF_DT, QF_UFDT | 544 | cvc5-cvc5-xyz (398) | Z3-Z3++ (336) | cvc5 (334) | cvc5 | Z3-Z3++ | SMTInterpol |
| **qf_fparith** | QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFPDTNIRA | 1476 | Bitwuzla (1440) | cvc5 (1407) | colibri2 (1095) | Bitwuzla | Bitwuzla | Bitwuzla |
| **bitvec** | BV | 608 | Bitwuzla (557) | cvc5 (552) | YicesQS (526) | Bitwuzla | cvc5 | Bitwuzla |
| **equality** | UF, UFDT | 1684 | cvc5 (653) | Yices2 (116) | SMTInterpol (90) | cvc5 | cvc5 | cvc5 |
| **equality_lineararith** | ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA | 6438 | cvc5 (4968) | SMTInterpol (3440) | UltimateEliminator+MathSAT (106) | cvc5 | cvc5 | cvc5 |
| **equality_machinearith** | ABV, ABVFP, ABVFPLRA, AUFBV, AUFBVDTLIA, AUFBVDTNIA, AUFBVDTNIRA, AUFBVFP, AUFBVFPDTNIRA, AUFFPDTNIRA, UFBV, UFBVDT, UFBVDTLIA, UFBVDTNIA, UFBVDTNIRA, UFBVFP, UFBVFPDTNIRA, UFBVLIA, UFFPDTNIRA | 5179 | cvc5 (3158) | SMTInterpol (1449) | Bitwuzla (1213) | Bitwuzla | cvc5 | cvc5 |
| **equality_nonlineararith** | ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA | 4152 | cvc5 (2778) | SMTInterpol (1255) | UltimateEliminator+MathSAT (189) | cvc5 | cvc5 | cvc5 |
| **arith** | LIA, LRA, NIA, NRA | 1255 | Z3-alpha2 (1111) | Z3-GEX (1067) | YicesQS (1015) | Z3-alpha2 | Z3-GEX | Z3-GEX |
| **fparith** | BVFP, BVFPLRA, FP, FPLRA | 1178 | Bitwuzla (1142) | cvc5 (1101) | colibri2 (269) | Bitwuzla | Bitwuzla | Bitwuzla |
### 3.2 Single Query Track — SMT-COMP 2025 (larger benchmark sets)

| Division | Logics | Benchmarks | 1st (sequential) | 2nd | 3rd | SAT winner | UNSAT winner | 24s winner |
|---|---|---:|---|---|---|---|---|---|
| **qf_bitvec** | QF_BV | 10703 | Bitwuzla-MachBV (10523) | Bitwuzla (10498) | Yices2 (10491) | Bitwuzla | Bitwuzla-MachBV | Bitwuzla-MachBV |
| **qf_equality_bitvec** | QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT | 8489 | Bitwuzla (8279) | Yices2 (8230) | Z3-Owl (8056) | Bitwuzla | Bitwuzla | Bitwuzla |
| **qf_equality** | QF_AX, QF_UF | 3821 | Yices2 (3821) | OpenSMT (3820) | cvc5 (3819) | Yices2 | Yices2 | Yices2 |
| **qf_linearintarith** | QF_IDL, QF_LIA, QF_LIRA | 6040 | OpenSMT (5471) | Yices2 (5378) | cvc5 (5370) | Z3-alpha | OpenSMT | Yices2 |
| **qf_linearrealarith** | QF_LRA, QF_RDL | 842 | Yices2 (776) | OpenSMT (775) | cvc5 (758) | OpenSMT | Yices2 | Yices2 |
| **qf_nonlinearintarith** | QF_NIA, QF_NIRA | 12280 | Z3-alpha (9965) | z3siri (9693) | Yices2 (9071) | Z3-alpha | z3siri | Z3-alpha |
| **qf_nonlinearrealarith** | QF_NRA | 3104 | Z3-alpha (2856) | z3siri (2803) | cvc5 (2766) | Z3-alpha | Z3-alpha | Z3-alpha |
| **qf_equality_lineararith** | QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 1936 | SMTInterpol (1798) | cvc5 (1795) | OpenSMT (1778) | SMTInterpol | OpenSMT | SMTInterpol |
| **qf_equality_nonlineararith** | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 631 | Yices2 (450) | cvc5 (381) | SMTInterpol (306) | Yices2 | cvc5 | Yices2 |
| **qf_strings** | QF_S, QF_SLIA, QF_SNIA | 34228 | Z3-Noodler-Mocha (34110) | Z3-Noodler (33635) | OSTRICH (32766) | Z3-Noodler-Mocha | Z3-Noodler-Mocha | Z3-Noodler-Mocha |
| **qf_datatypes** | QF_DT, QF_UFDT | 552 | cvc5 (332) | SMTInterpol (194) | — | cvc5 | cvc5 | SMTInterpol |
| **qf_fparith** | QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFPDTNIRA | 1600 | Bitwuzla (1561) | cvc5 (1531) | colibri2 (1058) | Bitwuzla | Bitwuzla | Bitwuzla |
| **bitvec** | BV | 1040 | cvc5 (952) | YicesQS (886) | Bitwuzla (839) | Bitwuzla | cvc5 | YicesQS |
| **equality** | UF, UFDT | 4426 | cvc5 (1714) | iProver v3.9.3 (1058) | Yices2 (323) | cvc5 | cvc5 | cvc5 |
| **equality_lineararith** | ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA | 16936 | cvc5 (13158) | iProver v3.9.3 (10081) | UltimateEliminator+MathSAT (253) | cvc5 | cvc5 | cvc5 |
| **equality_machinearith** | ABV, ABVFP, ABVFPLRA, AUFBV, AUFBVDTLIA, AUFBVDTNIA, AUFBVDTNIRA, AUFBVFP, AUFBVFPDTNIRA, AUFFPDTNIRA, UFBV, UFBVDT, UFBVDTLIA, UFBVDTNIA, UFBVDTNIRA, UFBVFP, UFBVFPDTNIRA, UFBVLIA, UFFPDTNIRA | 8931 | cvc5 (5168) | SMTInterpol (2695) | Bitwuzla (937) | cvc5 | cvc5 | cvc5 |
| **equality_nonlineararith** | ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA | 10232 | cvc5 (6722) | iProver v3.9.3 (3992) | SMTInterpol (2924) | cvc5 | cvc5 | cvc5 |
| **arith** | LIA, LRA, NIA, NRA | 1666 | Z3-alpha (1474) | YicesQS (1382) | cvc5 (1382) | Z3-alpha | Z3-alpha | Z3-alpha |
| **fparith** | BVFP, BVFPLRA, FP, FPLRA | 1849 | Bitwuzla (1751) | cvc5 (1697) | UltimateEliminator+MathSAT (272) | Bitwuzla | Bitwuzla | Bitwuzla |
### 3.3 The other four tracks — SMT-COMP 2026

#### Incremental Track — SMT-COMP 2026

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| arith | LIA, LRA | 11 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| bitvec | BV | 18 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality_lineararith | ALIA, UFLRA | 611 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality_machinearith | ABVFPLRA | 4 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| equality_nonlineararith | ANIA, AUFNIRA, UFDTNIA, UFNIA, UFNRA | 1117 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality | UF | 806 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| fparith | BVFP, BVFPLRA | 10 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| qf_bitvec | QF_BV | 661 | **Bitwuzla** | Yices2 | cvc5 |
| qf_equality_bitvec_arith | QF_AUFBVLIA, QF_AUFBVNIA, QF_BVLRA, QF_UFBVLIA | 1027 | **Yices2** | SMTInterpol | cvc5 |
| qf_equality_bitvec | QF_ABV, QF_AUFBV, QF_UFBV | 1191 | **Bitwuzla** | Yices2 | cvc5 |
| qf_equality_lineararith | QF_ALIA, QF_AUFLIA, QF_UFLIA, QF_UFLRA | 1207 | **cvc5** | SMTInterpol | Yices2 |
| qf_equality_nonlineararith | QF_ANIA, QF_UFNIA, QF_UFNRA | 507 | **SMTInterpol** | cvc5 | Yices2 |
| qf_equality | QF_UF | 577 | **plat-smt** | Yices2 | cvc5 |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_BVFP, QF_BVFPLRA, QF_FP, QF_UFFP | 2780 | **Bitwuzla** | cvc5 | — |
| qf_linearintarith | QF_LIA | 69 | **Yices2** | SMTInterpol | cvc5 |
| qf_linearrealarith | QF_LRA | 10 | **OpenSMT** | Yices2 | cvc5 |
| qf_nonlinearintarith | QF_NIA | 119 | **SMTInterpol** | cvc5 | Yices2 |

#### Unsat Core Track — SMT-COMP 2026

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| arith | LIA, NIA | 389 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| bitvec | BV | 300 | **cvc5** | Bitwuzla | SMTInterpol |
| equality_lineararith | ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA | 7467 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality_machinearith | ABV, ABVFP, ABVFPLRA, AUFBV, AUFBVDTLIA, AUFBVDTNIA, AUFBVDTNIRA, AUFBVFPDTNIRA, AUFFPDTNIRA, UFBVDTLIA, UFBVDTNIA, UFBVDTNIRA, UFBVFPDTNIRA, UFFPDTNIRA | 2781 | **cvc5** | SMTInterpol | Bitwuzla |
| equality_nonlineararith | ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA | 3208 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality | UF, UFDT | 1336 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| fparith | BVFP, BVFPLRA | 22 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| qf_bitvec | QF_BV | 989 | **Bitwuzla** | cvc5 | SMTInterpol |
| qf_datatypes | QF_DT, QF_UFDT | 400 | **cvc5** | SMTInterpol | — |
| qf_equality_bitvec | QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT | 1253 | **Bitwuzla** | Yices2 | SMTInterpol |
| qf_equality_lineararith | QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 598 | **Yices2** | OpenSMT | cvc5 |
| qf_equality_nonlineararith | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 294 | **SMTInterpol** | Yices2 | cvc5 |
| qf_equality | QF_AX, QF_UF | 1014 | **Yices2** | OpenSMT (min-ucore) | OpenSMT |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_BVFP, QF_BVFPLRA, QF_FP, QF_UFFP, QF_UFFPDTNIRA | 3976 | **Bitwuzla** | cvc5 | — |
| qf_linearintarith | QF_IDL, QF_LIA, QF_LIRA | 693 | **Yices2** | OpenSMT | SMTInterpol |
| qf_linearrealarith | QF_LRA | 204 | **OpenSMT** | OpenSMT (min-ucore) | Yices2 |
| qf_nonlinearintarith | QF_NIA, QF_NIRA | 839 | **Yices2** | cvc5 | SMTInterpol |
| qf_nonlinearrealarith | QF_NRA | 300 | **Yices2** | cvc5 | SMTInterpol |
| qf_strings | QF_S, QF_SLIA | 1665 | **cvc5** | — | — |

#### Model Validation Track — SMT-COMP 2026

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| qf_adt_bitvec | QF_ABV, QF_AUFBV, QF_UFBVDT | 1513 | **Bitwuzla** | Yices2 | cvc5 |
| qf_adt_linarith | QF_ALIA, QF_AUFLIA, QF_AX, QF_UFDTLIA, QF_UFDTLIRA | 798 | **cvc5** | SMTInterpol | Yices2 |
| qf_bitvec | QF_BV | 1909 | **Bitwuzla** | cvc5 | bv_decide-nokernel |
| qf_datatypes | QF_DT, QF_UFDT | 871 | **cvc5** | SMTInterpol | — |
| qf_equality_bitvec | QF_UFBV | 437 | **Bitwuzla** | Yices2 | SMTInterpol |
| qf_equality_lineararith | QF_UFIDL, QF_UFLIA, QF_UFLRA | 891 | **OpenSMT** | SMTInterpol | cvc5 |
| qf_equality_nonlineararith | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 506 | **cvc5** | SMTInterpol | Yices2 |
| qf_equality | QF_UF | 714 | **Yices2** | OpenSMT | cvc5 |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFPDTNIRA | 6249 | **cvc5** | Bitwuzla | — |
| qf_linearintarith | QF_IDL, QF_LIA, QF_LIRA | 1770 | **Yices2** | OpenSMT | SMTInterpol |
| qf_linearrealarith | QF_LRA, QF_RDL | 599 | **OpenSMT** | Yices2 | SMTInterpol |
| qf_nonlinearintarith | QF_NIA | 1901 | **Yices2** | cvc5 | SMTInterpol |
| qf_nonlinearrealarith | QF_NRA | 936 | **SMT-RAT** | Yices2 | cvc5 |

#### Parallel Track — SMT-COMP 2026

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| qf_bitvec | QF_BV | 52 | **Bitwuzllob** | Bitwuzla-BV_Parti | — |
| qf_equality_lineararith | QF_ALIA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 77 | **z3-parallel** | — | — |
| qf_linearintarith | QF_IDL, QF_LIA | 103 | **OpenSMT-SMTS** | z3-parallel | QiuQi |
| qf_linearrealarith | QF_LRA, QF_RDL | 68 | **z3-parallel** | — | — |
| qf_nonlinearintarith | QF_NIA | 50 | **Yices2** | z3-parallel | — |
| qf_nonlinearrealarith | QF_NRA | 50 | **Yices2** | z3-parallel | — |
*(The 2025 equivalents are in Appendix A.)*

### 3.4 Why 2026's numbers are so much smaller **[C]**

Two rule changes, both in the 2026 rules:

1. **A fourth benchmark-cap tier.** Through 2025 the cap was
   `min(n, max(300, 50n/100))`. In 2026 it became: all if `n ≤ 300`; 300 if `300 < n ≤ 600`;
   **50 % if `600 < n ≤ 1000`; and `500 + (n−1000)/10` if `n > 1000`.**
2. **Benchmarks are drawn from the *preceding* year's SMT-LIB release**, not the current one.

Rationale given verbatim: *"SMT-COMP 2025 took 9.98 CPU years to execute."* The effect on
axeyum's divisions: `QF_BV` 10 703 → 2 540; `QF_Strings` 34 228 → 7 633; `QF_LIA`-division
6 040 → 1 965; `QF_NIA`-division 12 280 → 2 857.

**[I]** For axeyum this is good news: a smaller, still-representative competition set is
cheaper to run locally, and the 2025 sets remain available for breadth testing.

### 3.5 Competition-wide winners

| Track | Best Overall 2026 | Best Overall 2025 |
|---|---|---|
| Single Query | **cvc5** (40.373142) | **cvc5** (45.708019) |
| Incremental | **cvc5** (40.380757) | **cvc5** (40.04554) |
| Unsat Core | **cvc5** (26.303383) | **cvc5** (27.384714) |
| Model Validation | **cvc5** (28.262747) | **cvc5** (31.577255) |
| Parallel | **Bitwuzllob** (0.649847) | **Z3-Parti-Z3pp** (0.751708) |

2026 Single Query, other rankings: **Biggest Lead** = cvc5-cvc5-xyz; **Largest
Contribution** = **Amaya** (sequential and parallel), with UltimateEliminator+MathSAT on the
SAT axis, Xolver on UNSAT, and Yices2 at 24 s. **[C]**

**[I]** The Largest-Contribution result is the interesting one for axeyum: **Amaya**, a
single-division automata-based solver for Presburger arithmetic, won the "solver that would
be most missed" ranking against cvc5. Largest Contribution rewards *unique* solving power,
not breadth — which is a realistic target for a young solver with a distinctive method,
whereas Best Overall is not.

### 3.6 Entrants

**SMT-COMP 2026 (36 competing entries)** **[C]**: Amaya, Bitwuzla, Bitwuzla-BV_Parti,
Bitwuzla-MachBV, Bitwuzla-SPFD, Bitwuzllob, bv_decide, bv_decide-nokernel, COLIBRI, colibri2,
cvc5, cvc5-cvc5-xyz, NeuroSym, OpenSMT, OpenSMT (min-ucore), OpenSMT-SMTS, OpenSMT-SMTS-seq,
OSTRICH, plat-smt, QiuQi (single-query and parallel entries), Roole, Samet, SMT-RAT,
SMTInterpol, UltimateEliminator+MathSAT, Xolver, Yices2, YicesQS, Z3-alpha2, z3-BooledASS,
Z3-GEX, Z3-Noodler, z3-parallel, Z3-siri, Z3-Z3++ — plus non-competing base solvers
(bitwuzla-dandelion, Bitwuzla-fixed, …).

**SMT-COMP 2025 (24 entries)** **[C]**: Amaya, Bitwuzla, Bitwuzla-MachBV, bv_decide,
bv_decide-nokernel, COLIBRI, colibri2, cvc5, iProver v3.9.3, OpenSMT, OpenSMT (min-ucore),
OSTRICH, SMT-RAT, SMTInterpol, SMTS, STP-Parti-Bitwuzla, UltimateEliminator+MathSAT, Yices2,
YicesQS, Z3-alpha, Z3-Inc-Z3++, Z3-Noodler, Z3-Noodler-Mocha, Z3-Owl, Z3-Parti-Z3pp.

**[I]** Three observations that bear on axeyum's positioning:

- **Plain Z3 has not competed under its own name in 2025 or 2026.** Every Z3-derived entrant
  is a *derived tool*; since 2025 the base solver must also be submitted, and the `-base`
  rows are the actual Z3 baselines. A "we beat Z3" claim cannot be read straight off these
  tables. **Bitwuzla, cvc5 and Yices2 are the real reference implementations.**
- **`bv_decide` is a Lean-based, kernel-checked bit-blaster** (authors include Böving, Bhat,
  Clune, Barrett, Grosser) that competed in `QF_BV` in both years and placed **3rd in 2026
  QF_BV** with 2404/2540. This is the closest existing analogue to axeyum's identity claim
  ("untrusted fast search, trusted small checking") and is the most directly comparable
  reference point in the whole competition. Note it entered **Model Validation** in 2026 too.
- **New 2026 entrants worth knowing**: NeuroSym, QiuQi (won `QF_LinearIntArith` outright),
  Roole, Samet, Xolver, plat-smt, Bitwuzllob. The field is not static and a first-time
  entrant *can* win a division — QiuQi did.

---

## 4. The SMT-LIB benchmark release: structure and canonical sources

### 4.1 Where the canonical lists live **[C]**

| What | Where |
|---|---|
| Benchmark releases (2023 onward) | **Zenodo, the `smt-lib` community** — `https://zenodo.org/communities/smt-lib` |
| Historical releases 2013–2023 | StarExec — `https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=239` |
| Benchmark submission | `https://github.com/SMT-LIB/benchmark-submission` |
| Theory & logic declarations | `https://smt-lib.org/theories.shtml`, `https://smt-lib.org/logics-all.shtml` |
| Metadata catalog (SQLite) | **SMT-LIB Catalog 2025**, DOI `10.5281/zenodo.16290040` |
| SMT-COMP's own selected+scrambled sets | e.g. SMT-COMP 2025 Benchmarks, DOI `10.5281/zenodo.16887742` |

**Important [C]:** *"Starting today, the benchmark library will no longer be publicly
available from the University of Iowa's GitLab server. Official yearly releases of the
library will be available [on] Zenodo."* — smt-lib.org news, **2024-04-02**. Any tooling or
document still pointing at `clc-gitlab.cs.uiowa.edu` is stale.

### 4.2 Release DOIs **[C]**

| Release | DOI | Published |
|---|---|---|
| SMT-LIB release 2025 (non-incremental) | `10.5281/zenodo.16740866` | 2025-08-04 |
| SMT-LIB release 2025 (incremental) | `10.5281/zenodo.15493096` | 2025-05-22 |
| SMT-LIB release 2024 (non-incremental) | `10.5281/zenodo.11061097` | 2024-04-24 |
| SMT-LIB release 2024 (incremental) | `10.5281/zenodo.11186591` | 2024-05-13 |
| SMT-LIB release 2023 (non-incremental) | `10.5281/zenodo.10607722` | 2024-02-01 |
| SMT-LIB release 2023 (incremental) | `10.5281/zenodo.10607775` | 2024-02-01 |
| SMT-LIB Catalog 2025 | `10.5281/zenodo.16290040` | 2025-07-21 |
| SMT-COMP 2025 Benchmarks | `10.5281/zenodo.16887742` | 2025-08-16 |

### 4.3 Physical structure **[C]**

- **Two separate collections**: `non-incremental` and `incremental`. They are *different
  Zenodo records*, with different logic sets and different release dates.
- **One `.tar.zst` archive per logic**, named exactly `<LOGIC>.tar.zst`, plus a `README.md`.
  Decompress with `tar -xf <archive>`.
- Inside an archive, benchmarks are nested by **submitter directory → submitter's own
  hierarchy**. The **bottom-level directory is the "family"** used by SMT-COMP for benchmark
  selection and Largest-Contribution normalization.
- License: **CC-BY-4.0** unless a benchmark's own `:license` says otherwise.
- **Compression is extreme** — 4.6 GB compressed expands to **78 GB** (non-incremental) and
  2.9 GB to **59 GB** (incremental). Budget disk before extracting.

### 4.4 Totals, 2025 release **[C]**

| | Logics | Benchmarks | Compressed | Uncompressed |
|---|---:|---:|---:|---:|
| Non-incremental | **89** | **450 472** | 4.6 G | 78 G |
| Incremental | **41** | **44 708** | 2.9 G | 59 G |
| Union of logic names | **94** | — | — | — |

### 4.5 The `:status` attribute — how expected answers are encoded **[C]**

From the SMT-LIB 2.7 reference document (§3.11.3, §4.2.9):

- Every official benchmark must set `:smt-lib-version`, `:source`, `:license` and `:category`
  **exactly once**, and `:smt-lib-version` **must be the very first command**.
- `:category` ∈ `"crafted"`, `"random"`, `"industrial"`.
- **`:status` ∈ `sat`, `unsat`, `unknown`.** *"Each occurrence of the command
  `(set-info :status sat)` … indicates that the next check command in the script is expected
  to return `sat` … More precisely, the expected value of a check command in a script is the
  one indicated by the most recent command of the form `(set-info :status v)` in the script,
  if `v` is either `sat` or `unsat`. If `v` is `unknown`, there is no expectation."*
- `:status` **must be set as many times as needed** so that every `check-sat` /
  `check-sat-assuming` is preceded by one — this is what makes incremental benchmarks
  self-describing.

**How SMT-COMP uses it [C]:** a disagreement with `:status` scores `e = 1` (an error). On a
benchmark whose `:status` is `unknown`, *any* `sat`/`unsat` answer scores as **correct** —
but if two solvers that are sound-on-known-status disagree there, the benchmark is **removed
from scoring entirely**. The library's own statuses are themselves partly derived from past
competitions: the 2019 release notes record *"Updated statuses of 3039 previously unknown
non-incremental benchmarks (based on the results from 2 or more solvers from SMT-COMP'18)."*

**[I] Practical warning for axeyum:** `:status` is *evidence*, not ground truth. It is
majority-vote-derived for a large fraction of the library. A disagreement with `:status` is a
reason to investigate, not automatically a bug in your solver — but the competition will
score it as an error regardless.

### 4.6 Per-logic benchmark counts, SMT-LIB release 2025 **[C]**

| Logic | Non-incr. benchmarks | Uncompressed | Incremental scripts |
|---|---:|---:|---:|
| `ABV` | 4975 | 29M | — |
| `ABVFP` | 60 | 416K | — |
| `ABVFPLRA` | 77 | 496K | 4 |
| `ALIA` | 3098 | 22M | 24 |
| `ANIA` | 78 | 1.2M | 3 |
| `AUFBV` | 1523 | 2.2G | — |
| `AUFBVDTLIA` | 1683 | 11M | — |
| `AUFBVDTNIA` | 552 | 14M | — |
| `AUFBVDTNIRA` | 5041 | 422M | — |
| `AUFBVFP` | 57 | 40M | — |
| `AUFBVFPDTNIRA` | 117 | 3.1M | — |
| `AUFDTLIA` | 795 | 178M | — |
| `AUFDTLIRA` | 11043 | 346M | — |
| `AUFDTNIRA` | 1567 | 38M | — |
| `AUFFPDTNIRA` | 166 | 4.9M | — |
| `AUFLIA` | 3327 | 119M | — |
| `AUFLIRA` | 20011 | 225M | — |
| `AUFNIA` | 3 | 12K | — |
| `AUFNIRA` | 1480 | 31M | 165 |
| `BV` | 6185 | 927M | 18 |
| `BVFP` | 208 | 1.1M | 1 |
| `BVFPLRA` | 266 | 1.4M | 9 |
| `FP` | 2669 | 11M | — |
| `FPLRA` | 41 | 164K | — |
| `LIA` | 536 | 4.1M | 6 |
| `LRA` | 2439 | 38M | 5 |
| `NIA` | 257 | 1.2M | — |
| `NRA` | 3819 | 15M | — |
| `QF_ABV` | 15148 | 3.4G | 1272 |
| `QF_ABVFP` | 18129 | 159M | 18429 |
| `QF_ABVFPLRA` | 74 | 1.3M | 7 |
| `QF_ALIA` | 176 | 9.4M | 44 |
| `QF_ANIA` | 157 | 167M | 5 |
| `QF_AUFBV` | 75 | 18M | 31 |
| `QF_AUFBVFP` | 1 | 24K | — |
| `QF_AUFBVLIA` | — | — | 441 |
| `QF_AUFBVNIA` | — | — | 44 |
| `QF_AUFLIA` | 1303 | 12M | 72 |
| `QF_AUFNIA` | 17 | 20M | — |
| `QF_AX` | 551 | 7.0M | — |
| `QF_BV` | 46191 | 35G | 2611 |
| `QF_BVFP` | 17250 | 75M | 521 |
| `QF_BVFPLRA` | 177 | 936K | 64 |
| `QF_BVLRA` | — | — | 1046 |
| `QF_DT` | 8700 | 425M | — |
| `QF_FP` | 40406 | 162M | 166 |
| `QF_FPLRA` | 59 | 384K | — |
| `QF_IDL` | 2528 | 3.9G | — |
| `QF_LIA` | 13306 | 7.7G | 69 |
| `QF_LIRA` | 7 | 1.7M | — |
| `QF_LRA` | 1753 | 2.5G | 10 |
| `QF_NIA` | 25452 | 3.9G | 119 |
| `QF_NIRA` | 3 | 804K | — |
| `QF_NRA` | 12154 | 3.3G | — |
| `QF_RDL` | 255 | 96M | — |
| `QF_S` | 22172 | 103M | 245 |
| `QF_SLIA` | 84411 | 2.3G | — |
| `QF_SNIA` | 70 | 328K | 2 |
| `QF_UF` | 7503 | 958M | 1778 |
| `QF_UFBV` | 2539 | 1.2G | 2330 |
| `QF_UFBVDT` | 76 | 13M | — |
| `QF_UFBVLIA` | — | — | 179 |
| `QF_UFDT` | 203 | 199M | — |
| `QF_UFDTLIA` | 76 | 19M | — |
| `QF_UFDTLIRA` | 146 | 676K | — |
| `QF_UFDTNIA` | 80 | 14M | — |
| `QF_UFFP` | 2 | 8.0K | 1 |
| `QF_UFFPDTNIRA` | 154 | 1.2M | — |
| `QF_UFIDL` | 628 | 340M | — |
| `QF_UFLIA` | 659 | 115M | 773 |
| `QF_UFLRA` | 1284 | 1.6G | 3058 |
| `QF_UFNIA` | 806 | 303M | 1012 |
| `QF_UFNRA` | 58 | 3.2M | 1 |
| `UF` | 7590 | 432M | 4067 |
| `UFBV` | 193 | 1000M | — |
| `UFBVDT` | 1 | 64K | — |
| `UFBVDTLIA` | 24 | 936K | — |
| `UFBVDTNIA` | 157 | 25M | — |
| `UFBVDTNIRA` | 1259 | 24M | — |
| `UFBVFP` | 2 | 76K | — |
| `UFBVFPDTNIRA` | 89 | 2.5M | — |
| `UFBVLIA` | 208 | 93M | — |
| `UFDT` | 4569 | 327M | — |
| `UFDTLIA` | 1583 | 746M | — |
| `UFDTLIRA` | 7749 | 152M | — |
| `UFDTNIA` | 1008 | 1.3G | 139 |
| `UFDTNIRA` | 4424 | 153M | — |
| `UFFPDTNIRA` | 795 | 9.7M | — |
| `UFIDL` | 68 | 852K | — |
| `UFLIA` | 10128 | 480M | — |
| `UFLRA` | 15 | 60K | 1870 |
| `UFNIA` | 13532 | 1.1G | 4063 |
| `UFNIRA` | 266 | 1.1M | — |
| `UFNRA` | — | — | 4 |
| **TOTAL** | **450472** (89 logics) | **78G** | **44708** (41 logics) |
**[I] Reading this for axeyum:** the eleven logics axeyum targets account for
**204 796 of 450 472** non-incremental benchmarks (**45.5 %**) — `QF_BV` 46 191,
`QF_SLIA` 84 411, `QF_NIA` 25 452, `QF_ABV` 15 148, `QF_LIA` 13 306, `UF` 7 590,
`QF_UF` 7 503, `QF_IDL` 2 528, `QF_LRA` 1 753, `QF_UFLIA` 659, `QF_RDL` 255 — but they
occupy only **11 of 94 logic directories (11.7 %)**. The benchmark mass is concentrated in
a few logics; the *coverage* gap is much wider than the *volume* gap.

---

## 5. Model validation, unsat cores, and proofs

### 5.1 Model Validation Track — what a model must look like **[C]**

**Divisions (2025):** `QF_Bitvec`, `QF_DataTypes`, `QF_Equality`, `QF_Equality+Bitvec`,
`QF_Equality+(Non)LinearArith`, `QF_(Non)LinearIntArith`, `QF_(Non)LinearRealArith`, plus
`QF_ADT+BitVec` and `QF_ADT+LinArith`. *"This year all divisions with non-linear arithmetic,
arrays, and datatypes are experimental divisions."* Benchmarks are drawn from `QF_BV`,
`QF_IDL`, `QF_RDL`, `QF_LIA`, `QF_LRA`, `QF_LIRA`, `QF_UF`, `QF_UFBV`, `QF_UFIDL`, `QF_UFLIA`,
`QF_UFLRA` with `:status sat` (unsat removed; `unknown` kept only if a sound solver reported
`sat`).

**The required output:** the solver answers `check-sat` with `sat`, then responds to
`(get-model)` with *"definitions specifying **all and only** the current user-declared
function symbols, in the format prescribed by the SMT-LIB standard"* — i.e. a sequence of
`(define-fun …)` forms. Two failure modes are explicitly named: **partial models** (missing a
declared symbol) are `UNKNOWN`, and a **model that does not satisfy the benchmark** is
`INVALID` (`e = 1`).

**The validator: Dolmen. [C]** *"the organizers will use the model validating tool, Dolmen,
which can be built using the `smtcomp` tool. It expects as model input a file with the answer
to the `check-sat` command followed by the solver response to the `get-model` command."*
Verdicts:

| Verdict | Means | Score |
|---|---|---|
| `VALID` | `sat` + a full satisfying model | `e=0, n=1` |
| `INVALID` | `unsat` answer, or a model that does not satisfy the input | `e=1, n=0` |
| `UNKNOWN` | no output, no `get-model` response, `unknown` answer, or a **malformed / partial** model | `e=0, n=0` |

**Time limits [C]:** 20 min to produce; model checking *"is yet to be determined, but is
anticipated to be around 15 minutes"* — identical boilerplate in the 2023, 2024, 2025 and
2026 rules.

**New model syntax for the experimental divisions [C]** (SMT-COMP 2026 model page —
this is syntax **not yet standardized by SMT-LIB**):

- **Partial functions** (division by zero, datatype selectors applied to the wrong
  constructor): a new **`refine-fun`** command; `define-fun` is *"kept for compatibility at
  least in 2026"*.
- **Algebraic / irrational reals** in `QF_NRA` models: **`root-of-with-ordering`** and
  **`root-of-with-interval`**, with the defining polynomial given as **coprime integer
  coefficients in ascending order**.
- **Array values**: via `store` and `const`.

**[I] What this means for axeyum.** The project's hard rule — *"Every `sat` result must be
checkable by evaluating the original term against the lifted model"* — is the same invariant
Dolmen enforces, so the semantics are already right. What is missing is (a) the SMT-LIB
`get-model` **surface syntax**, (b) the "all and only user-declared symbols" discipline
(no auxiliary/Tseitin symbols may leak), and (c) SMT-LIB 2.7's new restriction that model
output must have **no forward references**. That is front-end work, not solver work.

### 5.2 Unsat Core Track **[C]**

- Benchmarks are non-incremental `unsat` instances with **more than one** top-level
  assertion, rewritten to use **named assertions**: `(assert (! t :named f))`.
- The solver must answer `unsat` to `check-sat` and then produce `(get-unsat-core)` as a list
  of names. A solver answering `unknown` **must respond with an error** to the subsequent
  `get-unsat-core`.
- **Scored on reduction, not on solve count**: `n = N − |core|`, where `N` is the number of
  named top-level assertions. A smaller core is worth more than a faster one.
- `unsat` answered but no core produced = "no reduction", i.e. the whole benchmark as core.
- **Validation is by consensus of other solvers [C]:** the organizers pick *validation
  solvers* from the single-query track **that were sound in that division**, and *"the
  unsatisfiability of an unsat core is validated if the number of checking solvers whose
  result is `unsat` is strictly greater than the number of validation solvers whose result is
  `sat`. In particular, if no checking solver produces `unsat`, the unsat core is not
  validated."* That last sentence is the **2025 rule change** ("No point is given for an
  unsat core such that no solver is capable to verify it"), which also raised the validation
  time budget to the time taken to generate the core; 2026 gives validation the full 20 min.
- **[I]** Note the epistemics: there is **no proof checking here at all**. Cores are validated
  by majority vote of other solvers — precisely the kind of "checker that cannot fail
  independently" that axeyum's own discipline warns about. A DRAT/LRAT-backed core would be
  strictly stronger evidence than what the competition currently requires.

### 5.3 Proof Exhibition Track — history and current status **[C]**

| | |
|---|---|
| **Introduced** | SMT-COMP **2022** ("we … have defined a new Proof Exhibition Track") |
| **Ran** | **2022 and 2023 only** |
| **Discontinued** | **2024**, explicitly |
| **Status 2025, 2026** | absent from the rules and from the results pages |
| **Competitive?** | **No.** 2023 rules: *"Since the Proof Exhibition Track is non-competitive and we are not fixing a definition of a valid proof, there will be no score computed for this track."* |
| **Evaluation** | qualitative, on seven named criteria: **soundness, trust-base, proof overhead, granularity, readability, extractability, stability** |
| **Time limit** | 1200 s per solver/benchmark pair, **including proof-checking time** |
| **Benchmark cap** | reduced in 2023 to `min(n, max(150, 25n/100))` |
| **Divisions** | 19 in 2023 (same names as Single Query), 59 115 benchmarks |

The discontinuation rationale, verbatim from the 2024 rules: *"First, we were unable to find
a way of turning the proof track into a competition that would not lead to an unmanageable
amount of overhead on the competition organizers or the participants. Second, we have
collected vast amounts of data in the last two years and thoroughly evaluating it takes time.
Third, this year we would need to restrict the allowed proof size due to hardware limits of
the new execution platform."* The 2023 rules note the 2022 track *"produced 800 GB of
output"*.

**[I] The strategic reading for axeyum.** There is **no competitive venue for proof
production in SMT today.** SMT-COMP measured it for two years, found it unscoreable — in
large part because *"we are not fixing a definition of a valid proof"* — and stopped. This
cuts both ways:

- **Against:** axeyum cannot demonstrate "Lean parity" (every unsat carries a machine-checkable
  proof) by winning anything. There is no leaderboard.
- **For:** the reason the track died is that **the field has no agreed proof format and no
  agreed trust base** — which is exactly the gap axeyum's "untrusted fast search, trusted small
  checking" identity is built to fill. The seven 2022–23 criteria (soundness, trust-base,
  proof overhead, granularity, readability, extractability, stability) are a ready-made,
  competition-sanctioned rubric for self-evaluation, and axeyum should probably adopt them
  verbatim as the axes of its own proof-quality reporting.
- The nearest live proxies are: **`bv_decide`**, the Lean-kernel-checked bit-blaster that
  competes in `QF_BV` and Model Validation (2025 and 2026), and the **Model Validation
  track** itself, which is the one place the competition demands checkable evidence rather
  than a bare verdict.

### 5.4 The proof-format ecosystem (2025–2026) **[C]**

Even without a competition track, the formats are real, shipping, and checkable.

**cvc5 emits four formats** (`--dump-proofs --proof-format-mode=…`):

| Format | Checker | Notes |
|---|---|---|
| **`cpc`** — **Cooperating Proof Calculus** | **Ethos** (C++), built on the **Eunoia** logical framework | cvc5's *native* modern format: *"designed to faithfully represent cvc5's internal reasoning."* Because of that it **deviates from SMT-LIB deliberately** — e.g. it uses mixed arithmetic internally where integers and reals appear together. CPC is formalized as a Eunoia signature shipped in the cvc5 repo. |
| **`alethe`** | **Carcara** (Rust), plus reconstruction in **Isabelle/HOL** and in **Coq via SMTCoq** | *"a flexible proof format for SMT solvers based on SMT-LIB … includes both coarse- and fine-grained steps and was first implemented in the veriT solver."* Carcara is described by cvc5's own docs as *"a high performance Rust proof checker and elaborator for Alethe."* cvc5's Alethe coverage: **EUF, linear arithmetic, bit-vectors, and parts of strings, with or without quantifiers.** |
| **`lfsc`** | LFSC checker (C++) | LF extended with **computational side conditions**. Still supported — *not* removed — with signature files in the cvc5 repo. |
| **`dot`** | — | *"only meant for visualization."* |

**The `trust step` mechanism — the most important design idea here. [C]** Both CPC and LFSC
handle rules they cannot yet express by emitting a **trust step**: *"A trust step proves an
arbitrary formula with no provided justification."* The proof carries warnings naming which
internal rules were degraded this way, and — critically — **the checker's exit verdict
reflects it**: *"Upon successful exit, `ethos` will return the output `incomplete` if any
trust step is used in the proof … Otherwise, if all proof steps are fully specified, `ethos`
will return the output `correct`."*

**[I] This is precisely axeyum's own "make the exit status depend on the finding" rule,
implemented by the leading SMT solver.** A three-valued checker verdict (`correct` /
`incomplete` / `invalid`) is the state of the art, and it is the right target shape for
axeyum's evidence artifacts — a checker that reports `correct` for a proof containing
unjustified steps is exactly the "checker that cannot fail" failure mode.

**Proof granularity is a tunable [C]:** `--proof-granularity=dsl-rewrite` (CPC) or
`theory-rewrite` (LFSC) produce finer proofs; with `theory-rewrite`, LFSC trust steps
*"correspond only to equalities corresponding to theory rewrites."*

**Structural shape [C]:** *"All proofs in the `cpc` format are closed refutations of the
input, in that the proof will assume formulas from the input and end with a step proving
`false`."*

**SAT-level formats.** DRAT / LRAT / FRAT sit below all of the above and are the mature,
universally-checkable layer. **[I]** axeyum already occupies exactly this layer:
`check_drat` (an independent RUP+RAT DRAT checker, ADR-0011) and `solve_with_drat_proof`
(a proof-producing CDCL core, ADR-0012). The gap between axeyum today and the SMT proof
ecosystem is therefore **not** "can we produce checkable proofs" — it is **lifting a
bit-level DRAT refutation to a term-level SMT proof**, which is what CPC/Alethe/LFSC exist to
express.

**[I] Recommended reading of this for axeyum's roadmap:**

1. **Alethe is the interoperability target**, not CPC. It is SMT-LIB-based (CPC deliberately
   is not), it has a Rust checker (**Carcara**) that axeyum could depend on or learn from
   directly, and it already has Isabelle and Coq reconstruction paths — i.e. it is the format
   with an existing bridge to a proof assistant, which is what "Lean parity" means.
2. **CPC/Ethos is the reference for how to structure a small trusted checker** — an explicit
   logical framework (Eunoia) plus a signature file per calculus, so the trusted base is a
   signature rather than a program.
3. **The `trust step` + `incomplete` verdict is the pattern to copy** for partial evidence,
   and it lines up with the seven Proof-Exhibition criteria (§5.3): trust-base, granularity,
   extractability.

### 5.5 Proof literature, and the actual state of each checker

**Provenance note.** The citations in this subsection come from a second, dedicated research
pass over the proof literature (DOIs and venue metadata verified against publisher records).
Where a claim rests on a paper's own self-measurement, that is flagged explicitly — see the
caveat at the end, which is the important part.

#### The papers worth reading before designing an evidence layer

| Work | Venue / DOI | Why it matters to axeyum |
|---|---|---|
| **eDRAT — "Extending DRAT to SMT"** (Hitarth, Codel, Lachnitt, Dutertre) | FMCAD 2024, `10.34727/2024/ISBN.978-3-85448-065-5_8` | **The published form of exactly the hybrid axeyum is positioned for**: DRAT below, theory lemmas above. Characterized by the Ethos authors as *"uses DRAT together with unjustified theory lemmas, which must be checked separately. **It does not support proofs for preprocessing.**"* That named limitation is the same hole axeyum would hit — its rewrite/canonicalization layer (`axeyum-rewrite`) is preprocessing. Read this before building the lift from `solve_with_drat_proof` to term-level evidence. |
| **RARE — "Reconstructing fine-grained proofs of rewrites using a domain-specific language"** (Nötzli et al.) | FMCAD 2022, `10.34727/2022/ISBN.978-3-85448-053-2_12` | The DSL behind cvc5's `ProofRewriteRule` catalogue and `--proof-granularity=dsl-rewrite`, and behind Alethe's `rare_rewrite` / `multi_rare_rewrite` rules. **Rewrite justification is where a from-scratch producer's proofs go holey first** — this is the field's answer to that problem, and Eunoia is described as *"partially inspired by it … a generalization of its functionality to arbitrary proof rules."* |
| **RESOLUTE** — SMTInterpol's proof format (Hoenicke & Schindler) | SMT workshop 2022, `https://ceur-ws.org/Vol-3185/paper9527.pdf` | The fourth data point, and the one that argues for a **small fixed calculus** instead of a general logical framework. Worth weighing against CPC/Eunoia before committing to framework machinery. |
| **"Flexible Proof Production in an Industrial-Strength SMT Solver"** | IJCAR 2022, `10.1007/978-3-031-10769-6_3` | Describes cvc5's *internal* proof infrastructure — the machinery CPC is **printed from**, not CPC itself (it predates CPC/Eunoia by two years). This is the architecture paper for "how a solver carries proofs internally without wrecking its search." |
| **Ethos** (the CPC checker) | IJCAR 2026, LNAI 16688, pp. 305–314, `10.1007/978-3-032-32589-1_19`, open access CC-BY | The current reference for framework-based SMT proof checking. |
| **DRAT** (Wetzler, Heule, Hunt) | SAT 2014, `10.1007/978-3-319-09284-3_31` | The canonical citation for the format axeyum already implements (ADR-0011 / ADR-0012). Still the SAT Competition's format. |

**Bibliographic gaps worth knowing [C]:** there is **no standalone "AletheLF" paper** and **no
separate Eunoia language paper** — the citable language reference is the
[Ethos user manual](https://github.com/cvc5/ethos/blob/main/user_manual.md). And the Alethe
specification is cited by the Ethos bibliography as *"The Alethe proof format: an **evolving**
specification and reference (2026)"* — **dated 2026 and explicitly still evolving**, which is a
standing maintenance cost for any producer that targets it.

#### Is LFSC still alive? Probably not, and the evidence is structural

**[C]** The `cvc5/LFSC` checker repository **has not been pushed since 2023-09-14**, and
`proofs/lfsc/signatures` **contains no bit-vector, array, datatype, or set signature at all**.

**[I]** That is a stronger and more independent signal than any benchmark: a checker whose
signature set omits bit-vectors cannot meaningfully check `QF_BV` proofs, whatever a coverage
table says. **Treat LFSC as legacy.** cvc5 still *emits* it, but CPC is the live format and
Alethe is the live interoperability format.

#### The measurement caveat — read this before quoting any coverage number

The IJCAR 2026 Ethos paper reports a coverage table (LFSC 454 / 20 940; CPC 20 813 with zero
holes; *"Ethos is 6.25× slower than Carcara"*), measured on SMT-LIB release 2025
non-incremental benchmarks (`10.5281/zenodo.16740866`), Intel Xeon E5-2620 v4, 8 GiB, 600 s,
with a mid-2026 cvc5.

**This is the Ethos authors measuring their own tool against competitors.** It was read out of
the PDF, not reproduced; and the LFSC column measures a pipeline whose maintainers are not the
paper's authors. **Quote it as "the Ethos authors measured," never as an independent
benchmark.**

**[I]** This is the same discipline CLAUDE.md already enforces internally — *"before believing
a result, ask what the command would print if it were broken"* — applied to someone else's
published table. The LFSC conclusion happens to survive, but on the *independent* evidence
above (dead repo, missing signatures), not on the paper's number.

---

## 6. What's new: SMT-LIB 2.7 / 3, and theories outside the standard

### 6.1 SMT-LIB standard version status **[C]**

**Version 2.7 is current.** Releases of the 2.7 reference document: 2025-02-05, 2025-07-07,
**2026-03-27** (latest). Version 2.6's last release was 2024-09-20.

**What 2.7 adds over 2.6** (from §1.1.2 of the reference document, verbatim in substance):

1. **Rank-1 (prenex) polymorphism.** A new command declares *global sort parameters*, which
   are treated as implicitly universally quantified sort variables in each asserted formula.
   "This has the effect of allowing prenex (or rank-1) polymorphism in assertions but not
   more general forms of polymorphism."
2. **A λ binder and an application symbol `@`**, with semantics in **a new theory of
   higher-order functions** (`HO-Core`) including the binary sort constructor `->` for map
   sorts. Crucially: *"values of sort `(-> τ1 τ2)` are treated as any other value … However,
   they are not identified with functions of rank τ1 τ2 …, keeping the underlying logic of
   Version 2.7 first order."* (`@` replaced `_` as map application on 2025-04-09.)
3. **`define-const`**, for defining constants — in particular of map sort.
4. `_` usable as a **wildcard in `match` patterns**.
5. **`check-sat-assuming` generalized** to arbitrary Boolean terms, with
   `get-unsat-assumptions` and `get-unsat-core` semantics correspondingly generalized.
6. **`get-model` output further restricted to prevent forward references in models.**
7. The 2026-03-27 release "clarifies a number of points on polymorphic constants and
   functions."

**Version 3 [C]:** footnote 2 of the reference document states plainly that the
identification of map values with functions *"will occur in Version 3, which will be based on
higher-order logic."* That is the only normative statement about SMT-LIB 3 I found; no
timeline is given.

### 6.2 New logic in 2026: `QF_EIA` **[C]**

smt-lib.org news, **2026-03-18**: *"Extended theory `Ints` with an exponentiation operator and
added logic `QF_EIA`."* `QF_EIA` is described as "Quantifier-free formulas over the theory of
integer arithmetic with exponentiation." It has a full official `(logic …)` declaration —
making it the 25th — but **no benchmark directory exists yet** (it postdates the 2025
release). **[I]** Expect `QF_EIA` benchmarks and possibly an SMT-COMP presence in a future
edition; `(_ ** )`-style exponentiation now has a normative home.

### 6.3 Theories NOT in SMT-LIB, but implemented and benchmarked

cvc5's documentation splits its theories into "Standardized" and **"Non-standard or extended"**.
The non-standard list is the best available map of where the field is going beyond SMT-LIB. **[C]**

| Theory | Status | Syntax / logic string | Notes |
|---|---|---|---|
| **Finite Fields** | cvc5 extension; **not** an SMT-LIB theory | sort `(_ FiniteField p)`; values `(as ffN F)`; ops `ff.add`, `ff.mul` (both n-ary); `=` | cvc5 supports **prime-order fields only**, interpreted as integers mod p with floor-division remainder. Backed by Gröbner-basis methods; cvc5 has an alternate solver from *"Split Gröbner Bases for Satisfiability Modulo Finite Fields"* (CAV 2024, `[OPB+24]`). Motivating application is zero-knowledge-proof / arithmetic-circuit verification. **No `QF_FF` logic name appears in the SMT-LIB benchmark release or in any SMT-COMP division, 2023–2026.** |
| **Sequences** | cvc5 extension; not standardized | sort `(Seq S)`; `seq.empty`, `seq.unit`, `seq.len`, `seq.nth`, `seq.update`, `seq.extract`, `seq.++`, `seq.at`, `seq.contains`, `seq.indexof` | The parametric generalization of the Strings theory. cvc5 supports element sorts that are infinite (e.g. Int) or of fixed finite cardinality (e.g. BV). `seq.nth` is **uninterpreted out of bounds** — the same partial-operator hazard axeyum already handles for `str.at`. |
| **Bags / multisets** | cvc5 extension | sort `(Bag S)`; `bag.union_disjoint`, …; logic string **`ALL`** | No dedicated logic name. |
| **Sets and relations** | cvc5 extension | sort `(Set S)`; logic string formed by **appending `FS`** — e.g. `QF_UFLIAFS` | The `FS` suffix is a **cvc5 convention, not SMT-LIB**. |
| **Transcendentals** | cvc5 extension | logic string formed by **appending `T`** — e.g. `QF_NRAT`; `real.pi`, `sqrt`, `sin`, `cos`, `tan`, … | Extends NRA/NIRA. The `T` suffix is likewise a cvc5 convention. |
| **Separation logic** | cvc5 extension | `declare-heap`, used under `QF_ALL` | |
| **Datatypes** | in the SMT-LIB **language** since 2.6, but **there is no `Datatypes` theory file** | `declare-datatype(s)`, `match`, constructors/selectors/testers | This is why ~30 `…DT…` logic names exist with no theory behind them. cvc5 still lists Datatypes under "non-standard or extended" because it extends what the standard specifies. |
| **Strings (extended)** | `Strings` **is** an official theory (added 2020-02-11) — but **no `QF_S`/`QF_SLIA` logic is officially declared** | | The largest benchmark family in the library (`QF_SLIA`, 84 411) runs on a logic name with no normative definition. |

**[I]** The pattern is consistent: **SMT-LIB standardizes theories slowly and logic names
almost not at all.** Solvers ship theories first (finite fields, sequences, bags,
transcendentals, separation logic), invent ad-hoc logic-string conventions (`…FS`, `…T`,
`ALL`, `QF_ALL`), and standardization follows years later if at all. A solver aiming at
breadth must decide independently which of these to implement; the standard will not tell it.

### 6.4 The sequential-vs-parallel scoring question **[C]**

There is a **design position**, recorded in the rules, but no recorded public "debate":

- The sequential score exists because *"the parallel score as defined above favors parallel
  solvers, which may utilize all available processor cores."*
- It is computed by imposing a **virtual CPU limit equal to the wall-clock limit**, so
  *"a solver should not benefit from using multiple processor cores. Conceptually, the
  sequential performance should be (nearly) unchanged if the solver was run on a single-core
  processor."*
- And the organizers refuse to cross-compare: *"We will not make any comparisons between
  parallel and sequential performances, as these are intended to measure fundamentally
  different performance characteristics."*
- The Parallel track gets **no sequential score at all** — *"Due to the nature of Parallel
  Track, we will not consider the sequential scores."*

The related live controversy is instead about **derived solvers**, and it produced a concrete
2026 rule: a derived solver *"can win a division, track, or logic only if it significantly
outperforms its base solver, i.e., only if it improves its PAR-2 score by at least 10 %"* —
which is why **PAR-2 was introduced in 2026** and why 2026 result tables carry the `ne`
(not-eligible) marker. Derived solvers must also now ship **source code**.

**[I] Consequence for axeyum:** axeyum is a from-scratch solver, not a derived tool, so it is
unaffected by the `ne` gate — and it competes on the **sequential** score on equal footing
with everyone, since the sequential score is explicitly designed to neutralize core count.
A single-threaded Rust solver is not structurally disadvantaged in the headline ranking.

---

## 7. What axeyum has not touched

axeyum currently measures parity on **11 logics**: `QF_BV`, `QF_ABV`, `QF_UF`, `UF`,
`QF_LIA`, `QF_LRA`, `QF_IDL`, `QF_RDL`, `QF_UFLIA`, `QF_NIA`, `QF_SLIA`.

### 7.1 The headline numbers **[C]** (counts) / **[I]** (framing)

| Measure | Covered | Total | Share |
|---|---:|---:|---:|
| SMT-LIB logic directories (2025 release, both collections) | 11 | **94** | 11.7 % |
| Non-incremental benchmarks | 204 796 | 450 472 | 45.5 % |
| Official SMT-LIB theories exercised (Core, ArraysEx, FixedSizeBitVectors, Ints, Reals, Strings) | 6 | **9** | 67 % |
| SMT-COMP 2026 single-query divisions at ~100 % logic coverage | **4** | 19 | 21 % |
| SMT-COMP 2026 single-query divisions with *any* coverage | 9 | 19 | 47 % |
| SMT-COMP 2026 single-query divisions at 0 % | 10 | 19 | 53 % |
| SMT-COMP tracks entered | 1 (single query) | 5 | 20 % |

**83 of 94 logics are untouched**, holding **245 676 non-incremental benchmarks**.

### 7.1b Division-by-division: coverage and the reference to beat

This is the operational view. "Covered" = benchmarks in that division drawn from one of
axeyum's 11 logics, using the SMT-COMP 2026 selection. **[C]** counts and winners; **[I]**
the coverage arithmetic.

| Division | 2026 benchmarks | Covered by axeyum's 11 logics | Coverage | Reference to beat (2026, sequential) | Logics axeyum lacks here |
|---|---:|---:|---:|---|---|
| `qf_bitvec` | 2540 | 2540 | **100 %** | Bitwuzla-MachBV — 2495/2540 | — (complete) |
| `qf_linearrealarith` | 766 | 766 | **100 %** | Yices2 — 700/766 | — (complete) |
| `qf_nonlinearintarith` | 2857 | 2855 | **100 %** | Z3-alpha2 — 2408/2857 | `QF_NIRA` |
| `qf_linearintarith` | 1965 | 1958 | **100 %** | QiuQi — 1807/1965 | `QF_LIRA` |
| `qf_equality` | 1404 | 1104 | **79 %** | Yices2 — 1404/1404 | `QF_AX` |
| `qf_equality_bitvec` | 2617 | 1914 | **73 %** | Bitwuzla — 2479/2617 | `QF_AUFBV`, `QF_UFBV`, `QF_UFBVDT` |
| `qf_strings` | 7633 | 5146 | **67 %** | Z3-Noodler — 7225/7633 | `QF_S`, `QF_SNIA` |
| `equality` | 1684 | 971 | **58 %** | cvc5 — 653/1684 | `UFDT` |
| `qf_equality_lineararith` | 1874 | 300 | **16 %** | SMTInterpol — 1746/1874 | `QF_ALIA`, `QF_AUFLIA`, `QF_UFDTLIA`, `QF_UFDTLIRA`, `QF_UFIDL`, `QF_UFLRA` |
| `equality_lineararith` | 6438 | 0 | **0 %** | cvc5 — 4968/6438 | **all of them** |
| `equality_machinearith` | 5179 | 0 | **0 %** | cvc5 — 3158/5179 | **all of them** |
| `equality_nonlineararith` | 4152 | 0 | **0 %** | cvc5 — 2778/4152 | **all of them** |
| `qf_fparith` | 1476 | 0 | **0 %** | Bitwuzla — 1440/1476 | **all of them** |
| `arith` | 1255 | 0 | **0 %** | Z3-alpha2 — 1111/1255 | **all of them** |
| `fparith` | 1178 | 0 | **0 %** | Bitwuzla — 1142/1178 | **all of them** |
| `qf_nonlinearrealarith` | 1020 | 0 | **0 %** | Z3-alpha2 — 946/1020 | **all of them** |
| `qf_equality_nonlineararith` | 631 | 0 | **0 %** | Yices2 — 473/631 | **all of them** |
| `bitvec` | 608 | 0 | **0 %** | Bitwuzla — 557/608 | **all of them** |
| `qf_datatypes` | 544 | 0 | **0 %** | cvc5-cvc5-xyz — 398/544 | **all of them** |
**[I] The four rows that matter most:**

- **`qf_bitvec`, `qf_linearrealarith`, `qf_linearintarith`, `qf_nonlinearintarith` are already
  ~100 % covered.** axeyum can enter these four divisions today with no new logic support.
  The bar is Bitwuzla-MachBV (98 %), Yices2 (91 %), QiuQi (92 %), Z3-alpha2 (84 %).
- **`qf_equality` needs one logic — `QF_AX` (551 benchmarks in the library)** — to go from
  79 % to 100 %. Note the division is *saturated*: Yices2, OpenSMT and cvc5 all solved
  1404/1404. Entering here means competing purely on time.
- **`qf_equality_bitvec` needs `QF_UFBV`** (plus the tiny `QF_AUFBV`/`QF_UFBVDT`) to go from
  73 % to ~100 %. axeyum has both `QF_BV` and `QF_UF`, so this is Nelson–Oppen plumbing.
- **`qf_strings` needs `QF_S`** to go from 67 % to 99 %. axeyum already does the harder
  `QF_SLIA`.

Ten of nineteen divisions are at **0 %**. Of those, `qf_fparith` (1 476) and `fparith`
(1 178) are unlocked by one capability axeyum already has partial infrastructure for
(`crates/axeyum-fp`); `arith` (1 255) and `bitvec` (608) are unlocked by quantifier support
over theories axeyum already decides.

### 7.2 Untouched quantifier-free logics, grouped by the capability that unlocks them

| Missing capability | Logics unlocked | Untouched benchmarks | Notes |
|---|---|---:|---|
| **Floating point** (`FloatingPoint` theory) | 9: `QF_FP` `QF_FPLRA` `QF_BVFP` `QF_BVFPLRA` `QF_ABVFP` `QF_ABVFPLRA` `QF_AUFBVFP` `QF_UFFP` `QF_UFFPDTNIRA` | **76 252** | The single largest QF gap. `QF_FP` alone is 40 406 benchmarks — the **second-largest logic in the library**. axeyum already has `crates/axeyum-fp`, so this is closer than it looks. Reference to beat: **Bitwuzla** (won `QF_FPArith` every year). |
| **Strings beyond `QF_SLIA`** | 2: `QF_S` `QF_SNIA` | **22 242** | `QF_S` is pure strings/regex without integers; `QF_SNIA` adds nonlinear integers. axeyum already does `QF_SLIA`, so this is mostly a matter of the regex fragment and `str.to_int`-style operators. Reference: **Z3-Noodler**, **OSTRICH**. |
| **Nonlinear real arithmetic** | 2: `QF_NRA` `QF_UFNRA` | **12 212** | Needs CAD / NLSAT / interval methods — a genuinely different decision procedure from the LIA/NIA path. Reference: **Z3-alpha2**, **Z3-GEX**, **cvc5**, **SMT-RAT**. |
| **Algebraic datatypes** | 6: `QF_DT` `QF_UFDT` `QF_UFBVDT` `QF_UFDTLIA` `QF_UFDTLIRA` `QF_UFDTNIA` | **9 281** | A *language* feature (2.6) plus a decision procedure; no theory file to implement against. Reference: **cvc5**, **SMTInterpol**. |
| **UF combined with other arithmetic** | 3: `QF_UFIDL` `QF_UFLRA` `QF_UFNIA` | **2 718** | axeyum has `QF_UFLIA` already; these are the same Nelson–Oppen machinery over a different arithmetic core. **Cheapest real coverage win on this list.** |
| **BV combined with UF/arith** | 3: `QF_UFBV` `QF_BVLRA` `QF_UFBVLIA` | **2 539** | Also cheap given `QF_BV` + `QF_UF` both exist. `QF_UFBV` has 2 330 *incremental* scripts too. |
| **Arrays beyond `QF_ABV`** | 8: `QF_AX` `QF_ALIA` `QF_ANIA` `QF_AUFLIA` `QF_AUFNIA` `QF_AUFBV` `QF_AUFBVLIA` `QF_AUFBVNIA` | **2 279** | axeyum's `eliminate_arrays` (ADR-0010) already does read-over-write + Ackermann for `QF_ABV`; extending it over non-BV index/element sorts is the work. `QF_AX` (551) is arrays with *no* other theory — likely the easiest single new logic in the whole library. |
| **Mixed Int/Real (`Reals_Ints`)** | 2: `QF_LIRA` `QF_NIRA` | **10** | Negligible benchmark volume, but `Reals_Ints` is a **prerequisite for 17 quantified logics** and for `to_real`/`to_int` coercions. Strategically larger than its benchmark count. |

### 7.3 The quantified half of the library — completely untouched

**48 quantified logic directories, 118 143 non-incremental benchmarks.** axeyum covers `UF`
(7 590) and nothing else quantified.

```
ABV ABVFP ABVFPLRA ALIA ANIA AUFBV AUFBVDTLIA AUFBVDTNIA AUFBVDTNIRA AUFBVFP
AUFBVFPDTNIRA AUFDTLIA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA AUFLIA AUFLIRA AUFNIA AUFNIRA
BV BVFP BVFPLRA FP FPLRA LIA LRA NIA NRA UFBV UFBVDT UFBVDTLIA UFBVDTNIA UFBVDTNIRA
UFBVFP UFBVFPDTNIRA UFBVLIA UFDT UFDTLIA UFDTLIRA UFDTNIA UFDTNIRA UFFPDTNIRA UFIDL
UFLIA UFLRA UFNIA UFNIRA UFNRA
```

Biggest by volume: `AUFLIRA` (20 011), `UFNIA` (13 532), `AUFDTLIRA` (11 043),
`UFLIA` (10 128), `UFDTLIRA` (7 749), `BV` (6 185), `AUFBVDTNIRA` (5 041), `ABV` (4 975).

**[I]** Note that `LIA`, `LRA`, `NIA`, `NRA` and `BV` are *pure quantified versions of logics
axeyum already decides*. These are the natural first quantifier targets — the theory solver
already exists; what's missing is instantiation/quantifier-elimination machinery. The
SMT-COMP `Arith` division (`LIA` `LRA` `NIA` `NRA`, 1 255 benchmarks in 2026) is a small,
self-contained entry point, currently won by **Z3-alpha2** with **YicesQS** (a
quantifier-elimination specialist) close behind. `Bitvec` (quantified `BV`) is 608 benchmarks
in 2026, won by **Bitwuzla**.

### 7.4 Tracks and evidence formats not touched

| SMT-COMP track | Status for axeyum **[I]** | What it demands |
|---|---|---|
| **Single Query** | the one axeyum measures | `sat`/`unsat`/`unknown` on a file argument |
| **Incremental** | untouched | a `smtcomp_run_incremental` script speaking SMT-LIB over stdin to the trace executor; `success` responses; `push`/`pop`. axeyum **has** `IncrementalBvSolver`/`IncrementalCnf` (ADR-0009), so the engine exists — the **front door does not**. 41 incremental logics, 44 708 scripts. |
| **Unsat Core** | untouched | `(assert (! t :named f))` handling + `get-unsat-core`. Scored on **reduction**, not solve count — a small core beats a fast one. |
| **Model Validation** | partially aligned | `get-model` emitting `define-fun` for **all and only** user-declared symbols. axeyum's hard rule "every `sat` must be checkable by evaluating the original term against the lifted model" is exactly this discipline; what's missing is the **SMT-LIB surface syntax** and the experimental-division model syntax (algebraic numbers via `root-of-with-interval` / `root-of-with-ordering`, arrays via `store`/`const`, partial functions via `refine-fun`). |
| **Parallel** | untouched, and correctly deprioritized | 20 min on 256 cores (2026); portfolio solvers explicitly allowed here only. |
| **Cloud** | **does not exist** as a scored track since 2024 | A separately-run AWS side event under the SMT-COMP'26 banner exists on a later schedule. |
| **Proof Exhibition** | **does not exist** — ran 2022–2023 only, discontinued 2024 | Nonetheless the *capability* is what axeyum's "Lean parity" claim is about. See §5. |

### 7.5 Theories nobody has standardized, that axeyum has not touched

`FiniteField`, `Seq` (sequences), `Bag`, `Set`/relations, transcendentals, separation logic,
higher-order (`HO-Core`, new in SMT-LIB 2.7), `QF_EIA` (integer exponentiation, new 2026-03).
**[I]** None of these appear in any SMT-COMP division, so none of them affect a parity claim.
They matter only as a statement about long-run reach — and `HO-Core` matters specifically
because **SMT-LIB 3 will be based on higher-order logic**, which is the direction axeyum's
kernel already points.

### 7.6 The honest summary **[I]**

- axeyum covers **the most contested and highest-volume corner of the library** — `QF_BV`
  alone is the flagship division — and **45.5 % of all non-incremental benchmarks**.
- But it covers **11.7 % of logics**, **~20 % of tracks**, and **0 % of the quantified half**.
- The **cheapest genuine coverage wins**, in order: `QF_AX`; `QF_UFBV`; `QF_UFLRA` /
  `QF_UFIDL` / `QF_UFNIA`; `QF_S`. All four reuse machinery axeyum already has.
- The **highest-volume single win** is **floating point** (76 252 benchmarks across 9 logics,
  with `axeyum-fp` already in the tree).
- The **highest-leverage structural win** is the **Incremental track front door**: the solver
  core already supports it, the track has 17 divisions, and no new decision procedure is
  required.
- The **most defensible competitive target** is not Best Overall (cvc5 owns it in 4 of 5
  tracks, both years) but **Largest Contribution** — won in 2026 single-query by **Amaya**, a
  single-division automata-based Presburger solver. That ranking rewards uniquely-solved
  instances, which is the natural shape of a differentiated new solver.
- On **evidence**, axeyum is further along than the logic count suggests: it already owns the
  SAT layer (`check_drat`, `solve_with_drat_proof`). The named next step in the literature is
  **eDRAT** (FMCAD 2024) — DRAT below, theory lemmas above — and its published limitation is
  that **it does not support proofs for preprocessing**. Since axeyum's rewrite/canonicalization
  layer *is* preprocessing, that gap should be designed for deliberately rather than
  discovered later. **RARE** (FMCAD 2022) is the field's answer to justifying rewrites, and
  is worth reading before `axeyum-rewrite` grows an evidence format of its own.

---

## Sources

Every URL below was fetched during this research (2026-09-06) unless noted.

### SMT-LIB (the standard, theories, logics, benchmarks)
- https://smt-lib.org/ — home; news feed with the 2.7 releases and the QF_EIA addition
- https://smt-lib.org/news.shtml — full news log (2.7 releases 2025-02-05 / 2025-07-07 / 2026-03-27; HO-Core `@` change 2025-04-09; QF_EIA 2026-03-18; GitLab→Zenodo move 2024-04-02; Strings theory 2020-02-11; 2.6/datatypes 2017-07-18)
- https://smt-lib.org/theories.shtml — the nine official theories
- https://smt-lib.org/logics.shtml — the logic naming conventions
- https://smt-lib.org/logics-all.shtml — the 25 full `(logic …)` declarations
- https://smt-lib.org/benchmarks.shtml — points to Zenodo and StarExec
- https://smt-lib.org/language.shtml — language/standard documents index
- https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf — **SMT-LIB 2.7 reference document** (§1.1.2 "Differences between Version 2.7 and Version 2.6"; §3.11.3 and §4.2.9 on `set-info` / `:status`; footnote 2 on Version 3 being higher-order)
- https://github.com/SMT-LIB/benchmark-submission
- https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=239

### Benchmark releases on Zenodo
- https://zenodo.org/communities/smt-lib — the community (7 records)
- https://zenodo.org/records/16740866 — SMT-LIB release 2025 (non-incremental), DOI 10.5281/zenodo.16740866
- https://zenodo.org/records/16740866/files/README.md — per-logic counts, 89 logics / 450 472 benchmarks / 78 G
- https://zenodo.org/records/15493096 — SMT-LIB release 2025 (incremental), DOI 10.5281/zenodo.15493096
- https://zenodo.org/records/15493096/files/README.md — 41 logics / 44 708 scripts / 59 G
- https://zenodo.org/records/11061097 — SMT-LIB release 2024 (non-incremental)
- https://zenodo.org/records/11186591 — SMT-LIB release 2024 (incremental)
- https://zenodo.org/records/10607722 — SMT-LIB release 2023 (non-incremental)
- https://zenodo.org/records/10607775 — SMT-LIB release 2023 (incremental)
- https://zenodo.org/records/16290040 — **SMT-LIB Catalog 2025** (SQLite metadata DB combining benchmark features with every SMT-COMP result since 2005)
- https://zenodo.org/records/16887742 — SMT-COMP 2025 Benchmarks (the scrambled selected sets, seed 757067271)

### SMT-COMP 2026 (current edition)
- https://smt-comp.github.io/ — redirects to /2026/
- https://smt-comp.github.io/2026/ — 21st edition; SMT Workshop Lisbon 24–25 July 2026, IJCAR-26 / FLoC'26
- https://smt-comp.github.io/2026/rules.pdf — rules, revised 2026-04-11 (five tracks; PAR-2 §7.2.2; derived-solver 10 % gate §7.5; four-tier benchmark cap §6; parallel track back to 20 min §5.6; "SMT-COMP 2025 took 9.98 CPU years")
- https://smt-comp.github.io/2026/results/ — results index, generated 2026-07-25
- https://smt-comp.github.io/2026/results/qf_bitvec-single-query/ (and the 94 sibling pages, one per division×track and per competition-wide ranking)
- https://smt-comp.github.io/2026/participants/ — 36 competing entries + non-competing base solvers
- https://smt-comp.github.io/2026/specs/ — BenchCloud, 168 apollon nodes, Xeon E3-1230 v5, 33 GB RAM, 4 cores
- https://smt-comp.github.io/2026/parallel_track/ — 20 min, 256 vcores, 2 TB; Cloud "not a part of SMT-COMP 2026"
- https://smt-comp.github.io/2026/cloud_track/ — the separately-run AWS side event
- https://smt-comp.github.io/2026/model/ — model syntax for the experimental divisions (`refine-fun`, `root-of-with-ordering`, `root-of-with-interval`, `store`/`const`)

### SMT-COMP 2025
- https://smt-comp.github.io/2025/ — 20th edition
- https://smt-comp.github.io/2025/rules.pdf — **the rules PDF quoted throughout §2** (tracks §3; limits §5.1–5.6; scoring §7; Best Overall §7.3.1; Biggest Lead §7.3.2; Largest Contribution §7.3.3; benchmark selection §6)
- https://smt-comp.github.io/2025/results/ — results index, generated 2025-08-11
- https://smt-comp.github.io/2025/results/qf_bitvec-single-query/ (and 73 sibling division×track pages)
- https://smt-comp.github.io/2025/results/best-overall-single-query/ , .../largest-contribution-single-query/ , .../biggest-lead-single-query/ (and the per-track variants)
- https://smt-comp.github.io/2025/participants/ — 24 entrants
- https://smt-comp.github.io/2025/introduction/ — history of the competition
- https://smt-comp.github.io/2025/model/ — Model Validation Track page
- https://smt-comp.github.io/2025/parallel_track/
- https://smt-comp.github.io/2025/previous/ — edition history

### SMT-COMP 2024 and earlier
- https://smt-comp.github.io/2024/rules.pdf — StarExec→BenchExec; memory 60→30 GB; parallel/cloud→2 min; **"The previously experimental evaluation proof track will be discontinued"**
- https://smt-comp.github.io/2024/results/ — six tracks incl. Cloud
- https://smt-comp.github.io/2024/results/results-cloud
- https://smt-comp.github.io/2024/specs/ — VerifierCloud / 168 apollon nodes
- https://smt-comp.github.io/2024/model.html — proposed model syntax for experimental divisions
- https://smt-comp.github.io/2024/parallel_cloud/
- https://smt-comp.github.io/2023/rules.pdf — **seven tracks incl. the Proof Exhibition Track**; §5.8 "there will be no score computed for this track"; the seven qualitative criteria
- https://smt-comp.github.io/2023/benchmarks.html — the 19 single-query divisions with full logic membership; 113 140 benchmarks
- https://smt-comp.github.io/2023/results.html
- https://smt-comp.github.io/2023/specs.html — StarExec, Xeon E5-2609, 61440 MB cap
- https://smt-comp.github.io/2023/parallel-and-cloud-tracks.html — 100× m4.4xlarge (cloud), 1× m4.16xlarge (parallel)
- https://smt-comp.github.io/2023/model.html
- https://smt-comp.github.io/2022/rules.pdf — **Proof Exhibition Track introduced**; QF_Datatypes split from QF_Equality
- https://smt-comp.github.io/2021/rules.pdf — **Parallel and Cloud tracks introduced**
- https://smt-comp.github.io/2020/rules20.pdf — four tracks only
- https://github.com/SMT-COMP/smt-comp — the `smtcomp` tooling
- https://github.com/SMT-COMP/scrambler — the benchmark scrambler
- https://github.com/SMT-COMP/trace-executor — the incremental-track driver
- https://github.com/sosy-lab/benchexec — the benchmarking framework
- https://gitlab.com/sosy-lab/benchmarking/competition-scripts/ — the competition container image

### Solver documentation
- https://cvc5.github.io/docs/latest/theories/theories.html — the "Standardized" vs "Non-standard or extended" split
- https://cvc5.github.io/docs/latest/theories/finite_field.html — `(_ FiniteField p)`, `(as ffN F)`, `ff.add`, `ff.mul`; prime fields only; Split Gröbner Bases (CAV 2024)
- https://cvc5.github.io/docs/latest/theories/sequences.html — `(Seq S)` and the `seq.*` operators
- https://cvc5.github.io/docs/latest/theories/bags.html — `(Bag S)`, `bag.union_disjoint`, logic string `ALL`
- https://cvc5.github.io/docs/latest/theories/sets-and-relations.html — `(Set S)`, the `FS` logic suffix
- https://cvc5.github.io/docs/latest/theories/transcendentals.html — the `T` logic suffix, `real.pi`, `sin`/`cos`/`tan`/`sqrt`
- https://cvc5.github.io/docs/latest/theories/separation-logic.html — `declare-heap`
- https://cvc5.github.io/docs/latest/theories/datatypes.html

### Proof formats and checkers
- https://cvc5.github.io/docs/latest/proofs/proofs.html — cvc5 emits **CPC, Alethe, LFSC, DOT**
- https://cvc5.github.io/docs/latest/proofs/output_cpc.html — Cooperating Proof Calculus; **Ethos** checker; **Eunoia** framework; trust steps → `incomplete` vs `correct`; `proof-granularity=dsl-rewrite`
- https://cvc5.github.io/docs/latest/proofs/output_alethe.html — Alethe; first implemented in **veriT**; **Carcara** (Rust checker + elaborator); Isabelle/HOL and Coq/SMTCoq reconstruction; coverage = EUF, linear arithmetic, bit-vectors, parts of strings, ± quantifiers
- https://cvc5.github.io/docs/latest/proofs/output_lfsc.html — LFSC = LF + computational side conditions; C++ checker; signature files; `proof-granularity=theory-rewrite`
- https://github.com/ufmg-smite/carcara — Carcara, the Rust Alethe checker/elaborator
- https://github.com/cvc5/ethos — "A Flexible and Efficient Proof Checker for SMT Solvers"
- https://verit.gitlabpages.uliege.be/alethe/ — the Alethe specification site

### Proof literature (DOIs verified against publisher records)
- https://doi.org/10.34727/2024/ISBN.978-3-85448-065-5_8 — **eDRAT**, "Extending DRAT to SMT", FMCAD 2024 (Hitarth, Codel, Lachnitt, Dutertre)
- https://doi.org/10.34727/2022/ISBN.978-3-85448-053-2_12 — **RARE**, "Reconstructing fine-grained proofs of rewrites using a domain-specific language", FMCAD 2022 (Nötzli et al.)
- https://ceur-ws.org/Vol-3185/paper9527.pdf — **RESOLUTE**, SMTInterpol's proof format, SMT workshop 2022 (Hoenicke & Schindler)
- https://doi.org/10.1007/978-3-031-10769-6_3 — "Flexible Proof Production in an Industrial-Strength SMT Solver", IJCAR 2022 (cvc5's internal proof infrastructure)
- https://doi.org/10.1007/978-3-032-32589-1_19 — **Ethos**, IJCAR 2026, LNAI 16688 pp. 305–314, open access CC-BY
- https://doi.org/10.1007/978-3-319-09284-3_31 — **DRAT**, Wetzler, Heule & Hunt, SAT 2014
- https://github.com/cvc5/ethos/blob/main/user_manual.md — the citable **Eunoia** language reference (there is no standalone Eunoia or AletheLF paper)
- https://github.com/cvc5/LFSC — LFSC checker; **no push since 2023-09-14**, and `proofs/lfsc/signatures` has no BV / array / datatype / set signature

### Method note
Result tables in §3 and Appendix A were produced by scraping every division×track results page
under `https://smt-comp.github.io/2026/results/` (95 pages) and
`https://smt-comp.github.io/2025/results/` (74 pages) and parsing the HTML tables directly.
Per-logic benchmark counts in §4.6 come from the `README.md` inside each Zenodo release
record. Logic-set arithmetic in §1.4 and §7 was computed by set operations over those two
sources; no figure in this document was transcribed by hand from prose.

**Not determined / open questions**
- The enforced 2024 memory limit (rules say 30 GB, results pages print `20480`).
- The enforced 2024 Parallel/Cloud time limit (rules say 120 s; results pages and the
  published wall-time sums indicate 1200 s).
- Whether the separately-run AWS "Cloud track of SMT-COMP '26" produced results — its
  deadlines were August 2026 and the participants page shows an empty Cloud column.
- Whether any `QF_FF` (finite field) benchmarks or SMT-COMP division exist: none found in the
  2025 SMT-LIB release or in any SMT-COMP division 2023–2026, but I did not find an explicit
  statement that none exist.
- The IJCAR 2026 Ethos coverage/performance figures (§5.5) were **read, not reproduced**, and
  are the paper authors' own measurement of their own tool. Not independently verified here.
- The "Flexible Proof Production" (IJCAR 2022) entry rests on verified venue/DOI metadata;
  the full text was not read.

---

## Appendix A — SMT-COMP 2025 results, other four tracks

#### Incremental Track

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| arith | LIA, LRA | 11 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| bitvec | BV | 18 | **cvc5** | Bitwuzla | SMTInterpol |
| equality_lineararith | ALIA, UFLRA | 959 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality_machinearith | ABVFPLRA | 4 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| equality_nonlineararith | ANIA, AUFNIRA, UFDTNIA, UFNIA, UFNRA | 2342 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality | UF | 2033 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| fparith | BVFP, BVFPLRA | 10 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| qf_bitvec | QF_BV | 1305 | **Yices2** | Bitwuzla | cvc5 |
| qf_equality_bitvec_arith | QF_AUFBVLIA, QF_AUFBVNIA, QF_BVLRA, QF_UFBVLIA | 1046 | **Yices2** | SMTInterpol | cvc5 |
| qf_equality_bitvec | QF_ABV, QF_AUFBV, QF_UFBV | 1832 | **Bitwuzla** | Yices2 | cvc5 |
| qf_equality_lineararith | QF_ALIA, QF_AUFLIA, QF_UFLIA, QF_UFLRA | 2031 | **SMTInterpol** | cvc5 | Yices2 |
| qf_equality_nonlineararith | QF_ANIA, QF_UFNIA, QF_UFNRA | 512 | **SMTInterpol** | cvc5 | Yices2 |
| qf_equality | QF_UF | 889 | **Yices2** | cvc5 | SMTInterpol |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_BVFP, QF_BVFPLRA, QF_FP, QF_UFFP | 9752 | **Bitwuzla** | cvc5 | — |
| qf_linearintarith | QF_LIA | 69 | **Yices2** | SMTInterpol | cvc5 |
| qf_linearrealarith | QF_LRA | 10 | **OpenSMT** | Yices2 | cvc5 |
| qf_nonlinearintarith | QF_NIA | 119 | **Z3-Inc-Z3++** | SMTInterpol | cvc5 |

#### Unsat Core Track

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| arith | LIA, NIA | 386 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| bitvec | BV | 300 | **cvc5** | Bitwuzla | UltimateEliminator+MathSAT |
| equality_lineararith | ALIA, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, UFDTLIA, UFDTLIRA, UFIDL, UFLIA, UFLRA | 23881 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality_machinearith | ABV, ABVFPLRA, AUFBV, AUFBVDTLIA, AUFBVDTNIA, AUFBVDTNIRA, AUFBVFPDTNIRA, AUFFPDTNIRA, UFBVDTLIA, UFBVDTNIA, UFBVDTNIRA, UFBVFPDTNIRA, UFFPDTNIRA | 4361 | **cvc5** | SMTInterpol | Bitwuzla |
| equality_nonlineararith | ANIA, AUFDTNIRA, AUFNIA, AUFNIRA, UFDTNIA, UFDTNIRA, UFNIA, UFNIRA | 5682 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| equality | UF, UFDT | 2698 | **cvc5** | SMTInterpol | UltimateEliminator+MathSAT |
| fparith | BVFP, BVFPLRA | 15 | **Bitwuzla** | cvc5 | UltimateEliminator+MathSAT |
| qf_bitvec | QF_BV | 2949 | **Bitwuzla** | Yices2 | cvc5 |
| qf_datatypes | QF_DT, QF_UFDT | 400 | **cvc5** | SMTInterpol | — |
| qf_equality_bitvec | QF_ABV, QF_AUFBV, QF_UFBV, QF_UFBVDT | 2470 | **Bitwuzla** | Yices2 | SMTInterpol |
| qf_equality_lineararith | QF_ALIA, QF_AUFLIA, QF_UFDTLIA, QF_UFDTLIRA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 591 | **Yices2** | cvc5 | SMTInterpol |
| qf_equality_nonlineararith | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 266 | **cvc5** | SMTInterpol | Yices2 |
| qf_equality | QF_AX, QF_UF | 2263 | **Yices2** | SMTInterpol | cvc5 |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_BVFP, QF_BVFPLRA, QF_FP, QF_UFFP, QF_UFFPDTNIRA | 13643 | **Bitwuzla** | cvc5 | — |
| qf_linearintarith | QF_IDL, QF_LIA, QF_LIRA | 1069 | **Yices2** | SMTInterpol | cvc5 |
| qf_linearrealarith | QF_LRA | 201 | **OpenSMT** | OpenSMT (min-ucore) | Yices2 |
| qf_nonlinearintarith | QF_NIA, QF_NIRA | 2477 | **Yices2** | cvc5 | SMTInterpol |
| qf_nonlinearrealarith | QF_NRA | 300 | **Yices2** | SMTInterpol | cvc5 |

#### Model Validation Track

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| qf_adt_bitvec | QF_ABV, QF_AUFBV, QF_UFBVDT | 5249 | **Bitwuzla** | cvc5 | SMTInterpol |
| qf_adt_linarith | QF_ALIA, QF_AUFLIA, QF_AX, QF_UFDTLIA, QF_UFDTLIRA | 772 | **SMTInterpol** | cvc5 | — |
| qf_bitvec | QF_BV | 8211 | **Bitwuzla** | Yices2 | cvc5 |
| qf_datatypes | QF_DT, QF_UFDT | 1943 | **SMTInterpol** | cvc5 | — |
| qf_equality_bitvec | QF_UFBV | 475 | **Bitwuzla** | Yices2 | SMTInterpol |
| qf_equality_lineararith | QF_UFIDL, QF_UFLIA, QF_UFLRA | 891 | **OpenSMT** | SMTInterpol | cvc5 |
| qf_equality_nonlineararith | QF_ANIA, QF_AUFNIA, QF_UFDTNIA, QF_UFNIA, QF_UFNRA | 475 | **cvc5** | SMTInterpol | Yices2 |
| qf_equality | QF_UF | 1571 | **OpenSMT** | cvc5 | SMTInterpol |
| qf_fparith | QF_ABVFP, QF_ABVFPLRA, QF_AUFBVFP, QF_BVFP, QF_BVFPLRA, QF_FP, QF_FPLRA, QF_UFFPDTNIRA | 24369 | **cvc5** | Bitwuzla | — |
| qf_linearintarith | QF_IDL, QF_LIA, QF_LIRA | 4895 | **OpenSMT** | Yices2 | SMTInterpol |
| qf_linearrealarith | QF_LRA, QF_RDL | 606 | **Yices2** | OpenSMT | SMTInterpol |
| qf_nonlinearintarith | QF_NIA | 7516 | **Yices2** | cvc5 | SMTInterpol |
| qf_nonlinearrealarith | QF_NRA | 2777 | **SMT-RAT** | cvc5 | SMTInterpol |

#### Parallel Track

| Division | Logics | Benchmarks | Winner | 2nd | 3rd |
|---|---|---:|---|---|---|
| qf_bitvec | QF_BV | 46 | **STP-Parti-Bitwuzla** | Bitwuzla | — |
| qf_equality_bitvec | QF_ABV, QF_AUFBV, QF_UFBV | 47 | **Bitwuzla** | Yices2 | — |
| qf_equality_lineararith | QF_ALIA, QF_UFIDL, QF_UFLIA, QF_UFLRA | 68 | **SMTS** | Yices2 | — |
| qf_linearintarith | QF_IDL, QF_LIA | 89 | **SMTS** | Z3-Parti-Z3pp | Yices2 |
| qf_linearrealarith | QF_LRA, QF_RDL | 62 | **SMTS** | Yices2 | Z3-Parti-Z3pp |
| qf_nonlinearintarith | QF_NIA | 44 | **Z3-Parti-Z3pp** | Yices2 | — |
| qf_nonlinearrealarith | QF_NRA | 44 | **Z3-Parti-Z3pp** | Yices2 | — |