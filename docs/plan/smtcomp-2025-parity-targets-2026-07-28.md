# SMT-COMP 2025 parity targets — 2026-07-28

**Why this note exists.** Every competitive figure in the current planning spine
— [`full-library-gap-closing-plan-2026-07-22.md`](full-library-gap-closing-plan-2026-07-22.md)
§2 in particular — is drawn from **SMT-COMP 2024**. The
[multi-agent integration diary](multiagent-integration-diary-2026-07-24.md)
recorded the open action: *"pull the per-division SMT-COMP 2025 rankings (UF
single-query, NRA single-query) to set concrete parity targets vs z3/cvc5, and
record the delta here."* This note discharges that action.

**Method.** Figures were read directly off the official per-logic result pages
at `https://smt-comp.github.io/2025/results/`. Percentages marked *(computed)*
are derived here from two counts on the page; they are not printed on the site.
The 2024 figures were independently re-read from the 2024 site rather than
copied from this repository — and the five that this repo already recorded
(QF_ABV, QF_BV, QF_FP, QF_LIA, UFLIA) reproduced **exactly**, which validates
the extraction.

---

## 0. The three findings that change how we talk about parity

### 0.1 Z3 did not compete in SMT-COMP 2025

Plain Z3 entered no division. It appears **only** as mandatory non-competing
*base* entries for derived tools (`Z3-alpha-base`, `z3siri-base`,
`Z3-Noodler-base`, `Z3-Owl-base`), a consequence of the 2025 rule requiring a
derived-tool submitter to also submit its base.

**Consequence for this repository:** "parity with Z3" can no longer be sourced
from a competition ranking. Our Z3 comparison is, and must remain, our **own**
head-to-head against z3 4.13.3 on committed slices — which is exactly what
`bench-results/SCOREBOARD.md` and the p4dfa controls already do. Do not write
"Z3 placed Nth in 2025" anywhere; it did not place.

The base entries are the only proxy, and they are *not* a single canonical Z3 —
`Z3-Owl-base` and `Z3-alpha-base` differ materially on QF_BV (8,541 vs 8,945),
so version/option sets differ per submitter. Treat as indicative only:

| Logic | Z3-as-base | Solved / total | % *(computed)* |
|---|---|---:|---:|
| QF_BV | Z3-alpha-base | 8,945 / 10,703 | 83.6 % |
| QF_BV | Z3-Owl-base | 8,541 / 10,703 | 79.8 % |
| QF_ABV | Z3-Owl-base | 7,433 / 7,574 | 98.1 % |
| QF_FP | Z3-Owl-base | 139 / 275 | 50.5 % |
| QF_BVFP | Z3-Owl-base | 501 / 527 | 95.1 % |
| QF_NIA | Z3-alpha-base | 9,653 / 12,278 | 78.6 % |
| QF_NRA | Z3-alpha-base | 2,847 / 3,104 | 91.7 % |
| QF_SLIA | Z3-alpha-base | 20,398 / 23,730 | 86.0 % |
| QF_S | Z3-Noodler-base | 8,962 / 10,428 | 85.9 % |
| QF_LIA | Z3-alpha-base | 3,998 / 4,825 | 82.9 % |

### 0.2 Lean's `bv_decide` competed in QF_BV — that is our honest peer

`bv_decide` (the Lean 4 bitblasting tactic; contributors include Henrik Böving,
Siddharth Bhat, Tobias Grosser, Clark Barrett) entered QF_BV single query:

| Entry | Solved / 10,703 | % *(computed)* |
|---|---:|---:|
| `bv_decide-nokernel` | 8,862 | 82.8 % |
| `bv_decide` | 8,638 | 80.7 % |
| *(for scale)* Bitwuzla-MachBV, winner | 10,523 | 98.3 % |

Two things follow, and both matter more to this project than the Bitwuzla number:

1. **This is the closest published analogue to axeyum's thesis** — bit-blast to
   SAT, check the result through a small trusted kernel, in a memory-safe
   language. When we state a QF_BV position, `bv_decide` is the peer comparison;
   Bitwuzla is the ceiling.
2. **The kernel-checked variant scores 224 lower than the unchecked one.** That
   is a published, third-party measurement of *what proof checking costs* on a
   real competition corpus — roughly 2.1 points of decide-rate. It is the best
   external evidence we have for sizing the "untrusted fast search, trusted
   small checking" tradeoff, and it should anchor the discussion in
   [`benchmarking-and-performance-methodology.md`](../research/08-planning/benchmarking-and-performance-methodology.md).

### 0.3 There is still no proof-production track — our differentiator is real but uninstitutionalized

SMT-COMP 2025 has **no proof-production or proof-checking track**, and the rules
PDF contains no proof-certificate requirements. The two nearest analogues:

- **Model-Validation Track** — validates *sat* answers mechanically via
  **Dolmen**: the model must satisfy the input and define all and only the
  user-declared symbols. INVALID scores as an error. This is precisely our hard
  rule *"every `sat` must be checkable by evaluating the original term against
  the lifted model,"* externalized as a competition track. We should be able to
  enter it on the fragments we support.
- **Unsat-Core Track** — core *minimization*, not proof checking. Validation is
  by cross-checking against other participants sound in that division: a core is
  validated if strictly more checking solvers say unsat than say sat. Two 2025
  tightenings are in our favor: no points for a core no solver can verify, and
  the verification budget was raised to the generating solver's own time.

**Consequence:** the competition validates *models* mechanically but validates
*unsat* only by solver-majority vote. So no 2024/2025 ranking can be read as
"these solvers produce checkable unsat." Our Lean/Alethe evidence axis (Track 3,
Lane E) is a genuine differentiator rather than a catch-up item — and by the
same token, no external number exists to measure it against.

> Note the direct tension with our own P0-B lesson: the Unsat-Core track's
> validation rule *is* "two untrusted searches agreeing." We rejected exactly
> that standard for our own QF_AUFLIA route (unchecked scalar refutations now
> return `unknown`). We hold the stricter line; that is deliberate.

---

## 1. Per-logic results, SMT-COMP 2025 Single Query

Sequential Correct Score (the ranking number). Percentages *(computed)*.

| Logic | Total | Winner | Solved | % | cvc5 | Bitwuzla |
|---|---:|---|---:|---:|---|---|
| **UF** | 2,857 | cvc5 | 1,158 | 40.5 % | **1st** | not entered |
| **UFLIA** | 2,849 | cvc5 | 1,656 | 58.1 % | **1st** | not entered |
| **UFNIA** | 6,313 | cvc5 | 3,772 | 59.8 % | **1st** | not entered |
| **AUFLIRA** | 1,683 | cvc5 | 1,575 | 93.6 % | **1st** | not entered |
| **AUFDTLIRA** | 4,721 | cvc5 | 4,158 | 88.1 % | **1st** | not entered |
| **QF_SLIA** | 23,730 | Z3-Noodler-Mocha | 23,626 | 99.6 % | 4th, 21,585 | not entered |
| **QF_S** | 10,428 | Z3-Noodler-Mocha | 10,414 | 99.9 % | 4th, 9,016 | not entered |
| **QF_BV** | 10,703 | Bitwuzla-MachBV | 10,523 | 98.3 % | 4th, 9,938 | 2nd, 10,498 |
| **QF_FP** | 275 | Bitwuzla | 255 | 92.7 % | 3rd, 230 | **1st** |
| **QF_BVFP** | 527 | Bitwuzla | 527 | 100 % | tied 527 | **1st** |
| **QF_ABVFP** | 627 | Bitwuzla | 624 | 99.5 % | 2nd, 617 | **1st** |
| **QF_ABV** | 7,574 | Bitwuzla | 7,555 | 99.7 % | 4th, 7,337 | **1st** |
| **QF_NIA** | 12,278 | Z3-alpha | 9,964 | 81.1 % | 4th, 8,508 | not entered |
| **QF_NRA** | 3,104 | Z3-alpha | 2,856 | 92.0 % | 3rd, 2,766 | not entered |
| NRA (quantified) | 99 | SMT-RAT | 96 | 97.0 % | 4th, 87 | not entered |
| QF_LIA *(reference)* | 4,825 | OpenSMT | 4,579 | 94.9 % | 2nd, 4,443 | not entered |

"not entered" is a read-off-the-page absence, not a missing figure.

Where a page shows Solved > Correct Score (e.g. QF_NIA Z3-alpha 10,093 vs
9,964), the sequential score discards results whose **CPU** time exceeded the
wall-clock limit, penalizing parallel solvers. Always cite Correct Score.

**Best Overall (reintroduced for 2025, last used 2018): cvc5, 45.708019**,
winning all five scoring variants. Biggest Lead and Largest Contribution also
cvc5; Largest Contribution UNSAT went to Z3-Noodler-Mocha.

---

## 2. Delta 2024 → 2025

| Logic | 2024 % | 2025 % | Δ pts |
|---|---:|---:|---:|
| UF | 41.20 | 40.53 | **−0.67** |
| UFLIA | 57.14 | 58.13 | +0.98 |
| UFNIA | 58.74 | 59.75 | +1.01 |
| AUFLIRA | 93.23 | 93.58 | +0.36 |
| AUFDTLIRA | 88.84 | 88.07 | **−0.76** |
| QF_SLIA | 98.10 | 99.56 | +1.46 |
| QF_S | 99.84 | 99.87 | +0.02 |
| QF_BV | 98.00 | 98.32 | +0.32 |
| QF_FP | 91.64 | 92.73 | +1.09 |
| QF_BVFP | 100 | 100 | 0 |
| QF_ABVFP | 99.68 | 99.52 | −0.16 |
| QF_ABV | 99.72 | 99.75 | +0.03 |
| QF_NIA | 79.48 | 81.15 | +1.68 |
| QF_NRA | 90.62 | 92.01 | +1.39 |
| NRA | 93.94 | 96.97 | +3.03 |
| QF_LIA | 93.55 | 94.90 | +1.35 |

**The frontier moved by ~1 point per year in most divisions.** That is the honest
rate of progress at the top, and it is the number to keep in mind when sizing our
own increments: the state of the art is nearly static, so a capability gap does
not close on its own while we work on something else.

Structural changes:
- **QF_BV crown moved within the Bitwuzla family** (Bitwuzla → Bitwuzla-MachBV).
  The top three (MachBV 10,523 / Bitwuzla 10,498 / Yices2 10,491) are within 32
  benchmarks of each other out of 10,703 — QF_BV is saturated at the top.
- **STP left QF_BV single query** (2nd in 2024); appears only as
  `STP-Parti-Bitwuzla` in the Parallel Track.
- **QF_S grew 8,867 → 10,428 benchmarks** (+17.6 %); QF_SLIA grew slightly.
- **Quantified block essentially flat**, and cvc5 is uncontested in all five
  quantified logics — on UF the runner-up (iProver, 748) is 410 behind.
- **Cloud Track cancelled** for 2025 (infrastructure); Parallel Track retained.
- Model-Validation gained **experimental** nonlinear-arith, array, and datatype
  divisions (QF_ADT+BitVec, QF_ADT+LinArith are model-validation-only).

---

## 3. Competition configuration (2025) — and why our 300 s runs are not comparable

From the [rules PDF](https://smt-comp.github.io/2025/rules.pdf) (rev. 2025-02-18;
organizers Bobot, Déharbe, Jonáš, Winterer):

- **Time limit: 1,200 s wall clock** per solver/benchmark pair for Single Query,
  Incremental, Unsat-Core, and Model-Validation. Parallel Track: 120 s.
- **Memory: ~30 GB.** (The results pages render `Memory Limit: 30720 GB`, a site
  typo for 30,720 MB. Do not copy that string into repo docs.)
- **Hardware:** BenchExec on SoSy-Lab's cluster, 168 apollon nodes, 4 cores per
  processor; read-only FS with RAM-disk overlay counted against the memory limit;
  no network.
- **Benchmark selection:** everything solved by every solver in under 1 s during
  2018–2024 is **removed**. Divisions are capped at min(n, max(300, 50n/100)) —
  50 % sampling above 600 benchmarks. Scrambled; 2025 seed 757067271, derived
  from the NYSE Composite open on 2025-06-30 (20338.41).
- **Soundness is negative-expected-value by construction.** One wrong answer sets
  e=1 and zeroes n for that benchmark; the best-overall ranking assigns **−2** —
  equivalent to two fully-solved divisions — to any division where the solver
  erred. The rules say so explicitly: *"Entering a possibly buggy solver that can
  solve all benchmarks has a positive expected value if the probability of some
  soundness bug in each of the divisions is below 1/3."* Our DISAGREE = 0 floor
  is the same policy, internalized.
- **Disagreement handling:** on unknown-status benchmarks, if two solvers sound
  on all known-status benchmarks in the division disagree, the benchmark is
  removed from scoring and the disagreement is reported.

### The comparability fix: use the published 24-second score

Our internal runs use a 300 s ceiling; SMT-COMP uses 1,200 s. Rather than scaling
a 1,200 s number — which would be indefensible — note that **SMT-COMP publishes a
24-second score for every division**, computed under the same scoring at T = 24 s
wall clock. For a short-budget head-to-head that is the correct published anchor.

Two standing caveats when using any of these numbers:
1. SMT-COMP corpora are **harder than the raw SMT-LIB logic** because the
   sub-1-second benchmarks are stripped out. Our full-library selection is not.
2. Division totals here are the 2025 *sampled* populations, not the library
   counts in the gap-closing plan §1. Never divide one by the other.

---

## 4. Revised parity targets per lane

Superseding the 2024 figures in
[`full-library-gap-closing-plan-2026-07-22.md`](full-library-gap-closing-plan-2026-07-22.md)
§2, and feeding the lane exits in
[`agent-program-2026-07-28/`](agent-program-2026-07-28/README.md):

| Lane | Target | 2025 anchor | Note |
|---|---|---|---|
| **A** quantifiers | UFLIA | **cvc5 58.1 %** (1,656/2,849) | Up 1 pt from 2024. Still the biggest capability gap; we are near 0 %. |
| **A** quantifiers | UF | **cvc5 40.5 %** (1,158/2,857) | Runner-up iProver is 748. 59 % of the division is unsolved *by anyone* — a new entrant can become non-embarrassing here quickly. Good first target. |
| **A** quantifiers | AUFLIRA | cvc5 93.6 % | Much less headroom than UF/UFLIA — do not start here. |
| **B** strings | QF_SLIA | **Z3-Noodler-Mocha 99.6 %** | Effectively saturated. Parity here means ~100 %, not "competitive." Our curated row is 36 %. |
| **B** strings | QF_S | Z3-Noodler-Mocha 99.9 % | Same; the population grew 17.6 %. |
| **C** floating point | QF_FP | Bitwuzla 92.7 % | Only 275 benchmarks. Note Z3-Owl-base at 50.5 % — FP is a genuine Bitwuzla specialty. |
| **C** floating point | QF_BVFP | Bitwuzla **100 %** (527/527) | Saturated; any residual we carry is ours alone. |
| **F** engine | QF_BV | Bitwuzla-MachBV 98.3 %; **`bv_decide` 80.7 % / nokernel 82.8 %** | Use `bv_decide` as the peer, Bitwuzla as the ceiling. |
| **E** evidence | — | no proof track exists | Model-Validation is enterable today on supported fragments; that is the concrete external validation available to us. |
| — | NRA (quantified) | SMT-RAT 97.0 % | Only 99 benchmarks — a tractable full-coverage target. |

---

## 5. Not obtained

Recorded explicitly rather than estimated:

- **Per-division logic membership** for QF_Strings, QF_FPArith, Equality+*, and
  Arith. Division totals exceed the sum of the logics fetched (QF_Strings by 70,
  QF_FPArith by 171); the division pages do not link their constituent logics.
- **Any competing plain-z3 result** — z3 did not enter. The `-base` proxies in
  §0.1 carry version uncertainty.
- **Bitwuzla placements** in QF_SLIA, QF_S, UF, UFLIA, UFNIA, AUFLIRA,
  AUFDTLIRA, QF_NIA, QF_NRA, NRA — not entered, not missing.
- **2025 Incremental and Parallel track** per-division numbers — out of scope.
- **Raw Zenodo execution data** — the news page says raw execution data and
  scrambled benchmarks upload "in a few days"; not fetched or verified.
- **Tie-break ordering below the winner** for every division — the sequential
  table order was read; sub-winner ties were not separately verified.

## Provenance

Per-logic pages under `https://smt-comp.github.io/2025/results/<logic>-single-query/`;
rules at `https://smt-comp.github.io/2025/rules.pdf`; participants at
`https://smt-comp.github.io/2025/participants/`; best-overall at
`https://smt-comp.github.io/2025/results/best-overall-single-query/`.
2024 figures re-read from the same URL pattern under `/2024/`.
Results generated 2025-08-11; presented at SMT Workshop 2025, Glasgow.
