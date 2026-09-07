# The competition and benchmark landscape, surveyed 2026-09-06

Four parallel research passes, each written by a separate agent from primary
sources, on the arenas this project could be measured in and the yardsticks it
should measure against. The four catalogs are reference material; **this file
is the part that changes what we do.**

| Catalog | Covers |
|---|---|
| [SMT-LIB and SMT-COMP](smt-lib-and-smt-comp.md) | all ~90 logics, every track 2022-2026, per-division standings, model validation, the benchmark release |
| [SAT-family competitions](sat-family-competitions.md) | SAT Competition, MaxSAT, model counting, QBF, pseudo-Boolean, proof-logging movement |
| [Adjacent reasoning arenas](adjacent-reasoning-arenas.md) | CHC-COMP, SyGuS, CASC/TPTP, proving benchmarks, termination/confluence, HWMCC, SV-COMP, CAS, OMT |
| [Reference solvers and proof formats](reference-solvers-and-proof-formats.md) | solver landscape per theory, DRAT/LRAT/Alethe/LFSC/CPC/VeriPB, scoring conventions, reusable result data |

**Provenance discipline.** Every claim in the four catalogs carries `[C]`
(read from a primary source), `[M]` (computed by the agent from a downloaded
result dump, with a reproduction recipe), or `[I]` (inferred or read only as a
search snippet). Counts at time of writing, by file:

| Catalog | `[C]` | `[M]` | `[I]` |
|---|---:|---:|---:|
| SAT-family competitions | 319 | 0 | 16 |
| Adjacent reasoning arenas | 112 | 0 | 40 |
| Reference solvers and proof formats | 82 | 40 | 10 |
| SMT-LIB and SMT-COMP | 67 | 0 | 32 |
| **Total** | **580** | **40** | **98** |
**`[I]` is not evidence** — treat it the way this repo treats a grep with no
positive control. Where a catalog quotes a published table, it says who
measured it; one prominent coverage table is a checker's own authors measuring
their tool against competitors, and is labelled as such in the body rather
than a footnote.

**Independently re-verified by the coordinator before this landed** (the rest
is the agents' own work, at the confidence their tags claim): that SMT-COMP
2026 lists no proof track; that the SyGuS benchmark repository has competition
directories for 2017-2019 only and last saw a commit in March 2023; that the
eDRAT paper exists with the authors and year cited; and every claim below
about *our own* code.

---

## 1. What this survey changes

### 1.1 Our reference solvers are not the frontier in six of eleven divisions

From the 2026 per-benchmark results, computed rather than quoted: **OpenSMT
and Yices2 lead QF_LRA, QF_LIA, QF_UF, QF_AX and QF_RDL; SMTInterpol leads
QF_UFLIA, QF_ALIA and QF_ANIA; Z3-Noodler leads the string logics.** cvc5's
lead is in the *quantified* and datatype logics. Bitwuzla remains correct for
BV/ABV/FP.

Consequence for [the parity plan](../../../plan/smt-parity-plan-2026-09-05.md):
the board's gap of 251 files is measured against a reference that is itself
behind the frontier in most arithmetic and equality divisions, so **the
distance to actual dominance is larger than the board states.** This is a
methodology finding, not a solver finding. It does not invalidate any measured
number — every ledger entry names its reference and its version — but the
phrase "parity" in those divisions means parity with cvc5, and the plan's §5
stop conditions inherit that. Fixing it means adding a second reference per
division, not replacing one.

### 1.2 There is no proof-exhibition venue in SMT

SMT-COMP introduced a Proof Exhibition track in 2022, ran it again unranked in
2023, and **discontinued it in 2024** — the 2024 rules give the reason verbatim
("we were unable to find a way of turning the proof track into a competition
that would…"); the 2025 and 2026 rules do not contain the word.
(One line in the [reference-solver catalog](reference-solvers-and-proof-formats.md)
said "since 2023"; corrected 2026-09-06. The 2024 rules PDF is the authority.)
So "we would win proof exhibition" is not a claim anyone can make. The
available honest framings are: an entry in the **SAT Competition main track**,
where a DRAT certificate is mandatory and a wrong one is disqualification
rather than a score penalty; a **trusted-base comparison** against cvc5's
published checker sizes; or a **head-to-head on QF_BV against a kernel-checked
pipeline**, for which there is now a public reference cost (§1.3).

This *strengthens* rather than weakens the uncontested-axis argument in
[the cost model](../../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md):
the axis is uncontested because the venue was abandoned for being too hard to
adjudicate, not because nobody values it.

### 1.3 The cost of certification is now publicly measured, and it is not the checker

Lean's bitvector pipeline entered SMT-COMP 2026's QF_BV division **twice**,
with and without kernel checking, which isolates exactly our design question:

| | result |
|---|---|
| kernel-checked pipeline, 20-minute limit | 2401 / 2540 (94.5%) vs Bitwuzla 2475 (97.4%) |
| cost of the kernel check itself | **median +6.9%** wall time (p90 2.05x) |
| cost of the certified pipeline overall | **median 8.7x** slower than Bitwuzla |

Corroborated by cvc5's own numbers: proof-producing mode costs 17.1% overall
and 11.94x on bit-vectors specifically, the worst of any category, while
strings are cheapest at 1.75x.

**Trusted checking is cheap; proof-*producing search* is what costs.** That is
the strongest external evidence for "untrusted fast search, trusted small
checking" that exists, and it also says where the engineering has to go. Our
[ADR-1704](../../09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
should carry these numbers.

### 1.4 Our proof contract has published prior art we do not cite

**eDRAT** ("Extending DRAT to SMT", Hitarth / Codel / Lachnitt / Dutertre,
FMCAD 2024) is the published form of ADR-1704's two-stream design: a
propositional refutation below, theory lemmas above. ADR-1704 cites no prior
art at all. It should, and the comparison is cheap: either we made a choice
they rejected, or we independently reached theirs.

**Its stated limitation is our gap.** eDRAT does not cover *preprocessing*
proofs (`[I]` — read from the PDF by the agent, not re-verified). `axeyum-rewrite`
**is** preprocessing. In the rewrite crate today, `RewriteRuleId` is documented
as being for "logs and future certificates" and `ProofObligation` as a "future
proof obligation checked outside the rewriter" — the placeholders exist and
nothing produces them. So every canonicalization, array elimination, int-blast
and quantifier expansion is a hole in the certificate chain, the literature
does not hand us a solution, and **this gap is invisible on the parity board,
which counts decisions rather than evidence.**

Related: cvc5 needs a whole DSL (RARE) and a granularity flag for rewrite
justification, which says a from-scratch producer loses proof coverage on
rewrite steps before anywhere else. Design the manifest for that now.

### 1.5 LFSC is settled as legacy, on structural evidence

The `cvc5/LFSC` repository has had no push since 2023-09-14 and its signature
directory contains **no bit-vector, array, datatype or set signature**. A
checker whose signatures omit bit-vectors cannot check QF_BV proofs. The live
choices are cvc5's native format (checked by Ethos, ~10k + ~8k lines of
trusted base) and **Alethe** for interoperability — with the caveat that the
Alethe spec describes itself as *evolving*, a standing maintenance cost.

### 1.6 We are far closer to the SAT Competition than assumed

We ship forward and backward DRAT checking, streaming variants with resource
limits, LRAT checking and writing, DRAT-to-LRAT elaboration in both
directions, XOR-DRAT and cube certificate composition. **Verified in-tree,
three specific things are missing:**

1. **No competition CLI** that takes a `.cnf` path and emits the competition's
   expected stdout/proof-file contract.
2. **Binary DRAT is absent** — `crates/axeyum-cnf/src/drat.rs` contains zero
   occurrences of "binary". The competition's own output spec puts binary at
   ~3x smaller files.
3. **The LRAT elaborator is RUP-only** and its module doc says it "rejects" an
   input requiring RAT — which is what inprocessing produces.

None is large. GRAT and dpr-trim consume DRAT directly, so no new format is
strictly required to enter.

### 1.7 Two arenas already run our architecture; one is a near drop-in

**Termination and confluence** competitions have required certification for
years: every tool submits an uncertified and a certified configuration, and
only answers a verified checker re-confirms score. One prover recovers 946 of
its own 1030 answers under certification, an ~8% certified gap. The confluence
competition scores the *checker* and the *prover* as separate categories on the
same problems, which is the scoring model our two-axis metric implies.

> **Do not compare that ~8% to our axiom-footprint number** (corrected
> 2026-09-06 after axeyum-08 caught the error; the first draft of this file
> called it "exactly the number our flywheel produces", which is false in both
> directions). **The two measure different things.** Theirs is answers whose
> proof their checker *cannot check at all*. Ours is checked facts whose
> footprint is *non-empty* — a named assumption, not an unchecked answer.
> Counted directly from `artifacts/facts/` on 2026-09-06: **2,692 proved facts,
> 2,584 with an empty axiom footprint, 108 with a non-empty one**; of those 108,
> 49 are witness-replay, 24 kernel-term, 19 exhaustive-enumeration and 16
> unsat-certificate, and the axioms they name are mostly semantic bridges
> (`cas.exact-rational-polynomial-normal-form` 31,
> `classical-two-valued-bool-semantics` 16,
> `geometry.cartesian-coordinatisation-of-the-euclidean-plane` 13) rather than
> gaps in checking. The denominator moves as lanes land, so re-count rather
> than quoting these. **No dominance claim survives the comparison**, and the
> repo's own rule applies: two audits that do not share a denominator cannot be
> quoted against each other without checking the method first
> ([evidence-and-checker-discipline](../../../contributor-guide/evidence-and-checker-discipline.md)).

**HWMCC's bit-level track was independently picked as the best fit by two of
the four agents**: input is AIGER 1.9, which `axeyum-aig` already exports; the
mandatory certificate *is* an AIG; checking it is five SAT calls. When
certificates became mandatory in 2024 participation went from 3 entrants to 9,
and the winner beat the previous uncertified champion with every certificate
verified.

### 1.8 Four of the arenas I would have sent someone to do not exist

- **SyGuS-Comp** is dormant (last edition 2019; benchmarks live and unclaimed).
- **There is no computer-algebra competition.** What exists is an independent
  scoreboard of ~107k integration problems across 9 systems (Mathematica 97.4%,
  Rubi 93.1%, SymPy 42.2%). **Not one entrant emits a certificate.**
- **OMT has no adopted standard** — SMT 2025's own proposal paper says so.
- **No arena exists for verified rewrite rules or certified CAS results.**

Each is an opening rather than a gap, given we have a CAS that produces
certificates and a kernel that can check them.

### 1.9 Method corrections to adopt

- **SMT-COMP does not use PAR-2.** It uses a lexicographic `⟨error, solved,
  wall, cpu⟩` tuple. We use PAR-2 (which is the SAT Competition's measure).
  Both are defensible; the divergence should be stated wherever we report.
- **Per-benchmark results for 2018-2026 are downloadable** (12-22 MB gzipped
  JSON at a stable URL pattern), and SMT-COMP's own tooling contains the
  reference scoring implementation. Future head-to-heads need not re-run
  reference solvers on our hosts at all.
- **Single-oracle differential testing is unsafe in strings and FP**, measured:
  103 of 45,905 benchmarks had a sat/unsat split among 2026 entrants, 79 of
  them in one string logic, and the FP disagreements split bit-blasting solvers
  against an interval solver. Our string and FP fuzzing needs two oracles.
- **Cross-year solved-counts do not transfer** (2025 selected 129,361
  benchmarks; 2026 selected 45,905).

### 1.10 Peers now exist that did not

Two Rust projects state something close to our thesis: one a pure-Rust
certificate-checked QF_BV solver whose verified LRAT checker is "the sole
trusted component", one a pure-Rust Z3 reimplementation with our crate
decomposition. Separately, **CreuSAT** is a Creusot-*verified* CDCL solver in
Rust — the other route to a trusted answer. Our choice of the certificate route
over the verified-solver route is currently implicit and deserves an ADR
paragraph.

---

## 2. Cheapest unentered targets, ranked by fit to what we already have

| Rank | Target | Why it is cheap | What it needs |
|---|---|---|---|
| 1 | **QF_NRA / NRA** | Divisions of SMT-COMP itself; same format, same harness, existing parity runner; ~12k files in our corpus | a committed 200-file list and a reference (Z3-GEX / SMT-RAT lead) |
| 2 | **The QF combination logics** (QF_UFLRA, QF_UFBV, QF_AUFLIA, QF_UFIDL, QF_AX) | Compose theory solvers we already ship; several are near-saturated for everyone, so they test correctness not power | lists + references (Yices2 / OpenSMT / SMTInterpol) |
| 3 | **SAT Competition main track** | §1.6: the checkers exist; the gap is a CLI, binary DRAT, and RAT in the elaborator | three small slices |
| 4 | **HWMCC bit-level** | §1.7: AIGER in, AIG certificate out, five SAT calls to check | a model-checking front end; the certificate half is closest to done |
| 5 | **Model validation track** | Already a track we could enter with the model-replay machinery we have | the SMT-LIB model output format and the official validator |
| 6 | **QF_FP** | `axeyum-fp` exists; 40k files in the corpus | list + reference (Bitwuzla / COLIBRI, and **two** oracles per §1.9) |

Not recommended without a labelling audit: the competition-style *proving*
benchmarks, where one widely used set is reported to have a high rate of
mis-stated problems.

---

## 3. Open questions this survey could not close

- No authoritative published figure exists for DRAT proof-logging slowdown in
  CaDiCaL or Kissat. **That is a cheap and genuinely publishable experiment we
  are positioned to run.**
- Two internal conflicts in the 2024 SMT-COMP rules (memory limit, parallel
  wall limit) are recorded in the SMT-COMP catalog's "not determined" section
  rather than smoothed over.
- Whether eDRAT's preprocessing limitation is stated as strongly as reported
  needs a read of the PDF by whoever picks up the rewrite-certificate work.
