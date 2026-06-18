# Foundational Example & Benchmark Suites

Status: draft
Last updated: 2026-06-17 (rev 2 — educational/double-duty lens added)

## Purpose

Scope and sequence the next wave of *example/benchmark suites* — beyond the
perf-oriented public QF_BV slice and the self-checking
[`axeyum-scenarios`](../07-verification/consumer-scenario-models.md) catalog —
so that "what should we demonstrate axeyum on next" is answered by decidability
and by the [foundational DAG](foundational-dag.md), not by appetite. It surveys
the external corpora worth learning from (SV-COMP, SMT-LIB QF_NRA/MetiTarski,
GeoCoq/Tarski geometry, TPTP) and proposes a tiered, self-checking design that
respects [ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md)
(oracle-free ground truth) and the
[benchmarking methodology](benchmarking-and-performance-methodology.md) (measure
on a committed slice, never sweep). It informs a future ADR (proposed
**ADR-0033**, *foundational example-suite tiers*) and Phase 7's open
"one real client example per audience" exit criterion.

**Second lens (rev 2):** the comprehensive artifacts these suites create should
*double as educational content*. The thesis below
([The educational lens](#the-educational-lens-testing-artifacts-as-curriculum))
is that this is not a separate product but the *same* artifacts viewed through a
second projection — a well-formed self-checking scenario is already a homework
problem with a sound auto-grader and a worked solution. The note records what
makes that true cheaply, and what must stay out of scope to avoid horizon
gravity.

Motivating prompt: *"can we build a 'Hello, World' software-verification suite,
and a 'real analysis 101 / geometry 101 / Peano 101' foundational-math suite?"*
The short answer is that these are **not one idea but three rungs of the ladder**
([north star](../00-orientation/north-star.md)), and only some are reachable as
benchmarks today. This note draws those lines.

## Scope

In scope:

- The candidate suites, their decidability class, and which axeyum capability
  each exercises.
- How each suite establishes oracle-free, self-checking ground truth (the
  ADR-0008 contract) — or an explicit statement that it cannot yet.
- External corpora to mine for shape and yardstick, and the rule against
  ingesting them wholesale.
- A recommended build order and the benchmark-vs-proof-target distinction.

Out of scope:

- Implementation (this note is research-first; no code lands with it).
- Perf-corpus selection for the Z3 head-to-head (that is the
  [benchmarking methodology](benchmarking-and-performance-methodology.md) note).
- A C/binary frontend or a full FOL frontend (neither exists; building one must
  not gate the examples — hand-port small instances instead).

## The decidability lens (the load-bearing distinction)

A suite is only a *useful* axeyum benchmark if axeyum can return a **checkable
decision** on it — `sat` with a replayable model, or `unsat`/`valid` with a
re-checkable certificate. Undecidable problems where the honest answer is
`unknown` measure nothing and invite "horizon gravity" (the roadmap's named
risk). The prompt's three math themes split sharply:

| Prompt phrasing | What it actually is | Decidable? | Axeyum locus | Verdict |
|---|---|---|---|---|
| **Geometry 101** | First-order theory of Euclidean geometry = theory of real-closed fields (Tarski). Incidence, midpoint, Pythagoras as polynomial constraints. | **Yes** (Tarski 1951; complete + decidable) | NRA / **P2.5** (linearization today; CAD/nlsat later) | **Benchmark now** for the existential/algebraic fragment; best near-term math corpus |
| **Real analysis 101** | ε–δ limits, continuity, derivative laws: quantifier alternation over reals + transcendental functions. | General case **no**; the *algebraic-inequality* fragment **yes** via RCF (this is what MetiTarski does) | NRA / **P2.5** for the algebraic fragment | **Partial**: only RCF-reducible inequalities; the limit/continuity layer is Lean-horizon |
| **Presburger ("Peano minus induction")** | Quantified linear integer arithmetic, no multiplication of variables. | **Yes** (Presburger 1929) | LIA + quantifier elimination | **Reachable** but needs QE/MBP axeyum has only in slices; second-tier |
| **Peano 101 (with induction)** | `∀n. n+0 = n`, commutativity of `+`, … require the **induction schema**. | **No** (Gödel; PA is incomplete/undecidable) | **Lean horizon** (P3.6 kernel + P3.7 reconstruction) | **Not a benchmark** — a *proof-reconstruction target* for later |

The trap a naive "Peano 101 / real analysis 101" suite walks into is that most of
its problems are undecidable proof-assistant problems. The reachable, exciting
subset is: **real-closed-field geometry and RCF inequalities** (decidable, and
exactly the corpus P2.5 lacks), plus the **finite/modular** math axeyum already
proves. Induction-bearing arithmetic and the limit layer of analysis belong to
the Lean rung and should be framed as reconstruction targets, not benchmarks.

## Candidate suites

### A. Software-verification "Hello, World" (recommended first)

The canonical small verification tasks — the SV-COMP `ReachSafety` /
`NoOverflows` tier — hand-ported as self-checking scenarios. This fits the
existing machinery almost exactly: `bmc.rs`, k-induction, `symexec.rs`, the
register-VM symbolic executor, and `SafetyCertificate::recheck` are already in
the tree; what is missing is a *named, curated, self-checking corpus*.

- **Safe-by-construction** (the verifier proves safety; UNSAT of the negated
  property, self-checked by bounded enumeration at small width):
  `max(a,b) ≥ a ∧ ≥ b`; saturating-add never wraps; XOR-swap preserves the
  pair; a bounded loop sum equals its closed form; `abs` is non-negative
  *except* `INT_MIN` (a deliberate gotcha that should fail-find).
- **Buggy-by-construction** (the verifier must find a counterexample, replayed
  by concrete re-execution — the ADR-0008 "SAT by execution" route): off-by-one
  array index; signed overflow in `(a+b)` and in the classic binary-search
  `mid = (lo+hi)/2`.
- **k-induction tier** (unbounded safety on tiny transition systems): a bounded
  counter that stays in range; a two-state mutex that never double-locks.

Ground truth is oracle-free exactly as the existing families are: SAT by
concrete execution, UNSAT by exhaustive enumeration at small width / sampled
above it. Yardstick: SV-COMP categories and the `sv-benchmarks` task layout
(YAML task + expected verdict), **hand-ported**, not ingested — there is no C
frontend and building one is out of scope here.

### B. Decidable geometry over real-closed fields (recommended second)

Euclidean geometry statements as polynomial (in)equalities over `Real`: a
genuine, citable math-benchmark family that directly exercises and pressures
**P2.5 (NRA)**, which today has only hand-written tests and no corpus. Examples:
Pythagoras on a coordinatized right triangle; collinearity/incidence; the
midpoint and intercept theorems; "the diagonals of a parallelogram bisect each
other." Each is an existential RCF query (decidable; Tarski), and many reduce to
the linear-abstraction + McCormick + monotonicity machinery P2.5 already has,
with the harder ones marking exactly where CAD/nlsat would pay off.

Ground-truth caveat: unlike the BV families, RCF problems are **not** finitely
enumerable, so ADR-0008's "exhaustive small-width" route does not apply. Two
honest options: (1) carry a **rational witness** for `sat` (verified by the
exact-rational evaluator — fully oracle-free, the preferred route), and (2) for
`unsat`/`valid`, rely on axeyum's own **Farkas/Positivstellensatz-style
certificate** where it exists, marking the rest as oracle-checked (Z3 QF_NRA)
until a native certificate lands. This suite therefore also *defines the
evidence gap* for NRA.

### C. Finite / modular "math 101" (low-cost extension)

Grow the existing `Family::Identity` (de Morgan, two's-complement, full-adder,
XOR-swap) into a richer self-checkable finite-math suite: modular-arithmetic
identities, bit-twiddling theorems (Hacker's-Delight class), small
number-theory-over-`BV(n)` facts (e.g. `x·x` is never `≡ 2 (mod 2^k)` for the
relevant residues). Fully oracle-free *today* (exhaustive enumeration), inside
the lowering subset, and the cheapest of the three to extend. Lower research
novelty, high reliability — a good "always green" growth area.

### D. Peano / real-analysis proof-reconstruction targets (Lean horizon, not now)

A small, frozen set of induction-bearing arithmetic theorems (`∀n. n+0=n`,
commutativity/associativity of `+`) and ε–δ analysis lemmas, kept as **targets
for P3.6/P3.7** (the in-tree Rust Lean kernel and Alethe→Lean reconstruction),
*not* as a benchmark suite. These are where "Lean parity" is demonstrated by
replaying a kernel-checkable proof — sequenced far later, gated by its own ADR,
and explicitly forbidden from starving a foundation phase.

## External corpora (mine for shape and yardstick; do not ingest wholesale)

- **SV-COMP / `sv-benchmarks`** — 33k+ C verification tasks across
  `ReachSafety` (~3.5k), `NoOverflows` (~4.7k), `MemSafety`, `Termination`,
  with per-task YAML + expected verdict. The reference taxonomy and difficulty
  ladder for suite A; hand-port the smallest reachability/overflow tasks.
- **SMT-LIB QF_NRA** — ~12k instances across families incl. **`meti-tarski`**
  (the RCF reduction of transcendental inequalities — the real-analysis-101
  bridge), `kissing`, `hycomp`, `LassoRanker`, `zankl`, economics. Yardstick for
  suite B and a source of difficulty calibration for P2.5.
- **MetiTarski** — proves inequalities over `sin/cos/exp/log/…` by reducing to
  RCF; the concrete template for "decidable real-analysis 101."
- **GeoCoq / Tarski's axioms** — Coq formalization (2800+ lemmas) showing the
  FO theory of Euclidean geometry is consistent, complete, **decidable**, with
  arithmetization to Pythagoras/intercept/nine-point-circle. The provenance and
  correctness reference for suite B's geometry statements.
- **TPTP (TFA/ARI)** — first-order + arithmetic ATP problems; the home of
  induction-bearing and quantified-arithmetic conjectures. Relevant only to
  suite D (Lean horizon) and to eventual quantifier work; SMT-LIB's quantified
  LIA/LRA divisions include `tptp`-derived classes.

## The educational lens: testing artifacts as curriculum

**The double-duty principle.** The architecture that makes an artifact a good
test/benchmark is the same architecture that makes it good educational content.
A self-checking scenario that is *parametric* (seeded), *known-by-construction*,
*evidence-exhibiting*, and *placed in a concept DAG* is simultaneously (a) a
regression test, (b) a benchmark instance, and (c) a homework problem with a
sound auto-grader and a worked solution. We should design every suite artifact
to serve all three: the marginal cost over a pure test is small, and the payoff
is a second product (educational content) that few solver projects can offer
*soundly*.

This is not a bolt-on. axeyum already has the four assets an educational engine
needs and that are otherwise hard to get right:

1. **Sound auto-grading for free — because grading is *trusted checking*, not
   search.** A grader that is trusted must be a small independent checker, not a
   600k-LoC oracle and not an LLM. axeyum's identity (untrusted search / trusted
   checking) *is* a sound auto-grader: a student's candidate answer is graded by
   `eval` (does the witness satisfy?), by `evidence.check`, or by `check_alethe`
   (does the submitted proof step actually entail?). The grader is small,
   independently checkable, and exhibitable. This is the central differentiator;
   it is just ADR-0008 applied to grading.
2. **Procedural generation with a *certified* answer key — because ADR-0008
   already gives two oracle-free constructions.** "Generate a random problem
   whose answer you know" is the crux of procedural homework. SAT-by-execution
   (pick inputs, run forward, the trace is the key) and UNSAT-by-identity
   (instantiate a theorem template, bounded-check) are exactly the two standard
   procedural-content patterns — but with machine-certified keys instead of
   trusted ones. The homework generator *is* the scenario generator.
3. **Difficulty is measured, not guessed.** The pipeline emits layer stats (AIG
   nodes, CNF vars/clauses, CDCL conflicts, solve time) and, for proof
   exercises, an LRAT/Alethe **proof length**. Difficulty tiers can be calibrated
   from real proof complexity rather than heuristics — and proof-step count is a
   natural, axeyum-specific difficulty metric for a *proving* exercise.
4. **The concept DAG already exists as the engineering gate.**
   [`foundational-dag.md`](foundational-dag.md) is a prerequisite graph
   (semantics → IR → evaluator → … → theories → evidence). A curriculum is a
   topological order over a concept DAG; the
   [capability matrix](capability-matrix.md) already tracks what is supported.
   Formalizing the DAG into `concept → {prereqs, exercises, mastery-check}` gives
   **triple duty**: curriculum sequencing + a test-coverage audit (which
   capability cells lack a self-checking exercise?) + the engineering gate the
   project already enforces.

### Angle 1 — using axeyum to *generate* educational content

- **Procedural/random homework with sound auto-grading.** Each suite's seeded
  generator becomes a problem bank; `self_check`/`evidence.check` is the grader;
  the width/depth/round knobs are the difficulty tiers; the produced model or
  proof is the worked solution. All four pieces already exist in
  `axeyum-scenarios` — the missing piece is *rendering* (below).
- **"Fill the proof step" interactive tutor.** Hand a student an Alethe proof
  with a hole (a missing rule or premise) and grade the filled step with
  `check_alethe` — whose resolution entailment is itself re-checked by
  `check_drat`. A proof tutor backed by a real, independent checker, not by
  "looks right." (This reuses the exact machinery already in `axeyum-cnf::alethe`.)
- **Concept sequencing via DAG resolution.** Topo-sort the concept DAG; a
  learner model is the set of mastered nodes; the next problem is drawn from the
  *frontier* (nodes whose prerequisites are mastered); spaced repetition walks
  the DAG. This is the same structured-reasoning task axeyum exists to do.
- **Honest scope (do not overclaim).** The solver *generates, grades, certifies,
  and sequences formal exercises*; it does **not** author conceptual prose or
  pedagogy. The realistic product is human/LLM-written narrative with
  axeyum-certified exercises embedded. For "real analysis 101" specifically,
  only the **RCF-decidable** exercises (suite B) are auto-certifiable; the ε–δ
  conceptual layer is narrative + a Lean-horizon target (suite D).

### Angle 2 — using axeyum to *teach about* logic, proofs, verification, and proof assistants

axeyum is a **glass-box pipeline**: term IR → rewrite → bit-blast → AIG → CNF →
SAT → model/proof, with every layer inspectable (AIGER ASCII, DIMACS, the
evidence envelope). That makes each layer a hands-on lab. The natural course map
follows axeyum's own layers:

- **Logic & SAT 101** — propositional logic → Tseitin CNF → DPLL/CDCL → DRAT
  proofs. Lab: `axeyum-cnf` (watch a formula become clauses; watch a proof come
  back).
- **SMT & theories** — BV, arithmetic, arrays, EUF; eager vs lazy; bit-blasting.
  Lab: the solver, with the layer-stats and export views.
- **Proofs & checking** — DRAT/LRAT/Alethe, Carcara + the internal
  `check_alethe`, the [trust ledger](trust-ledger.md); soundness vs
  completeness; **why we check proofs at all**. The trust ledger is itself a
  teachable artifact: a countable list of what is trusted vs checked.
- **Formal verification & safe software engineering** — suite A's bug zoo: each
  bug class (overflow, off-by-one, `INT_MIN`, double-lock) is a lesson and each
  safe version a contrast; BMC and k-induction as the proof techniques.
- **Foundational math, decidably** — suites B (geometry/RCF) and C
  (finite/modular), each exercise machine-certified.
- **Proof assistants** — the Lean horizon (P3.6 kernel, P3.7 reconstruction): a
  guided tour of kernels, proof terms, and reconstruction, with axeyum's own
  checker as the contrast to a trusted kernel.
- **The limits of automation** — the decidability table in this note is itself a
  lesson: `unknown` is first-class, decidable ≠ provable, search ≠ checking.
  Suite D (Peano-with-induction, undecidable) is reclaimed here as a *lesson
  about undecidability* rather than a failed benchmark — the earlier "trap"
  becomes pedagogy.

### What the educational lens adds to the artifacts (thin, additive, ADR-gated)

Three additive capabilities turn the test suites into educational artifacts with
**no new solver surface and no DAG change**:

1. A **rendering layer** (`Renderable` / `to_problem_statement` / `to_solution`):
   terms and scenarios → human-readable problem statement + worked solution. This
   is the single missing piece between "test artifact" and "homework problem."
2. A **machine-usable concept-DAG artifact**: formalize the prose
   `foundational-dag.md` into `concept → {prereqs, exercises, mastery-check}`.
   Doubles as the test-coverage map above.
3. The **concrete-execution trace artifact** already raised as an open question
   in [consumer-scenario-models](../07-verification/consumer-scenario-models.md):
   the same trace is the step-by-step worked solution.

## Design implications

- **Suite A is the highest-leverage and the cleanest fit**: it reuses
  BMC/k-induction/symexec, satisfies the open Phase 7 verification-audience exit
  criterion, and stays inside the established self-checking contract with no new
  evidence machinery.
- **Suite B forces a real evidence question for NRA** (no finite enumeration; a
  rational witness covers `sat`, but `unsat` needs a native certificate or an
  honest oracle-checked label). That is a feature: it turns the geometry corpus
  into the lever that motivates an NRA certificate, on the proof track.
- **Suite C is a safe, always-green extension** of an existing family; useful as
  filler/regression, low research value.
- **Suite D must be labelled a proof-reconstruction target, never a benchmark**,
  to keep `unknown` out of the benchmark numbers and resist horizon gravity.
- Across all suites the rule holds: **hand-port small instances**; do not build
  a C or FOL frontend to ingest a corpus, and do not sweep.
- **Education is a consumer/lens, not a phase** (destination-3 adjacent in the
  [north star](../00-orientation/north-star.md): a teaching system that the
  evidence-first architecture enables). It may not starve a foundation phase —
  the same horizon-gravity rule the roadmap applies to prover features. Ship
  educational capabilities only as byproducts of artifacts already justified as
  tests/benchmarks.
- **Auto-grading must route through the trusted checker** (`eval` /
  `evidence.check` / `check_alethe`), never "the search returned `sat`." A grader
  that trusts the search is unsound; this is ADR-0008 restated for grading and is
  the property that makes axeyum's grading defensible.
- **Design the artifact for triple duty up front.** A scenario should carry
  `(name, family, params, query, expectation)` *plus* concept-DAG node(s), a
  problem-statement renderer, a solution/evidence renderer, and a difficulty
  knob. The first five exist; the last three are the educational additions and
  are thin, optional, and ADR-gated (no solver-core entanglement).

## Risks

- **Horizon gravity** (roadmap risk, reconfirmed): a "Peano/analysis 101" suite
  framed as a benchmark would be mostly undecidable `unknown`s. Mitigation: the
  decidability table above; suite D is explicitly a target, not a benchmark.
- **Evidence drift for NRA (suite B):** a `sat` rational witness is oracle-free,
  but `unsat`/`valid` currently leans on Z3 QF_NRA. Mitigation: label the
  trust route honestly per instance ([trust ledger](trust-ledger.md)); treat the
  native NRA certificate as the suite's exit lever, not a silent dependency.
- **Self-check cost:** RCF and wider-width verification instances exceed the
  `EXHAUSTIVE_BIT_LIMIT`; enumeration is not a proof there. Mitigation: keep BV
  instances inside the budget; use witnesses + certificates elsewhere; mark
  `Sampled` honestly.
- **Frontend temptation:** suite A "should" parse C, suite B "should" parse a
  geometry DSL. Mitigation: hand-port; defer any frontend to its own ADR.
- **Overclaiming the educational reach:** the solver does not write pedagogy or
  prose; it generates, grades, certifies, and sequences *formal* exercises.
  Mitigation: keep the narrative layer human/LLM-authored; let axeyum certify the
  embedded exercises only.
- **Unsound auto-grading:** the dangerous failure mode is a grader that trusts
  the search. Mitigation: the trusted-checker grading rule above; a grader bug
  then yields a *failed check*, never a wrongly-accepted answer.
- **Education pulling effort off the foundation:** the most likely way this lens
  goes wrong. Mitigation: byproduct-only rule; no educational phase competes with
  a foundation phase for sequencing.

## Open Questions

- [ ] Does suite A become a new `Family::Verification` in `axeyum-scenarios`, or
      a sibling crate (`axeyum-verification-examples`) given it drives
      BMC/k-induction rather than the single-`Query` scenario shape? (Lean toward
      a Family if the single-query contract stretches; a crate if multi-check
      transition systems need first-class support — cf. the existing open
      question on multi-check scenario sequences.)
- [ ] What is the oracle-free `unsat`/`valid` evidence route for suite B before
      a native NRA certificate exists — Z3-checked with a ledgered trust note, or
      hold the suite to `sat`-with-witness instances only at first?
- [ ] Should suite D's reconstruction targets be authored now (as frozen
      `.smt2`/Lean stubs documenting the goal) so P3.6/P3.7 have a fixed target,
      or deferred entirely until that track is entered?
- [ ] Proposed **ADR-0033** scope: ratify the tier split (A/B/C build; D as
      target-only), the per-suite evidence contract, **and the double-duty
      artifact contract** (each artifact carries a concept-DAG node + statement/
      solution renderers + a difficulty knob; grading routes through the trusted
      checker). Author when suite A's first cut is designed.
- [ ] Concept-DAG artifact: extend the prose `foundational-dag.md` in place, or
      add a separate machine-readable file (`concept-dag.toml`/`.json`) that the
      curriculum sequencer and a test-coverage audit both consume? (The latter
      lets a CI check flag capability-matrix cells with no self-checking
      exercise.)
- [ ] Difficulty metric: which solver-effort signal is the calibrated difficulty
      knob per suite — CDCL conflicts and CNF size for BV/verification, Alethe/
      LRAT **proof length** for proof exercises, e-graph/CAD cost for B?
- [ ] Rendering layer placement: a `Renderable` trait in `axeyum-scenarios`, or a
      separate `axeyum-curriculum`/`axeyum-edu` crate once the boundary is proven
      by use (per ADR-0001's "add crates only after a boundary is exercised")?
- [ ] Is a small interactive "fill the proof step" tutor (graded by
      `check_alethe`) worth a standalone example early, as the concrete proof of
      the double-duty thesis?

## Source Pointers

- ADR-0008 (consumer scenario models): ../09-decisions/adr-0008-consumer-scenario-models.md
- Consumer scenario models note: ../07-verification/consumer-scenario-models.md
- Benchmarking methodology: ./benchmarking-and-performance-methodology.md
- Foundational DAG: ./foundational-dag.md
- North star (the ladder): ../00-orientation/north-star.md
- Trust ledger: ./trust-ledger.md
- SV-COMP 2025 benchmarks: https://sv-comp.sosy-lab.org/2025/benchmarks.php
- sv-benchmarks repository: https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
- SMT-LIB benchmarks (QF_NRA division): https://smt-lib.org/benchmarks.shtml
- MetiTarski: https://www.cl.cam.ac.uk/~lp15/papers/Arith/
- GeoCoq (Tarski-axiom Euclidean geometry): https://geocoq.github.io/GeoCoq/
- Tarski's axioms (decidability of elementary geometry): https://en.wikipedia.org/wiki/Tarski%27s_axioms
- TPTP problem library: https://tptp.org/TPTP/
