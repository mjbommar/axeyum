# Axeyum — Master Plan And Status

Single entry point for starting or resuming work. Read this first: it says what
the project is, where it stands, and the **followable roadmap to 100% Z3 + Lean
parity**. Update **Status** and the roadmap checkboxes at the end of every
session. Detailed dated session history lives in git; this file stays a
followable plan, not a changelog.

## What Axeyum Is

A Rust-first automated reasoning stack: typed term IR → rewriting → query
planning → solver backends (a pure-Rust bit-blast-to-SAT path + native SMT
oracles) → models, proofs, and checkable evidence.

Identity in one sentence: **untrusted fast search, trusted small checking** —
every `sat` gets a model checked by evaluation; every `unsat` gets a proof
artifact (DRAT/Farkas/term-level) or an independent oracle cross-check.

North star — a **usable, ideally pareto-dominant system for constrained program
optimization and software verification**, with **symbolic execution and
reachability analysis as first-class use cases**, reached in three destinations:
(1) **foundation** — the decidable + arithmetic core with checkable evidence;
(2) **complete solver replacement** — a drop-in Z3/cvc5-class SMT solver, gated
on *performance on real corpora*, not theory breadth; (3) **Lean / angr as
first-class functionality** — binary frontend + symbolic execution/emulation and
kernel-checkable proving + proof-assistant interop
([north-star](docs/research/00-orientation/north-star.md)).

Honest status: destination (1) is built and broad; (2) and (3) are the roadmap
below. Not yet performance-parity on real corpora (the open gate), not yet full
SMT-LIB breadth (unbounded strings, quantified arithmetic), not yet Lean parity
(reductions are trusted, not yet certified; no Lean proof export).

---

## Status (current state — 2026-06-15)

**Authoritative, golden-tested capability inventory:**
[capability matrix](docs/research/08-planning/capability-matrix.md) (generated
from `axeyum_solver::capabilities::CAPABILITIES`; a test fails if the doc drifts).
Assurance levels: **checked** (independent certificate — DRAT/Farkas/replay),
**validated** (differential vs an oracle), **sound-incomplete** (`unknown`-safe),
**experimental** (lower-assurance / bounded surface).

### By track

**Decidable theory surface — broad, mostly validated/checked:**

| Theory | Status / assurance |
|---|---|
| QF_BV (full scalar set; widths to 2^16) | validated; **UNSAT DRAT-checked** |
| QF_ABV (arrays, eager elim) · QF_UF (Ackermann) · QF_AUFBV | validated; UNSAT DRAT-exportable (modulo trusted reduction) |
| QF_LRA (exact-rational simplex) | **checked** (Farkas) |
| QF_LIA (bit-blast + branch-and-bound simplex) · QF_LIRA (MILP) | validated; bounded UNSAT DRAT-exportable |
| QF_NRA/NIA (abstraction + sign/zero lemmas + McCormick B&B) | sound-incomplete |
| QF_FP — add/sub/mul/div/fma/sqrt/rem/roundToIntegral/conv, F16/F32/F64/**F128** + small formats | validated (differential vs native f32/f64 + `rustc_apfloat`) |
| Datatypes (constructor axioms; elim + native) | validated; folded UNSAT DRAT-exportable |
| Quantifiers (finite-domain expansion + E-matching/MBQI instantiation) | sound-incomplete (complete on finite) |
| QF_S (bounded strings + regex, BV-lowered) | experimental (front-end fragment below) |
| Optimization — MaxSAT / OMT / MILP | experimental |

**Symbolic execution / reachability — first-class primitives** (`IncrementalBvSolver`):
`assert`/`push`/`pop`/`check`/`check_assuming`; `check_assuming_core` →
`AssumptionOutcome::Unsat{core}` (path pruning); `block_model` (all-SAT
reachable-state enumeration); `check_with_memory` (symbolic memory via eager
array elimination, ADR-0030 first slice). Self-checking oracle-free scenarios in
`axeyum-scenarios`.

**Proof / evidence (lean track) — checkable certificates across the BV-reducible
core:** DRAT certificates for QF_BV / QF_ABV / QF_UF / QF_AUFBV / bounded-QF_LIA /
datatypes, flowing through `prove` and `produce_evidence`; Farkas (QF_LRA);
term-level exhaustive certification (small QF_BV); model replay (all `sat`).
Per-layer provenance (`LayerVersions`) localizes replay failures.

**SMT-LIB front door** (`solve_smtlib` and friends): `set-logic`/`set-info`/
`set-option`, `declare`/`define-fun`, `declare-datatype(s)`, `assert` (`:named`),
`check-sat`, `check-sat-assuming`, `push`/`pop`, `get-value`, `get-model`,
`get-unsat-core`, `maximize`/`minimize`. **Bounded strings wired**:
`declare`/literals/`=`/`distinct`, `str.len` (sat-decides), `str.prefixof`/
`str.suffixof`/`str.contains` (both directions), `str.at` (const index),
`str.++` (const fold).

### Honest gaps (what "100%" still needs)

- **Performance** on real corpora — the binding gate for "solver replacement"
  (the pure-Rust path decides a slice of public QF_BV; no measured parity yet).
- **Breadth**: full `str.*` (variable concat/substr/regex/symbolic index),
  unbounded strings, quantified LIA/LRA, warm lazy arrays, parametric sorts.
- **Lean depth**: reductions (bit-blast/Ackermann/array/datatype/int-elim) are
  *trusted*, not certified; no unified proof format / independent kernel / Lean
  export.

---

## Roadmap to 100% Z3 + Lean parity

**What "100%" means (so the goal is well-defined):**

- **Z3 parity** = (i) *feature completeness* on the decidable theories + the full
  SMT-LIB 2 command surface, (ii) *performance parity* on real corpora, and
  (iii) on the *undecidable* fragments (general quantifiers, unbounded nonlinear,
  unbounded strings) **matching Z3's heuristic behavior with honest `unknown`** —
  decidability where none exists is not a gap.
- **Lean parity** = every result is **independently kernel-checkable** and
  **exportable to a proof term the Lean kernel accepts**, trusting only a small,
  ideally formalized kernel.

### Dependency DAG

```
 TRACK A — Z3 breadth & performance            TRACK B — Lean / proof depth
 ─────────────────────────────────             ───────────────────────────
 A0 decidable foundation  [DONE]               B1 DRAT across BV-reducible
        │                                          core + prove/evidence [DONE]
        ├──────────────┬───────────────┐               │
        ▼              ▼               ▼               ▼
 A1 performance   A2 warm-lazy    A6 SMT-LIB      B2 reduction certificates
    parity           arrays          command          (bit-blast/Ackermann/
    (the gate)       (sym memory)    surface           array/dt/int) ★ lever
        │              │               │               │
        │              ▼               │               ▼
        │         A3 theory-comb ◄─────┘          B3 unified proof format
        │            core CDCL(T)                    + independent kernel
        │            │     │                          │
        │            ▼     ▼                          ▼
        │   A4 full strings  A5 quantifier      B4 Lean proof-term export
        │   (typed results)     instantiation        │
        │            │          + quant. arith       ▼
        │            │                           B5 kernel formalization
        ▼            ▼                              (research)
 A7 nonlinear maturity (sound-incomplete)

 TRACK C — use-case capstones (ride A/B)
 ───────────────────────────────────────
 C1 symbolic-execution/reachability API + BMC driver   (needs A2)
 C2 angr/unicorn-class binary frontend + memory model  (needs C1, A2)
 C3 constrained-optimization (OMT lexicographic/Pareto, MILP hardening)
 C4 Lean / proof-assistant interop as a product        (rides B4/B5)
```

**Critical path to feature+perf Z3 parity:** A1 (perf) ∥ A2 (arrays) → A3 (theory
combination) → A4 (strings) ∥ A5 (quantifiers) → A6 (commands).
**Critical path to Lean parity:** B2 (reduction certs) → B3 (unified proof +
kernel) → B4 (Lean export) → B5 (formalized kernel).
**B2 is the single highest lever** — until reductions are certified, no amount of
clausal proof closes the trusted base.

### Track A — Z3 breadth & performance

- [ ] **A1 — Performance parity (the binding gate).**
  - [ ] Honest baseline doc: decided-instance count + PAR-2 vs Z3 on a *fixed*
        public QF_BV slice (OOM-safe: `--jobs 1`, guarded budgets — see memory
        `avoid-public-benchmark-runs`). No progress claims without this number.
  - [ ] Encoding/preprocessing + SAT-core work the
        [methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md)
        gates on; targeted CaDiCaL/Kissat comparison over Axeyum-generated CNF.
  - **Exit:** decide *most* of a public QF_BV family within ~2–5× Z3 at 1–10 s.
- [ ] **A2 — Warm lazy arrays** (ADR-0030 deferred half). `select`/`store` kept
        first-class in the warm engine; read-over-write + congruence axioms
        discharged lazily as selector-scoped CNF lemmas (reuse learned clauses).
  - **Exit:** incremental QF_ABV decides without per-`check` re-elimination;
        differentially checked vs the eager eliminator. Unblocks fast C1.
- [ ] **A3 — Theory-combination core (CDCL(T) / Nelson–Oppen).** Replace
        reduction-based composition where it pays; integrated theory propagation
        + cross-theory conflict learning.
  - **Exit:** arrays+UF+arithmetic in one query without eager reduction; the
        **BV+LIA gap closes** (e.g. `str.len` unsat decides, not `unknown`).
- [ ] **A4 — Full string front end** (ADR-0029, typed results). The parser's
        result type carries `Term | Str` (or relocate `BoundedString` to a shared
        crate): `str.++`/`substr`/`replace`/`at`(symbolic)/`in_re`/regex,
        `get-value` string decode, configurable bound. Symbolic-index / `str.len`
        unsat ride on A3.
  - **Exit:** a QF_S benchmark fragment (incl. variable concat + regex) solvable
        from SMT-LIB text.
- [ ] **A5 — Quantifier instantiation maturity.** Production E-matching
        (trigger selection) + MBQI; quantified LIA/LRA (needs A3).
  - **Exit:** match Z3's heuristic coverage on a quantified set; honest `unknown`
        elsewhere.
- [ ] **A6 — SMT-LIB command/surface completeness.** `declare-sort`/`define-sort`
        (parametric/polymorphic), `reset`/`reset-assertions`, `echo`,
        `get-assignments`, `get-proof` (wires Track B), full `set-option`
        honoring, `get-model` formatting.
  - **Exit:** full SMT-LIB 2.6 command set parses and responds.
- [ ] **A7 — Nonlinear maturity** (sound-incomplete). Better McCormick/interval
        tightening; a CAD-style procedure for decidable sub-fragments.
  - **Exit:** match Z3's heuristic decide-rate on an NRA/NIA set; honest
        `unknown` elsewhere.

### Track B — Lean / proof depth

- [x] **B1 — DRAT across the BV-reducible core, through `prove`/`produce_evidence`**
        (+ Farkas for LRA, term-level for small QF_BV, model replay; capability
        ledger + per-layer provenance). Done this session.
- [ ] **B2 — Reduction certificates (the critical lever).** Emit, per reduction
        (bit-blast term→AIG→CNF, Ackermann for UF, read-over-write for arrays,
        datatype/int elimination, FP circuit lowering), a certificate that the
        step preserves (equi)satisfiability, independently checkable.
  - **Exit:** a checker validates *reduction certs + DRAT* end-to-end; the
        trusted base shrinks to {ground evaluator, clausal/Farkas kernel}.
- [ ] **B3 — Unified proof format + independent kernel.** Combine clausal
        (RUP/RAT), theory (Farkas / congruence / array axioms), and reduction
        certs into one artifact; a minimal kernel checks it. Evaluate Alethe
        (e.g. `carcara`) / LFSC / a custom format.
  - **Exit:** one proof object, one independent kernel, end-to-end for the
        BV-reducible core.
- [ ] **B4 — Lean proof-term export.** Elaborate the unified proof into a Lean
        term the Lean kernel accepts (lean-smt / `Smt`-tactic style).
  - **Exit:** Axeyum emits a Lean-checkable proof for the BV-reducible core;
        round-trip test.
- [ ] **B5 — Kernel formalization** (research). Prove the checker sound in Lean;
        name and minimize the trusted base.

### Track C — use-case capstones

- [~] **C1 — Symbolic execution / reachability as a first-class API + BMC
        driver** over the incremental engine (path pruning + all-SAT + symbolic
        memory). *BMC driver landed* (`bounded_model_check` over a
        `TransitionSystem`: warm unrolling, replay-checked counterexample traces,
        honestly-bounded unreachability — array-free BV/Bool first slice).
        *k-induction landed* (`prove_safety_k_induction`: base case + inductive
        step ⇒ unbounded `Safe`, counterexample, or honest `Inconclusive`).
        *Symbolic-memory BMC landed* (`bounded_model_check_with_memory`: array
        state via eager elimination, one-shot per depth). *Certified k-induction
        landed* (`certify_safety_k_induction`: a `Safe` verdict carries a
        drat-trim-checkable DRAT certificate per obligation — the reachability
        track meeting the proof/checking track). Remaining: warm lazy arrays for
        memory BMC + memory k-induction (rides A2), interpolation / invariant
        strengthening for k-induction completeness, and a CFG-shaped
        path-explorer API.
- [ ] **C2 — angr/unicorn-class** binary/IR frontend (lift + CFG), real memory
        model, concrete-emulation cross-check. Needs C1 + A2.
- [ ] **C3 — Constrained optimization**: OMT lexicographic/Pareto; MILP hardening.
- [ ] **C4 — Lean / proof-assistant interop as a product** (rides B4/B5).

### Honest-incompleteness boundary (not "gaps")

Complete quantified FOL / MBQI, unbounded-nonlinear completeness, and
unbounded-string completeness are **undecidable**. The target there is to match
Z3's *heuristic behavior and resource honesty* (sound, `unknown`-safe), not to
achieve decidability. Lean parity's B5 (formalized kernel) is genuinely
greenfield/multi-month research.

---

## How To Resume Work (for a human or an agent)

1. Read **Status** and the **Roadmap** above; pick the next unchecked item on the
   critical path (A1/A2/B2 are the current fronts).
2. Read the [roadmap notes](docs/research/08-planning/roadmap.md) and the
   [foundational DAG](docs/research/08-planning/foundational-dag.md) before adding
   operators, rewrites, encodings, backends, evidence artifacts, or logic
   fragments.
3. Decisions close as ADRs, not silent code: check
   [open questions](docs/research/08-planning/research-questions.md) and
   [decision records](docs/research/09-decisions/README.md) (30 ADRs, all
   accepted).
4. Update the [capability ledger](crates/axeyum-solver/src/capabilities.rs) when
   you add/strengthen a capability — the matrix doc regenerates from it and is
   golden-tested.
5. When a session ends: update **Status** and check off / re-order roadmap items.
   Run `just check` or `./scripts/check.sh` (fmt + clippy + test + doc + links).

## Standing Rules

- The pure-Rust core builds with **no C/C++ dependency**; native backends (Z3) are
  feature-gated leaf crates.
- Semantics, model/proof lifting, and replay/checker routes must be explicit
  before a new operator, rewrite class, encoding, backend, or logic fragment
  becomes public surface. **No first-class FP op exists** — the evaluator runs the
  same lowered circuit the solver does, so a wrong FP/string/array circuit is not
  caught by replay: every such circuit must be differentially validated against an
  oracle, and unvalidated formats are refused (`enabled ⟹ validated`).
- Every transformation layer ships with its check (evaluator equivalence, round
  trips, lift maps) and a differential test once an oracle exists.
- Expensive bets are gated by the
  [benchmarking methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md).
- `unknown` is a first-class result; budget exhaustion reports `ResourceLimit`
  (retryable) vs `Incomplete` (fundamental). Determinism (same input/seed → same
  output) is a public API promise.
- Build discipline on this host: cap parallelism (`CARGO_BUILD_JOBS=4`); do not
  sweep the 41 GB public corpus (OOM hazard).

## Map

| Where | What |
|---|---|
| [capability matrix](docs/research/08-planning/capability-matrix.md) | Golden-tested inventory: capability × assurance × evidence × ADR. |
| [docs/research/README.md](docs/research/README.md) | Research index and reading order. |
| [roadmap.md](docs/research/08-planning/roadmap.md) | Phased plan notes with exit criteria and gates. |
| [foundational-dag.md](docs/research/08-planning/foundational-dag.md) | Logic/math dependency DAG and layer contracts. |
| [research-questions.md](docs/research/08-planning/research-questions.md) | Open question register. |
| [decisions/](docs/research/09-decisions/README.md) | ADRs (30, all accepted): how questions get closed. |
| `crates/` | `axeyum-ir`, `axeyum-aig`, `axeyum-bv`, `axeyum-cnf`, `axeyum-fp`, `axeyum-query`, `axeyum-rewrite`, `axeyum-scenarios`, `axeyum-solver`, `axeyum-smtlib`, `axeyum-bench`. |
| [CLAUDE.md](CLAUDE.md) | Agent guidance: session protocol, commands, hard rules. |
| [references/](references/README.md) | Gitignored reference clones; `scripts/fetch-references.sh`. |
