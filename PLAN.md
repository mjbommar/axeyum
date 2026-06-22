# PLAN.md — master index

This is the entry point. The full, end-to-end engineering plan to take axeyum to
**Z3 + Lean parity** lives under [`docs/plan/`](docs/plan/README.md). This file
is the map and the standing rules; **[STATUS.md](STATUS.md)** is the live tracker
(current focus, per-phase state, changelog) and is the only file with mutable
session state.

> The goal is large and deliberately multi-week/multi-month. It is decomposed
> into tracks → phases → tasks, each with concrete reference file paths, sizing,
> and exit criteria, so work can proceed one verifiable increment at a time
> without ever losing the thread. **We do not stop and we do not hand-wave; we
> advance the next task and record it.**

## What "done" means

See [`docs/plan/00-north-star.md`](docs/plan/00-north-star.md) for the full
definition. In one line: **Z3 parity** = feature coverage + competitive
measured performance on the decidable/semidecidable fragments, with honest
`unknown` where undecidable; **Lean parity** = every `unsat`/`valid` result
carries a machine-checkable proof a Lean-grade kernel accepts, produced by an
untrusted search and validated by small independent checkers.

## The two load-bearing fronts

1. **Performance, measured head-to-head (Track 1).** There is no parity claim
   without a clean Z3 comparison on real corpora. **Measured reframe (2026-06-18,
   public p4dfa 113 vs Z3 — see [findings](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md)
   + ADR-0037):** the lever is **word-level *reduction* before bit-blasting**
   (`solve_eqs`/canonicalize/`ite`-handling), *not* lazy bit-blasting — that slice
   is arithmetic-free, so lazy-bv CEGAR is inert (0/113 heavy ops). Reduction moved
   the number 2→7/113. The remaining gap **partitions** into: ~6 *EncodingBudget*
   (deeper reduction pulls them under the encode ceiling — the proven mechanism),
   ~9 *search-bound* (kissat-class CDCL cracks them; batsat/`xor_cdcl`/PBLS all
   miss), and ~90 *large-CNF* (reduction + genuinely hard). **Decision (both in
   parallel):** reduction leads near-term; the proof-producing CDCL core is
   incrementally modernized toward competitive as a slower parallel track. Track
   the honest pulse: **Timeout→decided**.
2. **Reduction certificates (Track 3).** Today only the clausal layer (DRAT) and
   the bit-blast reduction (miter) are independently checked; every other
   reduction is trusted. Certifying them — via an **Alethe emitter** checked by
   the Rust **Carcara** checker — is the critical path to Lean parity.

## The two engineering keystones

- **Incremental e-graph + CDCL(T) loop** (Track 1, P1.4/P1.5). Almost every lazy
  theory and all quantifier work depends on a shared congruence-closure equality
  bus and a theory-propagation loop. Build it once; it unlocks Track 2.
- **Alethe term/proof IR + emitter** (Track 3, P3.2). The format that is
  simultaneously Rust-checkable (Carcara, no C/C++), BV-shaped (matches axeyum's
  lowering and existing miter), and the on-ramp to Lean. Everything downstream in
  the proof track depends on it.

## Track map

| Track | Folder | Theme |
|---|---|---|
| 1 — Engine & Performance | [`track-1-engine/`](docs/plan/track-1-engine/README.md) | SAT inprocessing, preprocessing, SAT-core modernization, e-graph, CDCL(T), theory combination, PBLS, strategy |
| 2 — Theories & Breadth | [`track-2-theories/`](docs/plan/track-2-theories/README.md) | lazy BV, lazy arrays, EUF, LIA cuts (+ unbounded backstop), NRA/CAD, quantifiers, strings, FP polish, datatypes, **breadth backlog** (sequences/sets/sep-logic/finite-fields/co-datatypes/rec-fun) |
| 3 — Proofs & Lean | [`track-3-proof-lean/`](docs/plan/track-3-proof-lean/README.md) | trust ledger, LRAT, Alethe IR+emitter, Carcara-checked QF_BV, embedded checker, reduction proofs, Lean kernel + reconstruction, **Craig interpolation** |
| 4 — Use Cases & Frontend | [`track-4-usecases-frontend/`](docs/plan/track-4-usecases-frontend/README.md) | warm lazy memory, symexec/CFG frontend, OMT/MILP, SMT-LIB command surface, benchmarking & the perf gate, **CHC/Horn (PDR/Spacer)**, **synthesis/abduction** |

Cross-cutting: [`00-north-star.md`](docs/plan/00-north-star.md) (definition of
done), [`01-dependency-dag.md`](docs/plan/01-dependency-dag.md) (the end-to-end
DAG, keystones, critical paths), and
[`references/`](docs/plan/references/README.md) (the distilled top-down review of
Z3, cvc5, bitwuzla, CaDiCaL/Kissat, Carcara, lean4/nanoda, lean-smt that this
plan is built on).

## The gap to Z3/cvc5, itemized (2026-06-21)

A grounded audit against `crates/axeyum-solver/src/capabilities.rs` (the golden
capability ledger) corrected the framing: **the gap is not breadth — it is depth,
maturity, and ~3 missing engines.** axeyum already has *columns* for QF_BV,
QF_ABV, QF_UF, QF_LRA, QF_LIA, UFLIA/UFLRA, QF_NRA/NIA, QF_FP, datatypes,
quantifiers (finite + e-matching + MBQI), strings, optimization, incremental,
symbolic execution, BMC, and k-induction. The honest gap is three things, in size
order:

**1. Depth / completeness on a mostly-complete grid** — most fragments are
`validated`/`sound-incomplete`/`experimental` where Z3 is complete-and-tuned. The
depth ladders are already planned; this audit only sharpens their exit criteria:
- NRA: linear abstraction + McCormick → **nlsat/CAD** — [P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)
  (active; as of 2026-06-22 the **CAD decision side is complete** — N-var algebraic
  critical-point lifting — and the fuzz-measured QF_NRA Unknown rate fell 109→64,
  QF_NIA 498→146, QF_UFLIA 311→18; remaining = proof/Lean evidence for the new
  unsats. Five standing Z3 differential gates clean).
- LIA: **bounded** bit-blast/B&B → **unbounded-complete** (Omega/Cooper backstop) — [P2.4 T2.4.8](docs/plan/track-2-theories/P2.4-lia-cuts.md) (added).
- Strings: bounded BV-lowered → **unbounded** decision procedure — [P2.7](docs/plan/track-2-theories/P2.7-strings.md).
- Quantifiers: maturity of e-matching/MBQI — [P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md).

**2. Performance / maturity** — young SAT core (no inprocessing yet), eager-only
BV (the lazy path is built but inert), thin preprocessing. Already the whole of
Track 1 (SAT inprocessing [P1.1], preprocessing [P1.2], core modernization
[P1.3]); this is tuning depth, not a missing feature.

**3. ~3 categorically-absent engines** — **ALL THREE now addressed (2026-06-22),
each verify-guarded (untrusted search, trusted small checking); depth/fuller
versions remain:**
- **CHC / Horn (PDR/Spacer)** — *unbounded* invariant discovery, the step beyond
  today's bounded BMC + inductive k-induction. The single biggest categorical hole
  vs Z3. [P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md). **OPENED
  (ADR-0048):** verify-guarded single-predicate **IC3/PDR over QF_BV**
  (`prove_safety_pdr`) discovers invariants where k-induction is inconclusive —
  `Safe` only when the discovered invariant passes the 3 implication checks; **MBP
  for LRA** (P2.6-T2.6.6) **landed** as the Spacer predecessor primitive; an **IMC**
  (interpolation-based model checking) consumer of the interpolation API is the next
  slice. Depth: LRA-theory PDR, online LRA solver, multi-predicate Horn core.
- **Craig interpolation** — a feature column *and* CHC's lemma engine; read off
  the already-checked proof. [P3.8](docs/plan/track-3-proof-lean/P3.8-interpolation.md)
  **ENGINE DONE (2026-06-22, ADR-0047):** interpolants land for conjunctive
  **QF_LRA** (Farkas), **QF_UF** (congruence-explanation), **propositional/SAT**
  (McMillan over the LRAT resolution proof), **QF_BV** (joint bit-blast + lifted
  propositional interpolant), and **QF_UFLRA** (Ackermannize → LRA interpolant →
  translate) — every phase-exit fragment, each **verify-before-return** (declines
  rather than emitting anything unverified). Only the SMT-LIB `(get-interpolant)`
  parse surface remains (coordinate `axeyum-smtlib`).
- **Synthesis / abduction (SyGuS, `get-abduct`)** — turns the checker into a
  generator. [P4.7](docs/plan/track-4-usecases-frontend/P4.7-synthesis.md).
  **OPENED (ADR-0049):** `abduct(axioms, conjecture)` — bounded enumeration of
  shared-vocab atoms, each candidate returned only when `check_auto` confirms
  consistency + sufficiency + vocabulary. Depth: SyGuS grammar synthesizing *new*
  atoms, CEGIS, minimality, `(get-abduct)` surface.
- Plus the enumerated **breadth tail** (sequences, sets/bags, separation logic,
  finite fields, co-datatypes, rec-fun) kept *counted*, not forgotten:
  [P2.10](docs/plan/track-2-theories/P2.10-breadth-backlog.md).

**Where axeyum is already ahead:** self-checking evidence (DRAT + Alethe + an
in-tree Lean-grade kernel + universal model replay) — ahead of Z3, competitive
with cvc5. That is the moat and it exists today; the plan's job is to keep
*widening* it (Track 3) while closing depth (Track 2) and adding the three engines.

## How to use this plan each session

1. Read **[STATUS.md](STATUS.md)** — it names the current focus and the next
   task.
2. Open that task's phase file under `docs/plan/track-*/`. Each task lists its
   goal, the reference file paths to read, its size, and its exit criteria.
3. Do the task as a sound, tested, committed increment (the project's normal
   discipline: `just check`, model replay / independent re-check, ADR if it's a
   new public surface or decision).
4. Update STATUS.md (the phase row + changelog). Keep the capability ledger
   (`crates/axeyum-solver/src/capabilities.rs`) and its golden matrix in sync.

## Standing rules (do not violate)

- Default build is **pure Rust, no C/C++**; native/feature-gated leaves only.
- `unsafe_code` is denied workspace-wide; exceptions need an ADR.
- `unknown` is a first-class result; never a wrong `sat`/`unsat`.
- **Graceful `unknown`, never OOM/crash.** Every solving path must degrade to
  `Unknown` under a *deterministic* resource bound — no unbounded memory/time on
  adversarial input. Precedent: sat_bv's pre-lowering oversized-encoding refusal;
  NRA's `MAX_CROSS_PRODUCTS` admission bound (2026-06-19, refuses ≥3 distinct-operand
  cross-products before building lemmas — bounded *or* unbounded, since the blowup is
  inside a single LRA solve call that the wall-clock checks can't intercept). Add a
  bound before adding a feature that can blow up.
- Every `sat` replay-checks; every new `unsat` route gets an independent checker
  or an explicit, ledgered trust note.
- **Build caps:** `CARGO_BUILD_JOBS=4` / `-j4`. Default 16-way parallelism and
  high-`--jobs` benches OOM-kill this host. **Run test/build/bench under the 64 GiB
  memory cap** — `scripts/mem-run.sh <cmd>` (or `just test-guarded`) applies a
  `ulimit -v` so a runaway allocation aborts *that process* instead of OOM-killing
  the host. Override the cap with `MEM_LIMIT_GB=N`.
- **Coordination (multi-agent):** a second agent works `axeyum-rewrite` /
  `axeyum-smtlib` (word-level reduction, P1.2 — the destination-2 near-term lever).
  Treat those crates as theirs; this agent covers measurement, proof/Lean
  (Track 3), breadth/feature-parity (Track 2), and incremental SAT-core
  modernization. Do not edit `canonical.rs` etc. without coordinating.
- **Do not sweep the 41GB public corpus** to "make progress." Measure once on a
  committed slice, then stop.
- Decisions are recorded as ADRs in `docs/research/09-decisions/`.
- Commit trailer:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

## Provenance

The plan was synthesized from a top-down review of the cloned reference solvers
in `references/` (Z3 ~688k LoC, cvc5 ~512k, bitwuzla, CaDiCaL, Kissat, Carcara,
lean4, nanoda_lib, lean-smt, drat-trim) by five parallel Opus sub-agents on
2026-06-15; their full reports are in
[`docs/plan/references/`](docs/plan/references/README.md). axeyum today (2026-06-22)
is **~143k LoC of Rust across 14 crates** with a broad, evidence-backed
decidable+arithmetic foundation (destination 1) — including a complete CAD
decision side for NRA, a competitive pure-Rust proof-emitting SAT core, and
self-checking evidence (DRAT + Alethe + an in-tree Lean-grade kernel + universal
model replay) that already leads Z3. This plan is the route to destinations 2
(Z3-class performance) and 3 (Lean-checkable proofs). Live per-session state is in
[STATUS.md](STATUS.md); the foundation phase history is in the research
[roadmap](docs/research/08-planning/roadmap.md).
