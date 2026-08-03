# Phase 6 — parallel search, cube-and-conquer, and the compute story

Verdict from review: **the capability claim is correct; two supporting facts were
wrong; and the right position is build the splitter natively, delegate the conquer
phase to external solvers as untrusted engines, and keep all checking native.**

**Contains gate G3**: calibrate target selection to the reachable compute band
before scheduling any run.

## What holds and what was wrong

**Holds:** there is no lookahead solver, no cube generator, no splitting
orchestration, and no in-solver parallelism anywhere in the workspace. Every
landmark SAT-cracked conjecture used cube-and-conquer; none was in reach of a
single sequential CDCL run. For the open-problem track this is a hard prerequisite.
For *dispatch* it is not — portfolio-with-deadline is the cheap win there, and
`beyond-bit-blasting.md:39-41` already says so.

**Wrong 1:** cube-and-conquer appears **three times** in
`docs/research/05-algorithms/beyond-bit-blasting.md` (line 41 prose, line 53
technique table with prerequisite "Custom or cooperative SAT core", line 87 source
pointer to Heule's cube.pdf, plus a Mallob pointer at line 88), not once.

**Wrong 2:** the CDCL core's standing **is partially measured, and it cuts both
ways.** ADR-0220/0221 (STATUS.md:5740-5760, PLAN.md:2126-2141) ran 244 exported
UNSAT CNFs through BatSat, the proof core, Z3 Boolean, and **Kissat 4.0.4** with
full agreement; the proof core is 2.627× faster than fresh BatSat with all DRAT
rechecking. But PLAN.md:8381 records ~9 public QF_BV instances explicitly
*search-bound* where kissat-class CDCL cracks them and batsat/`xor_cdcl`/PBLS all
miss. The methodology doc gates core tuning on exactly this gap.

## The repo has far more than the branch credited

`crates/axeyum-cnf` is **24,836 lines across 18 modules**:

- `proof_sat.rs` (2,091 lines): 1-UIP, two-watched literals, **Luby + Glucose EMA
  glue restarts + blocking restarts** (:43-91), phase saving + target rephasing
  (:227-230), `reduce_db` with additive budget. `solve_with_drat_proof_with_limits`
  (:152) checks the deadline on a **deterministic conflict cadence** (:29-30,
  700-705), so the conflict budget — not the clock — is the reproducible unit.
  **No assumption interface** (grep `assum` returns nothing) — cube conquest needs
  one, or cube-as-units with proofs relative to F ∧ cube.
- `lrat.rs`: `check_lrat` (:198), `write_lrat`, and `elaborate_drat_to_lrat`
  (:451). **LRAT already exists**, which is the right substrate for composition.
- `alethe.rs` (4,556 lines), `interpolant.rs`, XOR/GF2 stack, `bve`/`simplify`/
  `vivify` inprocessing, `to_dimacs` (:233), `parse_dimacs` (:2839),
  `IncrementalSat` **with native assumptions** (`solve_assuming`, :686-816).
- `axeyum-bench`: rayon with `--jobs`, per-worker stack sizing, pool isolation
  (main.rs:1910-1928); `certificate_process.rs` + ADR-0235 **killable subprocess
  isolation** with wall budget, 1 ms poll, kill-and-reap, timeout-as-counted-
  non-certification. That is the exact skeleton a cube worker needs.
- Design groundwork: `api-design-concurrency-and-stability.md:47-51` already
  specifies ownership for portfolio parallelism.

**The blocking local fact:** `check_drat` (`drat.rs:58`) is **fully in-memory**
(`&[DratStep]`), with the active clause set as `Vec<Vec<CnfLit>>`, deletions by
linear `position_of` scan, no watch indices, no backward checking — roughly
quadratic and RAM-bound. It cannot check one hard cube's proof.

## Quantitative calibration

| Result | Compute | Cubes | Proof |
|---|---|---|---|
| Boolean Pythagorean triples (2016) | ~35,000 CPU-h solve + ~16,000 verify; ~2 days on 800 cores | **10⁶** first-level; leaves at ~3,000 binary clauses | **~200 TB DRAT**, published certificate **68 GB** (transformation 2 MB + summarized cube 127 MB + **tautology proof 365 MB** certifying the cube set is exhaustive). One cube was **SAT** in an intermediate phase |
| Schur number five (2018) | **14+ CPU-years** (27,600 h partition + 95,600 h solve); <3 days on 2,400 solvers | 10,330,615 top-level; **65 billion** subproblems | 2.18 PB compressed LRAT. **DRAT→LRAT conversion 20.5 CPU-yr + ACL2 checking 15.6 CPU-yr — checking cost more than solving** |
| Keller dimension 7 (2020) | **~30 min on 40 machines** after four months of encoding work | — | ~200 GB. Lesson: symmetry breaking and encoding quality decided it, not compute |
| Empty hexagon (2024) | 25,876 CPU-h ≈ 3 CPU-yr | — | **formally verified end-to-end in Lean** (ITP 2024) — directly relevant to the Lean-parity thesis |

**Modern alternatives:** MallobSat (clause-sharing Kissat portfolio, best cloud
track since 2020) and Painless won recent parallel tracks; Gimsatul does
proof-producing multi-threaded solving. **Assessment: clause-sharing portfolios
dominate competition-length (≤5,000 s) instances; cube-and-conquer remains state of
the art for month-scale open-problem instances** because it gives embarrassing
parallelism, checkpointing (a killed cube costs one cube), per-cube progress
measurement, and per-cube proofs — and it composes far better with the evidence
thesis than a globally entangled clause-ID stream.

Distributed proof production is solved in principle: LRAT with globally unique
clause IDs congruent mod #solvers (TACAS 2023 / JAR 2025), with follow-ups doing
**on-the-fly distributed LRAT checking during solving**, eliminating the giant
post-hoc proof.

**AlphaMapleSAT** (2024) does **MCTS-based cubing** with a propagation-rate
deductive reward, up to 27× sequential speedup over march. This unifies phase 3
and phase 6: the same search skeleton can drive bridge selection and cube
generation.

## The build-vs-delegate position

**The identity sentence licenses external conquer engines outright.** CLAUDE.md's
hard rule is that the default build must have no C/C++ *dependency* and that native
backends are feature-gated leaf dependencies. A kissat/CaDiCaL **subprocess over a
DIMACS-in/proof-out boundary, with every proof independently rechecked by axeyum's
own checker**:

- is not a linked dependency — the default build stays C/C++-free, literally;
- transfers no trust — UNSAT requires a natively checked proof, SAT requires native
  model replay;
- adds nothing to ADR-0002's *trusted* reliance on Z3, which is what its demotion
  narrative is about;
- follows two accepted precedents: `docs/research/03-architecture/gpu-accelerated-untrusted-search.md`
  explicitly slots untrusted search engines into the identity, and
  `axeyum-bench/examples/cnf_core_bench.rs` already shells a kissat binary.

The ADR must fence it: search-amplifier role only; the native proof-producing CDCL
stays the default and the only in-build engine; competitive measurements continue
against the external engines so the demotion path stays honest.

## Pipeline design

Mirrors PTN's three-part proof structure:

1. **Splitter** (new `crates/axeyum-cnf/src/cube.rs`): lookahead over the existing
   two-watched-literal propagation; variable ranking by failed-literal/propagation
   count; deterministic cutoff (binary-clause-count threshold, tunable). Emits a
   **cube manifest** in iCNF format (`p inccnf` + `a lit… 0`, the de-facto
   march/iLingeling interchange format), content-hashed, **plus a cube-tree
   tautology certificate**: the split is a binary tree, so exhaustiveness
   (⋁ᵢ cᵢ ≡ ⊤) has a linear-size DRAT proof checkable by the existing `check_drat`
   on a small input. **This certificate is the soundness keystone.**
2. **Conquer workers** behind `fn conquer(cnf, cube, budget) -> (Verdict, ProofSource)`:
   native proof CDCL (default build), BatSat via `solve_assuming`, and external
   subprocess (kissat → DRAT, CaDiCaL → native LRAT via `--lrat`) configured by
   path exactly like `cnf_core_bench.rs`; absent binary degrades to native.
3. **Per-cube checking**: each proof refutes F ∧ cᵢ; check it independently
   (streamed), record the derived lemma ¬cᵢ, then **check-then-delete** (PTN's
   200 TB → 68 GB pattern). Never accumulate raw proofs.
4. **Composition certificate**: UNSAT ⟺ every cube checked UNSAT ∧ tautology
   certificate checks. SAT ⟺ some cube SAT ∧ model replays against the original
   term. The evidence artifact = {transformation proof, cube manifest + tautology
   proof, per-cube verification ledger}.

## Two-tier determinism contract

This resolves the CLAUDE.md tension directly and is **stronger than portfolios can
offer** — a genuine differentiator.

- **Tier 1 — verdict determinism, unconditional.** Cubes are independent; per-cube
  verdicts under *conflict budgets* are pure functions of (CNF bytes, cube, budget,
  engine version). Aggregation is order-insensitive (all-unsat ⇒ unsat; any sat
  cube ⇒ same verdict). Scheduling, thread count, and completion order cannot
  change the verdict or the certificate's validity.
- **Tier 2 — trace determinism, opt-in `--deterministic`**: fixed cube ordering,
  fixed per-cube conflict budgets, no deadline → bit-identical artifacts.
- Wall-clock exists only at the **outer kill boundary** (ADR-0235 pattern); a
  timed-out cube is a counted non-certification that triggers **re-split**
  (recursive C&C, the Schur-5 pattern), never a verdict.
- External solvers are trace-nondeterministic; fine, because they live strictly on
  the untrusted side.

## G3 — hardware realism

One workstation (16–32 cores) ≈ 12k–23k CPU-hours/month at full duty.

- **Reachable:** Keller-class results (encoding/symmetry-dominated, ≤10² CPU-h);
  small Ramsey/van der Waerden/Schur-4-style re-derivations (10¹–10³);
  **new results in the 10²–10⁴ CPU-hour band** — real publishable territory.
  PTN-class (~5×10⁴ incl. verification) = 2–4 months of a dedicated 32-core box;
  feasible but monopolizing, and survivable only because C&C checkpoints.
- **Not reachable locally:** Schur-5-class (≥1.2×10⁵ h solve + ≥3×10⁵ h
  convert/check). The cube manifest is the natural unit of cloud distribution.
- **Disk binds before CPU.** Per-cube check-then-delete is mandatory; budget
  proof-bytes per cube.

## Tasks

| id | title | size |
|---|---|---|
| [T6.1](T6.1-adr-external-conquer.md) | **ADR: external CDCL as untrusted conquer engine** | S |
| [T6.2](T6.2-icnf-cube-manifest.md) | iCNF cube-manifest format: writer/parser/hash | S |
| [T6.3](T6.3-lookahead-splitter.md) | Deterministic lookahead splitter + tautology certificate | L |
| [T6.4](T6.4-cube-relative-proofs.md) | Cube-relative proof production in the native CDCL | M |
| [T6.5](T6.5-streaming-drat-lrat.md) | Streaming bounded-memory DRAT checking + per-cube LRAT elaboration | M |
| [T6.6](T6.6-conquer-orchestrator.md) | Parallel conquer orchestrator + budget ledger + deterministic aggregation | M |
| [T6.7](T6.7-external-conquer-adapter.md) | External conquer adapter (kissat DRAT / CaDiCaL LRAT) | M |
| [T6.8](T6.8-hardness-predictor.md) | Hardness predictor + adaptive re-split | M |
| [T6.9](T6.9-mcts-cubing.md) | MCTS cubing sharing the phase-3 search skeleton | L |
| [T6.10](T6.10-open-problem-pilot.md) | Pilot: re-derive a known small result with a fully axeyum-checked certificate | M |

Near-term validation of the *dispatch* goal needs only T6.6's degenerate case
(N engines, 1 cube) and can land before the splitter.

## Risks

- **Determinism loss** is the sharpest trap — any wall-clock check inside a worker
  makes verdicts machine-dependent. CI test: same manifest at `--jobs 1` and
  `--jobs 32`, certificates diffed byte-for-byte.
- **Exhaustiveness bug class (wrong-unsat with all proofs valid)** — a splitter
  that silently drops a branch yields per-cube proofs that all check while the
  composed claim is false. The tautology certificate must be *checked*, and per the
  Hard Rules needs a deliberate negative generator (drop/duplicate/mutate a cube).
- **Proof-scale blowup** — Schur 5's warning is stark: conversion + checking cost
  2.5× the solving. Prefer native-LRAT engines, stream + backward-check,
  check-then-delete, and adopt on-the-fly checking.
- **Split quality is a research artifact** — march-class heuristics embody years of
  tuning; a naive splitter yields catastrophically unbalanced cubes. AlphaMapleSAT
  shows a learned/MCTS route can beat march and suits this codebase better than
  replicating march.
- **Trust laundering** — an external solver's *verdict* must never propagate. A
  kissat timeout is unknown, never unsat. Enforce at type level: `ProofSource`
  required for UNSAT.
- **SAT cubes are normal** (PTN cube 343,864) — the SAT path must replay against
  the original term and still record which cubes were never conquered.
- **Compute mirage** — the reachable band is 10²–10⁴ CPU-hours. Target selection
  (encoding + symmetry breaking, the Keller lesson) matters more than the
  orchestrator's ceiling.
- **Crate sprawl** — ADR-0001: the orchestrator starts inside `axeyum-bench`, which
  already owns rayon, subprocess isolation, and ledger artifacts.
