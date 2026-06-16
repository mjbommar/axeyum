# GPU-accelerated untrusted search (horizon note)

Status: horizon / not committed. Captures a strategic assessment (2026-06-15) of
whether GPUs (e.g. a box with 128 GB RAM + 2× RTX 4070 Ti) could make axeyum's
bit-blasting / solving faster. The conclusion is **yes for specific components,
no for the core** — and it slots cleanly into our identity without disturbing the
trusted core.

## The core does not GPU-accelerate

The decision bottleneck — the **CDCL loop** (unit propagation + 1-UIP conflict
analysis) — is pointer-chasing, branch-heavy, latency-bound, deeply
data-dependent work. GPUs are throughput/SIMT machines wanting thousands of
coherent threads. Two decades of "CDCL on GPU" have generally **lost to a single
CPU core** running CaDiCaL/Kissat. The same holds for the theory solvers and the
e-graph (irregular, pointer-heavy). For the core engine, **RAM and CPU cores
dominate**: bigger learned-clause DBs, deeper BMC unrollings, larger e-graphs, and
a CPU portfolio of CDCL configs. Do **not** GPU-ify the CDCL core or theory
solvers — that is where the effort goes to die.

## Where GPUs genuinely win (and where they map onto the plan)

1. **GPU inprocessing — strongest, most plan-aligned.** Bounded variable
   elimination + subsumption ([P1.1](../../plan/track-1-engine/P1.1-sat-inprocessing.md),
   already implemented on CPU as `axeyum_cnf::{bve,simplify}`) are massively
   parallel over clauses/variables. Published GPU SAT simplification (Osama &
   Wijs, *ParaFROST*/*SIGmA*) reports large speedups on the *simplification* phase
   specifically. Pattern: **GPU shrinks the CNF, CPU solves it.**
2. **Massively-parallel local search — complements
   [P1.7](../../plan/track-1-engine/P1.7-pbls-engine.md).** Propagation-based /
   stochastic local search runs thousands of trajectories at once; a natural GPU
   portfolio partner for *satisfiable* QF_BV.
3. **All-SAT / #SAT / model counting on tree decompositions — for Track 4
   reachability.** GPU model counting (GPUSAT lineage) does DP over low-treewidth
   structure and wins; maps onto reachable-state enumeration / test-suite
   generation ([P4.2](../../plan/track-4-usecases-frontend/P4.2-symexec-cfg.md)).
4. **Learned heuristics** (GNN-guided branching/restart). Research-stage;
   in-loop inference latency is the open problem. *Watch, don't build.*

## Why it fits the architecture unusually well

Our identity is **untrusted fast search, trusted small checking.** GPUs belong
entirely on the *untrusted search* side: a GPU returns a candidate model or a
simplified CNF, and the **CPU still independently checks it** (model replay
through the ground evaluator; `unsat` via DRAT; the trust ledger, ADR-0031). So
GPU code does **not** need to be trusted or verified — a bug surfaces as a failed
check, never a wrong answer. That lowers the correctness bar that kills most
GPU-SMT efforts.

## Constraint: no C/C++ in the default build (ADR-0002)

CUDA is C++, so any GPU backend is a **feature-gated leaf** like the Z3 oracle —
never in the default build. The interesting twist: **`wgpu` / Vulkan compute is
pure-Rust**, so a GPU inprocessing / local-search backend could plausibly stay
within the no-C/C++ identity (at some perf cost vs hand-tuned CUDA). Committing to
GPU support — and the wgpu-vs-CUDA choice — would be an ADR.

## Recommendation

- **Highest ROI, lowest risk:** a feature-gated GPU **inprocessing** backend
  (BVE + subsumption over bit-blasted CNF) and a GPU **local-search** portfolio
  engine — both attach to existing plan phases, both are pure checkable search.
- **The RAM is the bigger gift** for the core engine and CDCL(T)/e-graph work.
- Treat this as a multi-week research track with upside on *specific* components,
  not an "everything faster" claim. Captured here; not scheduled into a track
  until the CPU foundation (P1.1–P1.5) is measured (P4.5) and proven.
