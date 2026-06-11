# Query Cost Control: Sharing Blowup And Budgets

Status: draft
Last updated: 2026-06-11

## Purpose

Plan how Axeyum identifies, optimizes, and caps exponential solver behavior
on heavily-shared terms — the dominant failure mode when clients feed
queries from obfuscated binaries or complex C++ symbolic execution.

## Scope

In scope:

- The two blowup classes, detection metrics, mitigation transforms, and the
  budget/degradation model.

Out of scope:

- Rewrite rule specifics (rewriting note) and engine alternatives
  (beyond-bit-blasting note).

## Core Claims

- There are two distinct exponentials. **Representational blowup** (a small
  DAG unfolded as a 2^k tree by any non-memoized pass, un-`let` printing,
  or duplicating rewrite) is always a bug, never a solver limitation.
  **Search blowup** (ite path-merging, MBA obfuscation, multiplication,
  symbolic store chains) is real and needs abstraction or budgets.
- Tree size vs DAG size is the discriminating metric: compute both
  (tree size saturating/log-space, memoized) and alarm on the ratio.
- Encode-time death vs solve-time death (layer-attributed timing) tells
  which class is occurring; the benchmarking methodology already requires
  this attribution.
- Deterministic resource budgets (Z3 `rlimit`-style) beat wall-clock for
  reproducing and bisecting blowups.
- Every layer gets an explicit budget; exhausting any budget yields
  `Unknown` with a diagnosis (which budget, observed sizes), never a hang.

## Mitigation Toolbox (cheapest first)

| Transform | Effect | Home |
|---|---|---|
| Memoized traversal + `let`-aware export | Prevents all representational blowup. | IR / formats (hard rule) |
| Size-guarded rewrites + fuel | Duplicating rules fire only when they shrink. | rewriter |
| Cone-of-influence slicing | Drops constraints irrelevant to the goal. | query planner |
| Word-level cutpoints (`v ≡ subterm` with fresh `v`) | Tseitin lifted to terms: bounds depth, caches pieces, adds decision points; cut at high fan-in × tree-mass. | query planner |
| Truth-table / ANF normalization of small-support subterms | Collapses MBA: evaluate exhaustively over the subterm's symbol support, re-synthesize minimal form; checked by evaluation + oracle. | rewriter + evaluator |
| UF abstraction + refinement for expensive ops | Multiplication etc. as uninterpreted + lemmas on demand. | BV backend loop |
| Structural query cache | Near-duplicate queries from symbolic executors hit cache. | query planner |

## Budget And Degradation Model

- Budgets: rewrite fuel + node ceiling; bit-blast clause ceiling; solver
  wall-clock, deterministic resource limit, memory limit. `SolverConfig`
  grows `resource_limit` and `memory_limit` alongside `timeout`.
- Admission control: planner computes cheap features (DAG nodes, sharing
  ratio, depth, ite-density, mul count, store depth) and degrades before
  submitting: canonicalize → slice → cutpoint/abstract → budgeted submit →
  `Unknown` with diagnosis.
- Anytime approximations: concretize symbols (under-approx; found models
  are real) for sat; drop constraints (over-approx; unsat transfers) for
  unsat. Both give clients progress under budget.
- Client guidance: unbounded ite path-merging is self-inflicted 2^paths;
  planners should expose merge-cost feedback so executors fork instead.

## Design Implications

- Add a sharing-metrics pass to `axeyum-ir` (DAG size, saturating tree
  size, per-node support size); it powers admission control and the
  MBA normalizer.
- Post-rewrite growth guards become invariants: nodes-out ≤ c · nodes-in
  or the pass aborts to `Unknown`.
- SMT-LIB export (Phase 2) must emit `let`/`define-fun` for shared nodes
  from its first version.
- `Unknown` payloads gain structure: budget kind, layer, observed sizes.

## Risks

- Cutpoint and abstraction choices can hurt easy queries; gate on features
  and measure (PAR-2 on the client tier), don't always-on.
- Truth-table normalization is exponential in support *bits*; cap support
  size strictly and fall through silently when exceeded.

## Open Questions

- [ ] What cut-selection heuristic (fan-in × mass threshold) wins on real
      symbolic-execution corpora?
- [ ] Should the planner's feature vector and admission decisions be
      recorded in evidence artifacts for replay/debugging?
- [ ] Does deterministic budgeting need its own abstraction over backends
      that lack an rlimit analogue?

## Source Pointers

- Z3 rlimit/statistics: https://github.com/Z3Prover/z3
- MBA deobfuscation context (MBA-Blast, SiMBA lineage): https://github.com/DenuvoSoftwareSolutions/SiMBA
- egg (equality saturation for normalization): https://github.com/egraphs-good/egg
- KLEE query optimization context: https://klee-se.org/
