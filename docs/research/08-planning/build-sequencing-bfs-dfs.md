# Build sequencing: BFS vs DFS over the capability DAG, ranked

Status: **strategy note** (2026-07-09). A traversal-strategy analysis over the
[cross-track dependency DAG](../../../docs/plan/01-dependency-dag.md) and the
[foundation roadmap](roadmap.md): what a breadth-first build looks like, what a
depth-first build looks like, and the rank-ordered hybrid that maximizes quality
(trusted small checking / Lean parity) and efficiency (unblock-most-first, no
rework, measurement-gated). Does **not** replace PLAN.md/STATUS.md (the live
mutable state); it reframes their ordering as an explicit DAG traversal.

## 1. The DAG, distilled to what's left

Foundation (Phases 0–7) and **most** of the five-track parity plan are landed:
QF_LIA/LRA (simplex+Farkas, bit-blast+B&B+Gomory), QF_NRA/NIA (CAD decision
side), conjunctive EUF+LIA/LRA combination, quantifiers (finite+e-matching+MBQI),
proofs (DRAT + Alethe + in-tree Lean kernel + reconstruction), the string
word-core + bounded model, and the incremental decide-rate deciders added this
session. So the interesting question is only about the **unbuilt frontier**, and
it has a very specific shape — **two keystones, a keystone-blocked deep interior,
and a skirt of independent leaves**:

```
                       ┌── independent LEAVES (no keystone dep, parallel) ──┐
                       │  P2.4 LIA cuts    P2.5 NRA/CAD tail   P2.7 strings  │
                       │  P2.8 FP polish   P1.1/P1.2 perf      P3.8-Farkas   │
                       │  P4.3 OMT/MILP    P4.4 SMT-LIB surface              │
                       └────────────────────────────────────────────────────┘

   K1 = P1.4 e-graph ─► P1.5 CDCL(T) ─┬─► P2.3 EUF-lazy ─► P2.2 arrays-lazy
   (ENGINE KEYSTONE:                  ├─► P2.1 BV-lazy    P2.9 datatypes-lazy
    everything is still EAGER)        ├─► P2.6 quantifier maturity (e-matching/MAM)
                                      ├─► P1.6 theory combination at scale
                                      └─► P4.1 warm lazy memory

   K2 = P3.2 Alethe IR ─► P3.3 Carcara QF_BV ─► P3.4 checker
   (PROOF KEYSTONE,                    └─► P3.5 reduction proofs ─► trust ledger → 0
    mostly landed)                          └─► P3.6 Lean kernel ─► P3.7 reconstruct

   CATEGORICAL GAP (largest vs Z3, needs BOTH keystones' outputs):
     P3.2 ─► P3.8 interpolation ─┐
     P1.5 CDCL(T) ───────────────┼─► P4.6 CHC/Horn (PDR/Spacer, unbounded)
     P2.6 MBP ───────────────────┘   P4.7 synthesis/abduction ◄ P2.6 + P3.8
```

Three node classes drive the whole analysis:
- **Keystones** (K1 engine, K2 proof): each unblocks a large downstream subtree.
  K1 is the big one — it converts eager/one-shot theories into lazy/integrated
  ones and is a prerequisite for the categorical gap (via P1.5).
- **Keystone-blocked interior**: lazy arrays/EUF/BV/datatypes, quantifier
  maturity, combination-at-scale, warm memory, CHC/Horn. High value, gated.
- **Independent leaves**: the arithmetic/string/FP theory tails and the perf
  passes. Deliver measurable Z3-gap value **without** waiting on a keystone.

## 2. BFS strategy (breadth-first / level-order)

**Definition.** Advance every track's next-shallowest phase before deepening any
one. Keep all fronts moving one "level" at a time.

**Ordering.** Round 1 (all in parallel): P2.4, P2.5, P2.7, P2.8, P1.1, P1.2, P3.1,
the P3.8 Farkas slice, P4.3, P4.4. Round 2: each track's *next* phase. Keystones
(K1's interior, K2's Lean tail) are deep nodes, so BFS reaches them **last**.

**Where BFS wins.** Maximum *breadth of capability* early: every logic/theory at
v1, the widest support-matrix, and the richest measurement surface (many things
to diff against Z3 at once). It is the **portfolio / coverage** strategy, and it
is the right default *while the leaves still have ROI* and *before* a keystone is
on the critical path.

**Where BFS fails — and the empirical signal that it just did.** The highest-value
work (K1 → lazy theories → CHC/Horn, and K2's reduction proofs → ledger→0) is
**deep** in the DAG. Pure BFS starves it: months of leaf-polishing while the
architectural keystone that unblocks the entire deep interior waits. This session
*is* a BFS pass over the theory leaves (nl-eq-infer, pythagorean, rewriting-sums,
+5 rows), and it has **empirically hit diminishing returns** — the remaining
leaves need either the engine keystone (eager encodings no longer scale), a
large-scale engine (MILP for dense ILP, 200–360 KB LPs), or a research-grade
completeness proof (Nielsen strings). BFS is local optimization; it walks you
straight into the wall this session hit.

## 3. DFS strategy (depth-first / one path to a leaf)

**Definition.** Pick the highest-leverage root and drive one critical path to its
leaf, backtracking only when it is *complete and checkable*, then take the next.

**The three DFS spines** (the roadmap's four critical paths collapse to these):
- **DFS-A, engine spine:** `P1.4 e-graph → P1.5 CDCL(T) → {P2.3 EUF, P2.2 arrays,
  P2.6 quantifiers} → P1.6 combination → P4.1 warm memory`.
- **DFS-B, proof/quality spine:** `P3.2 → P3.3 → P3.5 reduction proofs (ledger→0)
  → P3.6 kernel → P3.7 reconstruction`. Independent of perf; runs day-one parallel.
- **DFS-C, categorical spine (largest gap):** `P3.2 → P3.8 interpolation →
  {P2.6 MBP + P1.5 CDCL(T)} → P4.6 CHC/Horn → P4.7 synthesis`. Note it **re-enters
  DFS-A** (needs P1.5), so it cannot be run first.

**Where DFS wins.** Unblocks the most downstream value *fastest* if the root is
well chosen, and yields **complete, production-grade, checkable** capabilities
rather than a field of v1 stubs. It is the **depth / completeness** strategy, and
it respects the DAG doc's explicit warning — *do not bolt lazy behavior onto the
eager reductions; build P1.4/P1.5 and migrate cleanly* — which pure BFS violates.

**Where DFS fails.** A wrong root sinks months into a low-demand branch; a single
long spine delays *all* measurable signal (bad for honest parity tracking); and
DFS-C is a trap if attempted before DFS-A (its P1.5 dependency).

## 4. Ranked recommendation — keystone-DFS spine + leaf-BFS skirt

Neither pure strategy is right; the DAG's shape (two keystones + independent
leaves) dictates a hybrid. Ranked by quality×efficiency:

**Rank 1 — DFS the engine keystone K1 (`P1.4 → P1.5`) as the spine, NOW.**
Highest leverage in the graph: it unblocks lazy arrays/EUF/BV/datatypes,
quantifier maturity, combination-at-scale, warm memory, *and* is the P1.5
prerequisite for the categorical gap. The decide-rate leaves have empirically
exhausted their ROI this session — that is the data-driven trigger to pivot from
leaf-BFS to keystone-DFS. Build the independent congruence checker alongside
(cheap, on-identity) so the migration is trust-preserving.

**Rank 2 — keep a thin leaf-BFS skirt in parallel, but only measured-ROI leaves.**
`P2.5 NRA tail`, `P2.7 strings-Nielsen` (research-gated), `P2.8 FP`. These keep
the Z3 gap closing and the measurement honest *during* the long K1 build, at low
opportunity cost. Explicitly **de-prioritize** the leaves this session proved
feature/scale-blocked (dense-ILP MILP engine, 200–360 KB LP performance) — they
are not slices; fold them into a funded engine phase or defer.

**Rank 3 — DFS the proof/quality spine K2 tail (`P3.5 → ledger→0`) in parallel.**
It is independent of perf and is the *quality* axis of the north star (trusted
small checking). Every theory that becomes lazy under Rank 1 should immediately
get its Alethe reduction proof and drop a trust-ledger entry — coupling Rank 1
and Rank 3 keeps depth and trust advancing together.

**Rank 4 — after P1.5 lands, DFS the categorical gap (`P3.8 → P4.6 CHC/Horn`).**
The largest single categorical gain vs Z3 (unbounded verification). Its cheapest
slice — Farkas/LRA interpolants (P3.8) — rides certificates already in tree and
can start in the Rank-2 skirt *before* P1.5, de-risking the path.

**Rank 5 — Track 4/5 frontends ride demand-pull, never keystone-block the spine.**

**Why this maximizes quality × efficiency.**
- *Efficiency:* keystone-first DFS unblocks the most per unit effort and avoids
  the single most expensive rework in the plan (eager→lazy retrofit). The
  leaf-BFS skirt harvests cheap parallel value so there is never a dark period.
- *Quality:* DFS yields complete, checkable capabilities, not v1 sprawl; the
  trust-ledger spine keeps "trusted small checking" central; measurement-gating
  (Rank 2) keeps every parity claim honest, one variable at a time.

**The one-line takeaway.** BFS on the theory leaves is *done* — it hit its wall
this session. Pivot to **DFS on the e-graph/CDCL(T) engine keystone**, keep a thin
measured-leaf skirt and the trust-ledger proof spine running in parallel, and let
the CHC/Horn categorical gap fall out once P1.5 lands.

## Backlinks
- [Cross-track dependency DAG](../../../docs/plan/01-dependency-dag.md) (keystones,
  critical paths, waterfall+parallelism order — this note reframes it as traversal).
- [Foundation roadmap](roadmap.md) (Phases 0–7 + "Beyond Phase 7").
- Track plans: [engine](../../../docs/plan/track-1-engine/README.md) (K1 = P1.4/P1.5),
  [proofs/Lean](../../../docs/plan/track-3-proof-lean/README.md) (K2 = P3.2).
