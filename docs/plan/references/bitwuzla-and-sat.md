# Bitwuzla + state-of-the-art CDCL + the Rust SAT landscape

Distilled for axeyum's niche: **QF_BV (+FP +arrays)** decided by bit-blasting to a
custom CDCL SAT core. Paths under `references/`.

## Bitwuzla — the closest analog

Modern C++ QF_BV/FP/array solver on **bit-blast→AIG→CNF → CaDiCaL/Kissat**, with a
parallel **propagation-based local-search** engine. Almost exactly axeyum's
intended architecture.

### Design map (`references/bitwuzla/src/`)
```
lib/         644K   bitblast/ (AIG + Tseitin), bv/ (BitVector + BitVectorDomain), ls/ (local search), rng/
solver/      576K   solver_engine.cpp + per-theory bv/ fp/ array/ fun/ quant/ abstract/
rewrite/     408K   word-level term rewriter (rewrites_bv.cpp 120K is the bulk)
parser/      284K   smt2 + btor2
preprocess/  232K   preprocessor.cpp + pass/ (9 passes)
node/        132K   term DAG, node manager, structural hashing
sat/         108K   thin adapters: cadical.cpp, kissat.cpp, cryptominisat.cpp, gimsatul.cpp
```
Key files:
- `lib/bitblast/bitblaster.h` — operator-by-operator blasting, generic over
  `BitInterface<T>` so the same blaster targets AIGs or concrete bits.
- `lib/bitblast/aig/aig_manager.cpp` — AIG with structural hashing
  (`AigNodeUniqueTable`) + **two-level local AIG rewriting** (`rewrite_and`,
  Brummayer–Biere neutrality/idempotence/contradiction/subsumption/resolution
  rules at construction) → shrinks the AIG before CNF.
- `lib/bitblast/aig/aig_cnf.cpp` — Tseitin AIG→CNF.
- `solver/bv/bv_bitblast_solver.cpp` — **incremental discipline**: top-level
  assertions are hard clauses cleared after encoding; non-top-level assertions
  become **SAT assumptions** (`d_sat_solver->assume`), unsat cores via
  `failed(lit)`. **The model axeyum's `IncrementalSat` should mirror.**

### The PBLS engine (`lib/ls/`, `solver/bv/bv_prop_solver.cpp`) — the novel idea
Not WalkSAT — **propagation-based local search** over the *word-level* DAG
(Niemetz/Preiner/Biere). Solves hard satisfiable QF_BV that bit-blasting chokes
on, with no SAT solver.
- The DAG mirrors as `ls::Node<BitVector>` with a `BitVectorDomain` (fixed/const
  bits, optionally seeded from a bit-blast pass).
- Assertions = roots with target `true`; `compute_initial_assignment` bottom-up.
- Main loop `ls.cpp::move()`: pick a random unsat root; `select_move` propagates
  the target value **down one path** to a leaf input.
- `select_path` prefers an **essential input** (must change to satisfy the parent)
  with prob `prob_pick_ess_input` (0.99), else random (for completeness).
- Value selection: if invertible, with prob 0.99 compute the **inverse value**
  (exact child value making parent = target); else a **consistent value**; else
  conflict, retry.
- The per-operator **invertibility conditions / inverse-value / consistent-value
  functions** live in `lib/ls/bv/bitvector_node.cpp` (216K — the heart):
  `BitVectorAdd/And/Concat/Eq/Mul/Shl/Shr/Ashr/Udiv/Urem/Ult/Slt`. Closed-form
  solutions of "given `x op s = t`, find `x`" from the QF_BV invertibility
  catalog (add always invertible `x=t-s`; `and` needs `t&s==t`), exploiting
  constant bits and optional inequality bounds.
- `update_cone()` recomputes the affected cone; bounded by `max_nprops`/
  `max_nupdates`. `PREPROP` mode runs prop first with a small budget, then falls
  back to bit-blasting — a portfolio.

**Why bitwuzla is fast:** aggressive word-level rewriting; structural-hashed AIG +
two-level rewriting (small, sharing-maximal CNF); tight CaDiCaL/Kissat backend
with assumption-based incrementality; PBLS as a cheap front-line for sat
instances; constant-bit propagation (`BitVectorDomain`) shared between blaster and
LS.

### Preprocessing passes (`preprocess/pass/`, apply order in `preprocessor.cpp`)
`rewrite` → `flatten_and` → `variable_substitution` (top-level `x=t` elim) →
`skeleton_preproc` (Boolean skeleton via one SAT call) → `embedded_constraints` →
`elim_bvudiv` (replace udiv/urem by defining constraints) → `elim_lambda` →
`contradicting_ands` → `normalize` (big BV arithmetic normalizer, first call only).
Highest-value for axeyum: **variable substitution, rewrite/normalize, elim_bvudiv.**

## CaDiCaL — techniques ranked by impact (`references/cadical/src/`)
Default: EVSIDS (focused) + VMTF (stable), chronological backtracking on,
glue/EMA restarts with stabilization, full inprocessing (vivify/subsume/elim/probe
/transred). Ranked for bit-blasted QF_BV:
1. **Two-watched + blocking literals + arena locality** (`propagate.cpp`,
   `watch.hpp`, `clause.hpp`, `arena.hpp`): watch=`{Clause*,blit,size}`; binary
   fast-path; branchless `other=lits[0]^lits[1]^lit`; `clause->pos` caches last
   replacement (Gent 2013). ~70% of runtime. *Verify axeyum does these.*
2. **1-UIP + LBD/glue + 3-tier clause keeping** (`analyze.cpp`, `reduce.cpp`):
   glue via timestamp table; tier1 glue≤2 kept, tier2 ≤6, tier3 deleted. *Biggest
   learned-clause-quality lever.*
3. **Bounded Variable Elimination** (`elim.cpp`, `elimfast.cpp`): resolution,
   score `prod·pos·neg+sum·(pos+neg)`, bounded by `elimclslim=100`. **Very high on
   bit-blasted CNF** (collapses Tseitin intermediates). Most intricate to port.
4. **Vivification** (`vivify.cpp`): assert clause lits under propagation, strengthen.
5. **Subsumption** (`subsume.cpp`): forward, via min-occurrence literal. Simpler
   than BVE — good first inprocessing step.
6. **Glue/EMA restarts + stabilization** (`restart.cpp`, `ema.hpp`, `reluctant.hpp`).
7. **Chronological backtracking** (`backtrack.cpp`).
8. **Probing / failed-literal + hyper-binary resolution** (`probe.cpp`, `transred.cpp`).
9. **LRAT/DRAT/FRAT tracing** (`drattracer.cpp`, `lrattracer.cpp`): clause IDs in
   `clause->id`; LRAT chain built during `analyze()`. Correctness, no speedup.

## Kissat — deltas vs CaDiCaL (`references/kissat/src/`)
- **Flat arena, bit-packed clauses, packed 32-bit watches** (`arena.c`, `clause.h`,
  `watch.h`): header packs `glue:19,flags,used:5,searched:32,size:32`; refs are
  arena offsets; watches are a 31-bit lit/ref + 1 binary-tag bit in a flat stream.
  **Most portable high-value idea: a structure-of-arrays / arena clause DB.**
- **Stable/focused mode switching** (`mode.c`/`decide.c`/`queue.c`/`heap.c`):
  focused = VSIDS heap + frequent glue restarts; stable = VMTF queue + reluctant
  restarts + trail reuse. ~10-15%.
- **Tier-based reduction with adaptive fraction** (`reduce.c`).
- **Multi-tier vivification** (`vivify.c`). **Rephasing 6-cycle** (`rephase.c`;
  `walk.c` embedded GSAT). **`kitten`** embedded sub-solver — skip for MVP.

Ranked for axeyum QF_BV: (1) arena+packed watches, (2) stable/focused switching,
(3) tiered+adaptive reduction, (4) trail reuse on restart, (5) multi-tier vivify.

## Rust SAT landscape
| | varisat | splr | batsat |
|---|---|---|---|
| Lines / maint. | 13K / inactive | 13.6K / active | 7K / active |
| Clause store | arena, u32 offsets | `Vec<Clause>` | generic `RegionAllocator<T>` |
| Heuristic | VSIDS | VSIDS/EVSIDS + LRB + rephase | VSIDS heap (MiniSat) |
| Restarts | Luby | Glucose/EMA + chrono BT | geometric |
| Reduction | LBD tiers | LBD/RAS tiers + vivify | activity |
| **Proof** | **DRAT + LRAT + checker** | DRAT only | DRAT stub |
| `unsafe` | 19 | 190+ | 17 |

- **varisat** — only mature Rust solver with **both DRAT and LRAT plus an in-tree
  checker** and the cleanest proof architecture (`varisat/src/proof/`,
  `varisat-lrat`). Unmaintained but **the best architectural reference for proof
  output** — axeyum's differentiator.
- **splr** — richest modern heuristics (LRB, rephasing, vivify, EMA, chrono BT)
  but DRAT-only and 190+ unsafe (axeyum denies unsafe). Mine for *algorithms*.
- **batsat** — simplest, already axeyum's adapter; keep as differential oracle.

Verdict: **model proof handling on varisat; harvest heuristics from splr; keep
batsat as the differential oracle.** axeyum's no-`unsafe` rule is achievable with
index-based arenas.

## Recommended adoption order for axeyum (sized S/M/L)
axeyum already has: AIG with structural hashing, term→AIG lowering, Tseitin +
DRAT checker + a proof-producing 1-UIP CDCL, incremental lowering/SAT. So gaps are
SAT-core *performance* and BV *preprocessing*, plus the optional PBLS engine.

**Single highest-leverage item: inprocessing on the bit-blasted CNF — start with
Bounded Variable Elimination, then subsumption (*M→L*).** Tseitin of an AIG floods
intermediate variables; BVE (`cadical/src/elim.cpp`) collapses them and is *the*
technique that makes bit-blast CNF tractable. Pair with forward subsumption first
as a simpler warm-up.

Then:
1. **Glue (LBD) + 3-tier clause reduction** (*S–M*) — `analyze.cpp`/`reduce.cpp`.
2. **Word-level BV rewriting + variable substitution + elim_bvudiv preprocessing**
   (*M–L*) — port the high-value subset of `bitwuzla/src/preprocess/pass/` and
   `rewrite/rewrites_bv.cpp` into `axeyum-rewrite`. Co-priority with #1
   (encodings/preprocessing before SAT-core tuning, per the methodology gate).
3. **Two-level local AIG rewriting at construction** (*S–M*) — port
   `aig_manager.cpp::rewrite_and` into `axeyum-aig`; shrinks CNF before the SAT core.
4. **Vivification** (*M*) after BVE+subsume.
5. **Glue/EMA restarts + stable/focused mode switching** (*M*) — VMTF alongside VSIDS.
6. **Arena clause DB + packed watches** (*M–L*) — Kissat layout but **indices not
   pointers** (varisat pattern) for the no-`unsafe` rule. Defer until propagation
   is proven the bottleneck.
7. **Chronological backtracking** (*M*) — lower priority.
8. **Strategic / ADR-gated: a PBLS BV engine** (*L*) — port `bitwuzla/src/lib/ls/`
   (`ls.cpp` loop + `bitvector_node.cpp` invertibility functions). Huge upside on
   hard *satisfiable* QF_BV, complements bit-blasting as a `PREPROP` portfolio,
   reuses axeyum's `BitVectorDomain`-equivalent. Top *new-capability* candidate
   after the SAT/preprocessing wins land.

Sequencing: items 2 and 3 (preprocessing/AIG rewriting) are low-risk and shrink
the problem feeding the SAT core — do them first/in parallel with BVE so the
SAT-core work is easier to measure. Keep batsat as differential oracle; model any
new proof surface on varisat's `proof/`.
