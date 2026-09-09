# CaDiCaL and Kissat — inventory and gaps (2026-09-09)

Scope: two Armin Biere solvers, read from `references/`, no build.

| | CaDiCaL | Kissat |
|---|---|---|
| Commit | `c60730422e758ef1cebe7aeddf2dda31c996bf04` | `8af8e56f174b778aef3aa45af9f739b2a5f492c2` |
| Clone HEAD date | 2026-07-19 | 2025-10-16 |
| `VERSION` | 3.0.1 | 4.0.4 |
| Language | C++ (plus `src/kitten.c` in C) | C |
| Source files (`src/*.{c,h,cpp,hpp}`) | 160 | 205 |
| Source lines | 69,381 (63,710 excluding `mobical.cpp`, the model-based tester) | 38,944 |
| License | MIT (`LICENSE:1`) | MIT (`LICENSE:1`) |

**Read the date row before reading any Kissat-vs-CaDiCaL difference as a design
decision.** These clones are nine months apart. Kissat 4.0.4 is a released
version; CaDiCaL 3.0.1 at this SHA is a development head. Some of what looks
like divergence below is version skew, and where I cannot tell the two apart I
say so.

## Summary

- **CaDiCaL is an inprocessing solver with a CDCL loop inside it, not a CDCL
  solver with some preprocessing bolted on.** The main loop
  (`internal.cpp:280-347`) has ten branches, and five of them
  (`inprobe`, `elim`, `compact`, `condition`, `reduce`) are simplification, not
  search. The single largest source file in the tree is
  `congruence.cpp` at 7,925 lines — a simplification pass, not the solver.
- **24 named reduction passes, each in its own file**, listed in
  [§D](#d-inprocessing-during-search). Ours has five
  (`simplify`, `vivify`, `bve`, `compact`, `xor_propagate` —
  [`01-sat-core-and-cnf.md`](../solver-inventory-2026-09/01-sat-core-and-cnf.md)),
  and all five are off in a default run because `SolverConfig::default()` sets
  `cnf_inprocessing: false` (`backend.rs:390`, cited there).
- **Everything is budgeted in *ticks*, and ticks are the mechanism, not a
  metaphor.** `SET_EFFORT_LIMIT` (`limit.hpp:136-164`) computes each pass's
  budget as `opts.<pass>effort / 1000 * (search ticks since this pass last
  ran)`, and refuses to run the pass at all if the resulting budget is below
  `opts.<pass>thresh * clauses.size()`. Our `ticks.rs` implements the same idea
  and **no shipping budget consumes it** — every axeyum budget is in conflicts
  (`01-sat-core-and-cnf.md`, "`ticks` has no consumer to be deterministic
  *for*"). This is the single closest structural gap in the comparison: we built
  the meter and never wired it to a valve.
- **The inprocessing schedule is a fixed sequence inside one function**, not a
  set of independent triggers: `Internal::inprobe` (`probe.cpp:914-990`) runs
  deduplication → SCC/ELS → ternary resolution → failed-literal probing →
  gate extraction and congruence closure → backbone → SAT sweeping →
  vivification → transitive reduction → backbone → BVA, re-running `decompose()`
  after any step that can produce a new binary clause. BVE (`elim`) is scheduled
  separately in the main loop and has its own inner alternation.
- **DRAT stays valid across all of it by an asymmetry, not by cleverness.**
  Every clause a pass *adds* is either RUP (resolvents, vivified clauses,
  hyper-binary/ternary resolvents, backbone units) or is emitted as an explicit
  RAT addition with the witness as the first literal (`factor.cpp:617-628`,
  `clause.cpp:559-570`); every clause a pass *removes* is emitted as a plain `d`
  line, and deletion is always sound in the refutation direction. The SAT
  direction is carried entirely **outside** the proof, on the extension stack
  (`extend.cpp:49-80`). See [§J](#j-proof--certificate-production).
- **The default decision heuristic is two heuristics.** `use_scores()` is
  `opts.score && stable` (`internal.hpp:476`): EVSIDS in stable mode
  (`analyze.cpp:105-151`), a VMTF bump queue in focused mode
  (`analyze.cpp:52-86`, `decide.cpp:12-24`). Restarts likewise:
  Glucose EMA fast/slow glue with a 10% margin in focused mode, reluctant
  (Luby) doubling in stable mode (`restart.cpp:91-116`, `options.hpp:186-198`).
  Mode switching is driven by **ticks with quadratic growth**
  (`restart.cpp:19-84`).
- **Clause tiers are recomputed from measured usage, not from constants.**
  `recompute_tier` (`tier.cpp:7-80`) builds a histogram of the glue of clauses
  that were actually used in conflict analysis, then sets tier1 at the 50th and
  tier2 at the 90th percentile of that distribution
  (`options.hpp:246-249`). `reducetier1glue = 2` / `reducetier2glue = 6` are
  only the seed values used before any usage data exists.
- **Six proof back ends and two in-tree checkers.** DRAT, LRAT, FRAT, IDRUP,
  LIDRUP, VeriPB (`drattracer.cpp`, `lrattracer.cpp`, `frattracer.cpp`,
  `idruptracer.cpp`, `lidruptracer.cpp`, `veripbtracer.cpp`), behind one
  `Tracer` observer interface (`tracer.hpp:18-120`); `checker.cpp` (649 lines,
  DRAT) and `lratchecker.cpp` (833 lines, LRAT) run online when `opts.check` is
  set, defaulting to `checkproof = 3` = both (`options.hpp:48`).
- **Kissat is a rewrite with a smaller technique set, not a superset.** It has
  no failed-literal probing, no hyper binary or ternary resolution, no blocked
  or covered clause elimination, no globally blocked clause elimination, no
  instantiation, and **no LRAT** — `proof.c` writes DRAT only. What it adds over
  CaDiCaL at these SHAs: a formula classifier that gates heuristics
  (`classify.c:5-27`), decision `reorder` (`reorder.c:14-22`), BVA on by default,
  and a much tighter memory layout.
- **Neither solver is parallel.** No `pthread`, no `std::thread`, no OpenMP in
  either `src/` (verified below).
- Three things in this pairing that are directly actionable for us: the tick
  valve, gate/structure recovery from CNF, and the extension stack as the
  general model-reconstruction mechanism. They are ranked in
  [§Gaps](#gaps-against-axeyum).

## Schema

### A. Input front end

**CaDiCaL.** DIMACS CNF and incremental `p inccnf` (cubes), one hand-written
recursive-descent parser, `parse.cpp:103-260`. The header is parsed strictly:
`expected digit after 'p cnf '` and friends are hard errors (`parse.cpp:167-215`),
not skips. There is a `strict` parameter (`parse.cpp:103`) controlling how
tolerant the literal scanner is. It also parses a *solution* file for
`opts.check`-style validation (`solution.cpp`). No SMT-LIB, no AIG input.

**Kissat.** DIMACS only, `parse.c` (445 lines); the application layer is
`application.c` (879 lines). `krite.c` writes DIMACS back out
(`krite.c:8-30`), which CaDiCaL does through `Solver::traverse_clauses`.

Neither silently ignores malformed input; both fail with a line number.

### B. Preprocessing (before search)

**CaDiCaL.** Two stages, both in `internal.cpp`.

1. `preprocess_quickly` (`internal.cpp:750-802`), gated on
   `opts.preprocesslight` (**default 0**, `options.hpp:163`): gate extraction +
   SCC, binary backbone, SAT sweeping + SCC, BVA, fast BVE.
2. `preprocess_round` (`internal.cpp:701-746`), repeated up to
   `lim.preprocessing` times (`internal.cpp:515-522`), each round running
   `inprobe(false)` → `elim(false)` → `condition(false)`. A round "succeeded"
   and the loop continues only if it removed active variables or raised the
   elimination bound (`internal.cpp:740-745`).

Before either, `lucky_phases()` (`lucky.cpp`) tries all-true / all-false /
forward / backward / clause-order assignments, and `deduplicate_all_clauses()`
runs if `opts.deduplicateallinit` (default 0).

**Order is the same code path as inprocessing**: `preprocess_round` calls the
same `inprobe`/`elim`/`condition` the search loop calls, with `update_limits =
false`. There is exactly one implementation of each pass. Ours has two
implementations of the same three passes with different certificate mechanics
(`inprocess.rs` vs `sat_bv_backend::inprocess`, recorded as integration gap #2
in [`11-wiring-and-integration.md`](../solver-inventory-2026-09/11-wiring-and-integration.md)).

**Model reconstruction is maintained by the extension stack**, `extend.cpp`, and
it is a *witness* stack, not an inverse map: `push_clause_on_extension_stack`
(`extend.cpp:56-64`) records the clause and its id; the two-argument form
(`:66-69`) records a *pivot* witness literal first. Blocked clauses, eliminated
clauses and equivalence substitutions all push here (`restore.cpp:15-18` names
`block`, `elim` and `decompose` as the writers), and a `witness` bit per
external literal drives incremental restoration.

**Kissat.** `kissat_preprocess` (`preprocess.c:29-`), gated on
`preprocess && probe && preprocessprobe` (all default 1, `options.h:89-95`),
looping `preprocessrounds` (default **1**) over
`kissat_probe_initially` then `kissat_fast_variable_elimination`
(`preprocess.c:70-73`). `probe_initially` (`probe.c:44-67`) is a *different*
schedule from the inprocessing one: congruence → substitute → backbone →
sweep → substitute → factor, each behind its own `preprocess*` option.
`fastel` defaults to **0** (`options.h:62`), so that second call is off.

### C. Core SAT engine

| Component | CaDiCaL | Kissat |
|---|---|---|
| Decision | EVSIDS heap in stable mode, VMTF queue in focused mode; `use_scores() { return opts.score && stable; }` (`internal.hpp:476`), dispatched at `decide.cpp:103-115` | Same split (`heap.c` + `queue.c`, `decide.c`), plus `reorder.c` |
| Score decay | `scorefactor = 950` per mille (`options.hpp:203`), rescale on EVSIDS overflow (`analyze.cpp:87-101`) | `decay = 50` per mille (`options.h:34`) |
| Random decisions | `randec` on, focused only by default (`randecstable = 0`), bursts of `randeclength * log(count+10)` conflicts (`decide.cpp:38-58`) | `randec` 1, `randecstable` 0 (`options.h:103-108`) |
| Restart, focused | Glucose EMA: restart when `slow_glue * (1 + margin) <= fast_glue`, `restartmarginfocused = 10` percent (`restart.cpp:91-116`, `options.hpp:196`); base interval `restartint = 2` | `restartmargin = 10` (`options.h:126`) |
| Restart, stable | Reluctant (Luby) doubling, `reluctantint = 1024`, `reluctantmax = 1048576` (`options.hpp:186-188`), consulted at `restart.cpp:96-97` | `reluctantint = 1<<10`, `reluctantlim = 1<<20` (`options.h:115-116`) |
| Mode switching | `stabilizing()` (`restart.cpp:19-84`), budgeted in **search ticks**; next interval `= inc.stabilize * stabphases^2` (`restart.cpp:60-62`); starts focused, `stabilizeinit = 1000` | `mode.c`, `modeinit = modeint = 1000` conflicts (`options.h:84-85`) |
| Trail reuse | `restartreusetrail = 1` (`options.hpp:198`), Marijn's reuse-trail (`restart.cpp:120+`) | `restartreusetrail = 1` |
| Clause DB tiers | core (irredundant) / tier1 / tier2 / tier3, **percentile-recomputed** from a used-glue histogram (`tier.cpp:7-80`); a 2-bit `used` counter decremented per reduce (`reduce.cpp:44-51`) | `tier1 = 2`, `tier2 = 6` seeds with `tier1relative = 500`, `tier2relative = 900` per mille (`options.h:151-154`), `tiers.c` |
| Reduce schedule | `reducing()` = `conflicts >= lim.reduce` (`reduce.cpp`), `reduceinit = 300`, `reduceint = 25`, `reducetarget = 75` percent, `reduceopt = 1` (sqrt growth) (`options.hpp:179-183`) | `reduceinit = reduceint = 1000`, `reducelow/high = 500/900` per mille (`options.h:109-114`) |
| Watches | Blocking-literal watches; binaries stored inline in the watch, no clause allocation | Same idea, packed into a 32-bit union: `struct binary_tagged_literal { unsigned lit : 31; bool binary : 1; }` (`watch.h:19-36`) |
| Phase saving | saved + target + best + forced (`decide.cpp:118-175`, `backtrack.cpp:46-84`), `target = 1` (stable only) | `phasesaving = 1`, `target` (`options.h:88`, `:150`) |
| Rephasing | `rephase = 1`, `rephaseint = 1000`; cycle original / inverted / flipped / random / best / **walk** (`rephase.cpp:37-160`), where `walk` is ProbSAT-style local search (`walk.cpp`) | `rephase = 1`, `walk.c` (966 lines), `walkinitially = 0` |
| Chronological backtracking | `chrono = 1`, `chronolevelim = 100`, `chronoreusetrail = 1` (`options.hpp:50-53`), implemented at `analyze.cpp:656-680` + `backtrack.cpp:129-133` | `chrono = 1`, `chronolevels = 100` (`options.h:21-22`) |
| Conflict analysis | 1-UIP + recursive minimization (`minimize.cpp`) + **shrinking** (`shrink.cpp`, `shrink = 3` full) + on-the-fly self-subsumption (`otfs = 1`, `analyze.cpp:550-568`) | `shrink = 3`, `otfs = 1` (`options.h:86`, `:129`) |
| Eager subsumption | `eagersubsume = 1`, up to `eagersubsumelim = 20` recently learned clauses (`options.hpp:82-83`, `backward.cpp`) | `eagersubsume = 4` (`options.h:40`) |
| Embedded sub-solver | `kitten.c`, 2,599 lines — a separate CDCL used by sweeping and definition mining, with core extraction | `kitten.c`, 2,877 lines |

Against ours: `proof_sat.rs` is VSIDS + Luby only, `PhasePolicy::pinned()` never
rephases and `use_ema_restart` defaults false with **no setter outside
`#[cfg(test)]`** (`01-sat-core-and-cnf.md`, doc-drift items 2 and 3). So the
stable/focused split — which is what gives CaDiCaL two different search
personalities on one instance — has no analogue on our side at all.

### D. Inprocessing (during search)

This is the centerpiece. CaDiCaL's search loop (`internal.cpp:280-347`) reaches
simplification through five guards, in this priority order after
restart/rephase: `reducing()` → `inprobing()` → `ineliminating()` →
`compacting()` → `conditioning()`.

`inprobing()` (`probe.cpp:16-26`) fires when `lim.inprobe <= stats.conflicts`
**and** at least one clause-DB reduction has happened since the last probe
phase. The new limit is set at the end of `inprobe`:

```
lim.inprobe = stats.conflicts + 25 * opts.inprobeint * log10(inprobingphases + 9)
```
(`probe.cpp:981-983`, `inprobeint = 100`). The comment above it
(`probe.cpp:876-912`) states the design intent explicitly: the number of
inprocessing rounds is "always the square root of the number of conflicts with
some constant factor."

The 24 passes, with the scheduler that reaches each one:

| # | Pass | File | Reached from | Default | Proof story | Kissat | axeyum |
|---|---|---|---|---|---|---|---|
| 1 | Binary deduplication | `deduplicate.cpp` | `inprobe` (`probe.cpp:938`, `:948`) | on | `d` only | yes (in `substitute`) | **no** |
| 2 | SCC + equivalent-literal substitution (ELS) | `decompose.cpp:125-140`, `:736-740` | `inprobe` (`probe.cpp:939`, and re-run at `:941`, `:943`, `:946`, `:950`) | on, `decomposerounds = 2` | `d` + RUP; `weaken_minus` at `:452`, `:472` for reconstruction | `substitute.c` (617 lines) | **no** |
| 3 | Hyper ternary resolution | `ternary.cpp` | `inprobe` (`probe.cpp:940`) | on, `ternaryeffort = 8` per mille | resolvents are RUP | **absent** | **no** |
| 4 | Failed-literal probing | `probe.cpp:787-880` | `inprobe` (`probe.cpp:942`) | on, `probeeffort = 8` per mille | failed literal ⇒ unit, RUP; LRAT chain built by `probe_dominator_lrat` (`:113`) | **absent** | **no** |
| 5 | Hyper binary resolution | `probe.cpp:218-290` | inside 4, `opts.probehbr = 1` | on | resolvent is RUP | **absent** | **no** |
| 6 | Gate extraction + congruence closure | `congruence.cpp` (7,925 lines) | `inprobe` (`probe.cpp:945`) | `congruence = 1`; AND, XOR (arity ≤ 4), ITE (`options.hpp:64-72`) | merges are equivalences ⇒ binary clauses, RUP with chains | `congruence.c` (4,636) | **no** |
| 7 | Binary-clause backbone | `backbone.cpp` | `inprobe` (`probe.cpp:947`, `:953`) | `backbone = 1`, `backboneeffort = 20` per mille | units, RUP | `backbone.c` | **no** |
| 8 | SAT sweeping | `sweep.cpp` (1,976 lines) | `inprobe` (`probe.cpp:949`) | `sweep = 1`, env ≤ 256 vars / 1024 clauses | equivalences proved by `kitten`; `kitten_trace_core` yields the antecedents for an LRAT chain (`sweep.cpp:603-604`, `:913-938`) | `sweep.c` (1,724) | **no** |
| 9 | Vivification | `vivify.cpp` (1,893 lines) | `inprobe` (`probe.cpp:951`) | on; separate budgets per tier (`vivifytier1eff/2eff/3eff = 4/2/1`) and for irredundant clauses (`vivifyirredeff = 3`) | strengthened clause is RUP, original deleted | `vivify.c` (1,480) | **yes** (`vivify.rs`, off by default) |
| 10 | Transitive reduction of the binary implication graph | `transred.cpp` | `inprobe` (`probe.cpp:952`) and `subsume` (`subsume.cpp:639`) | on | `d` only | `transitive.c` | **no** |
| 11 | Bounded variable addition (BVA / "factor") | `factor.cpp` (1,018 lines) | `inprobe` (`probe.cpp:954`) | **off** in CaDiCaL (`factor = 0`, `options.hpp:119`); **on** in Kissat (`options.h:54`) | the only genuinely non-RUP addition: `add_derived_rat_clause` with the fresh literal pushed first (`factor.cpp:617-628`) | `factor.c` (1,156) | **no** |
| 12 | Bounded variable elimination (BVE) | `elim.cpp` (1,175 lines) | main loop, `ineliminating()` (`elim.cpp:60-84`) | on, `elimint = 2000`, `elimrounds = 2`, bound grows to `elimboundmax = 16` | resolvents are RUP; originals `weaken_minus` + `d` (`elim.cpp:630`, `:652`) | `eliminate.c` | **yes** (`bve.rs`, off by default) |
| 13 | Forward subsumption + self-subsuming resolution | `subsume.cpp` (646 lines) | `elim` (`elim.cpp:1048`, `:1097`) and standalone `subsume()` (`subsume.cpp:607`) | on | strengthened clause RUP (`subsume.cpp:140`, `:164`) | `forward.c` + `strengthen.c` | **yes** (`simplify.rs`, off by default) |
| 14 | On-the-fly self-subsumption during elimination | `elim.cpp:209-262` | inside 12 | on | RUP | in `eliminate.c` | **no** |
| 15 | Eager backward subsumption of resolvents | `backward.cpp` | inside 12 (`elimbackward = 1`) | on | `d` only | inside `forward.c` | **no** |
| 16 | Gate detection to bound BVE resolutions | `gates.cpp` (766 lines) | inside 12 (`elimands`, `elimequivs`, `elimites`, `elimxors` all 1) | on | — (search restriction, not a formula change) | `gates.c`, `ands.c`, `ifthenelse.c`, `equivalences.c` | **no** |
| 17 | Definition mining with `kitten` | `definition.cpp` | inside 12, `opts.elimdef` | **off** (`options.hpp:91`) | kitten core ⇒ LRAT chain (`definition.cpp:87`) | `definition.c`, `definitions = 1` (**on**) | **no** |
| 18 | Blocked clause elimination | `block.cpp` (824 lines) | `elim` round loop (`elim.cpp:1099`) | **off** (`block = 0`, `options.hpp:34`) | `d` + `weaken_minus` (`:274`, `:410`, `:626`) | **absent** | **no** |
| 19 | Covered clause elimination | `cover.cpp` (704 lines) | `elim` round loop (`elim.cpp:1101`) | **off** (`cover = 0`) | `weaken_plus` (`:406`, `:442`) | **absent** | **no** |
| 20 | Variable instantiation | `instantiate.cpp` | end of an `elim_round` | **off** (`instantiate = 0`) | RUP with an explicit chain (`instantiate.cpp:73-74`) | **absent** | **no** |
| 21 | Globally blocked clause elimination ("conditioning") | `condition.cpp` (942 lines) | main loop, `conditioning()` | **off** (`condition = 0`) | `weaken_minus` with a **multi-literal** witness (`:792`) | **absent** | **no** |
| 22 | Fast BVE (preprocessing-only variant) | `elimfast.cpp` | `preprocess_quickly` (`internal.cpp:787-788`) | `fastelim = 1`, but its **caller** is gated on `preprocesslight = 0`, so off in practice | as 12 | `fastel.c`, `fastel = 0` (**off**) | **no** |
| 23 | Variable compaction / renumbering | `compact.cpp` | main loop, `compacting()` | `compact = 1`, `compactint = 2000` | not a proof event (external ids unchanged) | `compact.c` | **yes** (`compact.rs`, off by default) |
| 24 | Local search (ProbSAT-style walk) | `walk.cpp` + `walk_full_occs.cpp` | `rephase` (`rephase.cpp:98-108`) | `walk = 1` | no proof events (phases only) | `walk.c` | see below |
| — | Gaussian / XOR propagation | — | — | — | — | — | **yes** (`xor_propagate.rs`) — no CaDiCaL analogue |

Counting the ones with a dedicated source file: **24 in CaDiCaL, 5 in axeyum**,
and of our five, four (subsumption, vivification, BVE, compaction) have a
CaDiCaL counterpart and one (XOR/Gaussian propagation) does not.

Three points about that table that a raw count hides:

1. **Seven of CaDiCaL's are off by default** (11, 17, 18, 19, 20, 21, and 22 in
   Kissat). Biere ships them and does not run them. That is a different posture
   from ours: ours are off because a lever was never flipped
   (`11-wiring-and-integration.md` gap #1 lists `cnf_inprocessing: false` as an
   *integration gap*, not a decision), his are off because they lost a
   measurement. The difference matters for how we should read the count.
2. **The re-run discipline is the real structure.** `decompose()` is called five
   times inside one `inprobe` (`probe.cpp:939`, `:941`, `:943`, `:946`, `:950`),
   each time guarded by "did the previous step derive a binary clause". Our
   `inprocess()` is a straight line of five stages
   (`sat_bv_backend.rs:1827-2083`, order recorded in
   `01-sat-core-and-cnf.md`) with no fixpoint and no re-entry.
3. **Budgets are per-pass and self-calibrating.** `SET_EFFORT_LIMIT(limit, probe,
   true)` at `probe.cpp:796` expands (`limit.hpp:136-164`) to: measure search
   ticks since this pass last ran; take `probeeffort/1000` of them; if that is
   less than `probethresh * clauses.size()`, **return false and do not run at
   all**; otherwise add the delta to a running per-pass tick budget. The
   `Delay` struct (`delay.hpp:9-34`) adds exponential back-off on top for passes
   with expensive setup (sweep, vivify, factor), doubling the skip count when a
   pass was useless and halving it when it paid. We have `PassWork`
   (`pass_work.rs`, 310 lines) as a work meter for two passes, and no
   cross-pass budget, no threshold refusal, and no back-off.

**Local search (24)**: we do have a stochastic local search, `pbls.rs`
("`WalkSAT` family", its own header), but it is a **word-level portfolio member
over the typed IR** returning `Sat`-or-`Unknown`, `full`-gated
(`crates/axeyum-solver/src/lib.rs:162`). CaDiCaL's `walk` is a CNF-level phase
*producer* consumed by rephasing — it never answers the query, it seeds
`phases.target`. Different mechanism, same paper lineage; do not score these as
equivalent.

### E. Encoding / bit-blasting

n/a in the forward direction — both take CNF as input and neither has a term
level, an AIG, or structural hashing.

**But the reverse direction is live and is a finding.** `congruence.cpp` (7,925
lines), `gates.cpp` (766) and `definition.cpp` exist to *recover* AND, XOR and
ITE gate structure that was destroyed when someone else Tseitin-encoded the
problem, and `definition.cpp` goes further, mining definitions with an embedded
SAT solver. We are on the other side of that fence: `axeyum-bv` builds an AIG
with structural hashing and constant folding (`axeyum-aig/src/lib.rs:136`,
`:345`), `tseitin_encode` flattens it, and the only thing carried across is
`variable_bindings`, a CNF-var→AIG-literal map kept for **model replay**
(`axeyum-cnf/src/lib.rs:2680-2705`). Nothing consumes the gate structure for
simplification. Our own `xor_extract.rs` (531 lines) then recovers XOR gates
*from clauses* — re-deriving, at the CNF level, structure the AIG one layer up
already had. Neither solver has this option; we do, and do not take it.

### F. Theory solvers

n/a — pure propositional solvers, no theory layer of any kind.

### G. Theory combination

n/a — follows from F.

### H. Quantifiers

n/a — follows from F.

### I. Model production

**CaDiCaL.** The internal model is the trail; the **external** model is produced
by replaying the extension stack backwards (`extend.cpp`), which re-satisfies
every clause that BVE, BCE, CCE, conditioning or ELS removed. Self-validation
is real and on by default at the API level: `opts.checkwitness = 1`
(`options.hpp:49`) makes `External::check_assignment` (`external.cpp:704`) run
after `solve` returns 10 (`external.cpp:555-556`), and `solver.cpp:1529`
re-checks a user-supplied solution. `flip`/`flippable` (`cadical.hpp:353`,
`:361`, `flip.cpp`) let a caller mutate a returned model in place and have the
solver confirm it stays a model.

**Kissat.** `witness.c` + `extend.c`, same extension-stack mechanism;
`DBGOPT (check, 2, ...)` (`options.h:20`) — model checking is a *debug* option
here, not a default.

Ours: replay is per-route and there is no choke point
([`08-models-proofs-and-evidence.md`](../solver-inventory-2026-09/08-models-proofs-and-evidence.md),
"`sat` model replay is NOT universal and NOT centralized"). The default QF_BV
backend does replay unconditionally (`sat_bv_backend.rs:2387`, `:2424`), which
is the same guarantee CaDiCaL gives, on one route.

### J. Proof / certificate production

**CaDiCaL — six formats behind one observer interface.** `Tracer`
(`tracer.hpp:18-120`) is a pure-virtual event stream: `add_original_clause`,
`add_derived_clause(id, redundant, witness, clause, antecedents)`,
`delete_clause`, `demote_clause`, `weaken_minus`, `strengthen`,
`finalize_clause`, `begin_proof`, plus incremental events (`solve_query`,
`add_assumption`, `add_constraint`, `reset_assumptions`) and
`conclude_unsat/sat/unknown`. Implementations:

| Tracer | File | Granularity |
|---|---|---|
| DRAT | `drattracer.cpp` | clause additions and deletions, text or binary; **drops** the id, the redundancy flag, the witness and the antecedents (`drattracer.cpp:86-97`) |
| LRAT | `lrattracer.cpp` | id + antecedent chain per step |
| FRAT | `frattracer.cpp` | ids, optional antecedents (`with_antecedents`), finalization |
| IDRUP | `idruptracer.cpp` | incremental DRUP: per-query, with assumptions |
| LIDRUP | `lidruptracer.cpp` (657 lines) | incremental + antecedents + weakening/restore events |
| VeriPB | `veripbtracer.cpp` | pseudo-Boolean proof format, optional checked deletions |

`opts.checkproof` defaults to 3 = "1=drat, 2=lrat, 3=both"
(`options.hpp:48`), meaning **when checking is enabled at all, both internal
checkers run**.

**How the proof survives inprocessing.** Three mechanisms, and it is worth being
exact because this is the reason `axeyum-cnf/src/inprocess.rs` exists:

1. **Additions are RUP or explicitly RAT.** Every pass in §D that adds a clause
   adds a resolvent, a strengthened clause, a unit derived by propagation, or a
   binary derived from an implication chain — all RUP. The one exception is BVA,
   which introduces a *fresh variable* and therefore cannot be RUP; it goes
   through `Proof::add_derived_rat_clause`, and `Internal::blocked_clause`
   (`factor.cpp:617-628`) pushes the witness literal `not_fresh` as
   `clause[0]` before calling it, which is exactly the DRAT convention the plain
   DRAT tracer relies on since it discards the explicit witness argument.
2. **Removals are just deletions.** BCE, CCE, conditioning, transitive
   reduction, deduplication and BVE's discarded originals all emit `d` lines.
   Deleting a clause can only *weaken* the formula, so a refutation of the
   reduced formula is a refutation of the original. This is the asymmetry that
   makes inprocessing DRAT-compatible at all, and it is why our
   `ReductionLink::check_unsat` has to report *coverage* — checking against the
   reduced formula is not the same statement as checking against the original
   (`sat_bv_backend.rs:2701-2730`).
3. **The satisfiability direction leaves the proof entirely.** Everything needed
   to reconstruct a model of the *original* formula lives on the extension stack
   (`extend.cpp`), not in the DRAT file. `weaken_minus` exists as a tracer event
   for the formats that *do* care about restoration (IDRUP/LIDRUP/VeriPB); the
   DRAT tracer does not override it, so it is a no-op there
   (`drattracer.cpp` defines no `weaken_minus`; the base class's empty body at
   `tracer.hpp:61` applies).

Our side matches (1) and (2) in `inprocess.rs`, which "runs subsume/vivify/BVE
and emits one DRAT stream that checks against the **original** formula"
(`01-sat-core-and-cnf.md`) — and that module has no production caller. The
shipping path instead stitches a `ReductionLink` prefix and reports coverage.
For (3), `bve.rs` carries a `Reconstruction` and `compact.rs` a `CompactMap`,
i.e. per-pass inverse maps rather than one uniform stack.

**Kissat — DRAT only.** `proof.c` (408 lines) writes text or binary DRAT and
nothing else: `kissat_add_clause_to_proof`, `kissat_delete_clause_from_proof`,
`kissat_shrink_clause_in_proof` (`proof.c:317-400`). Confirmed absent by
`grep -rli lrat src/` over the Kissat tree, which returns only `kitten.c` — the
embedded sub-solver's internal core machinery — while the control
`grep -rli drat src/` returns `kitten.c` and `application.c`. So Kissat at
4.0.4 cannot emit LRAT, FRAT, IDRUP or VeriPB.

We emit DRAT (text and binary), LRAT, and Alethe
(`01-sat-core-and-cnf.md`, proof-artifact table). We do not emit FRAT, IDRUP,
LIDRUP or VeriPB.

### K. Proof checking

**CaDiCaL, in-tree, two checkers**: `checker.cpp` (649 lines) checks DRAT
online against the live formula; `lratchecker.cpp` (833 lines) checks LRAT
including RAT additions. Both are `Tracer` implementations, so they consume the
same event stream the file writers do — they are not parsers. Enabled by
`opts.check` (default 0) with `checkproof` selecting which
(`options.hpp:43-49`). Additional online invariants: `checkassumptions`,
`checkconstraint`, `checkfailed`, `checkwitness`, `checkfrozen`.
`solution.cpp` cross-checks every learned clause against a known solution file
(`check_solution_on_learned_clause`, `:13`) — a soundness-negative harness we
have no equivalent of.

**Kissat**: `check.c` (1,033 lines), enabled by a `DBGOPT` — debug builds only.

Ours: `check_drat` (forward RUP+RAT), `check_drat_backward`, `check_lrat`
(RUP+RAT since ADR-1722), `check_alethe`, plus external Carcara and Lean
cross-checks that are **not wired to any gate**
(`11-wiring-and-integration.md` gap #6). On this axis we are ahead of Kissat
and roughly level with CaDiCaL, with the important difference that CaDiCaL's
checkers are fed by the tracer interface (so they see every event any writer
sees) while ours parse artifacts.

### L. Interpolation

n/a for both — no interpolation in either tree. We have
`propositional_interpolant{,_certified}` (`axeyum-cnf/src/interpolant.rs`,
694 lines, WIRED into two solver modules), which is a capability neither
reference has.

### M. Optimization

n/a for both — no MaxSAT, no objectives. CaDiCaL is used *as* a MaxSAT back end
by other projects, but nothing in this tree implements it.

### N. Incrementality

**CaDiCaL** is fully incremental and is the reference implementation for the
hard part of it: `assume`/`failed`/`constrain`/`constraint_failed`
(`cadical.hpp:290`, `:370`, `:482`, `:491`), `freeze`/`melt` (`:830-831`),
`simplify(rounds = 3)` as a preprocess-only entry point (`:789`), and
`restore.cpp` (the SAT'19 Fazekas/Biere/Scholl restoration algorithm), which
solves the genuinely difficult problem: after BVE/BCE removed clauses, adding a
new clause mentioning an eliminated variable requires **restoring** exactly the
weakened clauses whose witness literal is now "tainted"
(`restore.cpp:8-46`). ILB (incremental lazy backtracking) keeps the trail
across calls (`opts.ilb`, default 0, `options.hpp:139`;
`internal.cpp:356-360`, `assume.cpp:551-605`). IPASIR-UP is implemented:
`connect_external_propagator`, `add_observed_var`, `propagate`, `lookahead`
(`cadical.hpp:412-539`, `external_propagate.cpp`, 1,601 lines).

**Kissat** exposes the IPASIR surface (`kissat.h`, `ipasir` shim in the build)
but the tree has no `restore.c` and no external-propagator file; its incremental
support is much thinner.

Ours: `IncrementalSat` / `NativeIncrementalCdcl` at the CNF layer with
assumptions and failed-assumption cores, but `Solver::push`/`pop` is a `Vec`
watermark that re-submits everything (`solver.rs:126-142`,
`11-wiring-and-integration.md` gap #4). We have no analogue of `restore.cpp`,
which is unsurprising — you only need it once inprocessing is on *and*
incremental, and ours is neither.

### O. Parallelism

**None in either.** Verified: `grep -rn "pthread\|std::thread\|#include
<thread>\|omp parallel" references/cadical/src/` and the same over
`references/kissat/src/` both return nothing, while the control
`grep -rc Internal references/cadical/src/internal.hpp` returns 13 and
`grep -rc kissat references/kissat/src/internal.h` returns 5, so the greps were
pointed at real files. (An earlier looser pattern including bare `omp` produced
false hits on `compare`/`complete` and was discarded — recorded so the negative
is reproducible.)

Cube-and-conquer is supported as *input* (`p inccnf`, `parse.cpp:109`,
`lookahead.cpp`) — CaDiCaL is the sequential worker in a parallel scheme
someone else runs. Ours has `axeyum-cnf/src/cube.rs` (1,863 lines, example and
test-only) plus a `portfolio` module whose fused group needs
`AXEYUM_PORTFOLIO_WORKERS >= 2` and defaults to 1 (`11-wiring-and-integration.md`
gap #8).

### P. Resource limits and determinism

**CaDiCaL.** Named limits through one string API, `Solver::limit(const char *,
int)` (`cadical.hpp:758`): conflicts, decisions, preprocessing rounds,
localsearch, terminate. `Solver::terminate()` and a `Terminator` callback for
asynchronous stop (`:379`, `:797`). `opts.seed = 0` (`options.hpp:204`) drives
every random choice: `Random random (opts.seed)` in rephasing
(`rephase.cpp:77`) and random decisions (`decide.cpp:84`), each offset by a
counter so successive draws differ but reproducibly. Effort is denominated in
**ticks** (a cache-aware work proxy), not wall clock, which is what makes the
inprocessing schedule reproducible across machines. `opts.realtime = 0` means
process time by default, so even the reported profile is not wall-clock.
Configurations: `default`, `plain`, `sat`, `unsat` (`config.cpp:38-41`) —
`sat` sets `stabilizeonly = 1` and reduces elimination effort, `unsat` disables
stabilization and local search (`config.cpp:24-31`).

**Kissat.** Same shape: `seed` (`options.h:128`), conflict and decision limits
(`search.c:145-165`), effort budgets in per-mille of ticks. Configurations
`basic`, `default`, `plain`, `sat`, `unsat` (`config.c:10-36`), with `sat`
setting `--target`/`--restartint` and `unsat` setting `--stable`
(`config.c:31-35`).

Both ship a model-based tester: CaDiCaL's `mobical.cpp` (5,671 lines — 8% of
the tree) generates API call sequences and delta-debugs failures. We have
differential fuzzes against z3 and a corpus sweep; we have no API-sequence
fuzzer for the incremental interface.

## Gaps against axeyum

### 1. They have, we do not

| Capability | Their implementation | Our status | Rough size |
|---|---|---|---|
| **A tick budget that actually gates work** | `SET_EFFORT_LIMIT` (`cadical/src/limit.hpp:136-164`): per-pass budget = `effort/1000 × (search ticks since last run)`, with a `thresh × clauses` floor below which the pass **refuses to run**; `Delay` back-off (`delay.hpp:9-34`) | `ticks.rs` exists (405 lines) and **no shipping budget consumes it**; every budget is in conflicts (`01-sat-core-and-cnf.md`, gap 4) | Small — the meter exists. Wiring it to `PassWork` and the five passes is days, not weeks |
| **Inprocessing on by default** | `opts.inprocessing = 1` (`options.hpp:144`); `inprobing()`/`ineliminating()` fire during search | `cnf_inprocessing: false` (`backend.rs:390`); all five passes dead on a default run (`11-wiring-and-integration.md` gap #1) | One line plus the measurement to justify it. The measurement note is already cited in `inprocess.rs:132-140` |
| **A fixpoint schedule instead of a straight line** | `inprobe` re-runs `decompose()` after every step that can produce a binary (`probe.cpp:938-954`); `elim` alternates BVE / subsume / block / cover until nothing changes (`elim.cpp:1072-1110`) | `inprocess()` is five stages in sequence, once (`sat_bv_backend.rs:1827-2083`) | Medium — needs a "did this change anything" signal per pass, which `PassWork` half has |
| **Equivalent-literal substitution (SCC/ELS)** | `decompose.cpp:130` (`decompose_round`, Tarjan; 742 lines total), driven by `decompose()` at `:736-740` for `decomposerounds = 2`, called 5x per inprocessing phase | absent (`grep -rniE 'tarjan\|strongly connected' crates/` finds only `capabilities.rs` and `horn.rs`, neither a CNF pass) | Medium. This is the highest value/effort ratio on the list — cheap, and every other pass produces binaries for it to consume |
| **Failed-literal probing + hyper binary resolution** | `probe.cpp:787-880` and `:218-290` (`probehbr = 1`, `options.hpp:166`) | absent | Medium |
| **Gate/congruence recovery from CNF** | `congruence.cpp` (7,925), `gates.cpp` (766), `definition.cpp` | absent — and see "Not comparable", we have the gates already | Large as written; **near-zero for us** if we pass AIG structure down instead of recovering it |
| **SAT sweeping with an embedded sub-solver** | `sweep.cpp` (1,976) + `kitten.c` (2,599); equivalences proved by a bounded sub-solve, LRAT antecedents from `kitten_trace_core` (`sweep.cpp:603`) | absent | Large |
| **Dynamic clause tiers from measured usage** | `tier.cpp:7-80`, percentile of a used-glue histogram | `ClauseDbPolicy::tiered()` with fixed glue thresholds (`clause_db_policy.rs`) | Small |
| **Stable/focused mode switching** | `restart.cpp:19-84`; two decision heuristics, two restart policies, tick-budgeted with quadratic growth | absent. `use_ema_restart` is false with no setter outside `#[cfg(test)]`; `PhasePolicy::pinned()` never rephases (`01-sat-core-and-cnf.md`, doc drift 2-3) | Medium — both halves (EMA restart, phase policy) are already written and unreachable |
| **Rephasing with a local-search phase producer** | `rephase.cpp:37-160` cycles original/inverted/flipped/random/best/walk; `walk.cpp` seeds `phases.target` | `pbls.rs` is a word-level SLS *portfolio member*, not a phase producer; `PhasePolicy::pinned()` never rephases | Medium |
| **Bounded variable addition** | `factor.cpp` (1,018); the only RAT-emitting pass, witness-first (`:617-628`) | absent | Medium; note it is default-off in CaDiCaL and default-on in Kissat |
| **A uniform model-reconstruction stack** | `extend.cpp` — one witness stack that every eliminating pass writes to, replayed once | per-pass inverse maps (`bve.rs` `Reconstruction`, `compact.rs` `CompactMap`) | Medium; the refactor is worth doing before adding passes 4-8, not after |
| **Incremental restoration after elimination** | `restore.cpp` (SAT'19): re-add a clause mentioning an eliminated variable, restore exactly the tainted weakened clauses | absent; `Solver::push/pop` is a `Vec` watermark that resubmits (`solver.rs:126-142`) | Large, and only needed once inprocessing is on and incremental |
| **IPASIR-UP external propagator** | `external_propagate.cpp` (1,601), `cadical.hpp:412-427` | absent at the CNF layer. `proof_sat/theory.rs` is the nearest thing and is `full`-gated with one caller | Large |
| **Proof formats: FRAT, IDRUP, LIDRUP, VeriPB** | four tracers, `frattracer.cpp` etc. | DRAT, LRAT, Alethe | Medium each; IDRUP/LIDRUP only matter once we are incremental |
| **Checkers fed by the event stream, not by parsing** | `checker.cpp`/`lratchecker.cpp` are `Tracer` implementations (`tracer.hpp:18`), so they observe every event | our checkers parse artifacts | Small conceptually, invasive in practice |
| **Learned-clause cross-check against a known solution** | `solution.cpp:13-46`: every learned clause, every shrunken clause, every learned unit checked against a solution file | absent | Small, and it is a soundness-negative harness — high value per line |
| **API-sequence model-based tester** | `mobical.cpp` (5,671), generates and delta-debugs incremental call sequences | absent | Medium |

### 2. We have, they do not

Short, and honestly so — most of it is a layering difference, moved to "Not
comparable" rather than counted here. What is genuinely a *propositional-layer*
capability we have and they do not:

| Capability | Ours | Theirs |
|---|---|---|
| XOR / Gaussian reasoning | `gf2.rs` (758), `xor_extract.rs` (531), `xor_propagate.rs`, `xor_cdcl.rs` (1,543, CDCL(XOR)), `xor_gauss_drat_refutation` (ADR-0035) | absent from both trees. CaDiCaL extracts XOR *gates* for congruence closure and BVE (`congruencexor`, `elimxors`) but does no Gaussian elimination |
| Propositional interpolation | `interpolant.rs` (694), McMillan from a resolution refutation, with a certified variant | absent from both |
| Alethe emission and checking | `alethe.rs` (5,152), `check_alethe`, `lrat_to_alethe` | absent from both |
| Backward / core-first DRAT checking + trimming | `drat_backward.rs` (2,866), ADR-0382 | CaDiCaL's checkers are forward and online; trimming is `drat-trim`'s job |
| Memory-model-driven proof route selection | `drat_resource.rs` (1,000): estimate proof shape and pick forward vs backward vs decline | absent |
| Memory-safety of the whole layer | `unsafe_code` denied workspace-wide | C/C++ throughout |
| WASM target | `cargo build --target wasm32-unknown-unknown -p axeyum-solver` (ADR-0017) | not a target for either |

Two of those need a caveat rather than a victory lap. `xor_cdcl` is
config-gated behind `xor_cdcl_fallback` (default false) and `xor_matrix.rs`
(1,595 lines) is bench-only; the interpolation route is `full`-gated. So most
of this column is *implemented* rather than *running*, which is the same
finding as gap #1 in the other direction.

## Not comparable

- **The whole stack above CNF.** axeyum has a typed term IR, sixteen rewrite
  passes, bit-blasting with an AIG, theory solvers for LRA/LIA/NRA/NIA/BV/
  arrays/FP/EUF/strings, quantifier instantiation, and reconstruction into a
  Lean-style kernel. CaDiCaL and Kissat have none of that and are not trying
  to. **This is a layering difference, not a capability win.** The right
  comparison object for our SAT layer is `crates/axeyum-cnf` (48,355 lines,
  of which `proof_sat.rs` is 8,333) against `references/cadical/src` (63,710
  excluding the tester), and on that comparison we are behind on inprocessing
  by roughly 19 passes. Any table that scores "axeyum: 30 logics, CaDiCaL: 0"
  is measuring the wrong thing and should not appear in the gap analysis.
- **"Kissat is newer than CaDiCaL."** Version numbers say 4.0.4 vs 3.0.1, but
  the *clones* are 2025-10 vs 2026-07, and CaDiCaL 3.0.1 at this SHA contains
  passes Kissat 4.0.4 does not (ternary, probing, HBR, blocked, covered,
  conditioning, instantiation, LRAT). Whether that is Biere consolidating on
  CaDiCaL, Kissat dropping what did not pay, or nine months of skew, **I cannot
  tell from these two trees**. Do not use this pairing to argue a direction of
  travel.
- **Default-off is not the same thing on both sides.** Seven CaDiCaL passes are
  default-off after measurement; our five are default-off because nobody flipped
  a lever, and one of the two implementations of them has no caller at all. The
  counts look similar and mean opposite things.
- **Gate recovery vs gate retention.** Comparing `congruence.cpp` (7,925 lines)
  to nothing on our side reads as a 7,925-line gap. It is not: those lines
  reconstruct structure from CNF that we still have one layer up in the AIG.
  The gap is an interface (pass gate structure from `axeyum-bv` into the CNF
  layer), not an algorithm. Sizing it as an algorithm would be the most
  expensive error in this file.
- **Effort budgets and our conflict budgets are not convertible.** Their ticks
  are a cache-aware work proxy; our `resource_limit` is conflicts
  (`DEFAULT_PROOF_SAT_CONFLICT_LIMIT = 2_000_000`, `proof_sat.rs:46`). A
  head-to-head "budget" row in the gap analysis would be comparing different
  units.
- **Kissat's `check.c` and CaDiCaL's `checker.cpp` are not peers.** Kissat's is
  behind a `DBGOPT` (debug builds); CaDiCaL's is a runtime option. Counting both
  as "in-tree checker: yes" would hide that.

## Confidence

**Solid source reads** (I read the code, not a comment or a name):

- The `inprobe` schedule and its exact call order (`probe.cpp:914-990`) and the
  limit formula (`:985-987`).
- The main loop's ten branches and their order (`internal.cpp:280-347`).
- `SET_EFFORT_LIMIT`'s full expansion including the refusal path
  (`limit.hpp:136-164`) and `Delay` (`delay.hpp:9-34`).
- `use_scores() = opts.score && stable` and both call sites
  (`internal.hpp:476`, `decide.cpp:113`, `restart.cpp:136`).
- The stable/focused switch and its quadratic tick growth (`restart.cpp:19-84`).
- Tier recomputation as a usage percentile (`tier.cpp:7-80`).
- Every default value quoted from `options.hpp` / `options.h` — these are the
  option-definition macros, read directly.
- `DratTracer::add_derived_clause` discarding the witness argument
  (`drattracer.cpp:86-97`) and `blocked_clause` pushing the witness first
  (`factor.cpp:617-628`). The two together are what make BVA DRAT-valid, and I
  checked both halves.
- `elim`'s inner alternation with subsume/block/cover (`elim.cpp:1017-1173`).
- Kissat's probe schedule (`probe.c:26-42`) and preprocess schedule
  (`probe.c:44-67`, `preprocess.c:29-73`).
- Absence of LRAT in Kissat, and absence of threads in both — both confirmed
  with a stated positive control, quoted in §J and §O.
- Absence of `block.c`, `condition.c`, `ternary.c`, `instantiate.c` in Kissat's
  `src/` by directory listing, with `cover.h` explicitly checked and found to be
  the `COVER()` assertion macro, **not** covered clause elimination — a name
  collision that would otherwise have produced a false positive.

**Inferences, flagged as such:**

- "24 named passes" is my count of files-with-a-pass in §D. A different
  granularity (counting `gates.cpp` as part of `elim`, or splitting `probe` into
  FLP and HBR) gives 22 or 25. The *ratio* to our five is the finding; the
  absolute number is a convention.
- The claim that CaDiCaL's default-off passes are "off after measurement" is
  inferred from Biere's practice and from the presence of tuned per-pass effort
  options, not from a comment in the tree saying so.
- Effort/size estimates in the gaps table are judgment, not measurement.
- Kissat's incremental support being "much thinner" rests on the absence of
  `restore.c` and an external-propagator file plus the presence of the IPASIR
  header; I did not read `kissat.h`'s incremental contract line by line.
- `congruence.cpp`'s algorithm: I read the gate types
  (`congruence.hpp:72`, AND/XOR/ITE), the entry point and the proof calls, not
  the 7,925 lines of closure logic. Claims about *what* it extracts are solid;
  claims about *how* it closes are not made.
- I did not read `mobical.cpp`, `external_propagate.cpp`, or `walk.cpp` beyond
  their headers and call sites.

**`[undetermined]`:**

- Whether Kissat 4.0.4's dropped passes were removed or never ported. Would need
  the Kissat NEWS/changelog history, which this shallow clone does not carry
  (`--depth 1`), or a non-shallow clone.
- Whether CaDiCaL's LRAT path covers *every* pass or degrades to DRAT for some.
  `sweep.cpp` and `probe.cpp` build explicit chains and `elim.cpp` asserts
  `!lrat || !lrat_chain.empty()` (`elim.cpp:407`, `:591`), which is suggestive,
  but I did not audit all 24 passes for LRAT completeness. Next file to read:
  `lratchecker.cpp` plus every `assert (!lrat ...)` site.
