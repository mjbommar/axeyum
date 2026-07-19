# axeyum + glaurung: a Pareto-dominance research and engineering plan

Status: draft
Date: 2026-07-18
Owners: axeyum (solver) + glaurung (consumer / symbolic-execution engine)
Companion artifacts:
- glaurung `docs/axeyum-integration/benchmark/` (benchmark + REVIEWER-CHECKLIST)
- glaurung `docs/axeyum-integration/07-decision-log.md` (ADR-022..025)
- axeyum `docs/research/09-decisions/adr-0236-canonical-tcpip-authority-policy.md`
- axeyum `docs/research/09-decisions/adr-0243-source-backed-glaurung-positive-control.md`

## 0. Thesis of this plan

The performance headline ("axeyum is 2.8-15.6x faster than z3") did not survive a
fair baseline: with a warm z3 control, DptfDevGen is parity cold (0.97x) and
**favors z3 warm (0.79x)**. Chasing raw speed against a mature bit-blaster is a
losing, non-Pareto game. Instead, this plan argues that axeyum's real
differentiators -- **in-process, warm-incremental, deterministic, pure-Rust,
proof-carrying** -- are the *enablers* of a symbolic-execution program that asks
whether it can move the measured Pareto frontier on the axes that actually
matter to the downstream use cases: reproducibility and validated bug-finding
coverage, at acceptable performance and footprint. No current result establishes
overall dominance. The lead methods contribution is strict typed
translation plus multi-oracle differential validation: it exposed real consumer
soundness defects that the permissive adapter masked. The integration
contribution is a **concretization policy** whose settings can be swept
reproducibly against separately reported raw, confidence-gated, and validated
finding populations. Axeyum's warm path may make richer settings affordable,
but whether any setting improves validated coverage is an experimental question,
not a premise of the plan.

## 1. The objective space (Pareto axes) and where we sit today

| Axis | What it means for the product | Current position (measured) |
|---|---|---|
| **Soundness** | never a wrong verdict | Strong: 0 verdict disagreements over ~250k real queries; strict typing caught 3+ consumer soundness bugs z3 masked |
| **Reproducibility / determinism** | same input -> same findings, across backends/runs/machines | Mixed: the bounded four-driver tier has exact raw authority parity, but tcpip AnyModel differs by two diagnostic rows and wall-clock timeouts remain nondeterministic |
| **Coverage (recall)** | fraction of true bugs found | Real-world recall remains unmeasured: tcpip first-15 and corrected usbprint are zero-positive. ADR-0243 adds a planted 14-row source/machine-validated regression denominator, not a representative sample |
| **Precision** | fraction of findings that are real | 14/14 with no unexpected producer-high row on the planted control; real-driver precision remains unquantified beyond the corrected producer confidence policy |
| **Performance (cold)** | one-shot small formulas | ~parity to 1.34x slower on the deduped corpus; bit_blast+cnf = 84% of cost |
| **Performance (warm)** | retained-state, real streams | Workload-dependent: favors z3 on DptfDevGen, favors Axeyum on IntcSST and SurfacePen, and is parity on vwififlt; formula size alone does not explain the split |
| **Deployability** | pure-Rust / no-C / WASM / footprint | Strong and unique: zero `unsafe`, wheel-shippable, WASM-buildable; qfbv-minimal profile now enforced (ADR-025) |
| **Verifiability** | checkable evidence for verdicts | Strong and unique: DRAT unsat certificates with self-recheck; unused downstream so far |

No single backend dominates. The frontier we must characterize is
**reproducibility x validated coverage** while holding soundness and
deployability (already strong) and honestly scoping performance.

## 2. Downstream use cases (who consumes this, and how they rank the axes)

1. **Driver/kernel IOCTL vulnerability hunting (IOCTLance-class)** -- the primary.
   Controlled-write / arbitrary-read / UAF / double-fetch / integer-overflow
   sinks in Windows `.sys` and Linux `.ko`. Ranks: **coverage > precision >
   reproducibility > speed**. Competes with DEADLINE (symbolic double-fetch) and
   Bochspwn (dynamic). The current tcpip model-sensitive rows are generic
   `Arg0` diagnostics, not validated bugs. Complete x64 `usbprint.sys` also
   falls to zero validated rows after separating the I/O-manager-owned
   SystemBuffer address from attacker-controlled contents (ADR-0242). ADR-0243
   now supplies a separate source/machine-validated planted positive control:
   14 finding rows at 12 sites across nine fixtures. It can gate policy
   regressions, but it is not a real-world recall sample.
2. **AI-native RE agent substrate (glaurung L1-L5 vuln discovery)** -- the LLM
   loop needs *fast, in-process, no-subprocess, no-C, deterministic* solving and
   **proof-carrying verdicts** (the "verdicts must cite" rule). Ranks:
   **determinism + latency + proofs > raw throughput**. This is where axeyum's
   in-process + DRAT story is uniquely valuable and z3-via-FFI is worst.
3. **WASM / browser / sandboxed analysis** -- pure-Rust/no-C is the *enabler*;
   libz3 simply cannot ship here. Ranks: **deployability = gating**, everything
   else secondary. Unique axeyum territory.
4. **Reproducible security research and CI regression gating** -- the product
   *is* determinism: same binary -> same findings, run to run, machine to
   machine. Ranks: **reproducibility = gating**. libz3's FFI nondeterminism and
   wall-clock timeouts make this hard today; a work-bounded pure-Rust solver can
   own it.

Observation: **three of four use cases rank determinism and deployability above
raw speed**, and none of them is served by "beat z3 on hard QF_BV." The plan
optimizes for what the consumers actually need.

## 3. State of the art, and axeyum/glaurung's honest position

### 3.1 Bit-vector SMT solving
- **Bitwuzla** is the QF_BV reference (SMT-COMP QF_BV leader; bit-blasting +
  local search + sequential combination; parallel STP-Parti-Bitwuzla won the
  parallel QF_BV track at SMT-COMP 2025; Bitwuzla+Mallob for massively parallel
  bit-precise verification). **z3/PolySAT** pushes *word-level* BV reasoning
  (polynomial/interval arithmetic, incremental linearization) rather than pure
  bit-blasting. **CoqQFBV** is a *Coq-certified* QF_BV solver -- the closest
  competitor to axeyum's proof-carrying angle.
- **axeyum's honest position:** not perf-parity on hard BV cold, and z3 wins warm
  on hard formulas. Its edge is not the decision procedure; it is
  deployability + proofs + in-process warm reuse. Do not fight Bitwuzla/z3 on
  raw QF_BV throughput; differentiate on the axes above.

### 3.2 Incremental / warm SMT
- Assumption-based incremental interfaces are standard; the frontier is
  **incremental abstraction-refinement for hard operators** (an incremental
  scheme with staged approximations for `mul`/`div`/`rem`, SMT 2020) and
  **word-level reasoning** (PolySAT, 2024). axeyum's warm path today reuses
  bit-blast/CNF/learned-clause state -- valuable, but *below the word level*.
  The unexploited lever for the cold bit_blast+cnf 84% cost is
  **abstraction-refinement + word-level preprocessing**, not more bit-blasting.

### 3.3 Symbolic-execution concretization (the crux)
- Known result: **concretization loses coverage, causes path divergence, and
  yields test-cases that do not reproduce the intended bug** (Symbolic Execution
  in Practice survey, 2025). The SOTA answer is **not "pick a better single
  value" -- it is symcrete values**: COLOSSUS (Deferred Concretization via
  Fuzzing, ISSTA 2019) and KLEEF (2024, 3rd at Test-Comp) carry a value that
  **masquerades as symbolic in the constraints but hides a concrete value
  consistent with the path**, so it delivers reproducibility (a fixed concrete
  witness) AND coverage (the symbolic constraint is retained, not thrown away).
  COLOSSUS reports **+66.94% coverage / >55% less divergence vs KLEE**, and
  recovers the ~38.6% of states KLEE drops. **memsight**-style fully symbolic
  memory removes concretization at memory accesses entirely (heavier).
- **Key correction (from iteration-1 research): a symcrete/consistent value is
  qualitatively different from a "better model choice."** Any single concrete
  value (any-model / least / greatest / boundary) *discards* the symbolic
  constraint; a symcrete value *keeps* it. This distinction is decisive for the
  double-fetch case (3.5).
- **glaurung today does the anti-pattern:** `concretize_addr` (explore.rs:1066)
  eagerly solves, takes an *arbitrary* model, and pins `addr == model`
  (`"glaurung-any-address-v1"`) -- discarding the symbolic address. This is the
  coverage-losing, divergence-inducing, non-reproducible pattern the literature
  warns about. In the measured tcpip slice it changes raw diagnostics, but the
  corrected producer reports no high-confidence finding to preserve or lose.

### 3.4 Diverse solutions / model sampling
- Active subfield: **disjoint projected enumeration without blocking clauses**
  (2024), **high-diversity SMT sampling** (2024), QuickSampler/cmsgen. Useful for
  *forking* concretization at value-dependent sinks -- but note (3.5) that
  enumerating diverse *concrete* values still discards the symbolic constraint,
  so for aliasing-dependent bugs it is a weaker tool than symcrete values.

### 3.5 Double-fetch / TOCTOU detection (the flagship use case) -- and why concretization policy is not enough
- **DEADLINE** (Xu et al., S&P 2018) is **static + source-level**: it finds
  multi-reads statically, then symbolically checks each for a changeable value
  (23 Linux + 1 FreeBSD bugs). **Bochspwn** is dynamic (x86 emulator, high
  overhead, ~87% FP under preemption). **SafeFetch** (USENIX Sec 2024) is
  protection, not detection. glaurung's differentiator: **binary-level (no
  source), per-path symbolic, reproducible, proof-carrying** -- a genuinely new
  point.
- **The load-bearing insight: a double-fetch is an *aliasing* property** -- "two
  reads from the *same* location," per the standard pattern definition. Detection
  requires the engine to reason that read1 and read2 target the same address.
  **Eagerly concretizing that address to a single value (of *any* policy) risks
  breaking the aliasing** if the two reads resolve to different concrete values.
  This is a mechanism to test on a labeled-positive case; it does not explain
  the two tcpip rows, which exact provenance analysis classified as generic
  `Arg0` diagnostics. **Therefore a diverse
  *concretization* policy (A3) is NOT guaranteed to recover them** -- the
  principled fix is a **symcrete / consistent-symbolic address** (the bounded
  first stage of A2),
  which keeps read1 and read2 provably aliased while retaining a reproducible
  concrete witness. This makes symcrete/symbolic memory a conditional
  architecture lever only after the cheap policy sweep leaves validated
  coverage headroom.

### 3.6 Constraint reuse in symbolic execution (prior art we must not re-claim)
- **Constraint caching/reuse is a mature SE field:** GREEN (Visser et al., 2012),
  GreenTrie (implication-based reuse), KLEE counterexample caching, Address-Aware
  Query Caching (2021), Partial-Solution Constraint Cache (FSE 2024) -- reported
  speedups ~1.07-2.3x. **So "reuse speeds up SE" is not novel and must not be
  claimed as such.** Critically, that literature caches at the *constraint-solution*
  level, in the SE engine, above the solver. axeyum's warm path is a *different*
  layer -- retained *solver-internal* AIG/CNF/learned-clause/SAT state across
  `check`s. The honest positioning: these are **complementary**, and a
  Green-aware reviewer will ask whether solver-internal warm reuse is *additive*
  over engine-level constraint caching or subsumed by it. That comparison
  (warm-axeyum vs a Green-style constraint cache in front of a cold solver) is a
  required experiment, not an assumption.
- **Proof-carrying verdicts are also mature** as SV-COMP *verification witnesses*
  (100k+ correctness / 71k+ violation witnesses validated in 2024; Witness Format
  2.0). "Attach a checkable proof to a verdict" is therefore not novel. axeyum's
  narrower, still-defensible slice: **DRAT-checked unsat certificates for
  infeasible-path pruning at the binary level, self-rechecked with no solver** --
  a solver-grounded, source-free variant of the witness idea, not a new concept.

## 4. The core tension, stated as a Pareto problem

From ADR-0236 and its ADR-0240/0241 corrected interpretation (tcpip, 15 functions):

| Concretization | Reproducible? | Raw diagnostics | High confidence | Notes |
|---|---|---:|---:|---|
| Any-model (default) | No (backend-dependent raw output) | z3 128 / axeyum 126 | 0 / 0 | two Z3-only `**Arg0` diagnostics |
| Least-unsigned canonical | Yes (identical hash) | 110 both | 0 / 0 | exact raw parity at substantially greater solve work |

Neither row establishes coverage: every emitted row on this slice is
diagnostic under the corrected producer policy, and no ground-truth positive
denominator exists **for this tcpip slice**. ADR-0243 independently establishes
a 14-row planted positive-control denominator; because those sinks are shallow
and intentional, it detects regressions but does not establish policy-driven
coverage improvement or real-driver recall.
Orthogonally, the **250ms wall-clock timeout** injects a *second*,
nondeterministic divergence (z3-unknown 52 vs axeyum-unknown 11 on tcpip) that
canonicalization does not touch. A Pareto claim therefore requires a nonzero
labeled-positive corpus and must compare validated recall, determinism, work,
time, and memory rather than maximize this raw union.

Crucially, these two rows are **not two algorithms -- they are two settings of
one knob.** `any-model` and `least-unsigned` are already-versioned policy tags
(`glaurung-any-address-v1`, `glaurung-min-unsigned-v1`); a candidate such as
`BoundarySet`/`DiverseEnum` is a *third setting of the same knob*,
not a research program. Making concretization a first-class configurable policy
(A0 below) is therefore the enabling move: it turns this table into an
**empirical sweep** where each row is one config, measured on the driver corpus.

The first two preregistered attempts add a critical constraint to that framing.
Minimum preserved the exact 14-row positive set but made complete usbprint exceed
the fixed resource boundary. Maximum preserved all 14 expected rows but added a
source-rejected `stack-overflow` classification at an arbitrary-pointer
`RtlCopyMemory`. Glaurung had inferred “stack” by comparing policy-selected
concrete `dst` and `rsp` values within a +/-64 KiB window. Thus the knob is cheap,
but detectors that derive semantic region facts from its arbitrary witnesses are
not policy-robust. ADR-0246 closes that prerequisite with structural expression-
DAG ancestry and restores the exact 14-row maximum-policy control. ADR-0247's
clean corrected sweep is now accepted: every scalar policy preserves the exact
14-row control, while tcpip policy variation remains entirely diagnostic and
unlabeled. The rejected v2 prefix remains evidence of the bug, not a source of
cells for the accepted matrix.

## 5. The Pareto-dominant program

Three pillars. Each move is chosen because it improves at least one axis with no
regression on the others (or an explicitly bounded, disclosed cost).

### Pillar A -- Concretization quality (the flagship). Most of it is *configuration*, not research.

**The load-bearing realization: concretization value-selection is a pluggable
policy, not a fixed algorithm.** Glaurung A0 has now made that half-built seam a
first-class public contract. `concretize_addr` and `eval_concrete` share one
policy mechanism while the explorer retains solver calls, checked evaluation,
address binding, and trace emission. This converts "which concretization is
Pareto-dominant?" from a debate into an **empirical sweep you run, not research
you speculate about**. Exactly one item in this pillar (symbolic memory) is
genuinely architectural; the rest are knobs or bounded explorer mechanics.

- **A0. Make concretization a first-class pluggable policy (DONE on isolated
  Glaurung branch).** The accepted `ConcretizationPolicy` covers the two
  value-selection seams; `witness_for_value` fixes its target by probe and
  remains outside the abstraction. Its stable contract is:
  ```rust
  pub trait ConcretizationPolicy {
      fn policy_id(&self) -> &'static str;
      fn choose(&self, request: ConcretizationRequest<'_>) -> ConcretizationChoice;
      fn trace_policy_id(&self, site: ConcretizationSite) -> &'static str;
  }
  ```
  `AnyModel` remains byte-for-byte default. Minimum, maximum, and the two stable
  site-hash schedules are executable settings selected by environment/config and
  self-identify in traces. `BoundarySet` and `Defer` are contract values, but
  fail closed until bounded successor forking or a changed memory model exists;
  they are not simulated by one scalar choice.
- **A0.5. Make semantic region classification model-independent (DONE,
  ADR-0246).** A concrete witness may execute a memory access, but accidental
  numeric proximity between two unconstrained witnesses must not prove that an
  address denotes stack storage. Glaurung now requires the destination to equal,
  contain the non-leaf DAG of, or share free-symbol ancestry with current
  `rsp`/`rbp` before applying numeric refinement. The exact maximum-policy
  control restores 14/14 precision and recall while the arbitrary-pointer row
  remains an arbitrary-read/write/null finding. This is a localized detector-
  correctness repair, not a new concretization research program.
- **A1. Deterministic work-bounded timeout (a config value, not a project).**
  Select the existing deterministic resource-budget surfaces instead of relying
  only on the 250ms wall: Axeyum already exposes `SolverConfig::resource_limit`,
  Z3 exposes `rlimit`, and ioctlance already has deterministic outer function and
  exploration-work bounds. The remaining work is to wire and record one explicit
  Glaurung policy/config value, not invent a new solver algorithm. Backend resource
  units are not numerically equivalent, so calibrate and report each backend's
  unit separately; reproducibility is a within-backend gate, while cross-backend
  finding parity remains the user-visible comparison. Keep the wall timeout as a
  safety cap and report any hit. This removes wall time from the accepted work
  boundary without pretending the existing outer function bound already controls
  each solver check.
- **A3. Diverse / boundary concretization (a policy under A0 -- but NOT a
  guaranteed fix).** The `BoundarySet`/`DiverseEnum` policies fork a
  *deterministic diverse set* at value-dependent sinks. This is deterministic
  (reproducible) and recovers *value-dependent* coverage (e.g. a size/offset that
  must hit a boundary to reach a sink). **Correction from iteration-1 research:
  it does NOT reliably recover the double-fetches**, because those are an
  *aliasing* property (two reads of the *same* address) and concretizing that
  address to any single value can break the aliasing. A3 is the right tool for
  value-dependent bugs, the wrong tool for aliasing bugs.
- **A2. Symbolic-address memory (the one architectural item, staged only if
  labeled evidence admits it).** The bounded first stage is COLOSSUS/KLEEF-style
  symcrete addressing: instead of pinning
  `addr == v` and discarding the constraint, keep `addr` symbolic in the path
  condition but attach a consistent concrete witness. This gives reproducibility
  (the witness) AND coverage/aliasing (the constraint survives, so read1 and read2
  stay provably the same location) -- the principled fix for the double-fetch use
  case. This is not the cheap `Defer` knob: Glaurung concretizes precisely
  because its memory model has no
  symbolic addresses ("symbolic memory is concretized, never SMT arrays",
  01-current-state.md). A2 therefore starts, if admitted, by tolerating a
  symbolic address only at bounded aliasing sites. Full read-over-write symbolic
  memory (memsight) is a later stage of the same architectural project, not a
  second pillar item, and proceeds only if the bounded stage leaves measured
  headroom. This is
  where **axeyum's warm path *might* pay for itself** (the constraint set grows;
  warm reuse may keep it affordable) -- but per 3.6 the SE reuse prior art is
  Green-style *constraint caching*, so whether solver-internal warm state is
  additive here is an open, must-measure question, not an assumption. Sequence
  it only after A0 and independent labels show a residual gap.

**The crisp config-vs-architecture boundary (what the user's "isn't it just
configurable?" gets exactly right, and where it stops):** choosing *which
concrete value* to pin is pure configuration -- A0's `AnyModel`/`Least`/`Greatest`/
`BoundarySet`/`DiverseEnum` are all knob settings that still concretize. Keeping
an address *symbolic* (A2, beginning with bounded symcrete addressing) is a
memory-model change,
not a knob. Value-dependent bugs are fixed by config; aliasing bugs
(double-fetch) are fixed by architecture. Both are worth doing; only the first is
cheap.

### Pillar B -- Performance where it actually matters (characterize and win the right regime)

- **B1. Fair six-cell across all drivers + neutral baselines.** The accepted
  `GLAURUNG_FAIR_SHADOW` four-cell map and cvc5 cold/reset plus
  source-owner-retained controls establish the starting regime. Glaurung
  `2961d7c` now adds benchmark-only Bitwuzla 0.9.1 as topology-equivalent cold
  and retained in-process cells. ADR-0272's fixed N>=5 campaign passes every
  all-six gate over 12,902 checks per four-driver pass. The honest map remains
  workload-dependent against Z3: Axeyum wins warm on vwififlt,
  IntcSST/SurfacePen and loses on Dptf. The neutral result prevents a stronger
  headline: warm Bitwuzla wins all four, although cold Axeyum leads on IntcSST
  and SurfacePen. Formula size and the FFI floor do not by themselves explain
  the reversal. Publish this six-cell characterization and separately scoped
  ADR-0233 hard-frontier cold result, not a pooled ratio, universal regime, or
  Axeyum performance-leadership claim.
- **B2. Attack the cold 84% via abstraction-refinement + word-level (not more
  bit-blasting).** The cold gap is bit_blast+cnf. Adopt the SOTA lever:
  incremental abstraction-refinement for `mul`/`div`/`rem` and word-level
  preprocessing (cf. PolySAT direction), which is where z3's maturity actually
  wins. This is the only principled path to cold parity.
- **B3. Parallel path exploration.** axeyum solvers are `Send`; z3's thread-hostile
  context forces sequential passes. Per-path warm solvers unlock parallel
  exploration -- a scaling axis z3 structurally cannot match, aligned with the
  Bitwuzla+Mallob parallel trend but *in-process and per-path*.

### Pillar C -- The differentiators as first-class contributions

- **C1. WASM demonstrator with a number.** Build the QF_BV path to wasm32; run a
  slice of the corpus in-browser; report latency. libz3 cannot do this -- it is a
  categorical, not incremental, advantage. One measured data point sells it.
- **C2. Proof-carrying infeasible-path pruning.** Wire DRAT certificates to
  glaurung's "infeasible path" verdicts (the "verdicts must cite" rule) and
  self-recheck them. **Position honestly:** verification witnesses are mature
  (SV-COMP validates 100k+/yr), so the novelty is not "proofs for verdicts" -- it
  is a *binary-level, solver-DRAT, source-free* certificate for path infeasibility
  that a checker re-validates with no solver, complementing (not replacing)
  source-level witnesses and CoqQFBV's certified-solving angle. A demonstrated
  capability, scoped modestly.
- **C3. Determinism as a product.** With A0+A1 (a reproducible policy plus a
  work-bounded timeout -- both config, not research), ship reproducible analysis:
  same binary -> same findings, gated in CI. This is a capability libz3-based
  pipelines cannot honestly claim, and it is what use cases 2-4 rank highest.

## 6. What each pillar buys the publication (thesis reframe)

Retire "a faster solver." The defensible, novel thesis:

> **A pure-Rust, proof-carrying, warm-incremental SMT backend co-designed with a
> binary symbolic-execution engine, whose in-process warm path supports
> reproducible sweeps of concretization policies -- separating raw
> diagnostics from validated coverage while rigorously characterizing the
> resulting performance regime.**

- **Lead methods contribution:** strict typed translation as a differential
  oracle, backed by the standing Axeyum/Z3/cvc5/Bitwuzla fuzz campaign and named
  regressions for the consumer soundness defects it exposed.
- **Integration contribution (scope it honestly):** the concretization
  Pareto experiment -- determine whether one reproducible setting improves
  validated coverage, work, or cost without hiding losses. The
  *value-selection* half is a configurable-policy sweep (A0) -- convincing and
  reproducible because it is measured across policies, not hand-tuned. The
  *coverage* half for aliasing bugs may need A2 symbolic-address memory,
  beginning with a bounded symcrete stage, but no such project starts until a
  labeled policy sweep demonstrates residual headroom. The current tcpip slice has zero accepted
  rows, so it is a determinism/cost control rather than publication coverage
  evidence.
- **Systems contribution:** the deployability + determinism story (C1/C3) -- a
  solver that ships where libz3 cannot and makes analysis reproducible.
- **Honest performance section:** the fair regime map (B1), not an inflated
  headline.

The solver is the enabler; the *symbolic-execution quality* is the result. That
is a stronger paper than "our QF_BV solver is fast," which the data does not
support anyway.

## 7. Sequenced roadmap (milestones, experiments, Pareto gate)

**Phase 0 -- Make concretization configurable (complete). The enabling refactor.**
- A0: extract `ConcretizationPolicy` at the two seams; implement `AnyModel`
  (behavior-preserving default) plus selectable scalar policies; select by env;
  write the policy name into the trace. **Gate:** existing runs reproduce
  byte-for-byte under `AnyModel`; a second policy is selectable and observably
  changes the trace tag. Glaurung's isolated A0 branch satisfies this gate for
  AnyModel plus least/greatest/site-hash-zero/site-hash-one. BoundarySet and
  DiverseEnum remain settings of this same policy surface, not separate research
  projects, but their set-valued choices require bounded successor forking and
  are not executable cells at `7f682e5`.

**Phase 1 -- Make the comparison honest and reproducible (WIP).**
- The fair four-cell small-driver map, cvc5 cold/reset and retained breadth, and
  ADR-0233's 50/100/250/1000 ms Axeyum/Z3/cvc5 formula frontier are complete.
  ADR-0233 closes neutral timeout-sensitive formula breadth; do not schedule
  another neutral formula sweep under that name.
- The missing in-process neutral control is complete. Glaurung `2961d7c` and
  ADR-0272's frozen v3 consumer run six rotated
  `{Z3, Axeyum, Bitwuzla} x {cold, warm}` cells under cold-Z3 authority and one
  source-owner topology. All 20 processes, 64,510 repeated occurrences, and
  387,060 cell executions pass parity, fallback, fixed-work, and variance
  gates. Warm Bitwuzla leads every driver, so preserve Axeyum's named
  workload-dependent Z3 wins without a leadership claim. Preregister the
  separately scoped harder-driver tier next; do not rerun these four drivers to
  tune the result.
- Remaining A1 is configuration/wiring: select and record backend-specific
  deterministic resource budgets while retaining the wall as a safety cap.
  ADR-0262 completes the wider timeout-sensitive sole-authority tier under
  ADR-0250's v6 stop partition: all six first-20 cells are valid, timeout is a
  measured no-op from 100 to 1000 ms, AnyModel remains raw-divergent, and
  LeastUnsigned gives exact parity at substantial policy cost. Preserve the
  exact source/config identity, stable within-backend work partitions, zero
  accepted deadline/timeout worklist stops, separately reported per-check
  nondecisions, and non-cherry-picked cells as standing gates. Remaining
  finding evidence is a genuinely broader labeled population, not another
  unlabeled tcpip prefix or timeout sweep.
- **Decisive classification (complete):** exact PDB, disassembly, trace, and
  taint-provenance analysis classify both model-sensitive tcpip rows as generic
  `Arg0` diagnostics. The producer now emits an exhaustive confidence
  partition. The subsequent usbprint control independently rejects all five
  apparent rows as consequences of a symbolic I/O-manager-owned SystemBuffer
  pointer; corrected Glaurung has 0/0 accepted rows with equal work. ADR-0243's
  fail-closed source/binary join then accepts all 14 rows across nine planted
  positive fixtures under both authorities. Use that population as a mandatory
  no-regression stratum, not as evidence that value selection changes recall.

**Phase 2 -- Recover coverage reproducibly (scalar sweep and exhaustive source-backed labeling complete).**
- **Scalar sweep complete.** ADR-0244 fails closed
  when minimum cannot complete usbprint under the fixed deadline. ADR-0245 then
  clears AnyModel/minimum but rejects maximum at the positive-control precision
  gate: 14/14 expected rows plus one model-dependent false `stack-overflow`.
  ADR-0246 repairs and accepts A0.5. ADR-0247's exact v3 run then accepts all
  five policies at 14/14 with zero unexpected high rows. Deterministic tcpip
  raw diagnostics vary from 84 to 110 with exact authority parity; AnyModel
  remains 128 Z3 / 126 Axeyum. Every tcpip row is producer-diagnostic and lacks
  independent ground truth. Site-hash-one is also the largest cost point
  (roughly 264 seconds / 235 MiB under Axeyum on the fixed tcpip prefix).
- Treat the accepted sweep as the completed cheap A0 mechanism result, using the
  same five executable policy identities at corrected Glaurung `7f682e5`:
  {AnyModel, LeastUnsigned, GreatestUnsigned,
  SiteHashZero, SiteHashOne}. Preserve raw, confidence-gated, and validated
  populations independently; never use raw `>= AnyModel` as an acceptance gate.
  ADR-0248 takes the stronger immediately available control: all 54
  policy-varying rows at 43 sites in the tracked source-backed population, with
  no sampling. Its complete source/instruction review classifies 30 as ordinary
  request plumbing and 24 as duplicate presentations of validated sinks, with
  zero independent primitives and zero indeterminate rows. No scalar policy has
  a validated finding difference. **Gate for any memory-model work:** a new,
  measured validated residual gap on a genuinely broader labeled population,
  not raw tcpip variation or usbprint's resource failure. Extend with
  BoundarySet/DiverseEnum only after bounded multi-successor execution exists
  and the labeled evidence justifies the extra work; do not approximate either
  policy by choosing one value.
- ADR-0262 independently confirms the mechanism/cost boundary on the wider
  first-20 tcpip prefix. LeastUnsigned produces exact 185/185 authority parity
  at all three timeouts but overlaps only 147 rows with AnyModel's 220-row
  combined union and requires about 25 times as many solve calls. Treat this as
  a policy-sweep characterization, not finding preservation or an invitation
  to build A2.

**Phase 3 -- The structural lever, only if new labeled evidence opens A2 (month+).**
- A2 symbolic-address memory, starting with bounded symcrete aliasing and
  widening to full memsight-style read-over-write only if needed; B2
  abstraction-refinement for
  mul/div/rem. **Gate:** measured coverage/divergence improvement vs the best
  A0/A2 point (target the COLOSSUS ballpark); cold-corpus ratio moved by B2. If
  the bounded symcrete stage closes the admitted gap, full symbolic memory does
  not proceed.

**Phase 4 -- Differentiators + write-up.**
- C2 proof-carrying detection; C3 CI determinism gating; B3 parallel exploration.
  Assemble the paper around the Section-6 thesis.

## 8. Risks and honest threats

- **Symbolic memory blowup** (A2): the classic SE scaling wall. Mitigation is
  precisely axeyum's warm reuse; must be *validated*, not assumed -- if warm reuse
  does not tame it, A2 degrades to A3 + bounded regions.
- **State explosion from diverse concretization** (A3): bound the boundary set;
  fork only at security-relevant sinks, not every concretization.
- **Abstraction-refinement complexity** (B2): high engineering cost; sequence
  after the cheaper wins land.
- **The frontier may not fully collapse:** in some cases reproducibility vs
  coverage may remain a genuine trade-off. Report it honestly; a characterized
  frontier is still a contribution.
- **The double-fetch evidence is thin (2 rows, one tcpip 15-function prefix).**
  It motivates the plan but cannot anchor a paper claim as-is. Before it is a
  contribution it must generalize -- more drivers, more findings, a labeled
  precision/recall denominator. If it does not generalize, the concretization
  result degrades to a methodology/characterization contribution, not a headline.
- **Warm reuse may not be additive over engine-level constraint caching (GREEN).**
  If a Green/GreenTrie-style constraint cache in front of a cold solver captures
  most of the reuse, axeyum's solver-internal warm state is redundant for SE. Must
  be measured (warm-axeyum vs cold-solver + constraint cache), not assumed; the
  in-process/no-FFI/proof/deployability advantages stand regardless.
- **Co-design confound (reviewer #5):** keep a clear line between axeyum-provided
  primitives (warm reuse, enumeration, proofs) and glaurung-side policy, so the
  transferable contribution is legible.

## 9. New research questions (feed into research-questions.md)

- Does bounded symbolic memory + warm reuse Pareto-dominate eager any-model
  concretization on coverage AND reproducibility for driver bug-finding?
- Is disjoint projected enumeration cheaper than per-expression optimization
  (least-unsigned probing cost 27x) for deterministic diverse concretization?
- Which QF_BV regime does an in-process pure-Rust solver win against a *warm* z3
  once the FFI floor is isolated -- and how large is that regime on real corpora?
- Can incremental abstraction-refinement (mul/div/rem) close the cold
  bit_blast/cnf gap without regressing the warm path?
- Are proof-carrying "infeasible path" certificates useful enough downstream
  (agent verdicts, CI) to justify their cost?

## References (SOTA anchors)

- Symbolic Execution in Practice: a survey (2025) -- concretization coverage loss,
  divergence, deferred concretization: https://arxiv.org/html/2508.06643
- COLOSSUS: Deferred Concretization in Symbolic Execution via Fuzzing (Pandey,
  Kotcharlakota, Roy), ISSTA 2019 -- symcrete values; +66.94% coverage / -55%
  divergence vs KLEE; recovers ~38.6% of dropped states:
  https://dl.acm.org/doi/10.1145/3293882.3330554
- KLEEF: Symbolic Execution Engine (2024, 3rd Test-Comp) -- symcrete memory model
  with lazy initialization / symbolic sizes:
  https://link.springer.com/chapter/10.1007/978-3-031-57259-3_18
- memsight: fully symbolic memory (angr/KLEE) -- removes concretization at memory
  accesses (heavier alternative to symcrete).
- An Incremental Abstraction Scheme for Hard BV SMT (mul/div/rem), 2020:
  https://arxiv.org/abs/2008.10061
- PolySAT: word-level bit-vector reasoning in Z3, 2024:
  https://arxiv.org/pdf/2406.04696
- DEADLINE: Precise and Scalable Detection of Double-Fetch Bugs in OS Kernels
  (Xu et al., IEEE S&P 2018) -- **static + source-level** multi-read detection +
  symbolic checking; 23 Linux + 1 FreeBSD bugs:
  https://taesoo.kim/pubs/2018/xu:deadline.pdf
- SafeFetch (USENIX Security 2024), double-fetch protection:
  https://www.usenix.org/system/files/usenixsecurity24-duta.pdf
- Bitwuzla (SMT-COMP QF_BV; parallel STP-Parti-Bitwuzla 2025):
  https://bitwuzla.github.io/ , https://zenodo.org/records/15920726
- CoqQFBV: a scalable certified QF_BV solver (CAV 2021):
  https://link.springer.com/chapter/10.1007/978-3-030-81688-9_7
- Disjoint Projected Enumeration for SAT/SMT without Blocking Clauses, 2024:
  https://arxiv.org/pdf/2410.18707
- High-diversity SMT sampling, 2024: https://arxiv.org/html/2503.04782v1
- GREEN / GreenTrie: reducing/reusing/recycling constraints in program analysis
  (Visser et al. 2012; GreenTrie, ISSTA 2015) -- engine-level constraint caching,
  the prior art for "reuse speeds up SE": https://arxiv.org/pdf/1501.07174
- Partial-Solution-Based Constraint Solving Cache in Symbolic Execution, FSE 2024:
  https://zbchen.github.io/files/fse2024.pdf
- SV-COMP verification witnesses + validation (SoTA 2024 / 2025), the prior art
  for proof-carrying verdicts:
  https://link.springer.com/chapter/10.1007/978-3-031-90660-2_9
