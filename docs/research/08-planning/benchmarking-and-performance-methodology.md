# Benchmarking And Performance Methodology

Status: draft
Last updated: 2026-07-10

## Purpose

Define how performance claims are measured and how performance-driven
decisions are gated. Several roadmap decisions ("custom SAT only when
benchmarks justify it") currently reference benchmarks that have no defined
methodology; this note makes those gates concrete and falsifiable.

## Scope

In scope:

- Corpus tiers, metrics, scoring, harness requirements, and decision gates.

Out of scope:

- Specific performance targets and final benchmark numbers.

## Core Claims

- No optimization or engine-replacement decision is made without a named
  corpus and a recorded baseline run.
- Three corpus tiers serve different questions:
  microbenchmarks answer "did this code change regress",
  public competition sets answer "where are we relative to the field",
  client-generated queries answer "does this matter for real workloads".
- Wall time alone is insufficient; layer-attributed time (rewrite, lower,
  encode, SAT) is what justifies replacing a layer.
- A configured wall-clock timeout covers the complete admitted pipeline,
  including preprocessing, lowering, encoding, and search. A downstream solver
  timeout is not a valid bound for an uninterruptible upstream phase.
- PAR-2 scoring with fixed timeout (the SAT/SMT competition convention) is the
  cross-corpus comparison metric, so results are comparable to published data.

## Corpus Tiers

| Tier | Contents | Question answered |
|---|---|---|
| Micro | Hand-written op-level cases, exhaustive small widths. | Regression per code change. |
| Scenario | Self-checking, oracle-free synthetic consumer workloads (`axeyum-scenarios`): SAT by concrete execution, UNSAT by bounded-verified identities, parameterized by width/rounds. | Does an optimization help on realistic, scalable workloads, without an oracle? |
| Public | SMT-LIB QF_BV / QF_ABV sets, SAT Competition CNF, HWMCC BTOR2. | Standing vs. mature solvers. |
| Client | Minimized queries captured from real frontends. | Real-workload relevance. |

The scenario tier (ADR-0008) is the bridge between micro and client until a real
client frontend exists: it is realistic in shape, scales toward the frontier,
runs in default CI without a native dependency, and carries its own ground truth
so backend agreement is a genuine cross-check rather than a comparison against
another solver. The [consumer-scenario-models note](../07-verification/consumer-scenario-models.md)
records the contract and the first measured baselines.

## Metrics

- Wall time, PAR-2 over corpus, timeout count.
- Decided count/rate and operational-error count. Every performance comparison
  declares a minimum decided percentage; a fast error/unsupported path is not a
  timing sample.
- Layer attribution: time in rewriting, bit-blasting, CNF encoding, SAT, model
  lifting.
- Encoding size: term nodes in/out of rewriter, AIG nodes, CNF vars/clauses.
- SAT internals: propagations, conflicts, decisions, learned/deleted clauses.
- Peak memory per phase.

## Decision Gates

- Custom CDCL core: building it is settled identity, not contingent
  ([ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md));
  this gate decides *priority*. It jumps the queue ahead of encoding work
  when, on the public + client tiers, (a) SAT time dominates end-to-end
  time, and (b) the best Rust adapter shows a consistent material gap to
  CaDiCaL/Kissat on Axeyum-generated CNF specifically. Until then, effort
  goes to encodings first.
- Word-level/lazy techniques (beyond-bit-blasting note): justified per
  technique by layer attribution showing the targeted operator class dominates.
- Backend default choice: highest PAR-2 on the client tier wins, revisited per
  release.

## Design Implications

- Build the harness early (`axeyum-bench` binary): runs a corpus against a
  named config, emits a versioned results artifact (source label, logic,
  selected families, config hash, corpus hash, solver versions, hardware note,
  seed). Artifact version 4 records the selected backend kind, timeout/limit
  config, deterministic corpus/config hashes, machine note, rewrite mode and
  enabled rule IDs, PAR-2 summary, per-instance input/output shape metrics,
  rewrite rule counts, original-vs-rewritten backend decision comparison,
  backend layer statistics such as AIG nodes and CNF variables/clauses for the
  pure Rust path, layer timings, unsupported/error triage, and `sat`
  model-replay failures against the original assertions. Artifact version 5
  extends that schema with node-budget provenance and optional Z3 oracle
  comparison fields, so pure-Rust public baselines can distinguish admitted
  decisions, budget-driven `unknown`, unsupported features, and soundness
  disagreements. Artifact version 6 extends the admission and planning
  provenance with CNF variable/clause budgets and the submitted query-plan mode
  plus `sat` replay-failure policy, so a wider node gate can be bounded before
  SAT solve and sliced/planned runs can be interpreted without weakening the
  original-query replay contract. Artifact version 7 adds replay-refinement
  limits and per-instance refinement telemetry, so query-planning experiments
  can report how many replay failures were used to grow a support slice and why
  refinement stopped. Artifact version 8 adds the harness `jobs` setting to
  distinguish single-instance solver timings from corpus-level parallel
  throughput when long public diagnostics are run with Rayon workers.
  Artifact version 9 adds replay-refinement batch size to the query-plan
  configuration, so exact-target refinement runs can distinguish "one failed
  original assertion per round" from batched failed-assertion admission while
  preserving full-query replay before any `sat` is accepted.
  Artifact version 10 adds the adaptive-batch flag and per-instance backoff
  count, so budget-aware refinement runs can be separated from static batch
  runs in both the JSON config and config hash.
  Artifact version 11 adds replay-refinement selection policy, so source-order
  failed-assertion refinement can be compared with deterministic cost-shaped
  selection heuristics without weakening the replay contract. Artifact version
  12 records the bounded plan-aware selection option and current root-direct
  assertion CNF encoder behavior, so plan-local and plan-aware refinement
  diagnostics can be separated in artifacts. Artifact version 14 adds a
  corpus-level `summary.layer_attribution` block: per-stage seconds and shares
  (bit-blast, CNF encode, SAT solve, model lift) over the decided pure-Rust
  (`sat-bv`) instances, plus an explicit `sat_dominates` boolean against a
  documented `sat_dominates_threshold` (0.5). This makes CDCL-priority gate (a)
  — "does SAT solve time dominate end-to-end?" — falsifiable from a single
  summary instead of requiring per-instance reconstruction. The four stages are
  non-overlapping and sum to the pure-Rust pipeline wall time (`translate`
  equals `bit_blast + cnf_encode` on this path, so it is not double-counted as a
  separate slice); the block is `null` when no `sat-bv` instance was decided, so
  a fabricated zero share is never reported as "SAT does not dominate". On the
  committed micro corpus the measured SAT share is ~0.31 (encoding stages ~0.57
  combined), so gate (a) reads **false** there — but the micro tier is only 3
  trivial instances dominated by fixed encoding overhead, which is precisely why
  the gate is defined on the public/client tiers. On a public QF_BV slice
  (`20190311-bv-term-small-rw-Noetzli`, 1416 decided `sat-bv` instances under a
  100k-var / 300k-clause guard) the SAT-solve share is **~0.95** (bit-blast
  ~0.016, CNF encode ~0.031, model lift ~0.0), so gate (a) reads **true** on that
  slice. Caveats before treating gate (a) as met corpus-wide: (i) it is one
  family of small-term rewrite benchmarks; the share must hold across a broader
  public/client sample. (ii) The measurement is over instances that *decide
  within the guard* — guard-rejected large instances never reach the SAT core,
  so the share characterizes the population where SAT-core quality actually
  matters. (iii) Gate (a) is necessary but not sufficient: the CDCL track still
  needs gate (b), a consistent material gap to CaDiCaL/Kissat on Axeyum-generated
  CNF, which is not yet measured. Net: SAT time *does* dominate on realistic
  decided QF_BV, so encoding-vs-SAT priority is now an open, data-driven question
  rather than a settled "encodings first" — the next measurement is breadth
  (more families) plus the CaDiCaL/Kissat comparison, not core tuning yet.
- 2026-06-13, gate (a) breadth: a second public family attribution settles the
  breadth caveat — and reverses the picture. On `bench_ab` (285 decided `sat-bv`
  instances, `--jobs 1`, node 5000 / CNF 7000-var / 20000-clause guard, all
  agreeing, 0 replay failures), the SAT-solve share is **0.243**, with bit-blast
  ~0.32 and CNF encode ~0.35 — `sat_dominates: false`; **encoding dominates**.
  So gate (a) is **family-dependent**: SAT-dominated on `Noetzli` (~0.95) but
  encoding-dominated on `bench_ab` (~0.24) and on the micro tier (~0.31). The
  conclusion for the CDCL track: gate (a) does **not** hold uniformly, so per the
  methodology the custom-CDCL/VSIDS work stays **deprioritized** — encoding
  reduction (bit-blast + CNF, ~0.67 of the pipeline on `bench_ab`) is the
  higher-value lever on the encoding-dominated families. CDCL core tuning would
  only be justified once gate (a) holds *and* gate (b) (a CaDiCaL/Kissat gap on
  Axeyum CNF) is measured, on families where SAT actually dominates. Baseline:
  `bench-results/baselines/qf-bv-bench_ab-sat-bv-layerattr-1s-n5000-cnf7k-20k-j1.json`.
  (Run safely: `--jobs 1`, guarded budgets — the node guard refuses large
  instances before bit-blasting, so peak memory is a single small instance.)
  Resource note: relaxing the CNF guard to admit large instances multiplies
  memory by the parallel `--jobs`; the guard ceilings and `jobs` must stay
  bounded together (a 2M-var / 6M-clause ceiling at `--jobs 16` OOM-killed a
  26 GB host). Broad attribution runs should keep moderate budgets and choose
  small-instance families rather than forcing large instances through.
- Layer attribution is also available off-corpus: `axeyum_solver::BvLayerStats`
  lifts the per-stage counters (bit-blast, CNF encode/inprocess, solve, model lift; AIG
  and CNF sizes; clause density) into a typed view, and the
  `scenario_pipeline_report` and `scenario_scaling` `axeyum-bench` examples
  report it across the scenario tier so an optimization's effect on encoding
  size and SAT cost is measured before it is committed to.
- Artifact version 15 adds explicit `decided` and `decided_percent` summary
  fields plus the hashed `--min-decided-percent` gate. Operational errors now
  fail the harness. This closes the fast-failure trap observed in the first
  Glaurung integration measurement, where a nominal 12–34x speedup was actually
  a 98% construction/error rate. Client-tier timing is publishable only after
  its decided-rate gate passes.
- Artifact version 16 makes the Glaurung attribution boundary executable:
  word-level preprocessing, bit-blast, CNF encode, optional CNF inprocessing,
  SAT search, and model lift each carry exact per-instance millisecond values,
  aggregate time, and deterministic p50/p95 distributions. The client comparison
  sends the untouched parsed assertions to in-process Z3 while charging Axeyum
  for its selected word preprocessing, then reports the aggregate Axeyum/Z3
  ratio and both timing distributions. Binary-Z3 fallbacks remain verdict-only
  and are excluded from that ratio because process startup is not comparable to
  the embedded target.
  The Glaurung recipe uses one worker so cross-query contention cannot masquerade
  as a layer cost, and `--require-in-process-z3` fails the run unless every file
  contributes to the embedded comparison.
- Artifact version 17 makes the external-corpus identity executable. A manifest
  v1 fixes the source and logic, exact relative-path membership, per-query
  SHA-256, expected verdict, family, stable order, and named tiers. The harness
  validates the entire pack before selecting a tier, rejects anonymous
  `--limit` prefixes, gates every selected decision against the manifest
  independently of SMT-LIB `:status`, and includes the manifest digest and tier
  in the experiment identity. The committed micro manifest is only a plumbing
  smoke; it does not satisfy the Glaurung representativeness requirement.
  A versioned capture-index generator now supplies the producer/consumer
  handshake: the shadow-diff exporter declares ordered paths, trusted verdicts,
  families, and tiers, while Axeyum requires exact `.smt2` membership, computes
  hashes from disk, and validates the generated manifest through the same run
  ingestion path. Exporter-provided hashes and unknown fields are rejected.
- Artifact version 18 makes client-shape representativeness inspectable rather
  than anecdotal. It profiles unique nodes in each untouched original-query DAG:
  formula shape, BV width diversity, extract/concat/extension and surviving
  array operations, extract demanded/source bits, and the exact nested shapes
  targeted by GQ3. Corpus summaries carry deterministic p50/p95 distributions,
  while the layer profile adds AIG/CNF size distributions. Memory provenance
  erased by lifter flattening is explicitly left to manifest family/source
  metadata rather than guessed from the lowered formula.
- Artifact version 19 closes the replay-attribution boundary. SAT model replay
  against untouched assertions is timed separately, included in the cold total,
  and charged symmetrically in the embedded Axeyum/Z3 comparison. An optional
  `--prove-unsat` companion uses the proof-producing core and fails closed unless
  every UNSAT carries an inline-checked DRAT proof. Its proof-check time and
  p50/p95 are nested diagnostics within SAT time, never a seventh additive stage;
  this high-assurance run is kept separate from the default batsat performance
  artifact because changing the SAT engine would invalidate that comparison.
- Artifact version 20 makes the fixed-environment requirement executable. Every
  run records the Axeyum Git revision/cleanliness, Cargo.lock SHA-256,
  rustc/cargo and build profile, exact solver backend names, CPU model,
  OS/kernel, logical parallelism, and total memory. `config_hash` remains the corpus/settings key;
  `environment_hash` covers locked tools and hardware but excludes the source
  revision, allowing consecutive commits to be compared only under the same
  environment. `--require-reproducible-run` fails before solving when source
  changes (excluding generated `bench-results/**`) or any required identity is
  missing, and every Glaurung recipe enables it.
- Artifact version 21 makes the fixed-seed requirement executable. It removes
  the old benchmark `--seed` label because that value was not consumed by a
  solver. Each run now records and hashes the actual Cargo.lock-pinned BatSat
  defaults (seed `91648253`, random-variable frequency `0`, randomized polarity
  off, and randomized initial activity off), explicitly sets and records Z3
  `random_seed=0`, and records deterministic corpus ordering. Unit tests pin the
  reviewed BatSat defaults, and the repetition validator fails closed on profile
  drift. This establishes configuration identity only; time variance and
  deterministic resource bounds remain separate acceptance gates.
- Artifact version 22 makes that resource gate executable for the cold QF_BV
  lane. `--require-deterministic-resources` fails before corpus work unless
  positive term-DAG, CNF-variable, CNF-clause, and search limits are present.
  The search limit is consumed as deterministic `BatSat` `within_budget`
  progress checks, proof-CDCL conflicts, or Z3 `rlimit` units according to the
  selected engine. Artifacts state those units and that identical numbers are
  not work-equivalent across backends. The provisional named client profile is
  300k DAG nodes / 3M CNF variables / 8M CNF clauses / 2M search units. It may
  be replaced by a versioned profile after real-capture admission measurement,
  but never silently loosened to preserve a timing result. Wall timeout remains
  a non-deterministic safety backstop.
- **Primary client QF_BV target (2026-07-13): Glaurung binary analysis.** Capture
  and minimize the real lifter-produced path conditions, preserving their
  extract/concat, mixed machine-width, and memory-derived shape. This client
  corpus outranks synthetic well-typed formulas for QF_BV preprocessing work:
  the consumer reports full correctness and robustness across roughly 180k
  queries but Axeyum is 1.7–3.2x slower than in-process Z3 on the real formulas.
  No optimization claim is accepted from a synthetic replacement when it does
  not also improve the captured client corpus at the same decided rate.
- Fixed seeds and pinned solver versions everywhere; repeated runs with
  variance reported for anything under a few seconds. For the Glaurung client
  lane, `bench-glaurung-qfbv-repeated` launches each whole-corpus trial in a
  fresh process. Its fail-closed summary requires byte-identical artifact
  configuration, clean source/tool/hardware identity, one worker, 100% decided,
  complete manifest and in-process Z3 agreement, and zero operational or replay
  failures in every trial. It reports nearest-rank p50/p95, sample standard
  deviation, and coefficient of variation across corpus totals for Axeyum, Z3,
  their ratio, and each Axeyum stage. Per-query p50/p95 within one trial is not
  misreported as run-to-run variance.
  Cross-commit tracking uses `compare-glaurung-qfbv-repeated`: both repetition
  summaries are revalidated from their trial records and must match in corpus,
  manifest, configuration, environment/toolchain/hardware, and backends while
  naming distinct clean source revisions. Reports keep raw Axeyum and raw Z3
  changes alongside the ratio and per-stage deltas, so an apparent ratio win
  caused by Z3 control drift is visible. Optional ratio/Axeyum regression and
  absolute Z3-drift thresholds are explicit caller policy; no threshold is
  inferred from the synthetic micro smoke.
- The regular `just check` lane runs the access-controlled Glaurung
  representative tier when its pinned NAS pack or an explicit
  `AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR` is available. Absence is an
  explicit skip; an explicitly configured incomplete pack is an error. Both
  raw/current-integration and canonical-candidate policies require complete
  manifest and in-process Z3 agreement, 100% decisions, deterministic resource
  bounds, and zero operational/model-replay failures. Artifacts live under
  ignored `target/` state because a regular dirty-worktree semantic check is
  not a publishable timing trial. Clean revision identity, independent-process
  repetitions, and full-tier thresholds remain the scheduled performance lane.
- Five clean canonical full-tier processes at revision `0cfd6cdc` establish the
  first scheduled variance boundary: Axeyum total, Z3 total, and their ratio
  have 0.514%, 0.310%, and 0.510% CV respectively; every attributed stage is
  below 1% CV. The provisional same-environment alarms are 3% maximum ratio
  regression, 3% maximum Axeyum-total regression, and 2% maximum absolute Z3
  control drift. `compare-glaurung-qfbv-repeated-guarded` applies them. They are
  deliberately conservative regression alarms, not hardware-independent
  guarantees or significance claims, and may be revised only with another
  recorded full-tier variance tranche.
- Timeout regressions must pin the exact pathological public or minimized query
  and exercise both admission outcomes: deterministic oversized refusal before
  allocation and cooperative expiry inside admitted superlinear work. Every
  budget exhaustion remains a classified `Unknown` (ADR-0083).
- Corpus-level parallelism is an execution accelerator, not a solver-quality
  claim by itself: artifacts must preserve deterministic file ordering and
  per-instance model replay/oracle comparison, and single-instance solver
  timings remain the evidence for encoding or SAT-core priority decisions.
- Statistics counters from sat-core-state and performance notes feed this
  harness; they are requirements, not nice-to-haves.
- CI runs the micro tier per PR through `axeyum-bench`; public-tier runs are
  scheduled, not per-PR.

## Risks

- Public corpora overweight problem classes Axeyum does not target; the
  client tier must exist before big architectural bets.
- Benchmark harnesses rot without scheduled runs and stored baselines.

## Open Questions

- [ ] What hardware baseline is recorded as canonical for published numbers?
- [ ] How large can the per-PR micro tier be before CI cost bites?
- [ ] Should published long-run results artifacts live in-repo, in CI storage,
      or a separate repo?
  - Current convention: small baseline artifacts live in
    `bench-results/baselines/`; local scratch runs stay in gitignored
    `bench-results/local/`.

## Source Pointers

- SMT-COMP rules and scoring: https://smt-comp.github.io/
- SAT Competition: https://satcompetition.github.io/
- SMT-LIB benchmarks: https://smt-lib.org/benchmarks.shtml
- Hardware model checking competition: https://hwmcc.github.io/
