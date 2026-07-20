# Benchmarking And Performance Methodology

Status: draft
Last updated: 2026-07-19

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
- Artifact version 28 closes the post-word operator-attribution gap exposed by
  the accepted Glaurung v3 rewrite. Both untouched and selected-policy DAGs now
  carry a complete unique-node inventory for scalar Bool/QF_BV arithmetic,
  bitwise, shifts, comparisons, structural operators, equality, and `ite`, plus
  an explicit `other` bucket. Per-instance inventories allow family and outlier
  correlation with measured AIG/CNF/SAT costs. This inventory is observational
  and outside the additive client timing boundary; a new optimization must be
  selected from the post-word counts rather than lexical source frequency.
- Artifact version 29 makes GQ4's demand-driven cold lowering a separately
  identified experiment. Config hashes include the policy bit; aggregate and
  per-instance demand records state whether lowering was actually applied;
  and strict Glaurung recipes separately measure the whole tier and the
  `register-slice` family. This production route must not be conflated with
  artifact v28's observational demand profile.
- Artifact version 30 gives ADR-0158's admission-controlled range path a
  separate configuration identity. Every absolute/relative savings threshold
  and the deterministic analysis-work budget enter the hash. Per-instance and
  aggregate records partition `no-candidate`, `insufficient-estimate`,
  `analysis-budget-exceeded`, `insufficient-exact-savings`, and `applied`, and
  expose admission time plus exact work/merge/promotion counts. This route is
  still an explicit experiment: compare its `register-slice` and whole-tier
  artifacts to the unchanged default before proposing any automatic policy.
- Artifact version 31 makes rewrite selection causal at the query/family
  boundary. Per-rule aggregate buckets count applications and distinct affected
  instances/families, then report the selected policy's output DAG/AIG/CNF/time
  totals with an explicit warning that these are not saved work. The repeatable
  `--rewrite-disable-rule <id>` experiment builds a validated default-minus-rule
  manifest and enters every disabled/enabled ID into configuration identity.
  Actual rule value is the paired per-path delta between base and ablated
  artifacts; aggregate fire count alone is never an optimization claim.
- ADR-0159 accepts the strict repeated comparison boundary for those artifacts.
  `bench-glaurung-qfbv-rewrite-ablation-repeated` alternates fresh-process base
  and exact one-rule ablation runs; its comparator rejects source, environment,
  corpus, non-rewrite configuration, instance-set, verdict, oracle/manifest, or
  replay drift. It reports `ablation - base` on the base rule's affected paths,
  keeps deterministic structure separate from repeated timing samples, and
  retains whole-corpus timing as a drift control. The first four-rule tranche
  finds `bv.extract_extend.v1` avoids 6,259 term-bit materializations and 1.657
  ms mean affected cold time, but none of the four rules changes an AIG node or
  CNF clause on the representative capture. Further extract work therefore
  requires a new downstream gate-cone hypothesis, not just lexical reach.
- ADR-0160 adds a separate native-client boundary. Glaurung hashes the exact
  capture-rendered bytes, preserves every occurrence in process-local sequence
  order, and times client translation, incremental lower/encode/SAT/model/
  replay phases without changing the raw assertion policy. JSONL output is one
  file per process and outside the reported native total. The fail-closed
  summarizer rejects schema/order/completeness/policy/count drift and can check
  overlapping verdicts/families against manifest v1. Ordinary Axeyum solver
  constructors do not pay diagnostic clock/counter overhead. Native profiles
  and deduplicated cold artifacts are complementary: the former retains
  occurrence/reuse and caller cost; the latter supplies controlled policy and
  Z3 comparisons. A publishable conclusion needs clean same-revision hashes,
  fixed tools/hardware, repeated processes, and the usual 100%-decided,
  zero-error/disagreement/replay gates.
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
  inferred from the synthetic micro smoke. The strict comparator rejects a
  changed rewrite manifest by default. A deliberate rewrite experiment uses
  `compare-glaurung-qfbv-repeated-rewrite-guarded` and must name the exact
  baseline/candidate rule-set identities plus the added rule ID. The comparator
  removes only those two manifest fields after verifying that the candidate is
  the baseline's ordered rule list plus exactly that addition; any removal,
  reorder, hidden addition, or other configuration drift still fails closed.
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
- ADR-0187's corrected five-driver full tier is larger than the established
  monolithic 4 GiB process envelope. It is partitioned only by the deterministic
  first-64-SHA-bits modulo shard count rule. `summarize-glaurung-shards.py`
  accepts a composite result only after the child capture indexes form an exact
  disjoint union of the byte-pinned parent, each artifact covers its complete
  manifest with trusted/Z3 agreement and original-model replay, normalized
  clean source/configuration identity is common, and every process records a
  successful 4 GiB time envelope. Stage and client seconds are additive across
  shards; RSS is reported as the maximum child peak. Shards are parts of one
  corpus trial, never repetitions. Variance and cross-commit alarms require
  multiple complete composite runs.
- ADR-0188 makes that repetition boundary executable. The shard-repetition
  summarizer recomputes each complete composite and requires exact capture,
  clean source/configuration, deterministic work, outcome, and shard identity.
  The guarded cross-commit comparator permits only a different clean source
  revision and code-induced construction counts; capture, environment,
  toolchain, policy, and resources remain exact. Initial corrected-corpus
  same-environment alarms are 3% Axeyum mean, 3% normalized ratio, 5% maximum
  child RSS, and 2% absolute Z3 drift. Two full composites measure raw
  Axeyum/Z3/ratio CV at 0.458%/0.558%/0.100% and canonical at
  0.787%/0.150%/0.937%. These are regression alarms, not significance claims.
- Five clean canonical full-tier processes at revision `0cfd6cdc` establish the
  first scheduled variance boundary: Axeyum total, Z3 total, and their ratio
  have 0.514%, 0.310%, and 0.510% CV respectively; every attributed stage is
  below 1% CV. The provisional same-environment alarms are 3% maximum ratio
  regression, 3% maximum Axeyum-total regression, and 2% maximum absolute Z3
  control drift. `compare-glaurung-qfbv-repeated-guarded` applies them. They are
  deliberately conservative regression alarms, not hardware-independent
  guarantees or significance claims, and may be revised only with another
  recorded full-tier variance tranche.
- ADR-0213 adds a distinct publication-grade client boundary. Engineering
  admission still requires every exact-work and replay gate above, but a paper
  speed claim additionally requires all of the following:
  - Each ordered check has a stable occurrence/query identity, both backend
    result classes, both positive timings, and an explicit execution class:
    retained warm, newly created warm, or named one-shot fallback reason.
    Aggregate footer counters cannot reconstruct this population after the
    fact.
  - Every configuration has at least five fresh-process fixed-work repetitions.
    Query identities, bytes, order, backend configuration, and execution-class
    membership must either be identical or the drift must fail closed. Report
    process-level mean, sample deviation, and CV; shards remain parts of a run,
    never repetitions.
  - Classify occurrences as both-decided, Z3-only, Axeyum-only, or neither.
    Operational errors and replay failures are separate fatal buckets. Latency
    comparisons use only the paired both-decided population; decided-rate and
    the other three buckets are reported beside, not hidden inside, the timing
    result.
  - The primary scalar is the geometric mean of the declared per-query ratio
    direction with a deterministic-bootstrap 95% confidence interval. Also
    report per-backend p50/p90/p95/p99 and latency CDFs. A ratio of sums,
    "median-sum" ratio, or single process is descriptive only.
  - Sweep the wall timeout over a predeclared set while keeping fixed work.
    Never mix retained warm checks with assertion-cap, path-cap, unsupported,
    or other cold fallbacks in one warm latency population.
  - Compare `{Z3, Axeyum} x {cold, warm}` on the same ordered stream with
    topology-equivalent persistence. Add at least one neutral solver point;
    identify whether it is in-process or subprocess-bridged and report boundary
    overhead separately.
  - Shadow verdict agreement is not authoritative analysis parity. Run each
    backend as the sole Glaurung authority, compare stable finding/sink sets,
    and report model-choice divergence. If exploration depends on model choice,
    a checked canonical selection policy and before/after parity table precede
    an end-to-end claim.
  These requirements govern publication claims, not ordinary microbenchmark
  iteration. A bounded optimization may still use the stricter exact-work
  engineering gate, but its aggregate ratio must remain labeled local
  screening evidence until the publication boundary is exercised.
  ADR-0214 implements the first mechanism in Glaurung `eb624c0` and
  `scripts/analyze-glaurung-paired-traces.py`. A typical single-configuration
  analysis is:

  ```sh
  python3 scripts/analyze-glaurung-paired-traces.py \
    --output target/glaurung-paired/report.json \
    --cdf-dir target/glaurung-paired/cdf \
    /path/to/repetition-{1,2,3,4,5}
  ```

  The command deliberately rejects historical unmarked traces, fewer than five
  repetitions, event/query-index/query-content integrity failures,
  configuration/work/execution-class drift, nonpositive timings, operational
  results, and decided disagreements. Invoke it separately
  for each timeout/configuration cell; never combine a timeout sweep into one
  fixed-configuration report. The first clean DptfDevGen `{1, 5, 60}`-second
  mechanism exercise and its exact reports/CDFs are committed under
  [`bench-results/glaurung-paired-dptf-20260717/`](../../../bench-results/glaurung-paired-dptf-20260717/README.md).
  It proves the evidence path, but it is only a no-timeout control: all cells
  decide the same 561/561 occurrences, and cold Z3 versus warm Axeyum remains
  topology-confounded. Use a timeout-sensitive driver for the actual
  sensitivity claim.
  ADR-0215 then implements the topology-equivalent control in Glaurung
  `4ae96cf` under `glaurung-ordered-check-measurement-v2`. A clean five-process
  Dptf run preserves 561/561 four-cell decisions, identical created/retained
  populations, and no fallback. Report cold Z3/Axeyum, warm Z3/Axeyum, Z3
  cold/warm, and Axeyum cold/warm as four separate paired populations. The fair
  warm geomean is 0.7875x [0.6893, 0.8977] Z3/Axeyum, while the deliberately
  retained legacy cold-Z3/warm-Axeyum alias is 7.0678x. The latter must not be
  used as a solver headline. Exact JSON and four-cell CDF evidence is committed
  under
  [`bench-results/glaurung-four-cell-dptf-20260717/`](../../../bench-results/glaurung-four-cell-dptf-20260717/README.md).
  ADR-0217 repeats that control on vwififlt, IntcSST, and SurfacePen. ADR-0218
  then joins the four accepted reports to hash-verified query features without
  changing the producer:

  ```sh
  python3 scripts/analyze-glaurung-regime-features.py \
    --output target/glaurung-regime/report.json \
    --rows-csv target/glaurung-regime/occurrences.csv \
    bench-results/glaurung-four-cell-dptf-20260717/report.json \
    bench-results/glaurung-four-cell-small-drivers-20260717/*/report.json
  ```

  The feature report is descriptive: preserve per-driver strata, label pooled
  ranks as composition-confounded, do not split equal feature values across
  quantile bins, and never describe marginal outcome/purpose standardization
  as a causal counterfactual. It selects the next measurement—per-check
  rewrite/AIG/CNF/SAT work and timing—rather than replacing it. Neutral-solver,
  timeout-sensitive, and authoritative finding-parity gates remain open.
  ADR-0219 consumes Glaurung's existing opt-in Axeyum profile JSONL for that
  internal measurement:

  ```sh
  python3 scripts/analyze-glaurung-profiled-trace.py \
    /path/to/glaurung-ordered-trace-PID-ID \
    /path/to/axeyum-profile-PID.jsonl \
    --output target/glaurung-profile/report.json \
    --rows-csv target/glaurung-profile/occurrences.csv
  ```

  Profile output is diagnostic only. Query identity rendering and synchronous
  JSONL writes occur inside the outer fair cell, so never use that run for a
  solver ratio. Use it to select a mechanism, then measure that mechanism in a
  fresh unprofiled repeated control.
  ADR-0220's next control exports the retained input-clause database plus active
  selectors as a standalone DIMACS instance, then sends the exact bytes through
  fresh cores:

  ```sh
  cargo run --release -p axeyum-bench \
    --example cnf_core_bench --features z3 -- \
    /path/to/retained-cnf-dir report.json 5 /path/to/kissat
  ```

  This control must distinguish four costs: BatSat fresh import/solve, proof
  generation, proof generation plus independent DRAT recheck, and oracle
  import/solve. An external CLI cell includes process startup and is verdict
  evidence unless solver-internal timing is separately captured. The exported
  problem excludes opaque learned clauses, so a fresh-core reversal cannot by
  itself explain a warm retained-engine reversal; follow it with an ordered
  persistent clause-stream/learned-state control.
  ADR-0221 implements that follow-up. Capture every actual retained SAT-core
  call, including SAT and UNSAT, but exclude replay-cache hits that never enter
  the core. Join the capture to the warm profile and fail on identity,
  cardinality, hash, shape, selector, verdict, or append-only-prefix drift:

  ```sh
  cargo run --release -p axeyum-bench \
    --example cnf_stream_bench --features z3 -- \
    /path/to/axeyum-profile.jsonl /path/to/cnf-dir report.json 5 250
  ```

  Keep one solver per captured path and let each core learn independently from
  the same clause/assumption/call sequence. Report clause ingestion separately
  from solving. This controls Boolean input topology and ordered retained use;
  it does not make learned clauses identical or reproduce word-level SMT
  integration. On Dptf, all 431 core calls agree over N=5 and retained BatSat
  beats retained Z3 Boolean by a 3.5527x per-call solve geomean. Therefore the
  fair native-Z3 win is not evidence for a generally faster Z3 Boolean core on
  Axeyum CNF. Move the next causal control to neutral end-to-end SMT and
  representation/integration, not a custom SAT-core rewrite.
  ADR-0222 adds the first neutral word-level point from an accepted ordered
  trace:

  ```sh
  taskset -c 3 cargo run --release -p axeyum-bench \
    --example cvc5_smt_stream_bench -- \
    /path/to/glaurung-ordered-trace /path/to/cvc5 report.json 5 250
  ```

  Validate the clean trace, event/index/query hashes, exact occurrence order,
  source verdicts, neutral verdicts, and SAT model-output cardinality. Use one
  external solver process per repetition but issue a full `(reset)` after each
  query: process startup is amortized while solver state remains cold. Report
  this as a **cold-reset external SMT integration** point that includes textual
  parsing and model output. It is not paired per occurrence with the in-process
  four-cell data and must not be divided into those geomeans. The Dptf cvc5
  point preserves all 561 verdicts over N=5 at 0.4222% timing CV; neutral warm
  topology and broader multi-driver evidence remain open.
  ADR-0223 applies the identical contract to the other three accepted traces.
  All 9,526 checks agree with cvc5 (6,801 SAT / 2,725 UNSAT / 0 Unknown), every
  model-output count matches, stdout is byte-stable per driver, and timing CV
  ranges from 0.1639% to 0.4222%. Keep each driver's aggregate external-SMT
  throughput separate. The fact that cvc5's per-check difficulty ordering does
  not mirror the Axeyum/Z3 warm ordering is regime evidence, not license to
  normalize unlike integration boundaries into a headline ratio.
  The timeout-sensitive one-shot frontier uses artifact v32 so an Axeyum
  `unknown` no longer prevents the in-process Z3 control from running. Produce
  at least five fresh-process Axeyum/Z3 artifacts at each predeclared timeout,
  run the same hash-bound files through the neutral subprocess control, and
  then analyze all cells together:

  ```sh
  cargo run --release -p axeyum-bench \
    --example cvc5_qfbv_timeout_sweep -- \
    /path/to/corpus /path/to/manifest-v1.json /path/to/cvc5 \
    cvc5-sweep.json 5 50,100,250,1000

  python3 scripts/analyze-qfbv-timeout-sweep.py \
    --cvc5 cvc5-sweep.json --out analysis.json \
    axeyum-z3-*.json
  ```

  The analyzer requires a clean source, one worker, identical manifest/config
  identity apart from timeout, complete four-bucket accounting, and no error,
  replay failure, decided disagreement, or cross-solver SAT/UNSAT
  contradiction. Outcome drift around a timeout is reported, not discarded.
  Paired latency uses only the queries both solvers decide in every repetition
  of that timeout cell. The cvc5 wall time includes a fresh process, parsing,
  and model output and is never divided into the in-process ratio. This
  deduplicated one-shot boundary is timeout sensitivity evidence; it is not a
  retained-warm or end-to-end authoritative finding-parity experiment.
  ADR-0233 exercises that contract on the exact 52-formula post-concat-fix
  tcpip frontier. Five runs at each of 50/100/250/1000 ms have zero error,
  replay failure, decided disagreement, or three-solver SAT/UNSAT
  contradiction. Axeyum/Z3 decision counts rise 28/13, 30/25, 41/33--34, and
  52/52; cvc5 rises 46, 51, 52, 52. The fixed both-decided Axeyum/Z3 geomeans
  are 0.14165, 0.14548, 0.14112, and 0.21095 (ratio below one favors Axeyum),
  with all bootstrap intervals below one. The all-decided 1000 ms tier removes
  solved-subset selection and establishes a cold one-shot Axeyum win on this
  exact corpus. Keep the FFI/context/representation/search cause unresolved
  and do not substitute this deduplicated formula control for retained-warm or
  finding-authoritative evidence.
- Generated correctness gates must distinguish a solver nondecision from an
  invalid oracle invocation. ADR-0224 keeps 4,000 deterministic well-typed
  QF_BV rows on Axeyum/direct-Z3 with original-model replay and sends a fixed
  250-row sample to cvc5. An explicit cvc5 `unknown` is a counted nondecision;
  parser, process, status, and output-protocol failures fail closed with the
  standalone SMT-LIB reproducer. The accepted run has 4,000 two-way and 250
  three-way agreements, 1,487 replayed SAT models, and zero skips or failures.
  Malformed consumer width metadata and use of a model after non-SAT remain
  separate strict contract regressions; do not pretend well-typed formula fuzz
  alone tests those invalid consumer states.
  ADR-0225 promotes the publication lane, not routine CI, to a cvc5 stride of
  one: all 4,000 generated formulas must receive a neutral decision and agree
  three ways. It also makes the five random widths and 35 required generator
  classes an executable coverage gate. Report the bounded inventory and exact
  seeds; “all operators covered” is not permission to claim all shapes,
  constants, widths, or interactions are exhausted.
  ADR-0237 preregisters the independent continuation before its full results:
  `uniform-v1` seeds 1,000,000..1,004,000 and 2,000,000..2,004,000 plus
  `edge-v1` seeds 3,000,000..3,004,000. Every row must decide in Axeyum,
  direct Z3, cvc5 1.3.4, and Bitwuzla 0.9.1; external failures fail closed and
  every Axeyum SAT must replay. The edge round reports per-instance frequencies
  for 14 declared semantic-corner families rather than inferring edge coverage
  from operator presence. Use `scripts/run-qfbv-independent-oracle-rounds.sh`;
  its 256-row seeds 4,000..4,256 engineering pilot is explicitly excluded. The
  first full attempt exposed seed 1,002,261 exceeding the inherited 5,000 ms
  Axeyum worker cap after 3,999 four-way agreements, so it failed closed before
  later rounds. Preserve that log; the amended runner names a 30,000 ms cap,
  records exact nondecision seeds and the first timeout reproducer, and asserts
  all-decided directly without changing any preregistered seed. That second
  attempt completed `uniform-a` 4,000/4,000, then cvc5 1.3.4 reproducibly
  exhausted the inherited 2,000 ms limit at `uniform-b` seed 2,003,009. Preserve
  that attempt too. The final amended protocol uses and reports 30,000 ms for
  Axeyum and every external oracle; the exact script decides `sat` in cvc5 and
  Bitwuzla under that cap. Seeds remain unchanged.
  The third attempt closes both uniform rounds but exposes `edge-c` seed
  3,000,881 as genuinely solver-bound: Axeyum exceeds 120 seconds, while the
  unchanged formula is `unsat` in direct Z3 (25.225 seconds isolated), cvc5
  (41.67 seconds), and Bitwuzla (12.62 seconds). Use a final uniform 600,000 ms
  correctness bound, which also lets Axeyum decide; never reuse those loaded,
  single-formula diagnostics as comparative performance measurements.
  The final same-commit run passes all three exact rounds: 12,000/12,000
  four-way decisions and agreements, 4,471/4,471 Axeyum SAT replays, all five
  widths, all 35 operator/generator classes, and all 14 declared edge families.
  Unknown, timeout, crash, process/parser failure, replay-indeterminate, and
  disagreement counts are zero. This accepts ADR-0237 as bounded correctness
  evidence, not a QF_BV completeness theorem or performance comparison.
  Proof coverage needs two denominators: the full decided-UNSAT population and
  the predeclared attempted subset. ADR-0226's 4,000-row generator has 2,513
  UNSAT results; its width-at-most-8/seed-divisible-by-4 subset contains 169
  rows (6.725030%). All 169 have rechecked CNF DRAT and rechecked end-to-end
  faithfulness-plus-DRAT certificates, so selected-subset coverage is 100% and
  whole-population measured coverage is 6.725030%. Do not classify the 2,344
  unattempted rows as either certified or not-certified. Seed 83 proves the
  widening harness also needs a cooperative deadline or killable process:
  CNF DRAT finishes, but end-to-end certification exceeds the bounded
  diagnostic and remains unmeasured.
  Artifact v33 exposes the same deadline-aware end-to-end route on exact
  manifest-bound real corpora. It is valid only on the raw, full-query QF_BV
  proof path: every primary UNSAT must be attempted and classified as
  certified, not-certified, a satisfiable contradiction, a recheck failure, or
  an operational error. Keep not-certified rows in the denominator; fail the
  other three alarm classes. The certificate timer is separate assurance work,
  not part of the cold solver ratio. Its absolute deadline covers the two
  proof-producing searches, while construction and completed-proof checking
  remain cooperative work until a later whole-process isolation gate. Version
  33 also fingerprints the already-recorded CNF-vivification switch so two
  artifacts cannot compare under one configuration hash when that policy
  differs.
  ADR-0234 applies this gate twice to ADR-0187's exact corrected 162-query
  representative Glaurung manifest at a predeclared 1000 ms per-UNSAT
  proof-search policy. Both runs attempt and independently recheck 74/74
  end-to-end certificates with zero not-certified or alarm row, while
  preserving all 88 SAT model replays, 74 CNF DRAT rechecks, Z3 decisions, and
  manifest decisions. The certified family split is 26 register-slice, 24
  slice-partial, 18 arithmetic, 5 comparison, and 1 mixed. Max certificate
  work is about 154 ms, so retain the cooperative-deadline and separate-timing
  caveats without claiming that this real-query run exercised expiry.
  ADR-0235 closes that whole-call caveat at the artifact boundary. Artifact v34
  can launch the same pinned executable as a source-hashed one-query worker;
  the parent wall covers worker parse, construction, both proof searches, and
  both completed-proof self-rechecks, then kills/reaps an overdue worker. Two
  clean corrected-representative runs certify 74/74 under a 1500 ms process
  wall with zero hard timeout or alarm. A same-population 1 ms control retains
  all 74 UNSAT rows as `not-certified` plus `hard_timeout`, with zero missing
  partition or false verdict. Process scheduling, one-millisecond polling,
  kill, and reap add bounded observed return overhead (1.456 ms maximum in the
  control); keep all worker time outside solver performance.
  Artifact v35 adds an explicitly selected, profile-only CNF construction
  census. It independently accounts for literal canonicalization, tautology
  causes, exact duplicates, clause lengths, and fingerprint-index work without
  adding counters or hot-loop branches to the ordinary encoder. Artifact v36
  extends only that opt-in route with stable first-producer and duplicate-
  producer origins, same-owner/cross-owner partitions, and exact length-aware
  duplicate totals. Artifact v37 adds bounded parity-leaf identity and shape to
  parity/parity duplicates, partitioned as within-leaf, cross-leaf/same-owner,
  or cross-owner. Every version must re-sum per-instance rows into the corpus
  aggregate and preserve complete decisions, oracle agreement, and original-
  model replay. The analyzer retains v36 compatibility, but v37 artifacts fail
  closed if the parity-overlap block is absent or inconsistent. All timing from
  these profiled paths is diagnostic; a production change requires a separate
  preregistration and repeated unprofiled timing gate.
  Artifact v38 was reserved by ADR-0285's subsequently reverted flat-CNF
  storage experiment; retained v38 artifacts remain interpretable and the
  version is not reused. Artifact v39 extends the existing observational
  bit-demand profile with representation-neutral full-lowering memo accounting:
  representation identity, source terms, slots/occupancy, lookup/hit/write
  counts, literal payload length/capacity, native logical bytes, and explicit
  invariants appear per instance and in aggregate. Profiled rows also carry
  deterministic FNV-1a regression digests over the ordered lowering/AIG and
  CNF/lift-map structures; the digests detect drift but are not cryptographic
  evidence. Unprofiled production runs report this block as unavailable.
  ADR-0300 requires a committed v39 BTree baseline before the dense candidate
  is built, then exact structural comparison before any separately built
  unprofiled timing pair.
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
