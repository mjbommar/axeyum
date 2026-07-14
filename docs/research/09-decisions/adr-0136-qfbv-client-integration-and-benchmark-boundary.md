# ADR-0136: QF_BV client integration and benchmark boundary

Status: accepted
Date: 2026-07-13

## Context

A real binary-analysis integration exercised roughly 180,000 formulas without
a crash or hang and reported correct decisions, replay-safe `Unknown`, honored
warm timeouts, and independently recheckable UNSAT proofs. It also exposed
integration friction and a performance result that synthetic, uniformly typed
QF_BV formulas had hidden: Axeyum was about 1.7--3.2x slower than in-process Z3
on width-mixed, extract/concat, and memory-derived Glaurung path conditions.

The same integration found a benchmark soundness trap. A nominal 12--34x
speedup was actually the client returning construction errors for about 98% of
queries. Verdict agreement alone cannot make such a run comparable; the
decided rate and operational-error count are part of benchmark validity.

## Decision

Adopt the following QF_BV client boundary:

- IR builders remain strictly sorted. There is no implicit arithmetic coercion.
  `TermArena::coerce_to` is the explicit unsigned machine-width helper:
  zero-extend, identity, or low-bit truncate. Signed widening remains an
  explicit `sign_ext` operation.
- `axeyum-solver` re-exports `Value`. The command-faithful
  `solve_smtlib_get_model` remains unchanged, while `solve_smtlib_model`
  retrieves a declaration-ordered model from any satisfiable single-query
  script independently of `(get-model)` or `(get-value)` commands.
- `default-features = false, features = ["qfbv"]` is the minimal pure-Rust
  scalar QF_BV profile. A repository gate rejects accidental dependencies on
  the e-graph, floating-point, Lean-kernel, SMT-LIB, or string crates.
- The warm solver exposes `assert_preprocessed` and `assert_configured`.
  Preprocessing is exact and the original assertion remains the model-replay
  obligation. Narrow extracts distribute through pointwise bit-vector
  operations and bit-vector `ite`, preventing discarded wide-register bits from
  becoming AIG gates.
- The pure-Rust incremental solver is documented and compile-checked as `Send`.
  Its BatSat stop policy stores a per-solve `Instant` rather than a non-`Send`
  callback closure. Parallel consumers use one arena and solver per worker; no
  shared global native-solver context is implied.
- Benchmark artifacts record `decided` and `decided_percent`. Any operational
  error makes the run fail, and `--min-decided-percent` is an enforceable gate.
  The primary client recipe requires 100% decisions and Z3 comparison on an
  externally captured Glaurung SMT-LIB corpus.

Extract bounds are inclusive and `concat(high, low)` ordering is part of the
public embedding documentation. Precise construction errors remain a product
contract, not an implementation detail.

## Evidence

The accepted implementation is covered by:

- IR construction, rendering, evaluation, invalid-sort, and invalid-width
  tests for explicit coercion;
- command-faithful and command-independent SMT-LIB model-access tests;
- a no-default-features QF_BV compile, strict-Clippy, runtime model/proof/warm
  smoke test, and dependency-tree firewall;
- exhaustive small-width evaluator checks for extract distribution across
  `bvnot`, six binary bitwise operations, and bit-vector `ite`;
- Z3 differential SAT and UNSAT checks for the same lifter-shaped identities;
- a warm-path structural test showing that an 8-bit slice of a 64-bit bitwise
  assertion removes most discarded AIG gates while preserving replayed SAT;
  and
- benchmark-harness tests where 2 decisions plus 98 errors fail comparability,
  including exact decided-rate threshold behavior.

The local Glaurung reference checkout contains source but no captured SMT-LIB
query corpus. Therefore this ADR records no new end-to-end 1.7--3.2x ratio and
makes no parity claim. The external capture is required for that measurement.

The 2026-07-13 GQ1 readiness follow-up advances the artifact to version 16. It
times word preprocessing separately from term→AIG, AIG→CNF, optional CNF
inprocessing, SAT, and model lift; records exact p50/p95 distributions; and
compares against in-process Z3 on the original parsed assertions rather than
Axeyum's reduced terms. The client recipe also requires every file to receive an
in-process Z3 comparison; subprocess fallback cannot silently populate a partial
ratio. A three-query micro run validates the plumbing at 100% decided,
`DISAGREE=0`, and zero replay failures, but is explicitly not a client performance
result and does not substitute for the external capture.

The following GQ1/GQ10 ingestion increment advances the artifact to version 17
and makes corpus identity a hard pre-solve contract. Manifest v1 declares the
capture source and logic plus every query's normalized relative path, SHA-256,
expected verdict, family, stable order, and named tiers. The harness validates
exact directory membership and every digest before selecting a tier, rejects
anonymous manifest-backed limits, and exits nonzero unless every selected
verdict agrees with the manifest independently of SMT-LIB `:status`. The
manifest digest and tier enter the config identity. A committed micro manifest
tests this boundary without claiming to represent the missing client capture.

Artifact version 18 then makes the corpus-shape part of that boundary
machine-readable. Each instance profiles unique nodes in the untouched parsed
DAG, including formula size/depth/sharing, BV width diversity,
extract/concat/extension and surviving array operations, demanded-vs-source
extract bits, and exact extract-over-concat/nested-extract/extension
cancellation opportunities. Corpus summaries add deterministic p50/p95 formula
and AIG/CNF sizes. This instrumentation ranks GQ3/GQ4 without changing terms or
claiming that a synthetic fixture represents Glaurung; memory provenance erased
by BV flattening remains an explicit manifest-family responsibility.

Artifact version 19 makes replay cost and availability explicit. SAT model
reconstruction/checking against the untouched assertions is a separately timed
additive stage and is included on both sides of the in-process Axeyum/Z3
comparison. `--prove-unsat` provides a distinct high-assurance run: the native
proof-producing core must report an inline-checked DRAT proof for every UNSAT or
the harness fails closed, and the checker duration receives its own p50/p95.
That duration is nested within SAT search and is not added twice. The primary
Glaurung performance recipe remains on the default batsat path; a separate
proof-check artifact prevents assurance overhead from masquerading as the client
performance ratio.

Artifact version 20 separates *what changed* from *where it ran*. The experiment
identity records the Axeyum Git revision and clean-tree state, Cargo.lock hash,
rustc/cargo and build profile, exact backend names, CPU, OS/kernel, parallelism,
and memory. The existing `config_hash` continues to name corpus and solver settings; a new
`environment_hash` covers locked tools and hardware but deliberately omits the
source revision, so per-commit regression comparisons require matching config
and environment hashes while retaining distinct tested revisions.
`--require-reproducible-run` rejects dirty or incomplete identities before any
query is timed. Generated `bench-results/**` are excluded from the dirty check so
performance and proof companions can be emitted sequentially from one clean
source checkout without weakening the source-integrity gate.

Artifact version 21 closes a defect in the fixed-seed boundary. The prior
benchmark `--seed` option was only an artifact label and did not configure
BatSat or Z3. It is removed. Artifacts and `config_hash` now bind an executable
determinism profile: the actual Cargo.lock-pinned BatSat defaults read from
`batsat::SolverOpts::default` (seed `91648253`, random-variable frequency `0`,
random polarity disabled, random initial activity disabled), explicit Z3
`random_seed=0`, and deterministic corpus order. A Rust regression pins the
reviewed BatSat defaults and the repeated-run validator rejects profile drift.
This decision establishes solver-configuration identity; it does not turn
wall-clock measurements into deterministic values or replace bounded-resource
gates.

Artifact version 22 closes the remaining deterministic-resource gap for the
cold client lane. `--require-deterministic-resources` rejects missing or zero
term-DAG, CNF-variable, CNF-clause, or backend-search bounds before corpus work.
The existing `SolverConfig::resource_limit` now reaches every search engine used
by these recipes: deterministic `BatSat` `within_budget` progress checks, native
proof-CDCL conflicts, and Z3 `rlimit` units. Artifacts record the selected unit
and explicitly deny cross-backend numeric work equivalence. The first named
profile, `axeyum-qfbv-cold-bounded-v1`, sets 300k DAG nodes, 3M CNF variables,
8M CNF clauses, and 2M search units. The real capture may justify a new
versioned profile; it may not cause a silent relaxation. Wall-clock timeout is a
separate non-deterministic safety valve.

The capture-ingestion follow-up defines a versioned shadow-diff capture index
that contains only the producer-owned semantic facts: stable query path/order,
trusted expected verdict, workload family, and representative/full tier
membership. `axeyum-bench --generate-corpus-manifest` rejects unknown fields
and incomplete directory membership, computes every SHA-256 from the captured
query bytes, and re-parses its deterministic output through the ordinary
manifest-v1 validator before writing it. In particular, the index may not carry
a `content_hash`; this prevents stale exporter bookkeeping from being promoted
to corpus identity. The committed micro index tests the handshake but remains
non-client evidence.

The repeated-run follow-up makes the methodology's short-run variance rule
executable without weakening the cold boundary. The repeated Glaurung recipe
launches a fresh `axeyum-bench` process per whole-corpus trial and retains each
artifact independently. A streaming, fail-closed summarizer accepts only
artifact-v22 trials with byte-identical configuration, clean reproducible
source/tool/hardware identity, one worker, complete manifest and in-process Z3
agreement, 100% decisions, and zero operational or replay failures. It reports
sample standard deviation and coefficient of variation alongside p50/p95 for
whole-corpus Axeyum/Z3 totals, their ratio, and every attributed Axeyum stage.
This distinguishes between-query shape distributions from genuine run-to-run
noise and avoids multiplying the large artifact's in-memory footprint.

The cross-commit follow-up makes `config_hash + environment_hash` operational
rather than advisory. A comparator revalidates each repetition summary from its
trial records, requires identical corpus/manifest bytes, solver settings,
toolchain, hardware, and backend versions, and permits only the clean source
revision to differ. It reports candidate-minus-baseline raw Axeyum time, raw Z3
control time, Axeyum/Z3 ratio, and every stage, including sample distributions
and a descriptive standardized delta. Optional ratio, raw-Axeyum, and absolute
Z3-drift gates take explicit thresholds; the micro corpus does not set product
policy. Invalid identity/variance removes stale output, while a valid comparison
that exceeds a configured gate remains written for diagnosis and exits nonzero.

Artifact version 23 adds a paired structural boundary without changing the
solver. Every successfully parsed query is profiled both before and after its
explicit raw, canonical, or configured word policy. The artifact classifies
concat extracts by low/high/straddling region and exact whole operand,
extension extracts by low/high/straddling region, exact low-extension
cancellations, and nested-extract depth. Before/after/removed/added transitions
therefore distinguish opportunities eliminated at word level from those that
actually reach bit lowering. Repetition ingestion advances with the artifact
version so policies and shape contracts cannot be silently mixed.

Artifact version 24 adds bounded AIG/CNF construction attribution, again
without changing construction semantics. Every primitive AIG AND request is
classified exactly once as a trivial simplification, absorption simplification,
structural unique-table hit, or newly allocated node. CNF encoding separately
times reachability/use planning, retained-variable allocation, non-root gate
encoding, and root encoding; counts reachable nodes, skipped private helpers,
direct roots, and each recognized gate family; and classifies every clause
attempt as tautological, duplicate, or emitted. Per-instance and corpus records
publish the two partition invariants. CNF subphase timings are explicitly nested
inside the existing CNF-encode duration and never added to cold total twice.
The diagnostics identify where GQ5 engineering should occur; they do not make a
data-structure or encoding change acceptable without a valid real-corpus
end-to-end improvement. The repetition and comparison schema advanced with v24.

Artifact version 25 adds the corresponding pre-optimization relevant-bit
boundary. A conservative structural analysis begins with all root bits,
propagates exact demands through extract, concat, zero/sign extension,
pointwise BV operations, `ite`, rotations, and FP bit reinterpretation, and
falls back to every operand bit for operators without a bit-local rule. It
reports request counts, unioned demanded bits, all reachable available bits,
and actually materialized term/symbol bits. Coverage invariants reject an
analysis that demands unavailable bits or a lowering that fails to cover the
reported demand. Analysis duration is measured and explicitly nested in
bit-blast time. This is diagnostic only: v25 does not omit bits, change model
projection, or relax original-query replay. Repetition and comparison tools
advance to v25 so this cost/schema cannot mix with earlier trials.

## Alternatives

- **Implicitly widen or truncate binary operands.** Rejected: it masks client
  bugs and makes signedness policy invisible.
- **Change `solve_smtlib_get_model` to ignore script commands.** Rejected: it
  would silently break the command-faithful contract; a separate accessor is
  unambiguous.
- **Make every warm `assert` mutate the arena.** Rejected: the raw immutable
  assertion path is useful and source compatibility matters. Explicit and
  config-driven mutable methods add preprocessing without removing it.
- **Claim the synthetic QF_BV corpus represents binary lifting.** Rejected:
  the observed performance gap is shape-specific and must be measured on the
  client capture.
- **Score timing when most files error or remain undecided.** Rejected: early
  failure is not solver performance.

## Consequences

QF_BV embedders get a smaller dependency surface and less glue while strict
typing, original-term replay, deterministic state, and proof checking remain
intact. Warm preprocessing now has a targeted structural optimization for the
reported formula shape. Future performance changes are accepted only if the
Glaurung client artifact preserves the declared decided rate, has zero
operational errors/disagreements/replay failures, and improves comparable
end-to-end timing; synthetic wins alone are diagnostic, not dispositive.
