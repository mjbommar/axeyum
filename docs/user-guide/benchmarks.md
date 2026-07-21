# Benchmarks

Axeyum's benchmark posture is the same as its solving posture: **measure, don't
assert.** Every number here comes from a committed artifact under
[`bench-results/`](../../bench-results/), with `DISAGREE=0` and zero replay
failures (a wrong answer would fail the harness, not just score badly).

For consumer comparisons, timing is valid only when the decided-rate gate also
passes. Operational errors make `axeyum-bench` exit nonzero, and
`--min-decided-percent P` rejects a run whose `(sat + unsat) / files` falls below
`P`. This prevents a backend that fails quickly on most inputs from appearing
faster than a backend that actually solves them.

## Current measured map

No single corpus establishes "Z3 parity." The committed evidence intentionally
keeps distinct populations, limits, and consumer regimes separate.

### Regression scoreboard

The generated [scoreboard](../../bench-results/SCOREBOARD.md) contains 35 rows
across 24 logic labels: **753 / 992** files decided, **680 oracle-compared**, and
zero recorded disagreements. The rows are curated regression slices and include
overlapping file populations: 927 file occurrences contract to
**837 normalized paths** and 778 exact byte contents. The generated
[measurement-provenance matrix](../plan/generated/measurement-provenance-matrix.md)
records the row-local PAR-2 and identity layers, so 75.9% is not a global
completeness estimate.

### Harder public inventory

The [SMT-COMP-style reproduction](../../bench-results/smtcomp-repro-20260721/README.md)
runs a separate 228-file public convenience inventory at a 120-second ceiling:
**82 / 228** decided-correct, 144 explicit declines, two no-answer outcomes, and
zero wrong verdicts against recorded statuses. This is not the official
SMT-COMP selection and is dominated numerically by one hard 113-file p4dfa
family.

This view is not independent of the scoreboard. Exactly 99 contents occur in
both regimes—43.4% of the public inventory and 12.7% of the scoreboard's unique
file-backed contents. Keep the two results side by side; do not average them.

The separate 64,345-file full-tree candidate has no benchmark result. Its first
52-shard attempt stopped after 2,041 progress rows and wrote no raw shard JSON.
Do not reconstruct data from its logs or rerun the old launcher. The
[frozen handoff](../plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
and [resumable-run contract](../plan/generated/smtcomp-resumable-run-contract.md)
make atomic checkpoints, strict completion, and enforced aggregate resources
prerequisites to another attempt.
The local record primitive now passes forced-process-kill recovery on tmpfs and
ext-family storage, but the active runner, shared filesystem, resource envelope,
and remote retry protocol are still unchanged.

A separate 24-file QF_BV comparison has Axeyum, cvc5, and Bitwuzla each deciding
19/24; PAR-2 ranks Bitwuzla, cvc5, then Axeyum. That cell contains no Z3 result
and must not be described as a four-solver ranking.

### Registered p4dfa control

At the authoritative same-corpus, 20-second cell, Axeyum and the in-process Z3
crate each decide **8 / 113**, on different decided sets. A separately recorded
Z3 CLI artifact decides 9/113. Equal solved counts in this one deliberately hard
cell are bounded corpus parity, not general QF_BV or production parity. See the
[scoped parity analysis](../plan/gap-analysis-z3-lean-2026-07-21.md#corrected-public-qf_bv-control).

### Fair embedded Glaurung baseline

The preregistered six-cell experiment compares `{Z3, Axeyum, Bitwuzla} ×
{cold, warm}` over four real drivers. All cells decide and agree on all checks.
Warm Axeyum beats warm Z3 on vwififlt, IntcSST, and SurfacePen and loses on
DptfDevGen; warm Bitwuzla beats both on all four. The result establishes a
workload-dependent embedded regime and rejects an Axeyum performance-leadership
headline. See [ADR-0272](../research/09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md).

Embeddability, WASM availability, and independently checkable evidence remain
product advantages, but they are separate axes. A shell-out comparison includes
process overhead and is not evidence of solver-core speed against an in-process
baseline.

## Reproducing

```sh
just check                                       # fmt + clippy + test + doc gate
just bench-micro                                 # committed SMT-LIB micro corpus
just bench-public-qfbv-sat-bv-compare            # public sat-bv vs Z3 slice
just bench-public-qfbv-sat-bv-guarded            # node/CNF guarded run
just bench-public-qfbv-sat-bv-replay-refine      # replay-checked query refinement
just bench-glaurung-manifest-smoke               # client manifest/timing plumbing
just bench-glaurung-manifest-proof-smoke         # fail-closed DRAT-check plumbing
just generate-glaurung-manifest CORPUS INDEX OUT # bind capture facts to exact bytes
just glaurung-qfbv-regular                        # real capture when locally available
just bench-glaurung-qfbv-repeated CORPUS MANIFEST # raw process-level variance (5 trials)
just compare-glaurung-qfbv-repeated BASE CAND OUT # controlled cross-commit delta
```

**Resource rules** (this matters — the harness can OOM a small host otherwise):

- Build with one Cargo job on this host: `CARGO_BUILD_JOBS=1` / `--jobs 1`, and
  retain the aggregate cgroup memory cap described in [PLAN](../../PLAN.md).
- Do **not** sweep the full ~41 GB public corpus to "make progress." Measure once
  on a committed slice, then stop.

## Reading an artifact

Each JSON records the corpus + config hash, per-instance outcome, budgets,
backend stats, PAR-2, explicit `decided`/`decided_percent`, **disagreements**,
and **model-replay failures**. Artifact version 34 retains version 16's exact
floating-point millisecond values for each instance's word-level preprocessing,
bit-blast, CNF encode/inprocess, SAT, model lift, and cold total, plus corpus
totals and p50/p95 distributions. Its `client_comparison` block reports the
aggregate Axeyum/Z3 ratio plus each solver's p50/p95 over the same decided
queries. Version 17 additionally binds a run to an optional
[versioned corpus manifest](corpus-manifests.md), with exact membership,
per-query SHA-256, expected-verdict, and named-tier gates. Version 18 adds an
original-query `query_shape` block: formula and BV-width distributions,
extract/concat/extension/array-op counts, extract demanded-vs-source bits, and
exact extract-over-concat/extract/extension cancellation opportunities. The
layer block now includes AIG-input/node and CNF-variable/clause p50/p95 sizes.
Counts use unique nodes in the untouched parsed DAG; they are not distorted by
preprocessing or repeated expansion of shared terms.
Version 29 adds an explicit `demand_bit_slicing` configuration identity and
distinguishes observational bit-demand profiles from production demand-driven
lowering in both per-instance and aggregate attribution. Use
`--demand-bit-slicing` only with `--backend sat-bv`; the policy remains
off-by-default and every SAT result still replays against the original query.
Version 30 adds ADR-0158's separate `range_demand_slicing` identity, records
every admission threshold and deterministic work budget in the configuration
hash, and reports admission/fallback reasons, admission time, estimated bits,
work, range merges, and conservative promotions per instance and in aggregate.
Use `--range-demand-slicing` plus the `--range-demand-*` threshold flags only
with `--backend sat-bv`. It cannot be combined with v1
`--demand-bit-slicing`, remains off by default, and does not imply acceptance
until the `register-slice` and whole-corpus gates pass.
Version 31 adds causal rewrite targeting. `summary.rewrite.per_rule` reports
applications, affected query/family counts, DAG/tree reduction, and the selected
policy's output AIG/CNF/time totals without mislabeling those totals as saved
work. Repeatable `--rewrite-disable-rule <id>` flags (valid only with
`--rewrite default`) construct a checked default-minus-rule manifest; disabled
IDs and the resulting enabled rule list enter artifact identity. Pair the base
and ablated artifacts by manifest path to measure actual per-rule AIG/CNF/time
deltas before investing in a rewrite family.
Version 32 makes timeout-sensitive oracle coverage explicit. The in-process Z3
oracle now runs even when Axeyum returns `unknown`; each instance and the
summary partition the complete query set into `both-decided`,
`axeyum-only-decided`, `z3-only-decided`, and `neither-decided`. Z3 binary
fallback is limited to an in-process `unsupported` result and cannot replace a
real in-process timeout. Latency comparisons remain restricted to
`both-decided`; nondecisions are reported separately rather than rewarded as
fast solves.
Version 33 adds deadline-aware real-query end-to-end UNSAT certification.
`--certify-end-to-end-unsat --end-to-end-deadline-ms N` composes the
independent-reference bit-blast miter with the final CNF DRAT refutation and
then rechecks both certificates from text. Every primary UNSAT is classified as
`certified`, `not-certified`, a satisfiable contradiction, a recheck failure,
or an operational error. Only `not-certified` is an accepted coverage miss;
the other three alarms fail the run. This mode requires the raw full-query
`sat-bv` proof path and keeps its assurance time outside solver-performance
totals. The deadline is cooperative proof-search policy, not a whole-call wall
clock: construction and completed-proof checking still run to completion.
Version 33 also adds the already-reported `cnf_vivify` switch to `config_hash`;
earlier artifacts recorded that switch in `config` but did not fingerprint it.
Version 34 adds optional killable whole-certificate isolation. Supplying
`--end-to-end-process-timeout-ms N` launches the same pinned benchmark
executable as a private one-query worker after each primary UNSAT. The worker
re-reads the exact source hash, constructs both certificates, and self-rechecks
both stored proof texts; the parent kills and reaps it when the hard wall
expires. A hard timeout is an explicitly counted subset of `not-certified`,
never SAT, UNSAT, or an omitted row. Worker crashes, malformed protocol output,
source drift, satisfiable contradictions, and recheck failures remain fatal.
The per-instance and summary records distinguish `subprocess-hard-timeout`
from the historical `in-process-cooperative` route, and both cooperative and
process budgets enter `config_hash`.
ADR-0159 makes that pairing executable and fail-closed. The repeated ablation
recipe alternates an unchanged default run with the exact default-minus-rule
run in fresh processes. `compare-glaurung-rewrite-ablation.py` rejects any
non-rewrite configuration, source, environment, corpus, correctness, outcome,
or instance-set drift; it reports `ablation - base` deltas on the queries where
the rule fired, with exact structural values kept separate from repeated timing
samples and whole-corpus timing controls.
Version 19 separately times original-query SAT model replay and charges it to
the cold total and Axeyum/Z3 comparison. `--prove-unsat` selects the
proof-producing native core and makes every UNSAT fail closed unless its DRAT
proof checks; the artifact records checked/missing counts and proof-check
p50/p95. Proof-check time is already inside SAT time and is marked as nested, so
it is never added twice. Keep this high-assurance artifact separate from the
default batsat performance run because it intentionally changes the SAT engine.
Version 20 adds `config.experiment`: the Axeyum source revision and source-tree
cleanliness, Cargo.lock SHA-256, rustc/cargo versions, build profile, exact
solver backend names, CPU model, OS/kernel, logical parallelism, and total memory. Its
`environment_hash` covers the locked toolchain/solvers/hardware but deliberately
excludes the source revision. Compare artifacts only when both `config_hash` and
`environment_hash` match; the differing source revisions are the commits being
compared. `--require-reproducible-run` fails before solving if the source tree is
dirty (excluding generated `bench-results/**`) or a required identity field is
unavailable. The Glaurung recipes enable this gate by default.
Version 21 removes the old `--seed` label, which did not configure either
backend, and records an executable `config.determinism` profile instead. That
profile binds the actual Cargo.lock-pinned BatSat defaults (seed `91648253`,
random branching frequency `0`, random polarity disabled, and random initial
activity disabled), explicitly sets and records Z3 `random_seed=0`, and states
the deterministic corpus-order rule. These values enter `config_hash`; the
repetition validator rejects missing or drifting values. The BatSat seed is
still recorded even though all reviewed randomization switches are off. This
fixes configuration identity, not wall-clock noise, so repeated trials remain
required.
Version 22 makes the cold QF_BV resource boundary executable.
`--require-deterministic-resources` rejects a run unless positive
`--resource-limit`, `--node-budget`, `--cnf-var-budget`, and
`--cnf-clause-budget` values are all supplied. `resource_limit` now reaches the
actual search engine: it counts deterministic `BatSat` `within_budget` progress
checks on the default path, native proof-CDCL conflicts under `--prove-unsat`,
and Z3 `rlimit` units in the oracle. Artifact `config.resources` records those
units, all four limits, and the fact that equal numeric limits are not
cross-backend work-equivalent. The Glaurung recipes require the named
`axeyum-qfbv-cold-bounded-v1` profile: 300,000 term-DAG nodes, 3,000,000 CNF
variables, 8,000,000 CNF clauses, and 2,000,000 backend search units. Timeout is
retained as a non-deterministic safety backstop, not counted as proof of the
deterministic bound.
Version 23 adds paired shape telemetry without changing the solve path. Every
successfully parsed query records its untouched original snapshot and its
post-selected-word-policy snapshot, plus before/after/removed/added counts for
extract-over-concat, nested extract, zero/sign extension, same-side versus
straddling concat slices, whole-operand slices, low/high/straddling extension
regions, exact low-extension cancellation, and maximum nested-extract depth.
Raw runs should report no transition; canonical/configured runs reveal the
residual GQ3 opportunity set that would still reach bit lowering.
Version 24 adds construction attribution without changing the solve path. Each
instance and the corpus summary partition primitive AIG AND requests into
trivial simplifications, absorption simplifications, structural-hash hits, and
new nodes. CNF diagnostics time planning, retained-variable allocation,
non-root gate encoding, and root encoding; count reachable/skipped-helper/
direct-root nodes and recognized XOR/mux/not-AND/private-tree/binary-AND gates;
and partition clause attempts into tautological skips, duplicate skips, and
emitted clauses. The artifact reports both partition invariants. CNF subphase
timers are nested within `cnf_encode`, so do not add them to cold total again.
Version 25 adds a conservative bit-demand profile. It reports term/symbol bit
requests, unique demanded bits, all reachable available bits, and bits actually
materialized by the lowerer, with demanded/available and lowered/demanded
ratios. Extract, concat, extension, pointwise BV, `ite`, rotation, and FP-bit
reinterpretation propagation is exact; unclassified operators conservatively
demand every operand bit. The analysis time is reported and is already nested
within `bit_blast`. Coverage invariants must remain true. These counts expose a
potential GQ4 reduction; they do not claim that omitted bits are already safe or
that the current lowerer avoids them. In artifact v25/v26 this observational
pass was always-on inside `lower_terms`; the real full Glaurung run found it
consuming 29.57 of 50.75 Axeyum seconds after canonicalization. Artifact v27
makes it opt-in through `--profile-bit-demand`. Production artifacts set
`profile_complete: false`, publish request/available/demand/ratio/coverage
fields as `null`, and retain actual lowered counts. Separately named demand
profile recipes set `profile_complete: true`; their timing includes the
diagnostic and must not be cited as the client ratio.
Version 26 closes the canonical-only timing boundary: the elapsed default
rewrite is now charged to `word_preprocess`, the instance cold total, PAR-2,
and the Axeyum side of `client_comparison`, and is also exposed as
`instances[].rewrite.elapsed_ms`. Artifact v25 canonical ratios omitted this
cost and are therefore diagnostic structure/solver-time evidence only, not
publishable end-to-end client ratios.
Version 27 enforces ADR-0143's production/diagnostic boundary, records the
profiling flag in configuration identity, and prevents repetition summaries
from mixing v26's accidental diagnostic overhead with production timings.
Version 28 adds a complete sharing-aware scalar Bool/QF_BV operator inventory
to both the original and post-word query-shape snapshots. It classifies
arithmetic, bitwise, shifts, comparisons, structural operators, equality, and
`ite` individually, retains an explicit `other` bucket, and publishes
per-instance plus corpus totals. Use the post-word inventory—not lexical source
counts—to select a rewrite or lowering experiment.
A comparable run requires zero errors, zero disagreements, zero replay failures,
and the declared decided-rate threshold; only then is timing a performance
signal.

Short whole-corpus measurements also require repeated independent trials. The
single-run p50/p95 values describe variation **between queries of different
shapes**; they do not measure run-to-run noise. The repeated client recipe below
launches a fresh process for every trial, keeps each artifact intact, and writes
a small `summary.json` containing nearest-rank p50/p95, sample standard
deviation, and coefficient of variation for Axeyum and Z3 corpus totals, their
ratio, and every attributed Axeyum stage. The summarizer holds only one source
artifact at a time, so repetitions do not multiply the large corpus artifact's
memory footprint.
The committed
[`glaurung-repetition-smoke`](../../bench-results/glaurung-repetition-smoke/summary.json)
exercises this plumbing on the two-query micro tier; its sub-millisecond
variance is not client performance evidence.

## Binary-analysis client gate

The client target accepts an external Glaurung query capture (the client corpus
is not redistributed by this repository). Three policies are intentionally
separate:

| Policy | Recipe | Harness configuration | Use |
|---|---|---|---|
| `raw` | `bench-glaurung-qfbv-raw` | `--rewrite off`, preprocessing off | Current Glaurung one-shot integration and primary cold control |
| `canonical` | `bench-glaurung-qfbv-canonical` | `--rewrite default`, preprocessing off | Cheap exact word-level rewrite candidate |
| `configured` | `bench-glaurung-qfbv-configured` | `--rewrite off --preprocess` | Broader warm-oriented preprocessing diagnostic |

The unsuffixed `bench-glaurung-qfbv` compatibility recipe is the **raw**
control. This matters because the original producer profile and Glaurung's
current backend use raw assertions, while configured preprocessing has measured
as a cold loss in that integration. Never compare artifacts from different
policies as consecutive revisions of one experiment; their configuration hashes
also differ.

`just check` includes an availability-aware semantic regression over the real
128-query capture. `just glaurung-qfbv-regular` runs it directly. The gate uses
`AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR` when set, otherwise auto-discovers
the pinned 2026-07-14 NAS pack. If neither is available it prints an explicit
`SKIP` and succeeds, so ordinary CI does not pretend to own access-controlled
data. An explicitly configured missing directory or manifest fails. Set
`AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER=0` to disable NAS discovery and
`AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_MANIFEST` only when the manifest is not
`manifest-v1.json` inside the corpus root.

The regular gate runs both raw and canonical policies with the named
representative tier, in-process Z3, the fixed deterministic resource profile,
100% decided coverage, and zero manifest/oracle/error/model-replay failures.
It writes the latest raw and canonical artifacts under
`target/glaurung-qfbv-regular/` (override with
`AXEYUM_GLAURUNG_QFBV_REGRESSION_OUT_DIR`) and prints their stage totals and
Axeyum/Z3 ratios. These single, potentially dirty-worktree runs are semantic
and attribution diagnostics; publishable performance still requires the clean,
fresh-process repeated/full recipes below.

Run the current-integration control with:

```sh
just bench-glaurung-qfbv \
  /path/to/glaurung-smt2-capture \
  /path/to/glaurung-manifest-v1.json \
  representative
```

This first validates every file and SHA-256 declared by the manifest, selects
the named tier in manifest order, and gates each result against the capture's
expected verdict. It runs one query at a time, compares every result with
in-process Z3 on the **original parsed assertions**, requires a 100% decided
rate, requires in-process Z3 coverage for every selected file, and emits a
versioned artifact. Axeyum's comparison time includes whichever word policy the
named recipe selected; Z3 never receives Axeyum's rewritten or reduced assertion
set. Synthetic QF_BV corpora remain useful lower-level diagnostics, but do not
replace the extract/concat/mixed-width/memory-derived client shape. The shape
block can count `select`/`store` operations that survive parsing, but cannot
infer memory provenance after a lifter has flattened memory into BV terms;
preserve that provenance in the manifest `family` and `source` fields.

Run the two diagnostics explicitly rather than editing the raw recipe:

```sh
just bench-glaurung-qfbv-canonical CORPUS MANIFEST representative
just bench-glaurung-qfbv-configured CORPUS MANIFEST representative
```

For the publishable repeated measurement (five trials by default):

```sh
just bench-glaurung-qfbv-raw-repeated \
  /path/to/glaurung-smt2-capture \
  /path/to/glaurung-manifest-v1.json \
  representative \
  bench-results/glaurung-qfbv-raw-repeated \
  5
```

The unsuffixed repeated recipe is also a raw alias. Use
`bench-glaurung-qfbv-canonical-repeated` or
`bench-glaurung-qfbv-configured-repeated` for the other policies. Each has a
policy-specific default output directory so summaries cannot be mixed by
accident.

Measure one default rewrite causally with:

```sh
just bench-glaurung-qfbv-rewrite-ablation-repeated \
  /path/to/glaurung-smt2-capture \
  /path/to/glaurung-manifest-v1.json \
  bv.extract_extend.v1 \
  representative \
  bench-results/glaurung-extract-extend-ablation \
  5
```

The output directory contains paired `base-*`/`ablation-*` artifact-v34 files
and `comparison.json`. Positive deltas mean the enabled base rule avoided that
work or time. Fire counts and selected-policy output sizes remain targeting
telemetry, not causal savings.

Every source artifact must have byte-identical configuration, a clean
reproducible-run identity, one worker, complete in-process Z3 coverage, 100%
decisions, and zero operational errors, manifest/oracle disagreements, or
model/proof replay failures. Any violation prevents `summary.json` from being
written. The summary records each source artifact's SHA-256 and the exact
configuration/experiment identity, so trials cannot be silently mixed across
commits, hardware, toolchains, corpus bytes, or solver settings. `summary.json`
must remain in the common source-artifact directory; its portable relative
paths let the cross-commit comparator reopen and revalidate every trial.

Compare two repeated summaries from distinct clean source revisions with:

```sh
just compare-glaurung-qfbv-repeated \
  bench-results/baseline/summary.json \
  bench-results/candidate/summary.json \
  bench-results/comparison.json
```

The comparator independently revalidates both summaries and recomputes their
variance blocks from the source-trial records. It requires identical corpus and
manifest hashes, solver configuration, toolchain, hardware, and backend
versions; only `config.experiment.source.revision` may differ, and both sources
must be clean. The report shows candidate-minus-baseline changes for raw Axeyum
time, raw Z3 control time, the Axeyum/Z3 ratio, and every attributed Axeyum
stage. `standardized_delta` is a descriptive change divided by the combined
standard error, not a statistical-significance claim.

Once the real corpus establishes an accepted regression policy, explicit gates
can be applied without changing the evidence format:

```sh
python3 scripts/compare-glaurung-repetitions.py \
  bench-results/baseline/summary.json \
  bench-results/candidate/summary.json \
  --max-ratio-regression-percent 5 \
  --max-axeyum-regression-percent 5 \
  --max-z3-drift-percent 10 \
  --out bench-results/comparison.json
```

The generic command above illustrates the CLI. For the current full-tier
canonical boundary, five clean trials measured about 0.51% CV for Axeyum total
and the ratio, and 0.31% for Z3. The provisional same-environment policy is 3%
maximum ratio regression, 3% maximum Axeyum-total regression, and 2% maximum
absolute Z3-control drift:

```sh
just compare-glaurung-qfbv-repeated-guarded \
  bench-results/baseline/summary.json \
  bench-results/candidate/summary.json \
  bench-results/comparison.json
```

These are regression alarms, not universal hardware promises. A configured
gate writes the comparison for diagnosis and exits nonzero when exceeded.
Invalid or incomparable inputs remove any stale output and fail before
producing a report. The comparator accepts raw, canonical, and configured
series, but baseline and candidate must use the exact same policy and all other
configuration; it never compares one policy against another as a code delta.
The committed
[`glaurung-cross-commit-smoke`](../../bench-results/glaurung-cross-commit-smoke.json)
exercises this path across two clean revisions. Its high candidate variance
makes the result diagnostic plumbing only, not a speedup or threshold decision.

Run the separate proof-validation companion on the same immutable manifest:

```sh
just bench-glaurung-qfbv-raw-proof-check \
  /path/to/glaurung-smt2-capture \
  /path/to/glaurung-manifest-v1.json \
  representative
```

It retains the decided/error/oracle/manifest gates, adds the checked-proof gate,
and writes a separate artifact. Its native-CDCL timings are assurance overhead,
not a replacement for the default client performance ratio. The unsuffixed
proof recipe is a raw alias; canonical and configured proof companions are
available under the corresponding suffixed recipe names. Pair a performance
artifact only with the proof companion using the same word policy.

Run the stronger term-to-CNF faithfulness denominator separately on the raw
manifest-bound path:

```sh
just bench-glaurung-qfbv-real-faithfulness \
  /path/to/glaurung-smt2-capture \
  /path/to/glaurung-manifest-v1.json \
  representative \
  1000 \
  1500
```

The summary reports certified and not-certified rows over the complete primary
UNSAT population, including exact uncovered and hard-timeout paths. The first
budget is the cooperative proof-search deadline; the second is the hard
whole-worker wall covering parse, construction, proof search, and completed-
proof self-recheck. Do not add certificate-process time to the cold solver
total.
