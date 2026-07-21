# ADR-0340: Preregister a reason-preserving Unknown-to-directed-fuzz handoff

Status: proposed
Date: 2026-07-21

## Context

P5.4/T5.4.1 supplies deterministic reflection-versus-reflection and
reflection-versus-source fuzz oracles. T5.4.2 turns decided, replay-confirmed
solver countermodels into stable seed corpora and compiled regressions. The
third branch is still missing: a proof attempt that honestly returns
`ProofOutcome::Unknown(UnknownReason)` leaves a consumer with a classified
nondecision but no bounded way to exercise the same guarded input space.

That gap must not be closed by relabeling. A sampled run cannot prove a
property, and a solver error, malformed term, unsupported input domain, replay
failure, or oracle disagreement is not `Unknown`. The Glaurung reviewer
feedback is explicit that attempted work, decided results, Unknown by cause,
errors, fallbacks, replay failures, and dropped work must remain separate.

The existing boundaries are sufficient for a narrow implementation:

- `axeyum_solver::prove` already returns checked `Proved`, original-term-model-
  replayed `Disproved`, or a structured `UnknownReason`;
- `TermArena` exposes declaration-ordered symbols, sorts, the ground evaluator,
  and exact hypotheses/goal terms;
- `axeyum-smtlib::write_script` emits a sharing-preserving, linear-in-DAG
  description of the violation query;
- T5.4.1 supplies the deterministic seeded/corner sampling convention.

Glaurung's current production adapter is not yet an admissible consumer seam:
`map_check_result` flattens `CheckResult::Unknown(_)` into the unit variant
`SolveResult::Unknown`. Its dirty `sec/axeyum-backend` worktree also carries
unrelated concurrent work. This cell therefore establishes and tests the
Axeyum-owned artifact/report contract first. A later Glaurung integration must
preserve the classified cause rather than infer it from timing or a unit enum.

This work is correctness and accounting infrastructure. It does not replace
the reviewer's standing multi-oracle differential-fuzz campaign, make a
performance claim, reopen concretization policy results, or authorize symbolic
memory.

## Decision

Add a public `axeyum_verify::directed_fuzz` module with one fail-closed hybrid
entry point over a QF_BV proof query and two caller-owned original-semantics
callbacks.

The v1 contract is:

1. `DirectedFuzzPlan` carries a stable target ID, explicit declaration-ordered
   input domains, deterministic seed, and nonzero sample budget. An input is a
   Bool domain or a full/bounded unsigned bit-vector interval. The arena remains
   the owner of symbol names and sorts.
2. Validation requires a Boolean goal and Boolean hypotheses, unique exact
   coverage of every free symbol, matching Bool/BV sorts, well-formed in-width
   bounds, and a quantifier-free Bool/QF_BV reachable DAG. Arrays, functions,
   Int/Real/Float/Seq/datatype terms, quantifiers, omitted/extra symbols, and
   malformed fields fail with typed errors before solving.
3. `check_with_directed_fuzz` invokes `prove` exactly once. It returns one of
   three disjoint public outcomes:
   - `Proved`, retaining the checked `EvidenceReport`;
   - `RefutedReplayed`, retaining the solver's original-term-replayed model only
     after a caller replay callback also succeeds exactly once;
   - `FuzzedOnly`, retaining the exact `UnknownReason`, owned target artifact,
     and sampled report.
4. The replay callback is never called for `Proved` or `Unknown`. The fuzz
   oracle is never called for `Proved`, `Disproved`, or guard-rejected samples.
   A false countermodel replay is a typed error and produces no refuted outcome.
5. Only `ProofOutcome::Unknown` starts sampling. Solver errors propagate as
   typed errors; no error becomes a fuzz target. The runner evaluates every
   hypothesis and the goal in the original arena, invokes the caller's concrete
   oracle only for guard-admitted tuples, and records reflected/source
   disagreement rather than selecting a convenient side.
6. Sampling is deterministic in `(inputs, domains, seed, sample_budget)`: first
   exercise range corners, then use the fixed Axeyum LCG. Bool values remain
   typed Bools; BV values retain width and an in-range `u128` pattern. Full
   width-128 ranges must not overflow range arithmetic.
7. `DirectedFuzzReport` separately counts requested samples, guard-admitted
   samples, guard rejections, agreed goal violations, oracle disagreements, and
   the first typed tuple for each exceptional class. Zero admitted samples are
   reported honestly and do not become success.
8. `DirectedFuzzTarget` emits canonical compact JSON containing a versioned
   schema, stable ID, exact Unknown kind/detail, seed/budget, ordered typed
   input domains, and the exact sharing-preserving SMT-LIB violation query
   `hypotheses AND NOT goal`. The report emits separate canonical JSON and uses
   the status `fuzzed-only`; it never says proved, unsat, safe, covered, or
   solver-refuted.
9. The library returns owned values and bytes only. It performs no filesystem,
   process, network, git, or hidden second-solver operation. Callers explicitly
   review and persist artifacts.

No IR operator, solver strategy, backend policy, proof format, native
dependency, unsafe code, or Glaurung source is changed. T5.4.4 remains the sole
owner of proof/refutation/fuzz coverage accounting.

## Frozen evidence gates

Implementation is accepted only if all of these gates pass:

1. Commit and push this zero-result ADR plus PLAN/STATUS/task/question/index
   registration before adding production code or observing target/report
   fixture bytes.
2. Unit tests cover every `UnknownKind` label and typed rejection of zero
   samples, invalid IDs, duplicate/omitted/extra symbols, Bool/BV sort mismatch,
   reversed/out-of-width ranges, non-Boolean goals/hypotheses, and every
   unsupported reachable sort/operator family. An operational `SolverError`
   must never produce `FuzzedOnly`.
3. One integration exercises the three outcome branches with callback counters:
   a universally true guarded QF_BV goal is `Proved` with neither callback; a
   false goal is `RefutedReplayed` after exactly one source callback and no fuzz
   oracle; the true goal under `node_budget=0` is a classified
   `node-budget` `FuzzedOnly` outcome with no replay call.
4. The Unknown case uses at least two scalar inputs, explicit intervals, and a
   nontrivial hypothesis. Its real Rust oracle runs only on admitted samples;
   the report has nonzero admitted and rejected counts, zero disagreement, and
   zero violation. Range-min/max/adjacent/midpoint tuples are exercised before
   seeded samples.
5. A false refutation replay fails before outcome construction. A mutated source
   oracle creates an explicit disagreement. A seed/domain/goal/Unknown-detail
   mutation changes canonical artifact bytes. Repeating the same plan produces
   byte-identical target and report JSON.
6. Commit exact target/report fixtures for the artificial hard-goal integration
   and compare them byte-for-byte. Independently parse the embedded SMT-LIB
   query and prove it is the same `hypotheses AND NOT goal` query; JSON control
   escaping and width-128 full-range sampling have dedicated checks.
7. Existing T5.4.1 oracle tests, T5.4.2 corpus/reproduction tests, source
   contracts, property SDK, and the current 129-test reflection semantics gate
   remain green. The public module has warning-clean rustdoc and a compile-
   checked example.
8. Formatting, strict all-target/all-feature Clippy, warning-denied rustdoc, the
   complete `axeyum-verify` package, the reflection semantics gate, qfbv profile,
   foundational resources, and docs links pass with one Cargo job inside the
   4 GiB cgroup and test debug info disabled. A capped OOM is a failed gate.
9. Update P5.4, PLAN, STATUS, the research question, ADR index, and this ADR with
   exact counts, artifact sizes/hashes, and measured limits. Commit and push
   without staging unrelated frontier/CAS/corpus/review work.

The accepted claim, if the gates pass, is only: a classified solver nondecision
can be handed to a deterministic, guarded, source-oracle-checked sampled run
without confusing it with proof, solver refutation, error, or coverage. No
bug-discovery-rate, completeness, general-Rust, general-theory, Glaurung finding,
or performance claim follows.

## Rejected alternatives

- **Retry with a larger solver budget.** Rejected: continuation is solver policy,
  not a directed-fuzz handoff, and can hide the original nondecision.
- **Flatten Unknown to a string or unit status.** Rejected: it loses the cause
  accounting required by both Axeyum's mission and the Glaurung review.
- **Treat no sampled violation as proof.** Rejected: finite sampling says nothing
  universal outside the sampled tuples.
- **Convert unsupported/error/replay-failure into fuzzing.** Rejected: malformed
  or operationally failed work must remain visible and separate.
- **Generate arbitrary Rust source from diagnostics/model text.** Rejected: only
  caller-owned closures execute; solver strings are escaped data.
- **Combine T5.4.4 coverage accounting.** Deferred: this cell records sampled
  work but does not define proof-covered versus sampled-space denominators.
- **Wire the current Glaurung unit-Unknown seam.** Deferred until the consumer
  preserves `UnknownReason` and can gate real, source-owned fuzz callbacks.

## Consequences

- Track 5 gains the missing honest branch after proof and replayed refutation.
- Consumers receive deterministic, reviewable work instead of a bare
  nondecision, without gaining permission to call samples a proof.
- The exact reason and dropped sample populations become artifact-owned.
- Glaurung integration has a precise prerequisite: preserve the structured
  cause first, then supply a real source/execution oracle.

## References

- [P5.4 fuzz-oracle loop](../../plan/track-5-verified-systems/P5.4-fuzz-oracle.md).
- [ADR-0339 witness corpus](adr-0339-preregister-deterministic-witness-seed-corpus.md).
- [Glaurung feedback reconciliation](../08-planning/glaurung-feedback-reconciliation-2026-07-20.md).
- [Benchmarking and performance methodology](../08-planning/benchmarking-and-performance-methodology.md).
