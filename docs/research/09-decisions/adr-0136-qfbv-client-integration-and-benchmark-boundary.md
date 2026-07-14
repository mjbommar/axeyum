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
