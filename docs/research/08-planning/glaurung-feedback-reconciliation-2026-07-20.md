# Glaurung feedback reconciliation

- Status: active guardrail
- Feedback snapshot: 2026-07-16
- Reconciled: 2026-07-20
- Rechecked: 2026-07-21 against the user-provided copy and the current
  Glaurung reviewer checklist; no disposition changed

## Purpose

This note reconciles the ten-item Glaurung consumer feedback snapshot with the
evidence landed after it. It is a claim-control document: it distinguishes
requirements that remain binding from historical measurements that later fair
controls superseded. It does not reopen concretization coverage, symbolic
memory, or a solver-performance leadership thesis.

The publication spine is **correctness + deployability + a rigorously
characterized performance regime**. Concretization remains a configurable
policy and reproducibility mechanism; its completed sweep found no validated
coverage difference. Warm reuse remains useful engineering, but the neutral
six-cell result makes it a workload-dependent mechanism rather than the paper's
lead claim.

## Item-by-item disposition

| # | Original feedback | Current disposition and controlling evidence | Remaining action |
|---:|---|---|---|
| 1 | Strict sort checking exposed real Glaurung defects. | **Retained; promoted to the lead methods result.** Strict width/sort construction, fail-closed result typing, and ordered model replay exposed distinct defect classes. The four-oracle valid-formula campaign then supplied systematic bounded evidence rather than anecdotes ([ADR-0224](../09-decisions/adr-0224-standing-qfbv-multi-oracle-fuzz.md), [ADR-0225](../09-decisions/adr-0225-exhaustive-neutral-qfbv-fuzz-coverage.md), [ADR-0237](../09-decisions/adr-0237-independent-edge-qfbv-four-oracle-fuzz.md)). | Preserve explicit coercion only, named invalid-consumer regressions, exact diagnostics, and original-term replay. Describe the bounded generator populations exactly; do not claim QF_BV completeness. |
| 2 | Warm Axeyum was reported 2.8--4x faster than Z3. | **Superseded as a headline.** That measurement established that reuse exists, but did not provide a topology-equivalent neutral baseline. [ADR-0272](../09-decisions/adr-0272-preregister-six-cell-neutral-warm-regime.md) is controlling: across four fixed-work drivers Axeyum beats warm Z3 on three and loses on Dptf, while warm Bitwuzla wins all four. | Keep warm reuse as workload-dependent integration evidence. Report every cell and driver; make no general speed-lead claim. |
| 3 | Cold one-shot was slower, with about 84% in bit blast plus CNF. | **Retained as revision- and corpus-bounded attribution.** It selects term-to-AIG-to-CNF reduction as the cold optimization lane, not SAT tuning. Several later leaf/layout candidates failed their preregistered gates, so the percentage is a direction, not permission to keep guessing implementations. | Reopen cold optimization only from a fresh diagnostic that names a fixed structural delta, then require repeated end-to-end fixed-work evidence. |
| 4 | `assert_configured` is warm-only and loses cold. | **Closed as an API and roadmap guardrail.** Scalar, preprocessed-batch, and configured-batch documentation now all say this explicitly; raw assertion remains the cold control. | Preserve the documentation and cold control. Any automatic selection needs a new workload gate and cost model. |
| 5 | Precise `IrError` messages are load-bearing. | **Retained and regression-owned.** Consumer-discovered width/range failures stay distinct from valid-formula fuzz, and [ADR-0207](../09-decisions/adr-0207-glaurung-declared-concat-width-soundness.md) records why silent Z3 acceptance was not semantic agreement. | Keep operation, actual and required sorts/widths, and invalid ranges in errors. Never convert malformed input or adapter failure into UNSAT/Unknown. |
| 6 | Empty-theory projection made model lift dramatically cheaper. | **Accepted and guarded by [ADR-0195](../09-decisions/adr-0195-skip-empty-warm-theory-model-projection.md).** The scalar fast path still constructs a complete deterministic model, validates assignment reconstruction, and replays original assertions. Warm array/UF work takes the unchanged projection route. | Every new projection class must enter the emptiness predicate in the same change. Never trade completeness or replay for the historical speedup. |
| 7 | One shared bounded replay memo removed most repeated replay work. | **Accepted and guarded by [ADR-0193](../09-decisions/adr-0193-bounded-shared-memo-model-replay.md).** The gain depends on sharing within a bounded session while retaining original-root evaluation. | Preserve deterministic clearing and bounded storage. Audit new embedders for per-root evaluator recreation without introducing unchecked verdict reuse. |
| 8 | Large real-driver runs showed robustness and structural Unknown. | **Retained only as population-bounded evidence.** The exact accepted artifacts support zero crashes, hangs, decided disagreements, or replay failures on their named rows. Later tcpip work contains sound resource-limit nondecisions, so the stronger “all queries decide within 250 ms” phrasing is withdrawn. | Report attempted, decided, Unknown-by-cause, error, replay, fallback, and dropped-work counts for every population. Do not turn a sound nondecision into success or failure. |
| 9 | Self-rechecked DRAT is a differentiator. | **Demonstrated, with scope.** Generated and real-query proof denominators are measured in [ADR-0226](../09-decisions/adr-0226-generated-qfbv-proof-coverage-denominator.md) and [ADR-0231](../09-decisions/adr-0231-deadline-aware-qfbv-proof-coverage.md); [ADR-0278](../09-decisions/adr-0278-preregister-glaurung-infeasible-path-certificate.md) demonstrates downstream source rebinding and external consumption. The reviewer cell's proof is intentionally trivial. | Keep `UnsatProof::recheck()` prominent. Proof prevalence, nontrivial traces, cost, and whole-CFG composition remain open unless a separately preregistered real workload justifies them. |
| 10 | Pure Rust/no-C, WASM, a minimal profile, and honest dropped-work accounting are deployability strengths. | **Measured and retained with precise scope.** [ADR-0227](../09-decisions/adr-0227-executable-qfbv-webassembly-deployability.md) supplies executable Node/Chromium evidence; the real Glaurung `qfbv` consumer compiles without native solver features; [ADR-0304](../09-decisions/adr-0304-correct-canonical-cache-identity-and-rerun.md) characterizes the accepted memory trade. The benchmark methodology makes operational errors and dropped work visible rather than rewarding fast failure. | Preserve the no-native default and minimal consumer gate. Report latency/RSS, feature identity, exact work, fallbacks, Unknown, errors, model replay, and proof recheck separately. Do not equate a feature profile with the smallest possible parser or artifact footprint. |

## Consequences for the active plan

1. Correctness-oracle evidence leads the paper. Strict consumer-boundary
   failures and well-typed multi-oracle fuzzing are complementary methods, not
   substitutes.
2. Performance is a regime map. Cold, warm, fresh-context, retained-context,
   Z3, Bitwuzla, and cvc5 numbers keep their actual topologies and cannot be
   blended into one multiplier.
3. Concretization policy work remains closed after the behavior-preserving
   extraction and measured sweep. Symbolic memory is conditional on a future
   independently demonstrated coverage gap, not an automatic next project.
4. The active artifact-readiness work may reorganize code and configuration,
   but it must preserve the strict errors, replay, proof, and measurement
   contracts above. The next implementation step therefore remains the A3 ABV
   lazy-ext seam census, not a new performance or concretization experiment.
