# Artifact-readiness refactor inventory

Status: active
Date: 2026-07-20
Baseline: Axeyum `06ed4b78`

## Purpose

Rank the remaining code-organization and duplication work after R1--R4 and
ADR-0314, using measured reviewer-facing cost rather than the original rough
line-count report. This is the execution inventory for PLAN item 10; it does not
authorize solver-policy, proof-rule, or semantics changes.

The completed work materially changes the starting point:

- `reconstruct.rs` is 2,793 lines, down from 18,517, with its proof families in
  named child modules;
- the documented root API is organized into measured semantic facades and R4 is
  closed; and
- the one explicit `SolverConfig` illegal state is now a typed choice.

The remaining work should therefore target the walls a reviewer still opens,
not repeat completed namespace/configuration sweeps.

## Measured residuals

| Surface | Current measurement | Relevant structure |
|---|---:|---|
| `abv.rs` | 14,953 lines / 547,072 bytes | 11,439 lines before the test module; 3,514-line inline test module |
| ABV lazy-ext replay/repair lane | 4,968 lines (6,138--11,105) | Cohesive but coupled to the preceding ROW/projection state |
| ABV eager array-elimination certificate | 334 lines (11,106--11,439) | Independent trust/evidence unit; two narrow parent helper dependencies |
| `int_reconstruct.rs` | 8,876 lines / 371,286 bytes | Shared integer kernel context plus several proof families |
| Integer-inequality tail | 1,196 lines (7,681--8,876) | Cohesive reconstruction family after the shared context |
| `nra_real_root.rs` | 7,544 lines / 333,529 bytes | 7,077 production lines; strict, non-strict, and algebraic CAD share correctness-sensitive machinery |
| `reconstruct.rs` | 2,793 lines / 122,834 bytes | R1--R3 target is no longer a top residual |

Raw size is not the only ranking signal. ABV has 28 public or crate-visible
declarations and sibling consumers in auto-dispatch, evidence, reconstruction,
and the online UFBV solver. Integer reconstruction has 17 public or
crate-visible declarations and several dispatcher/interpolation consumers. CAD
deduplication changes code that decides SAT/UNSAT and therefore needs stronger
differential evidence than a module-only move.

## Ranked next slices

1. **A1 -- extract the ABV tests (done).** The exact 3,514-line inline module is
   now a 3,510-line `abv/tests.rs` child plus the four-line parent module seam.
   Six `include_str!` paths gained one relative parent component; test bodies,
   names, privacy, and production code are unchanged. `abv.rs` falls from
   14,953 to 11,443 lines (23.5%), and all 891 library tests retain their
   `abv::tests::*` identities. Strict Clippy and both strict rustdoc profiles
   pass under the bounded profile.
2. **A2 -- extract the eager array-elimination certificate (done).** The exact
   333-line certificate/rechecker body now lives behind a seven-line module
   prelude in the 340-line `abv/array_elim_certificate.rs`. Its module remains
   private; `ArrayElimUnsatCertificate` and `certify_array_elim_unsat` are
   re-exported at their unchanged `abv` and crate-root paths. Child privacy uses
   `select_congruence_lemma` and elimination error mapping as the only parent
   helpers without widening either visibility. All seven dedicated certificate
   mutation/recheck tests, seven Ackermann controls, end-to-end Lean
   reconstruction, namespace compatibility, all 891 library tests, strict
   Clippy, and both strict rustdoc profiles pass. `abv.rs` is now 11,112 lines,
   down 25.7% across A1--A2.
3. **A3 -- census then extract lazy-ext replay/repair (next).** The 4,968-line lane is
   the largest cohesive production family, but it shares ROW context and model
   projection helpers. Record the exact seam before moving it; do not respond to
   size by making dozens of helpers broadly visible.
4. **I1 -- extract integer-inequality reconstruction.** The 1,196-line tail is
   the clearest `int_reconstruct.rs` family, but it depends on the shared kernel
   context. Take it after the ABV opening slices establish the module-move gate.
5. **N1 -- parameterize CAD only under a semantic gate.** Strict/non-strict/
   algebraic repetition remains a valid duplication target, but any shared
   engine must preserve boundary sampling, algebraic decline, exact replay, and
   timeout behavior under focused oracle/differential tests. It is not the next
   behavior-neutral artifact cleanup.

## Standing gate

Every structural slice must preserve public paths, visibility, default features,
generated proof bytes where applicable, solver verdicts, and replay/checker
behavior. Run the complete 891-test all-feature solver library, relevant focused
integration tests, strict all-target Clippy, full/minimal warning-denied rustdoc,
format/link checks, and the bounded OOM audit before acceptance. Keep each slice
in its own add/commit/push checkpoint.
