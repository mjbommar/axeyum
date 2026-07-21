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
| `abv.rs` | 10,675 lines / 373,923 bytes | A1--A3 removed the test wall, eager certificate, and lazy-ext orchestrator |
| ABV lazy-ext CEGAR orchestrator | 446 lines / 17,014 bytes | Named child module; ten items; one parent entry point |
| ABV replay/repair residual | 4,531 parent lines (6,137--10,667) | Shared by ROW and extensional replay; 16 private items directly test-reached |
| ABV eager array-elimination certificate | 340 child-module lines | Independent trust/evidence unit; two private parent helper dependencies |
| `int_reconstruct.rs` | 7,683 lines / 316,411 bytes | Shared integer kernel context plus the remaining proof families |
| Integer-inequality reconstruction | 1,201 lines / 55,224 bytes | Private child; three public re-exports; one parent helper seam |
| `nra_real_root.rs` | 7,544 lines / 333,529 bytes | 7,077 production lines; strict, non-strict, and algebraic CAD share correctness-sensitive machinery |
| `reconstruct.rs` | 2,793 lines / 122,834 bytes | R1--R3 target is no longer a top residual |

Raw size is not the only ranking signal. ABV has 28 public or crate-visible
declarations and sibling consumers in auto-dispatch, evidence, reconstruction,
and the online UFBV solver. Integer reconstruction has 17 public or
crate-visible declarations and several dispatcher/interpolation consumers. CAD
deduplication changes code that decides SAT/UNSAT and therefore needs stronger
differential evidence than a module-only move.

The A3 census also corrects the initial “cohesive 4,968-line lane” shorthand.
Thirteen items defined in that historical range were already referenced by
earlier parent code, and 16 residual private items are imported directly by the
existing `abv::tests` child. Moving the entire range as a proper module would
therefore require a wide artificial `pub(super)` surface or a simultaneous
multi-thousand-line test reorganization. The actual CEGAR orchestration has a
much cleaner boundary: ten top-level items, no direct test imports, and only
`check_qf_abv_lazy_ext` called by the parent dispatcher.

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
3. **A3 -- census and extract lazy-ext orchestration (done).** The census
   rejects a monolithic replay/repair move at the current privacy boundary. The
   clean 434-line body now forms the 446-line private `abv/lazy_ext.rs` child.
   Its ten items remain private except for the single parent entry point; public
   APIs, test imports, shared ROW helpers, and replay ownership are unchanged.
   The 42 focused private lazy-ext tests, 10 end-to-end extensionality tests,
   five lazy-ROW controls, differential fuzz, all 891 library tests, strict
   Clippy, and both rustdoc profiles pass under the bounded profile. `abv.rs`
   is now 10,675 lines, down 28.6% from the initial 14,953.
4. **I1 -- extract integer-inequality reconstruction (done).** The 1,196-line
   body now forms the private 1,201-line `int_reconstruct/inequality.rs` child.
   All three public functions are re-exported at their exact historical paths;
   the only parent-facing internal seam is `lt_lit_lit`, used by six earlier
   proof sites. Fifteen explicit parent dependencies remain imports, not wider
   visibility. A representative generated Lean module keeps exact SHA-256
   `27edf9b04f41ce7ca537798fd17f486bb43336dfdaf06e3ad9f15f95c93205de` before
   and after. All 14 interval tests (including three real-Lean executions), 12
   UFLIA interpolant tests, 10 namespace controls, all 891 library tests, strict
   Clippy, and both rustdoc profiles pass. The parent is now 7,683 lines, down
   13.4% from 8,876.
5. **N1 -- census, then parameterize CAD only under a semantic gate (next).** Strict/non-strict/
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
