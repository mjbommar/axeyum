# Artifact-readiness refactor inventory

Status: active
Date: 2026-07-21
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
| `int_reconstruct.rs` | 3,489 lines / 141,804 bytes | Shared integer kernel context plus deliberately coupled closed-universal/nested-XOR reconstruction |
| Integer-inequality reconstruction | 1,201 lines / 55,224 bytes | Private child; three public re-exports; one parent helper seam |
| Quantified counterexample-cover reconstruction | 1,465 lines / 58,079 bytes | Private child; one crate router and one public re-export |
| Single-pivot equality-partition reconstruction | 1,200 lines / 50,231 bytes | Private child; one crate router and one public re-export |
| Euclidean-residue reconstruction | 354 lines / 13,361 bytes | Private child; one crate router, one public re-export, one private parent helper |
| Affine-growth reconstruction | 467 lines / 17,354 bytes | Private child; one crate router, one public re-export, one private parent helper |
| Diophantine reconstruction | 767 lines / 37,425 bytes | Private child with two unchanged public re-exports, four family-only support items, and eight family-specific context methods; 17 shared kernel methods remain parent-owned |
| `nra_real_root.rs` | 7,503 lines / 329,731 bytes; 6,944 production lines | N1a--N1c share rational mechanics behind explicit policy; algebraic lifting remains distinct |
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
5. **N1 -- parameterize CAD only under the frozen semantic gate (done).** The
   [census and preregistered gate](cad-parameterization-gate.md) rejects a single
   strict/non-strict/algebraic engine: the algebraic traversal has a different
   value domain, boundary derivation, and preparation path. N1a is authorized
   narrowly: share the duplicated rational substitution/univariate cell
   decision behind the existing strict and non-strict wrappers. Projection,
   sampling, budgets, timeout polls, algebraic fallback, and public paths remain
   unchanged. That helper is now landed behind both named wrappers, with exact
   models pinned at `(1,1)` and `(1,0)` and the 2,000-seed Z3 differential gate
   at `DISAGREEMENTS: 0`. N1b now shares only two-variable projection/root
   preparation; exact roots `[0,1]` and a poll-removal mutation control pin its
   semantics. N1c then proves the two rational N-variable visitors identical
   except for explicit `OpenOnly`/`OpenAndRationalSections` selection. Zero-cell
   and ordering mutations are detected; the exact 2,000-seed tally remains
   unchanged; all 895 library tests pass. Production falls 7,077→6,944 lines
   across N1. The whole file is 7,503 lines because the new semantic controls
   add test code, still 41 lines below baseline. N1 is closed; algebraic
   traversal remains separate.
6. **I2 -- extract quantified counterexample-cover reconstruction (done).** The
   ADR-0108 family is one contiguous 1,449-line / 57,436-byte block with 28
   top-level items. Twenty-six are private implementation details; the only
   outward seams are the crate-visible router predicate and the existing public
   reconstruction entry point. Its source-bound checking, Boolean case tree,
   integer normalization, and compact Lean rendering form one proof family, and
   the existing 247-line integration suite exercises certificate checking,
   reconstruction, mutation rejection, evidence routing, and real-corpus use.
   Move the block to a private `int_reconstruct/counterexample_cover.rs` child,
   re-export the two historical paths, and import the parent integer-kernel
   context/helpers explicitly. Do not change proof search, source flattening,
   witness/case order, caps, generated Lean bytes, or public visibility. This
   reduces the 7,683-line parent to 6,233 lines without creating a new API. The
   child is 1,465 lines / 58,079 bytes with explicit imports. A committed
   7,197-byte/FNV-1a `e592f1787653a4bf` generated-module control proves exact
   Lean-byte preservation. All seven ordinary integration controls plus the
   explicitly exercised real-corpus Lean reconstruction, all 895 library tests,
   strict Clippy, and both rustdoc profiles pass under the bounded profile.
7. **I3 -- extract single-pivot equality-partition reconstruction (done).** The
   ADR-0101/0106 family is one contiguous 1,188-line / 49,816-byte block with 30
   top-level items. Twenty-eight are private lowering, finite-partition, proof,
   and kernel-rendering details; only the crate-visible shape router and the
   historical public reconstruction entry point leave the family. Move it to a
   private `int_reconstruct/equality_partition.rs` child with explicit imports
   and unchanged re-exports. Preserve lowering, representative order, exact
   assignments, proof construction, caps, public visibility, and generated Lean
   bytes. The focused gate is the six-test reconstruction suite plus the
   six-test evidence suite, including the 64-seed Z3 differential sweep. Add a
   pre/post byte-identity control to the existing SDLX reconstruction before the
   move. The private child is 1,200 lines / 50,231 bytes with explicit imports,
   and the parent falls exactly 6,233→5,045 lines without an API or semantic
   change. The committed SDLX control preserves the pre-move 30,644-byte Lean
   module at FNV-1a `84fe8e457b9b6b27`. All twelve focused tests pass, including
   mutation/near-miss gates and the complete 64-seed Z3 differential sweep; all
   895 library tests, strict Clippy, and both rustdoc profiles also pass.
8. **I4 -- extract Euclidean-residue reconstruction (done).** The ADR-0095/0104
   family is one contiguous 344-line / 13,041-byte block with four top-level
   items: the router, public reconstructor, decline helper, and exact canonical
   source matcher. Move it to private `int_reconstruct/euclidean_residue.rs`
   with explicit imports and unchanged re-exports. Preserve the exact clock
   matcher, branch/proof order, literal cap, public visibility, and generated
   Lean bytes. Add pre/post identity for the committed `clock-3` module. The
   focused gate is all three reconstruction/routing controls plus all three
   evidence/tamper/near-miss controls. Affine growth remains a distinct later
   family; do not combine the two merely because both use the general Euclidean
   theorem. The resulting private child is 354 lines / 13,361 bytes with
   explicit imports; the exact matcher reuses only the existing private parent
   `peel_closed_foralls` helper. The parent falls exactly 5,045→4,701 lines.
   The committed `clock-3` control preserves the pre-move 16,025-byte Lean
   module at FNV-1a `4e97fa307a29d1d0`. All six focused controls, all 895
   library tests, strict Clippy, and both rustdoc profiles pass.
9. **I5 -- extract affine-growth reconstruction (done).** The ADR-0097/0105
   family is one contiguous 456-line / 16,998-byte block with seven top-level
   items. Its only outward paths are the crate-visible router and historical
   public reconstructor; the private body owns its proposition bundle,
   parameter lowering, proof construction, decline route, and universal
   instantiation. Move it to private `int_reconstruct/affine_growth.rs` with
   explicit imports and unchanged re-exports. Preserve certificate matching,
   binder/parameter order, exact branch proof, cap, public visibility, and
   generated Lean bytes. Add pre/post identity for `repair-const-nterm`. The
   focused gate is all four reconstruction/routing controls and all five
   evidence/termination/differential controls, including the 64-seed Z3 sweep.
   The resulting private child is 467 lines / 17,354 bytes with explicit
   imports and only the existing private `peel_closed_foralls` parent helper.
   The parent falls 4,701→4,246 lines. `repair-const-nterm` remains exactly
   43,108 generated Lean bytes at FNV-1a `dd4d24cdf0168fb9`. All nine focused
   controls, all 895 library tests, strict Clippy, and both rustdoc profiles
   pass.
10. **I6 -- extract Diophantine reconstruction (done; dependency census
   corrected before acceptance).** The original ADR-0042 integer-infeasibility
   family has two historical public entries, four
   family-only support items, and eight context methods used only by this
   family. It is distinct from the shared
   integer normalizer/context and from closed-universal/nested-XOR proof
   construction. Move only that body to private
   `int_reconstruct/diophantine.rs`, re-export both public paths unchanged, and
   keep all 17 context methods with existing parent or sibling-family consumers
   in the parent. The initial census counted only earlier same-file consumers;
   the first compile gate found four sibling-module consumers and four
   transitive helper dependencies before acceptance. The corrected shared seam
   is 383 lines / 17,165 bytes. Do not widen or move it for cosmetic
   completeness. Preserve certificate selection, equality/variable
   order, proof-size caps, kernel gating, rendered Lean bytes, and all evidence
   behavior. The resulting private child is 767 lines / 37,425 bytes, and the
   parent falls 4,246→3,489 lines / 141,804 bytes (60.7% below its original
   8,876 lines). The canonical `two_x_eq_one` module remains exactly 868,243
   bytes at FNV-1a `d2f76675b12631ea`. All five reconstruction controls
   (including real Lean), all four evidence controls, all 19 math-resource LIA
   routes, all ten namespace controls, all 895 library tests, strict Clippy,
   and both rustdoc profiles pass.

## Post-I5 census and residual posture

1. I6 is complete and closes the integer structural lane. Its dependency
   correction retained all shared helpers before acceptance; no generic size
   sweep follows.
2. Keep closed-universal and nested-XOR reconstruction in the parent. Their two
   entry points share a large kernel-helper region, and a combined move would
   hide two distinct proof families behind one cosmetic module.
3. Keep the 4,531-line ABV replay/repair residual in place. Sixteen private
   items are directly test-reached and the block shares ROW/extensional replay
   ownership; moving it now would widen visibility or combine a test
   reorganization with production ownership changes.
4. Stop CAD cleanup at N1. Rational strict/non-strict mechanics are shared;
   algebraic lifting has a different value domain and needs new semantic
   evidence before any common traversal is authorized.
5. Do not turn the repository's next-largest-file list into an automatic
   refactor queue. Remeasure reviewer navigation and dependency seams before
   adding `incremental.rs`, `qinst_egraph.rs`, or `auto.rs` to this inventory;
   raw line count alone is not the acceptance criterion.
6. The remaining parent is the shared integer kernel context plus the deliberately coupled
   closed-universal/nested-XOR region; further movement would widen shared
   privacy or separate helpers from all of their consumers.

## Standing gate

Every structural slice must preserve public paths, visibility, default features,
generated proof bytes where applicable, solver verdicts, and replay/checker
behavior. Run the complete all-feature solver library, relevant focused
integration tests, strict all-target Clippy, full/minimal warning-denied rustdoc,
format/link checks, and the bounded OOM audit before acceptance. Keep each slice
in its own add/commit/push checkpoint.
