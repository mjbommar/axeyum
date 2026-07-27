# Batched value propagation on the QF_BVFP hard tail — 2026-07-27

## Bounded verdict

`propagate_values` now applies independent top-level constant definitions in one
shared DAG rebuild per fixpoint round.  It preserves the existing first-definition
order, leaves later conflicting definitions in the assertion set, records every
elimination in the model-reconstruction trail, and still iterates when one round
exposes a dependent fact.

On the exact public QF_BVFP ESBMC conversion row
`Double-to-float-no-simp1-main.smt2`, the isolated propagation pass fell from
4.02 s to 50.38 ms on this host (about 80x).  A five-run clean release replay
returned `unsat` every time in 0.20--0.35 s (median 0.33 s), versus the retained
2.25 s pre-change observation.  The clean corpus harness measured the same row
at 202.573 ms; Z3 4.13.3 returned the same `unsat` verdict.

This is a preprocessing performance result, not a new FP semantic operator or a
credited full-library run.  The complete selected QF_FP/QF_BVFP/QF_ABVFP slices
remain open under the resumable-run work stream.

## Why this row selected the change

The stale diagnostic run contained 54 wrong-answer markers.  Current code
re-adjudicated the 51 distinct non-query FP rows as follows:

- all 13 division, 17 FMA, and 20 multiplication rows now return their declared
  verdict in 0.1--0.2 s in a debug build;
- the remaining conversion row returns the declared `unsat` in release mode;
- the two duplicate `query.26.smt2` markers are already covered by the retained
  signed-zero repair, and `pipeline-invalid.smt2` by the AUFLIA sound-decline.

A preregistered diagnostic census then selected, for every one of the 14
Wintersteiger QF_FP operator directories, the five lowest SHA-256-ranked
relative paths from each of the `has-solution` and `has-no-other-solution`
classes.  At a 2 s solver budget and 3 s process ceiling, all 140 rows returned
their declared result: 140 correct, zero wrong, zero unknown, and zero timeout.
That ruled out a missing primitive and redirected the increment to the measured
conversion hard-tail cost.

The exact conversion input has 197 assertions and 81,417 parsed arena nodes.
Before this change, `propagate_values` selected one symbol, rebuilt all remaining
roots, and repeated.  The definition-heavy formula therefore paid for the same
large shared DAG once per independent symbol.  Batching preserves the logical
fixpoint but pays for one shared traversal per dependency layer.

## Immutable implementation and evidence

- implementation commit:
  `6b5b42acc87ab9f741719b68f04f31b470e61209`;
- clean release `smtcomp_cli` SHA-256:
  `18139d52d444d35958977fa66b774fb1b6590dd5518c58940153105cf32760f6`;
- exact benchmark SHA-256:
  `adae1f93ab0fc985139aea3927f2c9c92ffc289fc5ffae9988b94af75fd7255d`;
- local diagnostic artifact:
  `/tmp/axeyum-qfbvfp-esbmc-batched-propagate-clean-20260727.json`, SHA-256
  `ba916f78d12a4ec2a48e327f3d5175176c301531bfb98fd1010eebdc86ca1d44`
  (not committed and therefore not durable evidence by itself).

The 34-file public `QF_BVFP/ramalho/esbmc` population at a 5 s solver budget and
four jobs produced 30 `unsat`, four `unknown:Timeout`, zero wrong verdicts, zero
errors, and zero model-replay failures (88.24% decided; PAR-2 mean 1.348 s).  Z3
returned the declared `unsat` result on all 34 files; 30 rows were jointly
decided with zero disagreement, and the other four were Z3-only decisions.

The four current residuals, all declared/Z3 `unsat`, are:

- `Float4-main.smt2`;
- `Float4_1-main.smt2`;
- `Float-no-simp2-main.smt2`;
- `Float-no-simp2_1-main.smt2`.

They are the next preregistered P2.8/P1.2 hard-tail cluster.  The observed
7.7--9.3 s wall times also show that the cooperative five-second deadline does
not cover all preprocessing/construction work; those overruns are classified as
timeouts, not decisions.

## Verification

The implementation is covered by a 64-definition regression that requires
linear-size arena growth, checks the reduced assertion directly, reconstructs
all eliminated symbols, and replays every original assertion.  Existing chain,
duplicate-conflict, Boolean, finite-domain Float/RoundingMode, and randomized
reconstruction tests remain green.

Focused gates on the implementation commit:

- `cargo test -p axeyum-rewrite --all-features`: 114 library tests plus two
  datatype integration tests passed;
- `cargo test -p axeyum-solver --all-features --test fp_preprocess`: 1 passed;
- `cargo test -p axeyum-solver --all-features --test fp_ground_division`: 3
  passed, including the Z3 differential;
- warning-denied all-target/all-feature Clippy for `axeyum-rewrite` and
  `axeyum-solver`, `cargo fmt --all --check`, and `git diff --check`: passed.

No full `just check`, remote CI, push, origin/main integration, proof-producing
UNSAT, or credited full-library completion is claimed.
