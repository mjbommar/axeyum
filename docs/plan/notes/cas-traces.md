# LIB-5 CAS trace implementation evidence

Worktree `/home/mjbommar/projects/personal/axeyum-cas-traces`, branch
`feat/cas-rewrite-traces-20261010`, base `af552455a` (includes the exact-input
normalizer repair). ADR-2500 defines the polynomial equality trace contract.

## First useful path and rule census

| Rule | Producer | Certificate/replay | Assumptions | Kernel admission |
|---|---|---|---|---|
| polynomial.add.v1 | deterministic postorder normalizer | local MultiPoly normal form + exact context replacement | none | pending T3 |
| polynomial.mul.v1 | same | same | none | pending T3 |
| polynomial.neg.v1 | same | same | none | pending T3 |
| polynomial.pow.v1 | same; carries exact exponent | same; requires matching exponent | none | pending T3 |

The pinned multi-step example is `(x+1+2)*(-(-(x+1)))`; child arithmetic,
negation and final product are separate steps. The unsupported conditional
example is `(x*x)/x`; no unchecked cancellation or domain tag is admitted.
`normalize` remains the ordinary fast path; tracing is opt-in. Replay shares
exact polynomial arithmetic, not the producer or heuristic `equal` search.
A checked trace establishes equality and is not a kernel admission receipt.

## Fresh validation

Latest integration run 19990 passed 5/5 tests after allocation/byte-bound
hardening: multi-step deterministic JSON/replay and discriminating rational
evaluation; endpoint change; eleven step/witness/context/path corruptions;
external source binding/empty traces; unsupported versus resource exhaustion.
The two example test harnesses ran zero tests: they establish compilation only
and receive no behavioral-test credit.

Separate-process export/replay runner 56439 is live: builds the two examples,
exports a trace plus separate expected statement, requires a genuine checked
trace, and requires five tampered artifacts/source bindings to exit nonzero.
Focused clippy runner 27791 is live; no complete-workspace lint claim is made.
Build/test target `/home/mjbommar/projects/personal/axeyum/target/cas-traces`.

## Remaining scope

Mutation sensitivity; complete gates; Python trace export/replay/failing step;
guarded fraction cancellation with nonzero certificates; arbitrary-precision
trace coefficients; trace cost/size comparison; kernel reconstruction and
axiom-footprint measurement. No inventory/theorem count is advanced by adding
logs. All T0–T3 and LIB-6 requested final features remain part of the goal.

## External replay, lint and mutation terminal results

Runner 56439 exited 0. Fresh examples exported 4 steps under
`/var/tmp/axeyum-cas-trace-replay-jyi3nor7`; standalone checker accepted that
trace against a separate statement and rejected deleted step, changed context,
missing witness, unknown rule and changed external source (all exit 1).
Initial focused clippy 27791 failed items_after_statements; moved the nested
location walker before statements, then 25978 passed with -D warnings.
No full-workspace lint claim is made.

Mutation 41526 is terminal: private snapshot
`/data0/axeyum/scratch/snap-cas-traces-6fa838357`, baseline 5/5, context guard
deleted mutant 4 pass/1 fail, exit 101. Sole failure:
corrupt_steps_witnesses_and_contexts_are_rejected (changed context accepted).
Do not repeat the mutation in the active tree.

Python binding implementation provides normalize_trace and replay_trace with
TraceOutcome status/detail/failing_step and completed evidence only on success.
RewriteTrace exports JSON and typed source/result, with explicit source-bound
replay. Six Python tests exercise genuine and corrupted exports plus distinct
unsupported/resource outcomes. Fresh extension build 77251 is live; no Python
behavior credit before loading the new library in an isolated package.
Generated stubs, Python tests and broad gates still need completion.

## First Python build and classification hardening

Initial extension build 77251 ended exit 0. Isolated package
`/var/tmp/axeyum-cas-trace-python-cyjywwqd/axeyum` loaded its new library; SHA-256
`aa06c130ea3f78df795ff0fceca26da3d40a6ad38a094528827d4c9499ac2435`.
Import inspection confirmed that exact path. Run 94254 ended exit 0: 6/6 Python
tests passed; the rational demo exported 4 steps for `(x+1/2+1/3)*(-(-(x+1/7)))`
and rejected corrupted context at step 0. This first build precedes the final
coefficient-error classification edit, so a final-source rebuild remains needed.

Rust run 10021 ended exit 0: 6/6 tests passed, adding malformed-coefficient
rejection versus valid wide-coefficient ResourceLimit. Rust example/test input
was then aligned structurally with Python's binary Add/Neg constructors so
byte-identical cross-language traces can be required. Added an explicit zero
denominator unsupported control; neither it nor the aligned input has current
terminal test credit yet.

Stub generation 90112 is live. Final rebuild runner 99447 is live, queued
behind it: fresh Python extension, latest 6-test Rust suite, fresh export/replay
examples. It must complete before final-source Python/byte-equivalence credit.
Rust registry check passed without raising its certified-function floor (151);
new trace logging does not advance kernel/library inventory. Plan/ADR checks and
links passed earlier; final dirty-state checks remain necessary.

## Final-source export and current test evidence

Runner 99447 ended exit 0: rebuilt extension, six Rust tests and both examples.
Runner 99557 ended exit 0 against isolated package
`/var/tmp/axeyum-cas-trace-final-gz4a9wk8`; extension SHA-256
`bbae52336423d12295d0a30de00bca6411f5647cf05df8e2305ef16be834628a`.
Six Python tests passed. The structurally identical Rust/Python expressions
produced byte-identical four-step traces. The separate Rust checker accepted
both the Rust export and the rational Python export against their statements.
Stub generator 90112 ended exit 0 with 27 modules and 649 items; the CAS stub
includes both functions and trace/outcome classes.

Focused clippy 61496 passed after extracting coefficient decoding; that run
also passed six Rust trace tests. A subsequent test run passed seven tests,
adding independently evaluated powers, empty operators and changed-exponent
rejection. A malformed-local-witness test and step-attribution fix are pending
terminal verification. The final Python binary predates these private helper
and diagnostic changes; no fresh Python credit is claimed for those changes.
Broad gates, guarded cancellation, wide coefficients, cost comparison and
kernel admission remain pending. Earlier live-job entries above are historical;
the terminal records supersede them.

Step-attribution run 89405 ended exit 0: 8/8 Rust tests passed, including
malformed local witness reporting step 0. Focused clippy 58829 ended exit 0
with -D warnings. This is targeted validation, not a full CAS/workspace gate.

## Fresh diagnostic binding verification

Build 12261 ended exit 0 (`cargo build -p axeyum-py`, development cdylib;
no wheel packaging claim). Isolated package
`/var/tmp/axeyum-trace-step-diagnostic-ox5pbv08` loaded extension SHA-256
`389587d7d8f3be35b8c530f8c1ee6ed29c6090d5bd1170efe9948ddd5d5683f7`.
Python run 93494 ended exit 0: seven collected and seven passed, including
malformed witness attribution through the Python result's failing_step field.

A follow-up fresh-source proof smoke test used this isolated package and
explicit produce-proofs/get-proof commands. Positive control: contradictory
`(= (bvand a b) a)` / its negation on one-bit variables solved UNSAT and
returned 3141 proof bytes. The audit's Boolean, Boolean+LIA and negative-real
product examples all solved UNSAT and returned no proof. Source inspection
confirms the helper invokes emitters directly; the BV emitter only classifies
BV predicates, so Boolean-only input is excluded there. These are diagnostic
results, not external proof checking or repaired EVD-6 coverage. The successful
control supports proceeding to emitter/normalization investigation.
