# Codex Review - 2026-06-20

Reviewer: Codex

Scope: design, implementation, benchmark artifacts, and targeted validation of
the current local checkout. The worktree already contained non-review edits in
solver/CNF code; this review did not modify those files.

Companion log: [diary.md](diary.md)

## Executive assessment

Axeyum is no longer a small QF_BV prototype. The current workspace is a large
Rust solver/proof research stack: 13 crates, about 151k Rust source lines under
`crates/`, 107 integration test files, and committed benchmark artifacts. The
project has a coherent identity: typed IR, replayable models, explicit resource
budgets, deterministic artifacts, pure Rust by default, and an increasingly
serious proof/evidence route.

The strongest part of the design is the assurance instinct. `sat` answers are
generally replayed against original terms, many `unsat` routes carry explicit
proof/certificate/evidence objects, and benchmark artifacts record enough
context to avoid hand-wavy performance claims. That is exactly the right
direction for "untrusted fast search, trusted small checking."

The uncomfortable part: the project is not close to general Z3 parity, and it
is not yet at Lean-level end-to-end proof parity. Some fragments are
impressively covered, but broad parity would require years of sustained solver
engineering, theory implementation, proof reconstruction, and benchmark-driven
triage. The current benchmark evidence shows soundness discipline, not
competitiveness: on the public p4dfa QF_BV slice, the pure Rust BV path decides
4/113 at 3 seconds with preprocessing and 7/113 at 20 seconds, with no
disagreements or replay failures. That is valuable, but it is far from Z3.

My recommendation is to narrow the public promise and harden the base before
expanding breadth. The next tranche should fix the correctness/assurance issues
below, make the support matrix exact and machine-checked against tests, and
define fragment-specific parity milestones instead of using "Lean / Z3 parity"
as a single undifferentiated target.

## What is already strong

- The workspace shape is sensible. The major boundaries - IR, AIG, BV lowering,
  CNF, query, rewrite, SMT-LIB, solver, benchmark, FP, e-graph, Lean kernel, and
  scenarios - are justified by use rather than gratuitous splitting
  (`Cargo.toml:1-17`).
- The default pure Rust posture is real: `unsafe_code = deny`, Z3 is an optional
  dependency, and native oracles are leaf features (`Cargo.toml:38-46`).
- The SAT-BV backend has the right safety skeleton: unsupported preflight,
  lowering, CNF budgets, optional inprocessing, SAT solve, reconstruction,
  model completion, and original-term replay.
- Benchmark artifacts are useful and honest. They capture corpus, config hash,
  budgets, backend stats, replay failures, disagreements, PAR-2, and per-instance
  outcomes.
- The evidence stack is much better than a status-code wrapper. It includes
  DRAT/LRAT checking, Alethe-like proof checking, Lean-kernel reconstruction
  slices, trust-ledger provenance, Farkas/LRA/LIA certificates, EUF/Ackermann
  certificates, array/datatype certificates, and quantified instantiation
  certificates.
- The test suite is substantial. Targeted validation in this review passed 800
  tests across IR, solver, SMT-LIB, SAT-BV, evidence, CNF, and Lean-kernel crates,
  plus the committed micro benchmark corpus.

## High-priority findings

### 1. `prove_unsat` currently fails open on proof-core resource exhaustion

`SolverConfig::prove_unsat` documents that an `unsat` result is independently
re-derived by the proof-producing SAT core and DRAT-checked before being
returned (`crates/axeyum-solver/src/backend.rs:131-136`). But
`verify_unsat_proof` returns `Ok(())` when the proof core reports
`ResourceOut` or `Interrupted` (`crates/axeyum-solver/src/sat_bv_backend.rs:852-877`).

That means the high-assurance knob can still return an adapter `unsat` without
the promised independent proof check. This is not necessarily a wrong answer,
but it is an assurance-contract violation. In a proof-first solver, this should
be treated as critical.

Recommendation: when `prove_unsat = true`, proof-core `ResourceOut` should
return `Unknown(ResourceLimit)` or a typed "proof unavailable" result, not a
checked `unsat`. If the product wants "best-effort proof", make that a separate
configuration mode with different documentation and evidence.

### 2. `bv2nat` is wrong or panics at and beyond 128 bits

The builder accepts `bv2nat` for any bit-vector width
(`crates/axeyum-ir/src/arena.rs:1207-1215`). The evaluator's fast path casts the
underlying `u128` to `i128` (`crates/axeyum-ir/src/eval.rs:560-565`). For width
128, values with the high bit set become negative, which violates SMT-LIB
`bv2nat` semantics. For width greater than 128, the generic wide-bit-vector path
is entered (`crates/axeyum-ir/src/eval.rs:358-365`), but `apply_wide` has no
`Bv2Nat` case and panics (`crates/axeyum-ir/src/eval.rs:724-802`).

This is a concrete semantic correctness issue. It also undercuts the current
"QF_BV arbitrary width" message.

Recommendation: either represent `Int` values with an arbitrary-precision type
or reject/degrade wide `bv2nat` paths before evaluation. If bounded `i128` Ints
remain a deliberate reference-model limit, then `bv2nat` for values outside
`0..=i128::MAX` must return a typed evaluation error and the solver front doors
must map that to `unknown`, not panic or wrap.

### 3. Ground Int/Real evaluation can still panic on overflow

`Rational` is a normalized `i128` fraction and its arithmetic/comparison methods
panic on overflow by design (`crates/axeyum-ir/src/rational.rs:1-8`,
`crates/axeyum-ir/src/rational.rs:127-205`). Integer evaluation similarly uses
checked operations followed by `expect` for negation, addition, subtraction,
multiplication, division, and abs (`crates/axeyum-ir/src/eval.rs:584-617`).
Real arithmetic delegates to `Rational` operations
(`crates/axeyum-ir/src/eval.rs:622-640`).

The bounded-reference stance is understandable, but a public solver should not
crash on adversarial or merely large SMT-LIB arithmetic. The hard rule says
`unknown` is first-class and not an error; panic paths are inconsistent with
that posture unless every caller proves bounds before evaluation. I did not see
that universal guard.

Recommendation: introduce checked arithmetic APIs in the evaluator and propagate
`EvalError::Overflow`/`UnsupportedExactValue` upward. Map those to `unknown` or
front-door parse/support errors depending on API. Add fuzz/property tests for
large Int/Real constants, `abs(i128::MIN)`, rational cross-multiplication, and
mixed model replay.

### 4. UF model representation is still finite-scalar only

`FuncValue` encodes arguments and results as `u128` scalar codes for Bool,
BitVec, and Float bit patterns (`crates/axeyum-ir/src/value.rs:116-130`).
`Value::scalar_code` panics for wide BV, Array, Int, Real, and Datatype values
(`crates/axeyum-ir/src/value.rs:267-275`), and `Value::from_scalar_code` cannot
decode Int/Real/Array/Datatype results (`crates/axeyum-ir/src/value.rs:242-258`).
The evaluator applies UF models through this scalar code path
(`crates/axeyum-ir/src/eval.rs:228-235`).

The solver compensates by returning `Unknown(Incomplete)` for sat models of
arithmetic-sorted uninterpreted functions
(`crates/axeyum-solver/src/euf.rs:64-79`). That is sound, but it is a direct
parity blocker for QF_UFLIA/QF_UFLRA sat cases and for any richer model story.

Recommendation: replace `Vec<u128> -> u128` function tables with a deterministic
`ValueKey`/`Value` representation that supports Int, Real, Datatype, Array, and
wide BV values. This should be an IR-level design decision with explicit
normalization and ordering rules.

### 5. SMT-LIB `reset` and `reset-assertions` parse as no-ops

The parser accepts `reset` and `reset-assertions` as one-token no-op commands
(`crates/axeyum-smtlib/src/parse.rs:121-134`). They are not represented in
`ScriptCommand`, so `solve_smtlib_incremental` cannot implement their semantics
(`crates/axeyum-solver/src/smtlib.rs:322-357`).

Accepting these commands without effect is worse than rejecting them: it can
silently solve a different incremental problem than the script requested.

Recommendation: add `ScriptCommand::Reset` and `ResetAssertions` with correct
arena/assertion/scope semantics, or reject them explicitly until implemented.
Add regression tests with assertion stacks before and after reset.

### 6. `solve()` is becoming a tactic engine without tactic boundaries

The main solver entry point now performs top-level existential skolemization,
lazy BV dispatch, quantifier-free dispatch, valid-universal elimination,
multiple quantifier/arithmetic paths, finite expansion, e-matching, MBQI-like
fallbacks, and preprocessing (`crates/axeyum-solver/src/auto.rs:61-95`,
`crates/axeyum-solver/src/auto.rs:366-397`). The preprocessing route itself is
multi-step and replay-aware (`crates/axeyum-solver/src/auto.rs:435-507`).

The pieces are individually reasonable, but the front door is now a risk
concentration. It will become hard to explain, test, or certify which tactic was
allowed to prove which result under which assumptions.

Recommendation: turn this into an explicit strategy/tactic pipeline. Each tactic
should declare its fragment predicate, transformation class
(`denotation-preserving`, `equisatisfiable`, `over-approximation`, `proof-only`,
etc.), replay/proof obligation, timeout/resource behavior, and evidence route.
The pipeline should emit per-step metrics into benchmark artifacts.

### 7. Public support wording is ahead of the implementation

The capability ledger is a good anti-drift mechanism, and its golden test passed.
But several messages are broader than the implementation justifies. Examples:
`QF_BV arbitrary width` conflicts with the `bv2nat` and model representation
limits above; arithmetic UF sat projection intentionally degrades to unknown;
SMT-LIB accepts commands it does not semantically implement; string and
optimization support is partial; Lean-kernel docs still describe type checking
as absent even though tests exercise it (`crates/axeyum-lean-kernel/src/lib.rs:1-7`).

Recommendation: maintain a generated support matrix with four columns per
feature: parser accepts, IR/evaluator semantics, solver decision support, and
proof/evidence support. "Accepted but ignored" and "sat unknown, unsat supported"
should be first-class statuses.

## Benchmark and performance assessment

The benchmark harness and artifacts are a strength. The current public QF_BV
numbers are not.

Committed artifacts show:

- Public p4dfa QF_BV, eager `sat-bv`, 3s: 2 sat, 111 unknown, 0 disagreements,
  0 replay failures, PAR-2 about 5.899.
- Public p4dfa QF_BV, `sat-bv --preprocess`, 3s: 4 sat, 109 unknown,
  0 disagreements, 0 replay failures, PAR-2 about 5.837.
- Public p4dfa QF_BV, `sat-bv --preprocess --inprocess`, 3s: 4 sat,
  109 unknown, 0 disagreements, 0 replay failures, PAR-2 about 5.832.
- Public p4dfa QF_BV, `sat-bv --preprocess`, 20s: 7 sat, 106 unknown,
  0 disagreements, 0 replay failures, PAR-2 about 37.885.
- Curated QF_BV, `sat-bv --preprocess`, 2s: 8 sat, 24 unsat, 11 unknown,
  0 disagreements, 0 replay failures.

The 20s layer-attribution artifact says SAT dominates decided-instance time.
That supports the local conclusion that cheap solver-side preprocessing is not
the remaining lever for this slice. The next wins must come from stronger
word-level reduction, more selective lazy/CEGAR strategies, better CNF
inprocessing, or a competitive CDCL core.

I did not rerun the public corpus because `corpus/public` is absent in this
checkout. I did run the committed micro corpus through `axeyum-bench` in debug
mode: 3 files, 2 sat, 1 unsat, 0 unknown, 0 disagreements, 0 replay failures.

Recommendation: keep the artifact format, but add root-cause buckets for every
unknown: unsupported op, node budget, CNF budget, SAT timeout, proof timeout,
model projection gap, arithmetic overflow, tactic incompleteness, etc. Z3 parity
work needs a leaderboard of blockers, not just decided counts.

## Test-suite assessment

The targeted test results were strong:

- `cargo fmt --all --check`: passed.
- `./scripts/check-links.sh`: passed.
- `cargo test -p axeyum-ir --lib`: 9 passed.
- `cargo test -p axeyum-solver --lib`: 331 passed.
- `cargo test -p axeyum-solver --test capabilities`: 2 passed.
- `cargo test -p axeyum-solver --test evidence`: 24 passed.
- `cargo test -p axeyum-solver --test sat_bv`: 22 passed.
- `cargo test -p axeyum-solver --test smtlib`: 44 passed.
- `cargo test -p axeyum-cnf --lib`: 242 passed.
- `cargo test -p axeyum-lean-kernel --lib`: 126 passed.
- `cargo run -p axeyum-bench -- corpus/micro --backend sat-bv --timeout-ms
  1000`: 3 files, all expected outcomes, no replay failures.

This is not the same as `just check`; I avoided a full workspace all-features
run because the host had only about 35 GiB free and prior status notes warn that
full validation can consume tens of GiB. Still, the passed targets cover the
review's major surface areas.

What is missing:

- Regression tests for `bv2nat` width 128 with high-bit-set values and width
  greater than 128.
- Panic-resistance tests for large Int/Real/Rational evaluator cases.
- Incremental SMT-LIB tests for `reset` and `reset-assertions`.
- Repeated-solve tests checking top-level skolem naming does not collide with
  user symbols or previous solver calls. `skolemize_top_existentials` declares
  `!sk_0`, `!sk_1`, ... in the caller arena (`crates/axeyum-solver/src/auto.rs:304-335`).
- Public corpus reproducibility in CI or a documented artifact-refresh job.
- More property/differential tests for mixed-theory model projection, especially
  UF over Int/Real/Datatype/Array values once representation is fixed.

## Recommended change set

### Immediate correctness and assurance fixes

1. Make `prove_unsat` fail closed. If the proof-producing core cannot re-derive
   and check the proof, return `unknown` or a proof-unavailable status.
2. Fix `bv2nat` for width 128 and wide BV. Either add arbitrary-precision Ints
   or reject/degrade out-of-range values explicitly.
3. Convert evaluator arithmetic overflow panics into typed errors. Map those
   errors through solver front doors as `unknown` or unsupported, not process
   crashes.
4. Implement or reject SMT-LIB `reset` and `reset-assertions`.
5. Update stale docs and capability text, especially Lean-kernel docs,
   SMT-LIB support, preprocessing defaults, and arbitrary-width claims.

### Near-term architecture work

1. Replace scalar-only UF model tables with deterministic `ValueKey` function
   interpretations.
2. Split `solve()` into a declarative tactic pipeline with explicit tactic
   contracts and benchmark-visible per-step outcomes.
3. Add a generated support matrix distinguishing parser, IR semantics, solver
   support, model support, and proof support.
4. Add a small adversarial regression corpus for known edge cases: wide values,
   huge rationals, reset semantics, repeated solve freshness, mixed UF models,
   model replay overflow, and proof-core timeout behavior.
5. Preserve the review artifacts and add them to future roadmap triage rather
   than treating them as one-off notes.

### Performance track for credible Z3 progress

1. Continue word-level reductions, but focus on algorithms that explain public
   corpus unknowns: ITE elimination/hoisting, AC normalization and factoring,
   common subterm extraction, solve-eqs beyond the current bounded slice,
   array/BV read-over-write simplification, and bit-vector arithmetic identities.
2. Improve lazy BV/CEGAR only where artifact data shows it avoids large eager
   encodings. It should produce smaller proof/replay obligations, not just more
   modes.
3. If pure Rust Z3-like QF_BV performance is a real goal, plan a serious CDCL
   investment: watched propagation tuned for cache locality, restarts, LBD
   clause deletion, phase saving, vivification, bounded inprocessing, proof
   logging, incremental assumptions, and robust benchmark telemetry. This is a
   multi-month to multi-year effort, not a cleanup task.
4. Keep Z3 as the oracle and differential benchmark, but avoid expanding linked
   solver dependency as product behavior without an ADR.

### Proof track for credible Lean progress

1. Maintain the trust ledger per result and make it visible in benchmark output.
2. Collapse trusted reductions into checked certificates one fragment at a time:
   ROW-distinct, bit-blast lowering beyond the covered gadgets, integer/real
   reductions, datatype reductions, FP-to-BV, and quantifier instantiation.
3. Decide whether the in-tree Lean kernel is the proof target, a checker
   substrate, or a compatibility layer. Each implies different completeness
   obligations.
4. Treat "Lean parity" as "every public valid/unsat route emits a small
   independently checkable certificate accepted by a Lean-grade kernel." Anything
   short of that should be described as partial proof coverage.

## Realistic parity outlook

Z3 parity is not one milestone. Z3 is a mature industrial solver with decades of
engineering across SAT, SMT, arithmetic, arrays, datatypes, strings, FP,
quantifiers, optimization, incremental solving, model construction, tactics, and
proof logging. Axeyum has credible foundations and promising slices, but broad
Z3 parity would require sustained fragment-by-fragment investment.

A realistic ladder:

1. QF_BV scalar/wide core with complete replay, strong word-level reductions,
   competitive SAT/CDCL, and proof-producing bit-blast path.
2. QF_UF and QF_UFBV with complete sat model projection and checked congruence
   certificates.
3. QF_LIA/QF_LRA with complete model/evidence paths and no overflow panics.
4. Arrays and datatypes with complete reduction certificates and model support.
5. Floating point and strings, explicitly scoped and benchmarked.
6. Incremental SMT-LIB, unsat cores, assumptions, get-value/model/proof, and
   reset semantics.
7. Quantifiers and MBQI/ematching as a research program, not a small extension.
8. NRA/CAD/algebraic witnesses, which will require algebraic values in the IR
   and checkable certificates.

Lean parity is orthogonal. It is not about solving more benchmarks; it is about
shrinking trust. Axeyum has the right ingredients, but full proof parity means
every route that returns `unsat` or `valid` has a checkable certificate and every
trusted reduction is either eliminated or explicitly scoped.

The most objective summary: Axeyum is a serious and unusually well-instrumented
research solver. It has a good architecture and a strong assurance direction.
It also has correctness and assurance gaps that should be fixed before widening
the public surface. "Lean / Z3 parity" should be retained as a north star, but
near-term plans should be framed as measurable fragment parity, not global
parity.
