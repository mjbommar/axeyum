# Quantified-UFLIA evaluated-scalar measurement

Status: implemented; acceptance pending branch-gate blockers
Date: 2026-07-23
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Population

The frozen population is the eleven ordinary Z3-SAT Unknowns remaining after
ADR-0360 on the 256-case quantified-UFLIA differential:

```text
23, 30, 32, 70, 111, 122, 150, 175, 182, 231, 242
```

No new generator, oracle, or timeout regime is introduced.

## Measured policy

Starting from the initial quantifier-free ground candidate, the diagnostic
builds a deterministic integer pool from:

- zero and all scalar `Int` assignments;
- every `Int` UF default and overriding result; and
- every exact-source `Int` subterm that ground-evaluates under that candidate.

It then applies checked `-1`/`+1` closure once and declines unless the complete
pool has at most 16 values and the complete exact-source free-`Int` product has
at most 256 tuples. Each temporary fixing is untrusted. A result counts only if
the returned quantified model passes canonical `check_model` against the
unfixed original assertion sequence.

## Exploratory result and production correction

The fixed-query probe finds three of eleven cases in 46 candidate queries:

| Seed | Base pool | Closed pool | Exact free Ints | Tuples | Checked assignment |
|---:|---:|---:|---:|---:|---|
| 23 | 8 | 13 | 2 | 169 | `[-4, -4]` |
| 111 | 7 | 11 | 1 | 11 | `[-5]` |
| 231 | 8 | 12 | 2 | 144 | `[-10, -10]` |

The probe invokes the complete public MBQI loop with each fixing. Production
validation exposed that this is broader than the intended one-shot candidate
certification: seed 111 needs that recursive re-entry and remains Unknown in
the preregistered production path. Seeds 23 and 231 pass the actual path and
unfixed replay. The exact production result is therefore **two of eleven**.

The normal 256-case differential reports 227 jointly decided agreements, 209
Axeyum SAT, 24 Axeyum UNSAT, 23 Axeyum Unknown, 209/209 SAT replay, and zero
errors or disagreements. The ordinary-incomplete Z3-SAT residual is nine seeds:
`30, 32, 70, 111, 122, 150, 175, 182, 242`. No prior SAT or UNSAT result is
lost because evaluated completion runs only after ordinary MBQI and E-matching
both decline.

Seeds 30, 32, 70, 122, and 182 exhaust their bounded candidates without a
checked model. Seed 175 has a 23-value closed pool and declines without
truncation. Seeds 150 and 242 have no exact-source free `Int`, even though the
generator declared an unused scalar, and therefore do not enter completion.

This is a model-generation improvement, not evidence widening. It justifies
proposed
[ADR-0361](../research/09-decisions/adr-0361-preregister-evaluated-quantified-uf-scalar-candidates.md)
with the existing 16-value/256-tuple caps and a deferred post-decline retry.

## Implementation evidence

Commit `471738aa` implements the preregistered retry. It retains the original
ADR-0360 search, ordinary MBQI, and E-matching order, saves the initial ground
candidate, and only constructs the evaluated pool after all established routes
decline. This ordering is material: an earlier immediate retry consumed the
shared deadline on seed 145, while the committed deferred retry preserves that
prior checked-SAT result.

Focused unit coverage checks stable collection of scalar assignments, UF
default and override values, and exact-source ground term values. The same test
assigns a universal binder in the model and confirms that a binder-dependent
term is still excluded by source dependency rather than accidentally treated as
ground. Focused integration coverage checks the new seed-23 and seed-231 models
and the preserved seed-145 model. Warning-denied solver Clippy and the complete
256-case differential pass; the completed branch-wide outcome follows.

## Branch-gate outcome

The implementation and its frozen semantic gate are green. The complete
256-case differential reports 227/227 jointly decided agreements and 209/209
SAT replay, with zero errors or disagreements. Workspace all-feature Clippy,
warning-denied rustdoc, complementary workspace tests excluding the solver
package, foundational resources, QF_BV profile, SMT-COMP recovery, reflection
semantics, benchmark-repetition tests, the pinned 162-file Glaurung QF_BV pack,
rules-as-code, and documentation links also pass.

Two solver-package observations prevent accepting ADR-0361 at this checkpoint:

- A non-CI full solver-package run reaches `progress_frontier` and reproduces a
  hardware-relative `frontier_lia_cuts` ratchet miss: size 25 exceeds four
  seconds while size 26 completes in about 26 ms, so the measured frontier is
  24 versus the committed 26. The test's documented `CI=1` mode skips this
  noisy ratchet while retaining the curve diagnostic.
- The CI-mode full solver-package run passes that frontier and all changed
  quantified-UF coverage, then reports one late load-sensitive failure in
  `from_int_type002_arith_bound_is_sat`. The exact test immediately passes in
  1.18 seconds and its complete 14-test integration binary passes 14/14 in
  4.06 seconds. This is not a reproduced correctness regression, but it is not
  a clean uninterrupted aggregate run either.

The rebased `just parity-docs` gate independently remains red in the Lean-owned
retained evidence check with
`LEAN_PROCESS_ATTEMPT_ERROR|exit-zero-4g: run/spec attribution drift`. Every
preceding parity sub-gate passes. This SMT-COMP lane does not rewrite that
retained cross-lane evidence. ADR-0361 therefore remains proposed even though
its focused, differential, replay, lint, and documentation evidence is green.

## Reproduction

```sh
AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS='23,30,32,70,111,122,150,175,182,231,242' \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_fixed_query_evaluated_scalar_probe_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture
```
