# Quantified-UFLIA one-level fixed-MBQI measurement

Status: measured; preimplementation ordering corrected
Date: 2026-07-23
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Population

The frozen population is the nine ordinary Z3-SAT Unknowns remaining after
ADR-0361 on the 256-case quantified-UFLIA differential:

```text
30, 32, 70, 111, 122, 150, 175, 182, 242
```

No generator, oracle, timeout, value cap, or tuple cap changes.

## Classification

The existing fixed-query diagnostic reruns the public MBQI loop after adding
each candidate scalar equality. Across the nine seeds it checks 45 candidate
queries and finds one additional replay-clean model:

| Seed | Relevant source Ints | Closed pool | Fixed-MBQI result |
|---:|---:|---:|---|
| 30 | 1 | 16 | exhausted |
| 32 | 1 | 13 | exhausted |
| 70 | 1 | 18 | pool overflow; no search |
| 111 | 1 | 11 | checked SAT at `-5`, first candidate |
| 122 | 1 | 17 | pool overflow; no search |
| 150 | 0 | 5 | no relevant source scalar |
| 175 | 1 | 23 | pool overflow; no search |
| 182 | 1 | 13 | exhausted |
| 242 | 0 | 10 | no relevant source scalar |

Supplying complete scalar values from a Z3 model does not decide any of the nine
with the current one-shot candidate checker. Seed 111 therefore measures a
search-depth gap, not another candidate-value gap. Its source has one relevant
free scalar (`y1`) and a constant universal `forall x. f(x) = -2`; fixing
`y1 = -5` lets one ordinary MBQI pass repair and certify the function profile.

## Production boundary

The diagnostic calls the public entry recursively and is not itself a
production design: without an explicit guard, recursive completion has no
structural depth bound. Proposed
[ADR-0362](../research/09-decisions/adr-0362-preregister-one-level-fixed-query-mbqi-retry.md)
permits only a one-level internal retry for exactly one relevant source `Int`:

- reuse ADR-0361's complete deterministic value pool and 16-value cap;
- run only after ADR-0360, ordinary MBQI, and E-matching decline;
- try only the first ordered evaluated value, then continue ADR-0361's unchanged
  one-shot evaluated sweep if the inner attempt declines;
- pass the caller's remaining shared deadline to every inner attempt;
- disable this retry inside the inner MBQI invocation;
- ignore inner UNSAT and Unknown results; and
- accept inner SAT only when canonical `check_model` succeeds on the exact
  original assertions without the temporary scalar equality.

The initial proposed ordering placed the inner pass after ADR-0361's complete
evaluated sweep. A focused preimplementation test proved that ordering inert:
the sweep may consume the complete shared deadline before an inner pass can
start. The corrected first-candidate placement is strictly narrower than the
45-query diagnostic, permits at most one inner MBQI invocation, and preserves
all pre-ADR-0361 routes. It also matches the measurement: seed 111 succeeds on
that first candidate.

The expected frozen result is 228 jointly decided agreements, 210 Axeyum SAT,
24 Axeyum UNSAT, 22 Axeyum Unknown, 210/210 SAT replay, and zero error or
disagreement. The residual ordinary Z3-SAT Unknowns should be exactly
`30, 32, 70, 122, 150, 175, 182, 242`.

## Reproduction

```sh
AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS='30,32,70,111,122,150,175,182,242' \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_fixed_query_evaluated_scalar_probe_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture
```
