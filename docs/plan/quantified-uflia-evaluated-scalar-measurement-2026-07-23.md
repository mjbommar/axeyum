# Quantified-UFLIA evaluated-scalar measurement

Status: measured and preregistered; implementation not started
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

## Result

The strict policy checks three of eleven cases in 46 candidate queries:

| Seed | Base pool | Closed pool | Exact free Ints | Tuples | Checked assignment |
|---:|---:|---:|---:|---:|---|
| 23 | 8 | 13 | 2 | 169 | `[-4, -4]` |
| 111 | 7 | 11 | 1 | 11 | `[-5]` |
| 231 | 8 | 12 | 2 | 144 | `[-10, -10]` |

Seeds 30, 32, 70, 122, and 182 exhaust their bounded candidates without a
checked model. Seed 175 has a 23-value closed pool and declines without
truncation. Seeds 150 and 242 have no exact-source free `Int`, even though the
generator declared an unused scalar, and therefore do not enter completion.

This is a model-generation improvement, not evidence widening. It justifies
proposed
[ADR-0361](../research/09-decisions/adr-0361-preregister-evaluated-quantified-uf-scalar-candidates.md)
with the existing 16-value/256-tuple caps.

## Reproduction

```sh
AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS='23,30,32,70,111,122,150,175,182,231,242' \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_evaluated_source_scalar_completion_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture
```

