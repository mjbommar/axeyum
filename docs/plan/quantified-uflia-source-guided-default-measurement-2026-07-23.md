# Quantified-UFLIA source-guided default measurement

Status: implemented; focused and differential gates green
Date: 2026-07-23
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Population

The frozen population is the eight ordinary Z3-SAT Unknowns remaining after
ADR-0362 on the 256-case quantified-UFLIA differential:

```text
30, 32, 70, 122, 150, 175, 182, 242
```

No generator, oracle, timeout, function cap, value cap, Cartesian cap, source
fragment, certificate, or replay rule changes.

## Classification

ADR-0359 derives candidate UF defaults from model values, existing UF defaults
and entries, zero, and one checked predecessor/successor closure. The residual
sources contain additional exact integer information not yet used for default
repair: source literals and binder-independent integer subterms evaluable under
the initial ground candidate.

A retained diagnostic adds those source-derived values before the same one-step
neighbour closure, preserves every scalar assignment and explicit UF table
entry, and searches only when the existing 32-value and 256-combination caps
hold. Every reported success passes the independent finite-profile checker and
canonical replay of the complete original assertion sequence.

| Seed | Closed values | Relevant Int-result UFs | Product | Checked defaults |
|---:|---:|---:|---:|---|
| 30 | 16 | 1 | 16 | `[-10]` |
| 32 | 13 | 2 | 169 | `[-7, -7]` |
| 70 | 18 | 1 | 18 | `[5]` |
| 122 | 17 | 2 | 289 | decline: product overflow |
| 150 | 5 | 2 | 25 | `[-3, -3]` |
| 175 | 23 | 1 | 23 | exhausted |
| 182 | 13 | 2 | 169 | exhausted |
| 242 | 10 | 2 | 100 | `[-4, 4]` |

The mechanism closes five cases without cap growth. Seeds 150 and 242 are
especially discriminating: neither has a source-relevant free scalar, so their
models cannot be attributed to ADR-0360/0361 scalar completion. Seed 122
demonstrates fail-closed product overflow, while seeds 175 and 182 demonstrate
complete bounded exhaustion.

## Production boundary

Proposed
[ADR-0363](../research/09-decisions/adr-0363-preregister-source-guided-quantified-uf-default-repair.md)
adds one outer, initial-candidate-only retry:

- run ADR-0359's established model-only default repair first;
- preserve ADR-0362's one-level fixed-query retry and ADR-0360's complete
  free-Int completion before this new retry;
- derive an `Int` pool from ADR-0359's existing values plus exact source integer
  literals and binder-independent source integer subterms that evaluate under
  the unchanged initial candidate;
- apply one checked predecessor/successor closure, decline rather than truncate
  above 32 values, and decline above 256 complete default tuples;
- preserve scalar assignments, function signatures, and every explicit table
  entry byte-for-byte; admit only relevant `Int`-result functions;
- disable the retry in ADR-0362's inner MBQI invocation and attempt it at most
  once in the outer invocation; and
- accept only a model independently certified for every original universal and
  canonically replayed against every exact original assertion.

The placement preserves every established decision before spending work on the
new mechanism. On decline, ordinary MBQI, E-matching, and ADR-0361 continue
unchanged under the caller's shared deadline.

Two exact production-path prototype runs agree on 215 Axeyum SAT, 24 Axeyum
UNSAT, 17 Axeyum Unknown, 215/215 SAT replay, zero errors/disagreements, and the
same three ordinary Z3-SAT residuals. They report 232 and 233 jointly decided
agreements because the independent two-second Z3 call times out on ten versus
nine seeds. The frozen gate therefore requires at least 232 jointly decided
agreements plus the exact Axeyum/replay/residual invariants; it does not turn
oracle timeout scheduling into a solver-capability claim. The residual ordinary
Z3-SAT Unknowns must be exactly `122, 175, 182`.

## Reproduction

```sh
AXEYUM_QUANT_UFLIA_DEFAULT_DIAGNOSTIC_SEEDS='30,32,70,122,150,175,182,242' \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_source_literal_uf_default_repair_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture
```

## Implementation evidence

Commit `568efb15` implements the preregistered production boundary without
changing the source fragment, caps, candidate order, or evidence route. The
production-path differential returns exactly 215 SAT, 24 UNSAT, and 17 Unknown,
replays all 215 SAT models, reports no error or disagreement, and leaves exactly
seeds `122, 175, 182` Unknown among ordinary Z3-SAT cases. Repeated runs retain
the preregistered 232/233 jointly decided oracle-timeout variation.

Focused tests freeze source-value collection, binder-dependency exclusion,
explicit-entry preservation, deadline and product-cap decline, unsupported
result-sort decline, the five exact new models/default tuples, and the three
exact residual Unknowns. Solver all-target/all-feature Clippy with warnings
denied, strict rustdoc, and the documentation link gate pass. An uninterrupted
CI-mode solver-package run passed all 907 library tests and the changed
quantified-UFLIA differential, then exposed one unrelated load-sensitive
`word_int_coupling_sat::from_int_type002_arith_bound_is_sat` miss late in the
aggregate. The exact test immediately passed alone in 1.16 seconds and its
complete 14-test integration binary passed in 4.02 seconds under the same CI
configuration. This is recorded as an aggregate-gate observation, not as a
green full-package claim and not as evidence for ADR-0363.
