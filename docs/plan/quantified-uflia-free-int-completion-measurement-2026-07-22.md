# Quantified-UFLIA free-Int completion measurement

Status: completed baseline; ADR-0360 proposed
Date: 2026-07-22
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Frozen population

After accepted ADR-0359, the 256-case direct-Z3 differential contains 39
Z3-SAT Axeyum Unknowns, all at the ordinary satisfiable-instantiation boundary:

```text
0, 11, 14, 23, 27, 30, 32, 40, 50, 70, 79, 80, 94,
102, 110, 111, 122, 138, 150, 155, 156, 158, 161, 162,
163, 170, 175, 182, 196, 203, 207, 208, 214, 215, 225,
231, 232, 242, 246
```

The normal differential now retains up to 64 Z3-SAT seeds for every exact
Axeyum Unknown/Error reason. This is diagnostic metadata only; verdict and
replay gates are unchanged.

## Measurements

Two ignored, environment-selected diagnostics replay the same generator and
public solver path:

1. Fixing every free ground scalar to the value from one complete Z3 model
   turns 23 of 39 cases into checked Axeyum SAT and leaves 16 Unknown.
2. A pure-Rust production-shaped pool starts with zero and scalar assignments
   from the Axeyum ground model, adds exact source integer literals, then adds
   checked predecessor/successor values. It retains at most 16 values and tests
   at most 256 one/two-scalar tuples. This turns **33 of 39** cases into checked
   SAT after **180 total candidate queries** and leaves only seeds
   `30, 32, 70, 122, 182, 242` Unknown.

The second result exceeds the first because alternative small scalar values can
make the existing ADR-0359 default pool sufficient even when Z3 chooses a much
larger but equally valid scalar/function model. Every diagnostic SAT result
passes canonical replay against the original assertions plus its temporary
fixing; production ADR-0360 must then discard the fixing and replay the exact
original assertion sequence before granting credit.

## Bounded conclusion

Free-Int candidate completion is the dominant next measured SAT increment: it
can close at least 33 of the 39 remaining oracle-SAT declines without changing
the finite-profile checker. The six residual seeds mix source-threshold default
needs and nested/ground UF relationships and remain a separate measurement
boundary. They are not evidence for widening ADR-0360.

## Reproduction

```sh
SEEDS=0,11,14,23,27,30,32,40,50,70,79,80,94,102,110,111,122,138,150,155,156,158,161,162,163,170,175,182,196,203,207,208,214,215,225,231,232,242,246

AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS="$SEEDS" \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_z3_scalar_completion_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture

AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS="$SEEDS" \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_bounded_source_scalar_completion_for_quantified_uflia_unknowns \
  -j2 -- --ignored --exact --nocapture
```
