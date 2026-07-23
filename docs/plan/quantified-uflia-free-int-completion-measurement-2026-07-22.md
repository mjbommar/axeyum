# Quantified-UFLIA free-Int completion measurement

Status: implemented; ADR-0360 acceptance blocked on cross-lane parity evidence
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
2. The first pure-Rust production-shaped diagnostic fixed the generator's one
   or two declared ground symbols. Its pool starts with zero and scalar
   assignments from the Axeyum ground model, adds source integer literals, then
   adds checked predecessor/successor values. It truncated the pool at 16 and
   reported **33 of 39** checked SAT after **180 total candidate queries**.
3. Implementation validation tightened that experiment to ADR-0360's actual
   boundary: collect symbols only from the exact assertion sequence, exclude
   universal binders, and decline if the complete neighbor-closed pool exceeds
   16 rather than truncating it. That policy turns **28 of 39** cases into
   checked SAT. Eleven remain Unknown: `23, 30, 32, 70, 111, 122, 150, 175,
   182, 231, 242`.

The bounded results exceed the Z3-fixing result because alternative small
scalar values can make the existing ADR-0359 default pool sufficient even when
Z3 chooses a much larger but equally valid scalar/function model. The five-case
gap between the exploratory 33 and production 28 is now classified rather than
hidden: two cases rely on truncating an oversized pool, while three rely on a
generator-declared symbol absent from the assertion sequence. Production must
do neither. Every credited SAT result discards the fixing and passes canonical
replay against the exact original assertion sequence.

## Bounded conclusion

Free-Int candidate completion is the dominant next measured SAT increment: the
strict production policy closes 28 of the 39 remaining oracle-SAT declines
without changing the finite-profile checker. The eleven residual seeds mix
pool-overflow, extra default-value demand, source-threshold default needs, and
nested/ground UF relationships and remain a separate measurement boundary.
They are not evidence for widening ADR-0360.

## Implementation result

Commit `5b4c5b40` implements the strict policy in the ordinary MBQI path. The
normal 256-case direct-Z3 differential now reports:

- 225 jointly decided cases and 225 agreements;
- 207 Axeyum SAT, 24 Axeyum UNSAT, and 25 Axeyum Unknown results;
- 207 of 207 Axeyum SAT models accepted by exact canonical replay;
- 11 ordinary-incomplete Z3-SAT Unknowns, exactly seeds `23, 30, 32, 70, 111,
  122, 150, 175, 182, 231, 242`; and
- zero Axeyum errors and zero disagreements.

The 28 newly adjudicated SAT cases raise joint decisions from 197 to 225. Total
Axeyum SAT rises from 178 to 207 because the bounded search also certifies one
case for which the direct Z3 run returns Unknown. The complete
`axeyum-solver --all-features` package gate is green: 901 unit tests, all normal
integration/differential suites, and solver doctests pass; explicitly ignored
measurement and release-stress tests remain opt-in.

The complementary workspace test gate excluding `axeyum-solver` also passes;
it filters only the two separately registered CAS moment-family stress tests.
Workspace Clippy with warnings denied, strict rustdoc, foundational resources,
QF_BV profile, reflection semantics, all 130 benchmark-repetition tests, the
pinned 162-file Glaurung QF_BV raw/canonical pack, rules-as-code, the 52-test
portable SMT-COMP recovery gate, and links are green. The Glaurung pack decides
162/162 under both policies with zero manifest disagreements and zero
SAT/UNSAT conflicts.

ADR acceptance remains blocked on an unrelated branch-wide parity-evidence
failure. `just parity-docs` passes its ordinary compatibility/authority tests,
then the retained Lean process/store checks compare absolute commands captured
under `/home/mjbommar/projects/personal/axeyum-lean-parity` with commands
reconstructed from this worktree. The result is deterministic `run/spec
attribution drift` followed by `kill cell environment drift`; the associated
11-process and 23-store unit suites themselves pass. This lane does not own
those Lean evidence generators or retained artifacts, so it does not rewrite
them merely to accept ADR-0360.

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
