# ADR-0369: Preregister SMT `(15,64)` symbolic division

Status: accepted

Date: 2026-07-27

## Context

ADR-0368 validates SMT `(15,64)` add/sub/mul and deliberately keeps division,
sqrt, and FMA outside the common arithmetic allowlist. Its accepted front-door
run exposes the next exact boundary: selected `nan_longdouble/query.07.smt2` and
`units_meter_ft/query.116.smt2` now reach `fp.div: unvalidated symbolic format`.
Both are declared/Z3 UNSAT.

The generic division circuit already supports 231-bit F128 intermediates through
the pure-Rust wide-BV path and exact ground division for arbitrary admitted IEEE
layouts. SMT `(15,64)` needs a 133-bit intermediate. The representation is thus
available; the missing requirement is an operator-specific independent oracle
gate. Model replay alone cannot validate an FP circuit because the evaluator
executes the same lowered circuit.

## Decision

**Admit symbolic division for exactly SMT `(15,64)` after its existing circuit
matches the private 79-bit `rustc_apfloat` IEEE oracle in all five rounding
modes. Do not widen the common arithmetic allowlist or admit sqrt/FMA.**

The implementation must:

1. add one division-specific predicate which accepts the existing common set or
   exactly `exp_bits == 15 && sig_bits == 64`;
2. allow that format's 133-bit division intermediate through the wide-BV path;
3. retain the exact ground fallback and all existing formats unchanged;
4. validate signed zeros, infinities, NaNs, subnormals, overflow boundaries,
   every structured Cartesian pair, and deterministic random pairs in every
   SMT rounding mode; and
5. directly require symbolic `(15,64)` sqrt and FMA to remain unsupported.

## Acceptance evidence

The division circuit matches the private 79-bit IEEE oracle in all five rounding
modes over 12×12 structured Cartesian pairs and 512 deterministic random pairs
per mode: 3,280 input/mode cases, zero non-NaN bit mismatches, and zero NaN-class
mismatches.

Both selected boundaries become definite UNSAT and agree with declared status
and Z3 4.13.3: `units_meter_ft/query.116.smt2` in 50.344 ms and
`nan_longdouble/query.07.smt2` in 47.973 ms. The combined retained six-row
artifact is two SAT / four UNSAT, 6/6 Z3 agreement, zero unknown, unsupported,
error, or model-replay failure, with PAR-2 mean 0.371 s.

The frozen 108-family process diagnostic reports 87 correct, zero wrong, 19
unknown, and two process timeouts. Only these two exact unsupported-to-decision
rows are credited to division; two additional aggregate changes are
load-sensitive timeout recoveries. The standalone ESBMC process gate remains
34/34 correct with zero wrong, unknown, or process-timeout outcome. A deliberately
concurrent breadth/ESBMC run produced two ESBMC outer timeouts and is retained as
a host-contention negative, not used as no-loss evidence.

`cargo test -p axeyum-fp --all-features` passes 68 unit tests, 11 full
faithfulness tests, 14 simple faithfulness tests, two width guards, and doc-tests.
Warning-denied all-target/all-feature `axeyum-fp` Clippy passes. The focused
negative test continues to require symbolic `(15,64)` sqrt and FMA to return
`IrError::Unsupported`.

## Alternatives

### Admit all `(15,64)` arithmetic at once

Rejected. Sqrt lacks a `rustc_apfloat` operator and needs the separate exact
rounding-interval oracle used for F128; FMA needs a ternary sweep. Neither is
authorized by a division result.

### Rely on the exact ground-division path

Rejected as incomplete for these rows. Their operands remain symbolic while the
SMT-LIB expression is constructed, so the sound ground fallback correctly
declines.

## Consequences

`(15,64)` division joins add/sub/mul without changing the public
IR, solver trait, native-dependency boundary, or assurance accounting. The
larger circuit may still time out. Sqrt and FMA remain separate measured gaps.
