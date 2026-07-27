# ADR-0368: Preregister SMT `(15,64)` add/sub/mul circuits

Status: accepted

Date: 2026-07-27

## Context

A deterministic one-declared-status-file-per-family QF_BVFP census found 77 of
108 current-code decisions, zero wrong verdicts, 29 cooperative unknowns, and
two process-ceiling overruns. The largest explicit capability cluster is SMT-LIB
`(_ FloatingPoint 15 64)`: representative rows fail closed with
`fp.add: unvalidated format` or `fp.mul: unvalidated format`.

This is the 79-bit SMT IEEE format (one sign bit, 15 exponent bits, and 63 stored
fraction bits). It is not x87's 80-bit interchange encoding with an explicit
integer bit. Axeyum's generic circuits operate on SMT's implicit-integer-bit
layout and already use the wide-BV evaluator/lowerer for F128 intermediates, but
the `(15,64)` format is correctly excluded from the validation allowlist.

The selected family sample contains exact `(15,64)` add/mul demand in the
`halve_longdouble`, `inf_longdouble`, `nan_longdouble`, `sqr_longdouble`, and
`ld-add_default` families. Division and square root occur in only later members
of that cluster and require their own oracle gates.

## Decision

**Admit symbolic SMT `(15,64)` addition, subtraction, and multiplication only
after the existing generic circuits pass an independent all-rounding-mode oracle
sweep over structured and deterministic random bit patterns. Keep division,
sqrt, FMA, and every other previously unvalidated format fail-closed.**

The implementation gate is operator-specific:

1. add and mul may accept exactly `exp_bits == 15 && sig_bits == 64` in addition
   to the existing common allowlist;
2. sub inherits the add gate through the exact `a + (-b)` identity;
3. the existing wide-BV route may carry the 133-bit add/mul intermediates;
4. the common arithmetic allowlist must not be widened, so div/sqrt/fma do not
   gain accidental support; and
5. documentation must call this SMT binary79-like layout, not x87 extended.

The independent test oracle defines a private `rustc_apfloat::ieee::Semantics`
with `BITS = 79` and `EXP_BITS = 15`. That yields the same implicit-integer-bit
IEEE encoding as SMT-LIB, avoiding `X87DoubleExtended`'s incompatible explicit
integer bit. For add and mul, every one of the five SMT rounding modes must match
over signed zeros, normals, infinities, NaNs, the smallest subnormal, boundary
patterns, their Cartesian product, and a deterministic random population. NaN
payloads may differ, but the result must remain NaN.

## Acceptance evidence

The independent add and mul circuits agree across all five rounding modes on
12×12 structured Cartesian pairs plus 512 deterministic random pairs per mode:
6,560 operator/mode input pairs total, with no non-NaN bit mismatch and every
oracle NaN remaining NaN.

Four exact formerly unsupported family representatives now decide and agree
with their declared status and Z3 4.13.3, with zero model-replay failures:

- `halve_longdouble-flow/query.3.smt2`: UNSAT, 0.906 s;
- `halve_longdouble-noflow/query.1.smt2`: SAT, 0.325 s;
- `inf_longdouble/query.13.smt2`: UNSAT, 0.452 s; and
- `ld-add_default/query.2.smt2`: SAT, 1.897 s.

The negative boundary is live: selected `nan_longdouble` and `units_meter_ft`
rows still decline at symbolic division, while `sqr_longdouble` declines at
sqrt. A dedicated test directly requires div/sqrt/fma to return
`IrError::Unsupported` for symbolic `(15,64)` operands.

The frozen 108-family process-isolated diagnostic moves 77→83 decisions with
zero wrong verdicts; because three of the six aggregate changes are
load-sensitive timeout recoveries, only the four exact unsupported-to-decision
rows above are credited to this implementation. The 34-file ESBMC process gate
remains 34/34 correct with zero unknown, wrong, or process-timeout outcomes.

`cargo test -p axeyum-fp --all-features` passes 67 unit tests, 11 full
faithfulness tests, 14 simple faithfulness tests, two width-guard tests, and
doc-tests. Warning-denied all-target/all-feature `axeyum-fp` Clippy passes.

## Alternatives

### Use `rustc_apfloat::ieee::X87DoubleExtended`

Rejected. It is an 80-bit encoding with an explicit integer bit and pseudo-value
rules; its raw bit patterns are not SMT `(15,64)` values.

### Add `(15,64)` to the common arithmetic allowlist

Rejected. That would silently admit div/sqrt/fma before their circuits have an
operator-specific oracle sweep.

### Treat the unsupported rows as ordinary performance unknowns

Rejected. The parser reports an intentional validation refusal before solving;
tuning SAT search cannot cross that semantic boundary.

## Consequences

Three public symbolic operators gain one precisely validated
format through the existing pure-Rust wide-BV path. Circuit size and SAT cost
may still leave some rows unknown. The change adds no native solver dependency
and does not alter model replay, proof trust, other formats, or non-FP logic.
