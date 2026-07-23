# Lean U2 TL0.6.3 M2 R6 control-history R1 correction plan

Status: **preregistered after pre-process stop; no R6 control root or selected
process exists**

Date: 2026-07-23

Parents:
[R6 plan](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-plan-2026-07-23.md)
and [implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-implementation-2026-07-23.md).

## Observed stop

At clean remote-equal revision
`7076e453710e1cc22fed9b782ba8fa6981f9a5a8`, the exact direct stack probe
passed. The subsequent `run-control` invocation stopped in Python history
preflight before control-root creation, source installation, or released-Lean
launch. No R6 control/work/evidence root exists, so attempt 004 remains
unconsumed and all credit remains zero.

The adapter correctly rebound `R5.validate_history` to the R6 history entry for
the delegated control. That R6 entry called the R5 diagnostic validator, whose
raw validator calls `R5.validate_history`; under the temporary control binding,
this re-entered R6 history until Python raised `RecursionError`.

## Frozen correction

R1 changes only the R5-history delegation boundary:

1. capture the original R5 history function at R6 module load, before any
   temporary binding;
2. while validating the frozen R5 diagnostic closure, temporarily expose that
   captured function to the R5 diagnostic validator;
3. restore the caller's current R5 binding in `finally`, including when R5
   validation fails.

The plan, R5 result/completion identities, R6 attempt/run/lane/root identities,
control source/schemas, 32 GiB/512 MiB resources, conditional artifact rule,
shard/command/store, one selected process, no retry, and every credit rule stay
unchanged. The next control root is revision-named from the corrected pushed
implementation; the absent `...-7076e453` root is never reused.

## Gates and authorization

A regression must enter the exact temporary R6 control-history binding, call
the rebound `R5.validate_history`, return the frozen R5 completion without
recursion, prove the original R5 history function was used inside diagnostic
validation, and prove the caller binding is restored. Existing nine R6 tests,
five R5 control tests, generator/check, and offline no-process gates must pass.

No implementation or repeated control is authorized until this plan is
committed and pushed. The correction and its documentation checkpoint must then
be committed and pushed separately from the next harmless control invocation.
A failed corrected control still stops before selected execution; only an exact
successful completion authorizes the one attempt-004 process.
