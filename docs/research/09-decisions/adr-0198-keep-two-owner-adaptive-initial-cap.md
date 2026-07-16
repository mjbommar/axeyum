# ADR-0198: Keep the two-owner adaptive initial cap

Status: deferred
Date: 2026-07-16

## Context

ADR-0197 shows that the accepted SurfacePen adaptive stream sends 16 checks
through one-shot fallback. Those checks are only 0.63% of the stream but
consume 6.02% of profiled internal time. After ADR-0196's exclusive successor
transfer, the corresponding no-fallback fixed-lineage control peaks at only
three live owners. Raising the adaptive initial cap from two to three is
therefore the smallest apparent admission change.

The candidate must still satisfy the existing repeated semantic, finding,
time, normalized-ratio, RSS, and Z3-drift gates. Eliminating fallback work is
not sufficient if the retained third solver exceeds the memory envelope.

## Experiment

Run three order-balanced unprofiled SurfacePen processes under each policy with
the accepted owner-transfer and replay-cache defaults. The adaptive control
starts at two owners and records exactly 16 fallbacks, 207 created/closed paths,
peak two live sessions, and zero terminal state in every run. The fixed-lineage
ceiling records zero fallbacks, the same 207 created/closed paths, peak three,
and zero terminal state.

On this trace, fixed lineage and an initial-three adaptive candidate have the
same admission behavior: pressure never needs a fourth owner. The ceiling is
therefore sufficient to reject the policy before adding another environment or
artifact field.

## Result

All 15,306 combined checks agree with Z3 and finding output is unchanged. Mean
Axeyum time improves from 436.733 to 412.733 ms (-5.50%), and the normalized
Axeyum/Z3 ratio improves 6.30%. Absolute Z3 drift is +0.86%.

Median RSS rises from 78,708 to 84,736 KiB (+7.66%), exceeding the accepted 5%
alarm. The third retained owner buys the expected fallback speedup but fails the
memory objective. The mandatory SurfacePen gate is already decisive, so a
held-out NETwtw10 run cannot make this policy acceptable.

## Decision

Keep the adaptive initial cap at two and the pressure threshold at 128. Do not
implement or publish an initial-three control from this hypothesis. The fixed
lineage mode remains an explicit diagnostic ceiling, not the production
default.

Reopen admission only with a topology or cost signal that can release or avoid
the third retained solver before its RSS cost persists. Otherwise attack
fresh-sibling/fallback construction through immutable prefix reuse, which must
not share mutable SAT, cache, scope, model, or replay state.
