# Lean U2 TL0.6.3 M2 R6 completion-replay R2 correction plan

Status: **preregistered validator-only correction; no process or evidence
mutation authorized**

Date: 2026-07-23

Parent:
[pending-validation result](lean-u2-official-execution-tl0.6.3-m2-r6-attempt-004-pending-validation-result-2026-07-23.md).

## Correction boundary

R2 changes only completion reconstruction mode. `build_completion` gains an
explicit `allow_completion` argument defaulting to `false`. Pre-install
construction retains that default. Post-install `validate_complete_store`
calls the same builder with `true`, which forwards the flag to the existing
dependency validator. Accepted inventory continues to exclude completion, so
the reconstructed completion bytes, dependencies, record-set digest, credits,
and record identity must remain exactly unchanged.

No source, control, process, JUnit, case, post, projection, completion, retained
payload, or other evidence byte may change. No process, retry, append, repair,
reseal, result promotion by prose, or new selected root is authorized.

## Gates and decision

Tests must prove:

1. pre-install construction still rejects a present completion;
2. post-install validation forwards `allow_completion=true` exactly once;
3. the committed 152-file root validates to existing completion
   `1f0b9af8997d9cced7bbb141e979ecd169b882b3df57ae02b0cb5f34ff0f3b67`;
4. removing/tampering with completion, conditional predicate, retained payload,
   projection, JUnit, or case data still rejects;
5. the evidence tree is unchanged before and after validation.

The correction implementation and documentation checkpoint must be committed
and pushed before the validator is run against the frozen root. If exact replay
passes, a result authority may accept the already-sealed 64 local outcomes and
one local shard while preserving every parent/provider/Axeyum/pair/performance/
population/axis/gate/parity zero. If it fails, R6 remains zero-credit and no
retry is permitted.
