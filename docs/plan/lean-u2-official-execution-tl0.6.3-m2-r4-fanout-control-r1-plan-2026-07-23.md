# Lean U2 TL0.6.3 M2 R4 fanout-control R1 correction plan

Status: **preregistered correction; no corrected control, selected harness,
discovery, or selected process has run**

Date: 2026-07-23

Parents:
[R4 attempt plan](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-plan-2026-07-23.md)
and
[implementation checkpoint](lean-u2-official-execution-tl0.6.3-m2-r4-attempt-003-implementation-2026-07-23.md)

## 1. Observed control failure

Clean local/tracking/remote equality passed at pushed revision
`80b8b86df335d5d9eff42be72428b3c9ef0e76f9`. The direct environment control
passed with source `e7f746b0...12401`, exit 0, and value `524288`. The required
fanout control then exited before creating tasks because its Lean source omitted
`do` after the `fun task =>` binder. Released Lean reported:

```text
cannot lift `(<- ...)` over a binder ... fixed by adding a missing `do`
```

A no-credit diagnostic repetition retained 271 source bytes
(`11421ecf...89c3`) and 269 stdout bytes (`e6b532d9...7f2`) under temporary root
`/tmp/axeyum-r4-fanout-diagnostic-2s2oiisr`; stderr was empty. Both invocations
were harmless controls with empty selections. No R4 work root, evidence root,
source capture, harness, discovery, prelaunch record, or selected process was
created, so attempt 003 remains unconsumed.

## 2. Frozen correction

R1 changes exactly one Lean token sequence:

```text
fun task => IO.ofExcept (← IO.wait task)
```

becomes:

```text
fun task => do IO.ofExcept (← IO.wait task)
```

The nine-task construction, `Task.Priority.dedicated`, complete join, exact
success line, UTF-8 source encoding, 16 GiB limit, 512 MiB stack environment,
command, terminal/cleanup record, empty selection, and zero credits are
unchanged. R1 does not change the selected shard, attempt/run identity, CTest
command, watchdog, storage policy, or any parity projection.

## 3. Gates and next action

The corrected source and focused test must be committed and pushed separately,
the generated complete-parity source identity must be refreshed, and all R4,
R3-history, generator, and documentation gates must pass offline. A new
documentation checkpoint must disclose this failed control. Only then may the
corrected stack and fanout controls run from a new clean remote-equal revision.
The selected `run-r4` surface remains forbidden until the corrected fanout
record is valid and its digest is supplied explicitly.
