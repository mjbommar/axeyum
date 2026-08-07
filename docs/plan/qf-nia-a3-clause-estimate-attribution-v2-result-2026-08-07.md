# QF_NIA A3 clause-estimate attribution v2 result — 2026-08-07

## Verdict

V2 is rejected without a production edit. Its deduplicated structural-demand
fixed point stayed within every frozen work bound on both targets, but the
fresh-parse diagnostic did not reproduce either retained production estimate:

| Target | Retained/current production | Fresh-parse diagnostic | Difference |
|---|---:|---:|---:|
| `p31818` | 81,482,280 | 81,482,304 | +24 clauses |
| `p6984` | 82,590,729 | 82,590,768 | +39 clauses |

The v2 complete-record contract requires exact equality. Both invocations
therefore exited 1 before JSON serialization, the estimate-attribution route is
closed, and no constant-aware or demanded-lowering production mechanism is
authorized.

## Boundary discrimination

The mismatch is in the diagnostic entry boundary, not stale retained evidence.
Fresh release `explain_corpus` observations on current source and the frozen
SHA-verified files reproduced the production route details exactly:

```text
p31818: estimated 81482280 CNF clauses before lowering exceeds budget 64000000
p6984:  estimated 82590729 CNF clauses before lowering exceeds budget 64000000
```

The standalone analyzer starts from a new parse and immediate width-32 integer
blast. The production ladder is reached only after the earlier exact-real,
nonlinear, linearization, and bounded-blast dispatch sequence on the live arena.
The 24/39-clause differences prove those are not an interchangeable measurement
boundary, even though the final conservative estimator formula is the same.
V2 does not speculate which prior interned term accounts for each small delta;
doing so would require another newly preregistered pipeline probe, and the v2
stop rule explicitly says not to create v3 merely to rescue attribution.

## Fixed-point repair and safety evidence

The v2 implementation schedules each unique term bit once and propagates each
non-local arithmetic barrier once. A new test proves that a one-bit extract of
an 8-bit product demands one product bit, all 16 operand bits, and only one
barrier propagation; repeating the same root adds no unique work or transfer
edge. Together with the retained sharing/class/width tests, focused status is
3/3 passing, warning-denied example Clippy passes, format passes, and the link
check passes.

The release v2 diagnostic has SHA-256
`c577eeb709ef5df12e0cbae9b8dc3def3e3be112b90900fd4374ce84d05cba7d`.
Both frozen source digests passed. Reaching the estimate-equality check proves
that the 2,000,000 unique-bit and 8,000,000 transfer-edge bounds did not fire.
No AIG, CNF, solver, model, or verdict path is referenced by the diagnostic.

## Disposition

Keep the conservative 64,000,000 production ceiling unchanged. Do not infer a
constant-folding gain from incomplete records, raise an analysis/solver cap, or
run targets/controls/200 rows. A3 retains its honest 34/200 result and its
closed negative mechanism history. Per the preregistered stop rule, move to A4's
exact QF_UFLIA residual partition; return to these NIA refusals only after a new
independent pipeline-boundary design or other evidence supplies a bounded
candidate.
