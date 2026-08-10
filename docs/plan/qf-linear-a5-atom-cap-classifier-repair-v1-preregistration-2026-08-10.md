# QF linear A5 atom-cap classifier repair v1 preregistration — 2026-08-10

## Stop condition and observation

The fully gated moderate-envelope repair authorized a V2 restart from QF_LRA
row 1. Exact pushed checkpoint
`775446932508d16c39e9a9a70bf6cb0fbf981e1e` produced a structurally valid
200-row QF_LRA capture in 982,772 ms: start load 9.20, one isolated child per
file, inherited 8 GiB address-space limit, 24,000 ms query timeout, exit 0, and
zero stderr. The lossless join stopped before authorizing QF_IDL:
`sc-39.base.cvc.smt2` was typed `unknown`, but `classify` returned
`search-budget` instead of its required `normalization-resource` control bucket.

The observed trace is deterministic and byte-identical to the earlier invalid
V2 trace:

```json
{"route":"nra","outcome":"declined","reason":"budget","detail":"online CDCL(T) LRA atom cap exceeded (1492 > 1024)"}
```

This exposes a preregistration implementation defect, not a solver behavior
change. The frozen prose requires `sc-39` to return a typed bounded decline and
places deterministic normalization/resource ceilings ahead of search budgets.
Production returns `Unknown(ResourceLimit)`, but route-trace schema v1
deliberately collapses timeout and deterministic resource kinds into
`reason: budget`; the classifier must use the retained exact detail. Its test
used a synthetic `normalization coefficient work exhausted` trace and therefore
did not exercise the real control spelling.

The raw capture, metadata, and failure summary are retained as
[`V2-QF_LRA-classifier-attempt-001.axeyum.jsonl`](evidence/qf-linear-a5/failures/V2-QF_LRA-classifier-attempt-001.axeyum.jsonl),
[`capture metadata`](evidence/qf-linear-a5/failures/V2-QF_LRA-classifier-attempt-001.capture.json),
and [`failure metadata`](evidence/qf-linear-a5/failures/V2-QF_LRA-classifier-attempt-001.failure.json).
They remain permanently non-credited.

## Frozen repair

Change only `scripts/qf_linear_a5_census.py` and its focused test:

1. classify the exact phrase `atom cap exceeded` as
   `normalization-resource`, before the generic budget rule;
2. make the `sc-39` test use the actual production route, reason, detail, and
   absent `kind` field; and
3. retain the timeout negative control and every other vocabulary, priority,
   grouping, population, sidecar, timeout, resource, route, and score rule.

No solver, route trace, cap, timeout, memory ceiling, verdict, evidence policy,
or public API change is authorized. Broad terms such as `cap`, `exceeded`, or
`budget` alone are not accepted as normalization evidence.

## Acceptance and restart

The candidate must pass the focused classifier suite and show, on the
non-credited capture only, 200 rows, 90 current decisions versus 86 historical,
four agreeing gains, zero losses, zero wrong verdicts, 56 reference-only rows,
and `sc-39` in `normalization-resource`. Exactly 24 reference-only atom-cap
traces move from the generic search bucket to the deterministic resource
bucket; no other trace may change classification.

Then formatting, strict script tests, documentation gates, and one
uninterrupted external-frontier `just check` must pass at an exact pushed
checkpoint. Any code or validator change invalidates the observed stream: after
the full gate, V2 restarts QF_LRA from row 1 at host load at most 12. Only a new
zero-loss QF_LRA join authorizes QF_IDL.
