# QF_UFLIA A4 provenance recovery and causal census v2 preregistration

Date: 2026-08-07

## Amendment to v1

V1 stopped exactly as required because `explain_corpus` reported the first of
26 known valid wide-integer inputs as generic `parse-error`.  V2 retains every
v1 population, identity, budget, reference, ordering, soundness, aggregate,
artifact, bucketing, and no-solver-change rule except the explicit amendments
below.  Read this document with the
[v1 preregistration](qf-uflia-a4-provenance-census-v1-preregistration-2026-08-07.md)
and [v1 result](qf-uflia-a4-provenance-census-v1-result-2026-08-07.md).

This remains a measurement repair.  It authorizes changes only to
`crates/axeyum-bench/examples/explain_corpus.rs`,
`scripts/qf_uflia_a4_census.py`, and their focused tests.  It does not authorize
an IR widening, parser semantics change, solver edit, route reorder, or cap
increase.

## Typed ingest record

`explain_corpus` may emit a non-dispatch terminal record only when parsing
returns `SmtError::Unsupported(detail)` and `detail` matches exactly:

```text
integer literal `<one or more ASCII decimal digits>` exceeds the modeled `Int` range
```

The JSONL record is:

```json
{"file":"<exact list path>","status":"ingest-unsupported","verdict":"unknown","route":"smtlib-ingest","reason":"unsupported","kind":"wide-integer-literal","detail":"<exact parser detail>"}
```

It carries no `trace`: solver dispatch never started, so inventing a route trail
would be false provenance.  The explicit terminal ingest fields are the complete
provenance record for this class.  Any other `SmtError::Unsupported`, syntax or
IR error, resource/deadline record, missing field, extra trace, or detail-shape
mismatch remains a capture-stopping error.

V2 must observe exactly 26 such records at frozen-list rows 1--26.  Every other
row must still be `status="decided"` with a nonempty schema-1 trace.  This known
count is an integrity check discovered by v1, not a new capability claim.

## Census treatment and ADR-0376 control

Each typed ingest row enters the census with:

- terminal and first substantive boundary
  `(smtlib-ingest, unsupported, wide-integer-literal)`;
- a normalized detail family replacing the literal with `<n>`;
- coarse bucket `arithmetic-participation`; and
- `selection_eligible=false`, reason `ADR-0376 measured non-cause`.

The full reference capture determines which of the 26 are currently
reference-only.  Historical ADR evidence predicts five SAT and one UNSAT, but
v2 does not credit that prediction; it records the fresh outcomes and still
requires the overall 94/180/94/0/86/0 matrix exactly.

Lossless groups, coarse counts, artifacts, and all 86 reference-only cases
include the ingest rows.  The deterministic three-row cluster selector excludes
only rows with `selection_eligible=false`; it may select from the remaining
complete dispatch population.  This prevents the already-rejected wide-IR
lever from being rediscovered as if it were new evidence while preserving the
six cases honestly in the gap.

## Failure retention

Each capture command must predeclare a `--failure-metadata` path outside the
repository.  On nonzero process exit, malformed/incomplete records, or any
complete-record failure, it atomically writes a bounded JSON record containing
the exact commit/upstream, binary/list identities, command, start/end/load,
elapsed time, process exit, emitted row count, first validator error, and raw
stdout/stderr hashes and sizes.  It does not copy the failed raw stream into the
repository and grants no result credit.  Successful captures remove any stale
failure record for that stream.

## V2 gates

Before capture, focused tests must prove:

1. the exact wide-integer subtype maps to the typed ingest record;
2. other unsupported, syntax, IR, resource, and malformed records fail;
3. the validator requires exactly 26 typed records at rows 1--26;
4. typed ingest rows are present in artifacts but absent from selection
   candidates;
5. operational cvc5 failures remain fatal; and
6. v1's all-decided fixture plus aggregate/order/disagreement controls still
   pass.

Then commit and push the harness, rebuild and hash `explain_corpus`, and restart
both streams from row one.  Do not reuse the failed v1 stream.  Validation and
retention remain forbidden unless the exact historical aggregate and every v2
complete-record condition pass.
