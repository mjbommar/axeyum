# ADR-0184: Correct Glaurung wide-assertion exports

Status: accepted
Date: 2026-07-16

## Context

Glaurung's native Z3 and Axeyum backends already implement `Assert` as
arbitrary-width bit-vector truthiness: expected true means nonzero and expected
false means zero at the expression's actual width. The shared SMT-LIB/capture
producer instead compared every asserted term with a BV1 literal, and the
ordered trace rejected non-BV1 assertion roots. A real SurfacePen trace failed
at event 53 on a 64-bit assertion. The defect is the likely source of the 2,225
scripts previously classified as ill-sorted during GQ1 ingestion.

## Decision

Accept the downstream producer correction in Glaurung `fcc2de5`. One shared
renderer now emits `distinct(term, 0@width)` for expected true and
`term = 0@width` for expected false. Query dumps and ordered assertion artifacts
use that renderer; trace events carry positive `assertion_width`; the independent
validator checks it. Keep Axeyum's strict sort checking unchanged.

## Evidence

Native Axeyum, native Z3, the external SMT-LIB pipe, Axeyum's SMT-LIB text
bridge, and ordered-trace validation all pass both truthiness polarities at
width 64. The corrected real SurfacePen trace validates 12,574 events, 373
paths, 2,551 checks, 340 distinct assertions, and 2,078 distinct queries.
Focused gates pass: pipe 6/6, ordered trace 2/2, Axeyum backend 26/26, release
build, Python validator lint/format, and default Clippy subject to Glaurung's
pre-existing warning debt.

## Consequences

The previous GQ1/GQ10 query-byte identity is stale. Even BV1 expected-true
assertions change from equality-to-one to the equivalent nonzero form, and
formerly wide malformed dumps become well-sorted. Regenerate the raw capture,
strict corpus, manifests, excluded-hash accounting, and benchmark baselines
before making another cold-corpus claim. Warm native verdict/work counts remain
a separate semantic control and must still be rerun rather than assumed.

## Alternatives

Weakening Axeyum's sort checker was rejected because it would conceal a
producer defect. Restricting Glaurung `Assert` to BV1 was rejected because real
concretization callers already use native wide truthiness. Extending a BV1
literal was rejected because equality to one is not wide truthiness.
