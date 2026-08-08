# QF_UFLIA A4 provenance census v1 result

Date: 2026-08-07

## Verdict

**V1 failed its complete-record gate and receives no census credit.**  The
single Axeyum stream visited all 200 frozen-list rows, but row 1 was a typed
SMT-LIB `Unsupported` outcome rendered by `explain_corpus` as generic
`status="parse-error"`.  V1 required every row to be `decided` with a schema-1
dispatch trace, so the wrapper rejected the stream after completion.  It did
not publish raw data or metadata, cvc5 was not run, no sidecar or residual was
derived, and no solver mechanism was selected.

This is a measurement-front-door defect, not a wrong solver verdict.  The
shipped `smtcomp_cli` maps parse/solver errors to first-class `unknown`, and the
parser deliberately classifies the valid wide literal as `SmtError::Unsupported`
rather than malformed syntax.

## Exact boundary and observation

| Item | Value |
|---|---|
| Frozen source/harness commit | `2cd32ae1e65d661f5b7d06ce6f1403cc2cf86c95` |
| Upstream equality before capture | exact |
| Frozen list | `bench-results/parity-lists/QF_UFLIA.txt` |
| List SHA-256 / rows | `f88e67890fae78fb27bb35ecc0f19532dc3bc77fd7f1ac7453fcda343b36fb35` / 200 |
| Release `explain_corpus` SHA-256 | `b4c55749c5cfd25c89422f3e3251cd083563d84d2cac6ab30c3c7aeed78ad77e` |
| Release binary size | 11,697,064 bytes |
| Protocol | shipped default, 24,000 ms/query, 8 GiB process cap, one serialized stream |
| Start load | `7.96 5.26 6.43` on 24 cores |
| Live process evidence | all 200 rows emitted in about 38 minutes; RSS peaked near 355 MiB and later fell near 135 MiB; stderr stayed empty |
| First rejected row | `.../11775_ad46e5b8db4748c51973_42_QF_UFLIA.smt2` |
| Detail | `unsupported: integer literal \`115792089237316195423570985008687907853269984665640564039457584007913129639935\` exceeds the modeled \`Int\` range` |

The wrapper correctly withheld its final output, but it also deleted the failed
temporary stream and therefore could not retain terminal failure metadata.  V2
must keep a bounded failure record outside the repository while continuing to
grant it zero measurement credit.

## Scope of the gap

Frozen-list rows 1--26 are all from
`QF_UFLIA/20230314-Jaroslav-Bendik-Certora/` and all contain EVM-scale integer
literals outside `i128`.  An independent directory-mode diagnostic parsed all
76 files in that source family and deterministically returned the same typed
wide-integer `Unsupported` class for every file.  The frozen population contains
26 of them; no other family path occurs before row 27.

This exact issue is already decided by
[ADR-0376](../research/09-decisions/adr-0376-integer-literals-wider-than-i128.md).
Its controlled evidence found that cvc5 decided only six of the 26 residual
files and that removing every wide-literal assertion still left all six
unknown.  Widening `IntConst`/`Value::Int` would therefore touch hundreds of
core sites for zero solved-file gain.  The binding constraint is the downstream
QF_UFLIA decision procedure, not representation.

## Consequence

V1's assumption that all 200 rows could enter solver dispatch was false.  V2
will preserve the honest terminal boundary instead of fabricating a dispatch
trace: the exact wide-integer `Unsupported` subtype becomes a typed
`smtlib-ingest` unknown provenance record.  Generic syntax/parse errors remain
fatal.  These 26 rows enter the complete census but are ineligible for mechanism
selection under ADR-0376; selection operates only on the remaining validated
reference-only dispatch rows.

No production code, solver configuration, route order, cap, or retained parity
claim changed in v1.
