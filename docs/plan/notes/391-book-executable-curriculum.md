# Notes: 391-book-executable-curriculum

Detail moved out of [`../status/391-book-executable-curriculum.md`](../status/391-book-executable-curriculum.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

## Archived landed-changes rows

| 2026-08-30 | `172e0982a` | Three more source-bound routes cover exhaustive width-8 addition with flags/PC, a 16-bit store/load and trapped boundary, and taken/untaken branch traces. Wrong destination, reversed bytes, and wrong target-base controls each fire independently. |
| 2026-08-30 | `ac1f4f1f9` | A0 now distinguishes verification-bound exhaustion from a caller-returned running prefix. Semantic package v3 and a replay route cover halt, trap, zero-step exhaustion, prefix return, and resumed-prefix concatenation; false halt is rejected. |
| 2026-08-30 | `560792751` | Canonical A0 encoding covers all seventeen families. An exhaustive computation checks all 41,409 legal structured instructions, unique encodings, 82,818 reserved-bit mutations, targeted unused fields, and an unknown opcode; accepting one reserved form is rejected. |
| 2026-08-30 | `0b6d9ced7` | A source-bound step route executes all seventeen families, checks seventeen exact effect rows, all four trap classes, terminal stuttering, and complete-state frame containment. An undeclared r7 write is rejected. |
| 2026-08-30 | `e2ce56353` | The step control now independently requires rejection of a hidden write, missing condition update, and wrong sequential PC; unexpected acceptance has a distinct control-failure category. |
| 2026-08-30 | `41cd92f5e` | A0 concrete addition now instantiates a domain-parametric semantic definition that can also construct symbolic terms; primitive mappings remain an explicit trust boundary. |
| 2026-08-30 | `9cf18324f` | A0 addition emits term-bound DRAT/LRAT for all eight supported fixed widths. Replay rebuilds source terms and certificates; an inverted-carry SAT witness is exhaustively found at width 8 and replayed through encoded concrete execution. |

## Archived landed-changes rows

| 2026-08-30 | `172e0982a` | Three more source-bound routes cover exhaustive width-8 addition with flags/PC, a 16-bit store/load and trapped boundary, and taken/untaken branch traces. Wrong destination, reversed bytes, and wrong target-base controls each fire independently. |
| 2026-08-30 | `ac1f4f1f9` | A0 now distinguishes verification-bound exhaustion from a caller-returned running prefix. Semantic package v3 and a replay route cover halt, trap, zero-step exhaustion, prefix return, and resumed-prefix concatenation; false halt is rejected. |
| 2026-08-30 | `560792751` | Canonical A0 encoding covers all seventeen families. An exhaustive computation checks all 41,409 legal structured instructions, unique encodings, 82,818 reserved-bit mutations, targeted unused fields, and an unknown opcode; accepting one reserved form is rejected. |
| 2026-08-30 | `0b6d9ced7` | A source-bound step route executes all seventeen families, checks seventeen exact effect rows, all four trap classes, terminal stuttering, and complete-state frame containment. An undeclared r7 write is rejected. |
| 2026-08-30 | `e2ce56353` | The step control now independently requires rejection of a hidden write, missing condition update, and wrong sequential PC; unexpected acceptance has a distinct control-failure category. |
| 2026-08-30 | `41cd92f5e` | A0 concrete addition now instantiates a domain-parametric semantic definition that can also construct symbolic terms; primitive mappings remain an explicit trust boundary. |
| 2026-08-30 | `9cf18324f` | A0 addition emits term-bound DRAT/LRAT for all eight supported fixed widths. Replay rebuilds source terms and certificates; an inverted-carry SAT witness is exhaustively found at width 8 and replayed through encoded concrete execution. |
| 2026-08-30 | `63fbf51d7` | Explicit A0 zero/sign extension and truncation plus a source-bound report over 65,822 words and 2,106,910 operation checks. A signed-zero-extension mutation fires; the semantic package advances to v7. |
