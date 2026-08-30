# Lane: book-executable-curriculum — executable ISA textbook semantics and evidence

<!-- plan-section: lane-status -->

**Executable curriculum (`WIP`, book-executable-curriculum, 2026-08-30).**
Build the semantic and evidence layers required by *Instruction Sets,
Programs, and Proofs*. The first slice adds the `axeyum-machine` boundary and
complete A0 concrete execution. The reusable word layer exposes and audits
explicit extension and truncation, and complete states now have a canonical
binary artifact codec. Next: the A0 symbolic memory-frame theorem, then independently pinned RV64I and
x86-64 teaching slices, broader semantic relations, manifests, Python
projection, and clean-checkout book gates. A0 addition has fixed-width symbolic certificates;
do not generalize them into an arbitrary-width theorem. Do not describe future
interfaces as implemented until those routes run and their controls fire.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `9b0ba431c` | ADR-0811 and the first `axeyum-machine` A0 word/state/memory/decode/step/run slice. Seventeen direct tests cover every opcode family and branch predicate, exhaustive 8-bit arithmetic flags, modular code wrap, traps, byte order, terminal stuttering, and negative controls. |
| 2026-08-30 | `5e8f4dabb` | `axeyum-machine-evidence` binds the compiled A0 semantic-source digest and emits/recomputes the first finite computation report: all 65,792 8- and 16-bit byte round trips. Reversed byte order and source-digest mutation controls fire with categorized mismatches. |
| 2026-08-30 | `b2b72f777` | Canonical A0 observations and complete dynamic instruction footprints expose selected state, implicit effects, effective memory ranges, and aliased operands. The audit also repaired `halt` incorrectly advancing PC; 19 focused tests now cover the transition and selection controls. |
| 2026-08-30 | `361a733ce` | Semantic package v2 declares the bound A0 surfaces. A trace-class observation artifact recomputes a narrow agreement and broad r3 separation over two complete states; omitting requested r3 fires `semantic-mismatch`. |
| 2026-08-30 | `172e0982a` | Three more source-bound routes cover exhaustive width-8 addition with flags/PC, a 16-bit store/load and trapped boundary, and taken/untaken branch traces. Wrong destination, reversed bytes, and wrong target-base controls each fire independently. |
| 2026-08-30 | `ac1f4f1f9` | A0 now distinguishes verification-bound exhaustion from a caller-returned running prefix. Semantic package v3 and a replay route cover halt, trap, zero-step exhaustion, prefix return, and resumed-prefix concatenation; false halt is rejected. |
| 2026-08-30 | `560792751` | Canonical A0 encoding covers all seventeen families. An exhaustive computation checks all 41,409 legal structured instructions, unique encodings, 82,818 reserved-bit mutations, targeted unused fields, and an unknown opcode; accepting one reserved form is rejected. |
| 2026-08-30 | `0b6d9ced7` | A source-bound step route executes all seventeen families, checks seventeen exact effect rows, all four trap classes, terminal stuttering, and complete-state frame containment. An undeclared r7 write is rejected. |
| 2026-08-30 | `e2ce56353` | The step control now independently requires rejection of a hidden write, missing condition update, and wrong sequential PC; unexpected acceptance has a distinct control-failure category. |
| 2026-08-30 | `41cd92f5e` | A0 concrete addition now instantiates a domain-parametric semantic definition that can also construct symbolic terms; primitive mappings remain an explicit trust boundary. |
| 2026-08-30 | `9cf18324f` | A0 addition emits term-bound DRAT/LRAT for all eight supported fixed widths. Replay rebuilds source terms and certificates; an inverted-carry SAT witness is exhaustively found at width 8 and replayed through encoded concrete execution. |
| 2026-08-30 | `63fbf51d7` | Explicit A0 zero/sign extension and truncation plus a source-bound report over 65,822 words and 2,106,910 operation checks. A signed-zero-extension mutation fires; the semantic package advances to v7. |
| 2026-08-30 | `70dfcf3d6` | Canonical complete-state binary codec across all widths and outcome/trap forms; ten malformed encodings rejected, with a trailing-byte acceptance control. The semantic package advances to v8. |
| 2026-08-30 | `0a68b7ec2` | Replace the dense memory shortcut with a canonical sparse finite map, modular wrapped range checks, atomic trapped stores, and address-bound state serialization. The semantic package advances to v9. |
