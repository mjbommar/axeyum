# Lane: book-executable-curriculum — executable ISA textbook semantics and evidence

<!-- plan-section: lane-status -->

**Executable curriculum (`WIP`, book-executable-curriculum, 2026-08-30).**
Build the semantic and evidence layers required by *Instruction Sets,
Programs, and Proofs*. The first slice adds the `axeyum-machine` boundary and
complete A0 concrete execution. The reusable word layer exposes and audits
explicit extension and truncation, complete states have a canonical binary
artifact codec, and the source-derived symbolic memory-frame route covers all
eight supported widths. Next: independently pinned RV64I and x86-64 teaching
slices, broader semantic relations, manifests, the remaining Python machine
projection, and clean-checkout book gates. The PyO3 layer now projects the
complete A0 word, state, memory, instruction, step, and trace surface. The
source-pinned RV64I slice now has a complete reader-facing single-step Python
projection; x86-64, real-ISA bounded traces, and cross-machine relations remain.
A0 addition has fixed-width symbolic certificates;
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
| 2026-08-30 | `f267f50b5` | Extend the source-bound memory report with wrapped sparse addresses, stored bytes, missing-address trap, and complete-map preservation. |
| 2026-08-30 | `29c7ab0fd` | Advance the widened sparse-memory evidence contract to schema v2 so the old dense and new sparse report shapes cannot share one schema identity. |
| 2026-08-30 | `cfa215a12` | Derive concrete and symbolic A0 loads/stores from one domain-parametric orchestration; certify arbitrary-address frame laws at all eight widths through checked array elimination plus DRAT/LRAT, with a satisfiable and concretely replayed partial-store mutation. Semantic package v10. |
| 2026-08-30 | `65eba9118` | Add the source-pinned twelve-form RV64I decoder, encoder, complete step profile, and canonical refinement projection. Seven tests bind official source identity, book bytes, XOR table, x0, control, memory, traps, and projection; book evidence remains pending. |
| 2026-08-30 | `eac21f4d4` | Add replayable RV64I source-pin and decoder/step reports. The route executes all twelve selected forms, all nine XOR words, five trap classes, and three semantic mutations; source-digest and branch-base controls fail closed. Book manifests remain pending. |
| 2026-08-30 | `3c5d2cafb` | Add the source-pinned seventeen-form x86-64 decoder, encoder, complete step profile, flags, memory and implicit stack control, plus canonical projection. Eight tests execute all six manuscript listings; book evidence remains pending. |
| 2026-08-30 | `5ad3bbfcd` | Add replayable x86-64 source-pin and decoder/step reports. Six manuscript programs execute across all seventeen forms; three trap classes and four semantic mutations are checked; source-digest and following-RIP branch-base controls fail closed. Book manifests remain pending. |
| 2026-08-30 | `d75cd25bf` | Begin the faithful PyO3 machine projection with A0 words, dotted imports, generated stubs, and runtime/static-type controls. The focused surface passes; the aggregate Python suite separately exposes one stale agent fixture and a deterministic prelude-build segfault that remain full-gate blockers. |
| 2026-08-30 | `055536b5b` | Repair the deterministic Python prelude segfault by moving the grown CReal and Complex builders to the existing bounded deep-stack boundary; replace the stale fixed retrieval-miss fact with a derived live control. The full suite now completes (1,846 passed, 34 skipped) and exposes nine separate knowledge/autogenesis drift failures on the superseded pre-rebase snapshot. |
| 2026-08-30 | `4e93f9d62` | Complete the reader-facing A0 Python surface: memory, state codec, all seventeen typed instruction families, step, bounded traces, categorized traps, generated stubs, and thirteen direct reader controls. Rust, runtime/stub, static-type, lint, and formatting gates pass; RV64, x86-64, cross-machine, and book bindings remain open. |
| 2026-08-30 | `4548f3dda` | Move reader-facing A0 error formatting outside the source-pinned semantic file. The exact v10 digest is restored without relabeling message-only changes as new semantics; all sixteen book routes replay successfully again. |
| 2026-08-30 | `3884b8d04` | Project the complete source-pinned twelve-form RV64I single-step slice through Python: typed instructions, canonical encoding, complete state, traps, memory, projection, source identity, generated stubs, and reader controls. Bounded RV64 traces and cross-machine interfaces remain open. |
