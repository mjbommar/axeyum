# ADR-0585: Multi-source SIMD synthesis uses SSA live values

Status: accepted
Date: 2026-08-26

## Context

ADR-0566's complete bounded AVX2 search was unary: each instruction consumed only the
immediately preceding value. ADR-0583 deliberately retained that restriction while adding a
generic weighted-CNF objective. Blends, unpacks, two-source aligns, and two-source half
permutations require explicit access to more than one earlier value. Treating those operations
as unary would either exclude real programs or silently give them false semantics.

This decision closes the next SIMD boundary recorded in the open-problems programme. It does
not close the broad SIMD-minimality problem.

## Decision

Bounded multi-source SIMD synthesis represents the original input and every instruction result
as immutable SSA live values. Instruction `i` may select the input or any result before `i` as
each operand; the last result is the program output. Models lift to typed instructions and must
replay through a separate semantic evaluator before receiving SAT credit.

The first exact AVX2 language has fourteen family selectors:

1. lane-local `vpshufb`;
2. `vpermd`;
3. `vpermq`;
4. two-source lane-local `vpalignr`, immediate 0 through 16;
5. two-source `vperm2i128` with four nonzero half choices per destination half;
6. low and high unpack at byte, word, dword, and qword widths (eight families); and
7. `vpblendd`.

Controls are compile-time constants and do not count as separate instructions. Every state
byte is a one-hot choice among the 32 original provenance tags. Intermediate states may
duplicate or discard tags: separate SSA branches can later be recombined.

Zero-producing `vpshufb` and `vperm2i128` controls are omitted only because the public encoder
accepts permutation targets. This is complete for those targets. If a zero reaches the final
result, it cannot match a provenance tag. Otherwise replace that zero by any input tag; all
downstream selected bytes remain unchanged. Repeating this replacement from the first zeroing
step to the last normalizes any successful program into the retained nonzero-control language.

## Evidence

The reusable encoder is deterministic and resource bounded. Tests pin a genuinely two-source
unpack program, solve it, lift the model, and replay the typed program. Forward SSA references
and invalid align immediates fail closed.

An independent C intrinsic oracle covers two-source align, two-source half permutation, all
eight unpack modes, and dword blend: 11 modes times 32 output bytes agree with GCC 15.2.0 AVX2
execution. Changing the expected align shift from 12 to 11 is rejected at byte zero.

For global 32-byte reversal, the complete one-step query contains 2,697 variables and 97,314
clauses. CaDiCaL 3.0.1 seed 1223 emits a 1,922,088-byte textual DRAT refutation. Axeyum's
file-backed backward checker accepts it and rejects a two-byte truncation. The two-step query
contains 4,372 variables and 239,078 clauses; its model lifts and replays as lane-local
`vpshufb` reversal followed by a two-source `vperm2i128` lane exchange. Thus length two is
minimal in this exact language and SSA model.

Compatibility is evidence, not assumption: regenerating ADR-0566's unary one-step formula
remains byte-identical at SHA-256
`7da5e2668087334e73d7415e89fadee2e977d2e2937d6b263d2d4ad456cc88ec`.

A literature refresh through 2026-08-26 rechecked HieraSynth, Minotaur, MISAAL, LLVM's known
two-operation AVX2 reverse, arXiv, and exact web/Scholar-style queries. HieraSynth already
establishes optimal vector programs broadly, and LLVM records the two-operation upper bound.
No located source contains this exact language and portable lower-bound artifact, but negative
retrieval cannot prove novelty. No priority claim is made.

## Alternatives

A destructive accumulator with only the previous result was rejected because it cannot express
live branches. Encoding physical registers was deferred because register allocation is not part
of a pure instruction-count theorem. Whole-ISA enumeration was rejected as an undefined claim:
memory, insert/extract, logic-based composition, variable control construction, and other AVX2
families are not represented.

## Consequences

Axeyum can now express complete bounded multi-source selector programs with independently
replayable witnesses and checked UNSAT lower bounds. The result is still not a throughput,
latency, scheduling, register-pressure, memory, or whole-ISA theorem. The next extension must
either add a named missing family with the same hardware differential discipline or add an
explicit dependency/register scheduler; neither may silently widen this result's scope.
