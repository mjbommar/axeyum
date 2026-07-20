# ADR-0280: Preregister the first structured LLVM function-parser slice

Status: accepted
Date: 2026-07-19

Result state: accepted; implementation and compatibility migration complete

## Context

ADR-0279 selects P5.1/T5.1.2's structured textual LLVM parser as the next
reusable prerequisite. The current `reflect::llvm` implementation repeatedly
splits lines and whitespace and documents panics for malformed or unsupported
input. Replacing all instruction semantics at once would mix syntax, lowering,
and LLVM-semantic changes and would make regressions difficult to localize.

The first slice must establish a non-panicking syntax boundary and migrate one
real consumer without claiming that the complete `.ll` grammar is implemented.

## Decision

Add `reflect::llvm::syntax` with an owned, deterministic representation of one
textual LLVM function:

- a function name and source span;
- ordered typed/named parameters and spans;
- ordered labeled or unlabeled-entry blocks; and
- ordered instruction text with byte, line, and column spans.

Expose `parse_function(&str) -> Result<Function, ParseError>`. The parser uses a
small lexer for names (including quoted LLVM names), words, integers, strings,
and punctuation. Delimiter-aware parameter parsing must not split commas inside
attribute/type parentheses. Module comments, declarations, attributes, metadata,
and target lines outside the selected definition are ignored, but exactly one
`define` body is required.

Return structured error kinds for at least missing definition, multiple
definitions, malformed header/name/parameter, unterminated quoted token,
unbalanced delimiter/body, and duplicate block label. Every error carries a
source span and implements `Display`/`Error`.

Migrate `llvm::param_decls` through this parser while preserving its existing
signature and panic-on-invalid compatibility contract. Do not yet migrate
instruction lowering, add an LLVM opcode, change poison/UB semantics, accept a
kernel module, or create a new crate.

## Acceptance gates

Tests begin red and then require:

1. a compiler-shaped function with attributes, nested parameter attributes,
   quoted names, a labeled CFG, and comments parses with exact ordered fields;
2. an unlabeled single block receives no invented source label;
3. malformed inputs return the declared error kind and a nonempty, in-range
   source span rather than panicking;
4. duplicate labels and multiple definitions fail closed;
5. parse output is deterministic across repeated calls;
6. existing `param_decls` cases and all LLVM reflection/cross-IR suites remain
   unchanged and green; and
7. focused strict Clippy and rustdoc pass.

The implementation may add narrower negative cases discovered before any
external corpus observation, but it may not weaken these gates in response to
failures.

## Consequences

This slice creates the diagnostic seam T5.1.2 needs without pretending that
raw instruction strings are already a full syntax tree. Subsequent slices can
replace those strings one instruction family at a time and route checked
reflection APIs through `Result`. Existing callers retain behavior until that
migration is separately admitted.

## Observed result

The accepted implementation adds the frozen `reflect::llvm::syntax` boundary
and migrates `param_decls` without changing its compatibility signature. The
compiler-shaped, unlabeled-entry, malformed-input, duplicate-label,
multiple-definition, determinism, and source-span gates pass. An additional
fail-closed header case prevents a global call in the body from being mistaken
for a missing function name, and 4,096 deterministic ASCII-noise inputs confirm
that the public parser returns rather than panicking.

All five parser tests and the complete `axeyum-verify --all-features` suite
pass. Focused formatting, strict all-target/all-feature Clippy with
`-D warnings`, and rustdoc with `-D warnings` also pass. Instruction records
remain source text by design; typed instruction syntax and checked-reflection
migration require a separately preregistered follow-up slice.

## Alternatives

- Replace the whole reflector in one change: rejected because syntax and
  semantics failures would be conflated.
- Keep panics and only improve messages: rejected because a future Glaurung
  consumer needs typed unsupported accounting.
- Add a parser dependency or shared crate now: deferred until the implemented
  grammar and second consumer prove those boundaries.
