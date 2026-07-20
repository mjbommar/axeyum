# ADR-0284: Preregister canonical scalar LLVM CFG rendering

Status: proposed
Date: 2026-07-19

Result state: preregistered; implementation has not started

## Context

ADR-0280 through ADR-0283 now provide a fail-closed path from one textual LLVM
function through typed scalar instructions, validated control flow, and checked
acyclic execution. T5.1.2's remaining syntax-level exit criterion is still
missing: the supported structure cannot be printed canonically and therefore
has no parse -> print -> parse reproducibility gate.

That missing boundary also exposes a correctness defect in the current lexer.
LLVM quoted identifiers use two-hex-digit byte escapes such as `\22` and `\5C`.
The current lexer instead consumes one character after a backslash, so it can
silently change a compiler-provided identifier. This is exactly the class of
strict translation defect that Axeyum must reject or normalize visibly rather
than pass downstream under a different identity.

This slice closes canonical syntax and identifier identity only. It does not
broaden executable semantics or create a shared parser crate.

## Decision

Add one public canonical renderer:

```text
render_scalar_cfg(&ScalarCfg) -> String
```

The result is deterministic UTF-8 LLVM text for the already validated scalar
CFG. Rendering is infallible because every source object has passed the typed
parser; the function does not accept raw or partially parsed input.

The canonical form:

- emits one `define` with the scalar return width, ordered parameters, and
  ordered blocks;
- preserves an unlabeled entry block as unlabeled and quotes every explicit
  function, local, and block identity through one codec;
- emits every supported binary opcode, semantic flag, comparison predicate,
  select, cast, min/max intrinsic, PHI, branch, switch, return, and
  `unreachable` from its typed enum rather than retained source text;
- preserves instruction/PHI/case order and terminator metadata order;
- prints switch constants in their normalized unsigned representation;
- omits non-semantic source whitespace, comments, parameter attributes, call
  modifiers, and source spans; and
- ends with exactly one newline.

Canonical output need not reproduce source bytes. It must reproduce the typed
semantic structure and must be idempotent: parsing and rendering a rendered CFG
produces byte-identical output.

Replace the quoted-name lexer with the LLVM byte-escape rule. A backslash must
be followed by exactly two hexadecimal digits. Decode escaped and unescaped
bytes first, then require valid UTF-8 for Axeyum's current `String`-backed name
model. Add a stable located `ParseErrorKind::MalformedIdentifierEscape` for a
truncated, non-hex, or non-UTF-8 decoded name. The renderer leaves safe printable
ASCII bytes literal except `"` and `\`; those and every control/non-ASCII byte
are emitted as uppercase `\XX` byte escapes. This makes the codec injective for
the admitted UTF-8 names.

The typed structure remains authoritative. Retained source text is not used to
print operations, and malformed identifier escapes never receive a lossy
replacement. Strict sort/width errors and checked definedness are unchanged.

## Acceptance gates

Tests begin red and then require:

1. every supported opcode, flag, predicate, cast, intrinsic, PHI, terminator,
   metadata attachment, and switch case renders and reparses;
2. canonical render -> parse -> render is byte-identical for the unmodified
   clang 21 and rustc 1.97 division diamonds and every supported cross-IR LLVM
   fixture;
3. a span-free typed projection of each original CFG equals the reparsed CFG,
   including ordered names, operands, metadata, predecessors, and successors;
4. LLVM identifier escapes for quote, backslash, space, control bytes, and
   multi-byte UTF-8 round-trip through function/local/block identities;
5. truncated, non-hex, and decoded-invalid-UTF-8 escapes return the new stable
   located error kind without panicking or changing the identifier;
6. negative instruction constants remain exact, while normalized negative
   switch cases print their width-correct unsigned value and stay equivalent;
7. checked reflection of an original and canonicalized total CFG proves equal
   values and definedness; the unreachable-default fixture proves equal
   definedness and value equality under its existing range hypothesis;
8. canonical metadata-free compiler diamonds are accepted by the installed
   `llvm-as` when it is available; absence of that optional external tool is
   reported as a skip rather than fabricated success;
9. deterministic structured-name and graph noise cannot panic parsing, and
   every successfully parsed CFG renders deterministically; and
10. the complete `axeyum-verify --all-features` suite, workspace formatting,
    strict Clippy, strict rustdoc, and documentation link checker remain green.

The gates may become stricter before implementation observes a new fixture or
corpus. They may not be weakened after a failure.

## Consequences

The supported LLVM slice gains a reproducible, inspectable serialization and a
precise identifier identity boundary. Future memory, loop, call, or module-wide
work can use that canonical artifact in differential and fixture-drift gates
without inheriting source formatting or silently changing names.

The renderer is not a general LLVM pretty-printer. It does not preserve
attributes or comments, resolve metadata definitions, emit intrinsic
declarations, print modules, or make unsupported input supported. Memory,
`freeze`/`undef`, calls beyond the two typed intrinsics, loops, LLIR hardening,
and Glaurung lowering remain separate preregistered increments.

## References

- [LLVM Language Reference](https://llvm.org/docs/LangRef.html), identifiers and
  lexical structure.
- T5.1.2 in the Track 5 reflection plan.
- ADR-0279 through ADR-0283.

## Alternatives

- Reprint retained instruction strings: rejected because it does not test the
  typed representation and can preserve syntax the typed model did not own.
- Preserve source bytes exactly: rejected because this is a canonical semantic
  representation, not a lossless concrete-syntax tree.
- Keep the one-character escape rule: rejected because it silently changes
  legal LLVM identities.
- Add memory or Glaurung lowering in the same increment: deferred because
  neither is needed to close the current scalar syntax reproducibility gate.
