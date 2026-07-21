# ADR-0319: Preregister checked MIR lexical-scope metadata

Status: proposed
Date: 2026-07-21

## Context

ADR-0318's owning-Cargo page-table capture failed before artifact retention at
`scope 1 {`. The registered compiler places named-local declarations inside
nested lexical scope blocks:

```text
scope 1 {
    debug level1 => _3;
    let _8: usize;
    scope 2 {
        debug level2 => _8;
    }
}
```

These blocks are not executable CFG nodes, but their `let` declarations are
required to type later statements. The current parser accepts function-level
locals and ignores recognized `debug` declarations, yet owns no nested scope
grammar. Ignoring the whole block would drop types; treating it as execution
would fabricate semantics.

## Proposed decision

Extend only `reflect::mir::syntax` function-body metadata parsing. Admit a
bare `scope <decimal> {` header, balanced nesting, recognized `debug` lines,
ordinary admitted `let _N: TYPE;` declarations, and nested bare scopes. Flatten
the local declarations into the function's existing ordered local inventory.
Scope IDs and debug names do not enter checked execution or public semantic
terms.

Reject every other item inside a scope: basic blocks, assignments, storage
markers, terminators, attributes, promoted/inlined scope suffixes, nondecimal
IDs, trailing tokens, and malformed braces. Apply an explicit nesting cap of
64. Existing global duplicate-local checks include declarations across the
function root and every nested scope.

No MIR type, statement, rvalue, terminator, checked-memory rule, IR operator,
solver route, or public result structure changes. The parser continues to
select one named function and ignores unrelated unsupported functions.

## Frozen evidence gates

1. Commit this ADR before parser, fixture, capture, or test changes.
2. A focused exact-source parser test accepts root locals plus two nested scope
   levels, preserves deterministic declaration order/types/spans, and produces
   unchanged checked terms when scope/debug metadata is removed but the same
   locals remain at function root.
3. Empty scopes and debug-only scopes are accepted. The 64-level boundary is
   accepted; 65 levels, missing/extra braces, malformed IDs/headers, trailing
   tokens, executable content, blocks, and declarations after an unterminated
   child fail with stable located classes and never panic.
4. Duplicate locals across root/sibling/nested scopes and unsupported types
   keep the existing precise duplicate/type classes. Scope flattening cannot
   shadow or silently replace a local.
5. Deterministic structured-noise tests cover the new header prefix without
   hangs, recursion overflow, or nondeterministic diagnostics.
6. The exact ADR-0318 fixture functions then pass syntax selection through the
   existing checked-memory profile without another parser/semantic widening.
   If any later form fails, ADR-0319 stops there; it does not authorize reactive
   expansion.
7. Existing authenticated MIR fixtures and their parsed projections/terms are
   byte- and behavior-unchanged. The 81-variant semantics inventory remains
   unchanged because no executable variant is added.
8. Focused parser/checked-memory tests, complete `axeyum-verify` and doctests,
   strict Clippy/rustdoc, reflection semantics gate, formatting, links, and the
   one-job 4 GiB/OOM audit pass.

## Rejected alternatives

- **Ignore entire scope blocks.** Unsound: local types inside them are needed.
- **Preserve lexical scopes in checked execution.** Unnecessary: rustc lexical
  debug scope does not alter MIR CFG semantics.
- **Accept arbitrary brace blocks.** Rejected: it could hide executable or
  unsupported compiler forms.
- **Rewrite source to avoid named locals.** Rejected by ADR-0318's frozen
  negative result and contrary to real-source reflection.

## Consequences

- A positive result owns one compiler metadata grammar and unblocks a fresh,
  separately gated ADR-0318 successor.
- It does not itself admit or prove the page-table obligation.

## References

- ADR-0288: checked MIR byte-memory syntax and semantics.
- ADR-0318: rejected page-table capture selecting this boundary.
- `crates/axeyum-verify/src/reflect/mir/syntax.rs`.
