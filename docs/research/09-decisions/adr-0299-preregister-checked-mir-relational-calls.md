# ADR-0299: Preregister checked MIR relational scalar call composition

Status: proposed
Date: 2026-07-20

## Context

[ADR-0298](adr-0298-preregister-relational-scalar-call-results.md) accepts a
body-independent relational result for one checked straight-line LLVM caller.
The remaining [P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md)
checksum obligation is the MIR side. The existing MIR equality uses an inlined
fixture, so it does not yet show that a checked MIR caller can consume a callee
contract after the body is discarded.

The current MIR implementations do not provide a sound shortcut. The legacy
line executor panics on malformed input and does not parse calls. The newer
`reflect::mir::syntax` and `reflect::mir::checked` path is located,
non-panicking, and type-aware, but its semantic API requires exactly one byte
array and intentionally rejects calls. A string-level call rewrite or a call
arm in the legacy executor would bypass the strict-error property that the
Glaurung review identifies as Axeyum's strongest consumer-facing contribution.

The registered rustc source makes the boundary explicit. In
`rustc_middle::mir::TerminatorKind::Call`, operand types must match the callee,
the destination type must match the return, the destination is written only on
normal return, and a distinct unwind action handles panic. Current optimized
rustc prints the checksum caller as:

```text
bb0: {
    _3 = sum16(move _1, move _2) -> [return: bb1, unwind continue];
}

bb1: {
    _0 = Not(move _3);
    StorageDead(_3);
    return;
}
```

Consequently, inserting an arbitrary result and following `bb1` is sound only
after the selected callee has separately proved that the unwind edge is
unreachable. LLVM definedness is not a Rust panic proof. This experiment must
verify the same relational contract against a checked MIR `sum16` body and
prove its panic predicate false before discarding that body.

This is a correctness and modularity increment. It carries no speed, coverage,
or general-MIR claim.

## Decision

Preregister one opt-in, typed, acyclic scalar MIR contract route for the exact
checksum module. It reuses `ScalarCallContract` and its expression language;
no second contract AST or implicit coercion is introduced.

The implementation may land only with all of these boundaries:

1. Extend the located MIR syntax only with the source-derived scalar forms
   needed by the checked callee and caller: `Add`, unsigned `Shr`, integer
   `IntToInt` cast, unary `Not`, and an assigned direct `Call` terminator with
   scalar operands, one normal-return block, and exact `unwind continue`.
   Destination, arguments, locals, constants, casts, and return types are
   checked exactly. Bare direct identifiers only are admitted; function
   pointers, methods, generics, tuple destinations, cleanup blocks,
   `unwind unreachable`, diverging/tail calls, and call attributes remain
   rejected with located classes.
2. Add a checked scalar MIR executor over a caller-supplied `TermArena` and
   typed parameter terms. It reuses the existing typed function/block/local
   validation, acyclic/execution limits, statement semantics, switch joins, and
   explicit panic predicate. It accepts no byte arrays, memory, projections,
   references, aggregates, drops, loops, or calls by default. The existing
   checked memory API and legacy compatibility API remain unchanged.
3. A MIR contract resolver verifies one relational `ScalarCallContract`
   against an exact checked MIR callee body. Version one requires literal-true
   `requires`, immediate-definedness, and result-definedness. It proves the MIR
   body panic predicate false for every argument and proves the actual MIR
   result satisfies `ensures`. Counterexample, malformed body, type/signature
   drift, timeout, `Unknown`, or solver error fails closed. Successful
   construction stores the verified contract and no body.
4. The same logical checksum contract must be independently verified against
   the accepted LLVM body through ADR-0298. An LLVM proof does not certify MIR
   panic behavior, and a MIR proof does not certify LLVM poison/UB behavior.
   The test must expose both resolvers and compare their caller results under
   their separately produced relations.
5. The opt-in MIR caller route accepts exactly one static direct call. It checks
   the callee, scalar argument count/types, destination type, normal target, and
   total-contract restriction. It creates one deterministic internal BV result
   symbol, assigns it to the destination, conjoins the separately instantiated
   `ensures` relation, and follows the normal target. It does not add that
   relation to the caller panic predicate.
6. The result exposes the returned typed MIR value, caller panic predicate,
   combined assumptions, and ordered call metadata containing callee, exact MIR
   source span, internal result symbol, and relation. The ordinary checked
   scalar route rejects the same call. A user symbol with the same printable
   name cannot alias the internal symbol, and repeated reflection uses
   deterministic suffixes.
7. A weak verified `ensures = true` remains legal and must leave the MIR result
   genuinely arbitrary. No body result may survive resolver construction or be
   substituted at the caller. The exact LLVM and MIR havoc symbols are
   intentionally distinct; equivalence is proved from their relations, never
   by symbol identity.
8. This slice does not add general panic contracts. It admits the one total
   callee only because checked MIR body verification proves `panic = false`.
   Nontrivial callee panic conditions, caller-visible unwind/cleanup paths,
   annotations, recursion, nested/multiple calls, memory effects, loops, and
   external calls remain separate ADRs.

## Frozen evidence gates

Implementation is admitted only if one committed bundle passes every gate:

1. Freeze the exact optimized scalar `sum16` MIR body and one-call
   `cksum_pair` MIR caller produced by the registered nightly shape. Parse both
   through the checked MIR syntax with nonempty exact spans. The default scalar
   route must reject the call at its terminator span.
2. Verify ADR-0298's relation
   `Result = (a + b) + ite(bv_uaddo(a,b), 1_u16, 0_u16)` separately against the
   checked MIR and checked LLVM `sum16` bodies. Prove the MIR callee panic
   predicate is false, then discard both bodies. A MIR arithmetic/cast/shift
   mutation and a relation mutation must fail verification.
3. Reflect the modular MIR and LLVM callers with their separate resolvers.
   Prove each equals the inlined MIR and LLVM checksum for all `u16` pairs, the
   two modular callers agree under both relations, and both re-prove
   `sum16 + cksum_pair = 0xffff`. Prove caller MIR panic is false separately.
4. Extend the deterministic 100,000-input gate. For each input, assign both
   havoc results the real `sum16` value and require both relations plus all
   Rust/inlined/modular outputs to agree. Then assign a deliberately different
   result to each route and require both relations to reject it. Require exactly
   200,000 classified choices per route, nonempty carry/no-carry populations,
   zero disagreement, zero evaluation errors, and zero dropped rows.
5. Verify `ensures = true` against both exact bodies. Refute each modular caller
   against the exact inlined checksum and replay both arbitrary-result models.
   Omitting either relation must make the corresponding equality refutable.
6. Reject missing/duplicate/exact/non-total contracts; wrong callee, argument,
   destination, return target, unwind spelling, source type, cast direction,
   signed shift, multiple/nested calls, memory, cycles, undefined locals/blocks,
   symbol alias attempts, and explicit zero-resource `Unknown`. Every failure
   retains a stable class and source span; deterministic malformed input never
   panics.
7. Add every new public MIR syntax variant to the source-derived semantics
   manifest under one MIR scalar-contract group, with checksum proof,
   fuzz/replay, and refutation ownership. Add or strengthen checker mutation
   tests so an omitted variant, evidence reference, or binary fails closed.
8. Report only mechanism counts. Focused checksum/MIR tests, the standing
   semantics gate, complete `axeyum-verify` tests and doctests, strict Clippy,
   warning-denied rustdoc, formatting, links, and existing LLVM/MIR provenance
   validators must pass with one build/test job under the 4 GiB cap. Use
   `CARGO_PROFILE_TEST_DEBUG=0` for the complete package route, as registered by
   ADR-0298; a capped OOM is a failed gate, not an excuse to drop tests.

No gate may be weakened after observing implementation or test results.

## Evidence before implementation

The installed rustc source at
`compiler/rustc_middle/src/mir/syntax.rs` documents the type, destination,
normal-target, and unwind obligations above. A live `-O -Zunpretty=mir` probe
on the existing checksum source produces exactly one direct call followed by
`Not`, while optimized `sum16` contains only casts, `Add`, `BitAnd`, `Shr`, and
return. The accepted contract language already expresses the independent
one's-complement relation; the missing work is typed MIR syntax/execution and
separate MIR body verification, not a new logic feature.

## Rejected alternatives

- **Teach the legacy MIR line executor one call spelling:** rejected; it panics
  on malformed input and would weaken the strict-error correctness claim.
- **Use the LLVM-verified contract without checking MIR `sum16`:** rejected;
  LLVM definedness does not prove the MIR unwind edge unreachable.
- **Inline the MIR body while calling the route modular:** rejected; it does not
  exercise havoc or body discard.
- **Treat `ensures` as `!panic`:** rejected; a logical postcondition and Rust
  exceptional control flow are distinct channels.
- **Add general panic contracts now:** deferred. The selected callee is total;
  nontrivial panic propagation needs source-facing contract semantics and
  replayed unwind witnesses.
- **Accept `unwind unreachable` as a no-panic promise:** rejected; panic-abort
  compilation can print that edge even when a call may abort.

## Consequences

If every gate passes, the checksum module will compose body-independently on
both checked IRs, closing the runtime half of T5.2.2 and strengthening T5.2.4.
P5.2 will still require source annotation lowering, general panic-contract
composition, and their replayed violation UX before phase exit.

If MIR body verification, panic separation, havoc teeth, strict syntax, or the
resource gate fails, remove the implementation and retain ADR-0298 as the
accepted boundary.

## References

- `compiler/rustc_middle/src/mir/syntax.rs`, `TerminatorKind::Call`.
- ADR-0288, ADR-0290, and ADR-0296 through ADR-0298.
- P5.2 contracts and modular verification.
