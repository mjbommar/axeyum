# ADR-0317: Preregister an authenticated source-contract to checked-MIR bridge

Status: accepted
Date: 2026-07-21

## Context

ADR-0316 accepts the first source-local `requires` / `ensures` surface. It
retains a typed result, checks the contract against the macro's restricted Rust
AST, and gives postcondition violations an honest normally returning replay.
It deliberately emits no modular summary and makes no source-to-MIR identity
claim.

ADR-0299 and ADR-0315 accept the other half of the intended composition rule.
`MirVerifiedContractResolver` verifies a typed `ScalarCallContract` against one
checked MIR body, proves its panic and normal-result channels, discards the
body, and lets a caller consume only the verified summary. Those accepted tests
construct the contract by hand and use embedded MIR text. They therefore do not
show that a source annotation produced the summary or that the body came from
the annotated function's owning Cargo build.

The missing boundary is a binding problem, not a new logic problem. A source
contract must lower into the existing strict contract AST, and that exact AST
must be independently checked against compiler MIR selected from the same
source. Annotation text, a matching function name, a hand-copied MIR string, or
an LLVM definedness proof is insufficient by itself.

The current MIR call route also has an explicit limitation: it accepts only
literal-true `requires`. Bridging ADR-0316's checked-increment example would
silently expand that runtime rule because its precondition excludes overflow.
The first authenticated bridge must instead use a total function already
expressible by both accepted surfaces.

## Proposed decision

Preregister one total, scalar, source-to-MIR experiment:

```rust
#[axeyum_verify::verify]
#[axeyum_verify::requires(true)]
#[axeyum_verify::ensures(|result| result == x.wrapping_add(1))]
pub fn wrapping_inc(x: u8) -> u8 {
    x.wrapping_add(1)
}
```

The implementation may land only with the following boundaries.

1. Add one namespaced source-contract bridge under `axeyum_verify::reflect`.
   It consumes the typed `ContractProgram`; it does not reparse attribute text
   or introduce a second expression language. The first admitted source shape
   is one `u8` parameter, one `u8` retained result, no prefix statements,
   literal-true `requires`, a panic-free wrapping expression, and a Boolean
   `ensures` over that result and parameter.
2. The bridge first runs the accepted source-contract verifier and requires a
   certificate-rechecked `Verified` result. `Counterexample`, `Unknown`, an
   invalid/partial specification, or a lowering failure rejects summary
   construction. It then translates only the exact typed nodes required by the
   frozen function and already represented by `ScalarContractExpr`: the sole
   parameter, the retained result binding, fitting `u8` constants, literal
   `true`, strict equality, and `wrapping_add`. Every other source node,
   including checked arithmetic and currently unmatched overflow forms, is
   rejected rather than approximated. Later table-driven expansion requires a
   separate measured gate.
3. The emitted declaration is the existing relational `ScalarCallContract`:
   identical name and widths, literal-true `requires`, immediate/result
   definedness true, panic predicate false, and `ensures` translated without
   coercion. No body term, source AST, compiler term, or concrete return value
   may survive into caller resolution.
4. Extend `axeyum-mir-build` with one typed capture profile rather than another
   Boolean. The existing checked-memory profile and its v1 summary remain
   byte-compatible by default. The opt-in scalar-contract profile must select
   the same explicit manifest/package/target/function/compiler/width tuple,
   pass raw stdout through the located checked scalar parser/reflector, and
   retain it only after the selected function yields typed result and panic
   terms. It emits a distinct versioned summary; it does not verify or trust a
   source contract. That summary must replace caller-specific absolute
   manifest/target/output/executable roots with code-owned typed placeholders
   while retaining the complete ordered logical argument projection and exact
   Cargo/rustc identities. Raw compiler stdout is never normalized.
   The registered compiler spells `u8::wrapping_add` as the exact direct MIR
   intrinsic `core::num::<impl u8>::wrapping_add`. The scalar checker may lower
   only that two-`u8`/`u8` spelling to existing BV addition; it remains outside
   relational call inventory, and every other qualified call stays rejected.
5. Add one excluded, locked fixture Cargo package whose `src/lib.rs` contains
   the exact annotated function above and depends on the local
   `axeyum-verify`. The evidence test includes those same registered source
   bytes so the generated `ContractProgram` and the Cargo-built function do not
   come from duplicated source. Retain the raw MIR, capture summary, exact
   source/raw/summary SHA-256 identities, Cargo/rustc identities, and ordered
   arguments. Stable CI checks all committed bytes; the pinned-nightly route
   must reproduce them byte-for-byte.
6. Feed the generated `ScalarCallContract` and authenticated selected MIR into
   `MirVerifiedContractResolver`. Resolver construction remains the authority
   that proves body panic is false and the result relation holds before body
   discard. The bridge cannot infer acceptance from matching names, hashes, or
   source verification alone.
7. Freeze a hand-built `ScalarCallContract` for the same function. The
   generated and hand-built declarations must be structurally equal before
   either body check. Their independently constructed resolvers must produce
   the same modular caller result/panic/assumption formulas and match an
   independently inlined specification over every `u8` input.
8. Version one adds no source calls, branches, loops, arrays, signed values,
   nontrivial requirements, partial/panicking functions, cleanup behavior,
   memory/effects, recursion, general MIR places, LLVM contract generation, or
   new IR/contract operators. ADR-0315's hand-built panic contract remains the
   accepted runtime rule; source binding for that rule is a later experiment.

## Frozen evidence gates

Implementation is admitted only if one committed bundle passes every gate.

1. Commit this zero-row ADR before adding bridge, profile, fixture, or capture
   code. Record the exact preimplementation source/MIR/contract capability
   audit in PLAN/STATUS.
2. The annotated `wrapping_inc` verifies source-locally with certificate
   recheck. Mutating `ensures` to equality with `x`, changing the body increment
   to two, or making the postcondition partial must reject the bridge with a
   stable typed class; no mutation may become an accepted summary.
3. The generated contract is exactly equal to the hand-built declaration.
   Change each translated leaf/operator, parameter/result binding, width,
   signedness, name, or literal-true requirement independently and require a
   precise conversion failure or resolver refutation. Unknown names, result use
   in `requires`, non-fitting constants, ill-sorted expressions, prefix
   statements, checked arithmetic, and unsupported source nodes fail closed.
4. Two clean scalar-profile Cargo captures under the registered toolchain are
   byte-identical in raw MIR and summary. The committed raw artifact and summary
   are exact third copies. The summary records the typed scalar profile,
   canonical selection, compiler/Cargo identities, complete ordered arguments,
   byte count, parameter/result types, block count, and canonical result/panic
   terms. It contains no workspace-, home-, target-, output-, or executable-
   specific absolute path; unit tests vary those roots and preserve the
   placeholder projection byte-for-byte.
5. Source, raw MIR, summary, manifest/lockfile, compiler identity, selected
   package/target/function, and profile mutations each fail with a stable class
   before an authenticated bridge is credited. Missing/duplicate functions,
   malformed MIR, unsupported selected bodies, wrong compilers, existing
   outputs, and failed writes leave no partial accepted artifact.
6. `MirVerifiedContractResolver` independently accepts the generated and
   hand-built declarations against the selected checked MIR body, then retains
   no body. A MIR result or panic mutation, declaration mutation, zero-resource
   `Unknown`, or substituting unrelated same-signature MIR rejects resolver
   construction.
7. Reflect one direct caller separately through both resolvers and an inlined
   specification. Exhaust all 256 inputs with exactly 256 normal / zero panic,
   zero formula disagreement, zero evaluation error, and zero dropped rows.
   Removing the result relation or substituting the callee body at the call
   must make a dedicated mutation test fail.
8. Existing zero-annotation macro fixtures, ADR-0316 source-contract tests,
   ADR-0315 panic-contract formulas/counts, the checked-memory build profile,
   and ADR-0287 fixture bytes remain unchanged. No dependency, default feature,
   MSRV, native, unsafe, or WASM surface changes.
9. Register any new public bridge/profile surface in the relevant source-
   derived semantic and CLI ownership gates. Focused converter/capture/
   resolver tests, complete macro/runtime tests and doctests, the reflection
   semantics gate, exact provenance validators, strict Clippy/rustdoc,
   formatting, links, and OOM audit pass with one job inside 4 GiB.

No performance, general-Rust, general-contract, cross-compiler, source-to-LLVM,
or finding/coverage claim follows from this cell. No gate may be weakened after
observing implementation or capture results.

## Accepted result

The frozen cell passes in full. The typed source bridge proves the annotated
`ContractProgram` first and emits the existing relational contract with no new
contract or IR operator. The generated declaration is structurally identical
to the hand-built control, and two separately constructed MIR resolvers verify
it against the same compiler body before discarding that body.

Two clean registered-toolchain captures are byte-identical at 10,124 raw MIR
bytes and emit the same root-independent scalar summary. A committed third copy
binds the fixture manifest/lock/source, raw MIR, summary, Cargo/rustc identities,
ordered arguments, and provenance hashes. A pinned-nightly integration test
reproduces both committed files through the owning Cargo build. The pre-existing
checked-memory default and summary schema remain unchanged.

The real direct caller and independently inlined control agree under both
resolvers for all 256 `u8` inputs: 256 normal, zero panic, zero evaluation
failure, and zero dropped row. Removing the relation yields a replay-checked
countermodel. Source postcondition/body/partiality mutations, compiler-body and
qualified-call mutations, and zero solver resources all fail closed. The exact
compiler intrinsic noted above is admitted only at its two-`u8`/`u8` type and
spelling boundary.

The complete `axeyum-verify` package and doctests, strict all-target/all-feature
Clippy, the expanded 81-variant / 17-group / eleven-binary / 123-test reflection
semantics gate, exact capture replay, and provenance checks pass inside the
one-job 4 GiB execution policy. This remains a single total scalar identity
bridge, not nontrivial requirements, panic-summary authoring, effects, or a
general Rust/MIR contract front end.

## Rejected alternatives

- **Generate a summary from annotation text alone.** Rejected: it would trust a
  presentation layer without checking the compiler body.
- **Pair the annotation with the existing embedded checked-increment MIR.**
  Rejected: a hand-copied string does not establish owning-build identity.
- **Start with the checked increment and silently add nontrivial MIR
  requirements.** Rejected: call-site requirement obligations are a separate
  composition rule and already have explicit fail-closed boundaries.
- **Infer `panic_when` from LLVM definedness.** Rejected: LLVM poison/UB and
  Rust MIR unwind are distinct channels.
- **Emit an exact return value instead of a relational result.** Rejected: the
  accepted modular rule requires a fresh result plus relation so body discard
  and weak-contract mutation teeth remain observable.
- **Add another capture Boolean or a second Cargo wrapper.** Rejected: one typed
  profile in the existing explicit-selection command keeps policy states and
  provenance centralized.
- **Broaden the source fragment while adding the bridge.** Deferred: the first
  result must establish authenticated composition, not annotation ergonomics.

## Consequences

- T5.2 gains a preregistered, reviewable path from accepted source syntax to an
  accepted checked-MIR modular summary without conflating the two proofs.
- The first bridge is deliberately total and tiny. It closes the identity and
  AST-reuse seam, not nontrivial requirements or panic-summary authoring.
- The experiment strengthens the correctness/reproducibility spine selected by
  the Glaurung reviewer feedback and makes no performance claim.
- PLAN item 7's genuine second-machine row remains independently open; a pinned
  compiler replay on the current host is not cross-machine evidence.

## References

- ADR-0287 through ADR-0289: authenticated MIR capture and Cargo selection.
- ADR-0299 and ADR-0315: checked-MIR relational and panic composition.
- ADR-0316: typed source-local contract annotations and replay.
- P5.2 contracts and modular verification.
- `crates/axeyum-verify/src/reflect/llvm/loops/contracts.rs`.
- `crates/axeyum-verify/src/reflect/mir/checked.rs`.
- `crates/axeyum-verify/src/bin/axeyum_mir_build/`.
