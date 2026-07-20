# ADR-0298: Preregister relational scalar call results with explicit havoc constraints

Status: accepted
Date: 2026-07-20

## Context

[ADR-0296](adr-0296-preregister-verified-scalar-contract-composition.md)
accepts an exact functional scalar summary, and
[ADR-0297](adr-0297-preregister-call-requirement-obligations.md) makes failed
loop-call requirements explicit bad states before restricting a transition.
The next [P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md)
exit obligation is more general: a caller must compose with a relational
postcondition after the callee body is discarded, rather than substituting one
exact result term.

The existing checksum micro-module is the canonical bounded case. `sum16`
implements one's-complement addition over two `u16` arguments, while
`cksum_pair` returns its complement. Committed MIR and LLVM inlined fixtures,
real Rust execution, cross-IR proofs, and the receiver identity already provide
independent baselines. A modular LLVM caller can therefore test the result rule
without introducing annotations, memory, recursion, or a new source example.

The semantic distinction is load-bearing. A relational call result is a fresh
choice constrained by `ensures`; the constraint is neither LLVM poison nor an
ordinary Boolean value term. Hiding `ensures` inside `DefinedValue::defined`
would make a total callee appear not universally defined, because proving that
field would quantify over every unconstrained result. Substituting the verified
body result instead would make the apparent relational rule secretly exact and
would never exercise havoc.

This increment follows the reviewer-facing correctness spine: strict sorts,
precise failures, body-independent checking, replayed countermodels, explicit
`Unknown`, deterministic helper identity, and zero dropped rows. It carries no
performance or expanded Glaurung-coverage claim.

## Decision

Preregister one opt-in straight-line LLVM scalar-call experiment whose verified
contract introduces a fresh result symbol plus a separately exposed path
constraint.

For arguments `a`, fresh result `r`, and a body-verified relational contract,
define:

```text
call_defined(a, r) = args_defined(a) and result_defined(a, r)
call_immediate(a)  = args_defined(a) and immediate_defined(a)

relation(a, r) =
  not args_defined(a)
  or (requires(a)
      and (not immediate_defined(a)
           or not result_defined(a, r)
           or ensures(a, r)))
```

The reflected caller returns value/definedness terms plus a separate
conjunction of all `relation` terms. A consumer proves a postcondition for all
callee choices by supplying that conjunction as a hypothesis. It proves LLVM
definedness through the ordinary `DefinedValue::defined` term. It diagnoses a
failed callee requirement through the source-attributed call-site metadata;
these three channels must not be conflated.

The experiment may land only with all of these boundaries:

1. `ScalarContractExpr` may add a scalar `Result` reference, strict equality,
   and same-sort `ite`. `Result` is legal only in relational `ensures` and
   relational result-definedness. It remains illegal in `requires`, immediate
   definedness, and ADR-0296's exact result expression. Every malformed sort,
   missing argument/result, width, and expression-budget error fails before
   solving; no coercion is added to `axeyum-ir`.
2. `ScalarCallContract::new` retains its exact-result behavior.
   A separately named relational constructor records `ensures` instead of one
   result expression. Existing exact callers and formulas must remain
   byte-for-byte/term-for-term compatible.
3. Verification reflects the exact scalar callee body once. Under `requires`,
   immediate definedness and result definedness must still match exactly, and
   the actual body result must satisfy `ensures` whenever that result is
   defined. Counterexample, timeout, `Unknown`, solver failure, or signature
   drift fails closed. Successful construction stores no callee body.
4. Each static relational call site receives one fresh BV result in
   `TermArena`'s internal namespace. Static sites share their result across
   repeated path construction inside one reflection, separate reflections do
   not alias, and a user declaration with the same printable name cannot alias
   it. Declaration order and names remain deterministic.
5. The opt-in result exposes the returned `DefinedValue`, the combined
   relational assumptions, and ordered call metadata containing callee, exact
   source span, result symbol, requirement, and per-call relation. A caller
   cannot accidentally mistake a relational result for the ordinary checked
   API's closed term.
6. Version one admits exactly one checked straight-line scalar LLVM caller.
   The ordinary checked reflector continues to reject its call. Loop havoc,
   acyclic multi-block CFG calls, MIR calls, annotations, recursion, nested
   calls, memory, pointers, variadics, external effects, and unsupported call
   attributes remain rejected.
7. The checksum contract is total. ADR-0297's nontrivial loop-requirement rule
   remains accepted and unchanged, but this experiment does not invent a new
   acyclic requirement-violation result type. General straight-line
   precondition UX is deferred until the relational result rule itself passes.

The relation is deliberately allowed to be weaker than a function. A verified
`ensures = true` contract is a sound over-approximation and must leave the
return genuinely arbitrary; it is not rejected merely because it cannot prove
the caller's desired property.

## Frozen evidence gates

Implementation is admitted only if one committed bundle passes every gate:

1. Freeze the current real Rust `sum16`/`cksum_pair`, committed inlined MIR and
   LLVM fixtures, and a new one-call modular LLVM `cksum_pair` fixture. The
   ordinary checked API must reject the modular call at its exact source span.
2. State `sum16` relationally as:

   ```text
   Result = (a + b) + ite(bv_uaddo(a, b), 1_u16, 0_u16)
   ```

   with literal-true requirement/immediate/result-definedness. Verify it
   against the exact LLVM body, discard that body, and expose exactly one
   source-attributed 16-bit internal result symbol in the modular caller.
3. Prove under the exposed relation that modular LLVM `cksum_pair` equals both
   inlined LLVM and inlined MIR for all `u16` pairs. Re-prove the receiver
   identity `sum16 + cksum_pair = 0xffff`. Independently prove the selected
   relation equals the widened-and-folded body semantics.
4. Execute at least 100,000 deterministic input rows. For every row, assign the
   havoc result first to real Rust `sum16(a,b)` and then to a deliberately
   different 16-bit value. The first assignment must satisfy the relation and
   reproduce Rust/MIR/LLVM output; the second must be classified as a relation
   violation. Require zero disagreements, zero evaluation errors, and zero
   dropped/unclassified rows, with carry/no-carry corner counts reported.
5. Accept a deliberately weak `ensures = true` contract, then refute the
   checksum equality without the exact relation. Replay the solver's arbitrary
   result countermodel. This is the teeth control proving the caller uses havoc
   rather than a hidden body/exact-term substitution.
6. Reject an off-by-one strong relation and a mutated callee body. Reject
   `Result` in every forbidden contract component; non-Boolean `ensures`,
   ill-sorted equality/`ite`, missing/duplicate contracts, signature/call drift,
   result-symbol alias attempts, and an explicit zero-resource verification
   `Unknown`. Preserve stable error classes and source locations.
7. Independently show that omitting the exposed relation makes the modular
   equality refutable, while using it makes the equality provable. Prove
   result-definedness separately so no postcondition is counted as LLVM
   poison, panic, or immediate undefined behavior.
8. Add the public contract-expression enum to the source-derived semantics
   manifest and add `checksum_module` to its exact runner. Every old and new
   contract-expression variant needs proof plus deterministic fuzz/replay
   ownership; checker mutation tests must still fail closed.
9. Report construction/node counts only as mechanism observations. The focused
   checksum/direct-call tests, standing semantics gate, complete all-feature
   `axeyum-verify` tests and doctests, strict Clippy, warning-denied rustdoc,
   formatting, links, and current provenance checks must pass under a 4 GiB
   hard memory cap and single build/test jobs.

No gate may be weakened after observing the result. A resource limit or
unsupported construct remains explicit, never a safe result or agreement row.

## Evidence before implementation

The existing checksum module already proves the exact body facts on both IRs
and replays 2,000 deterministic real-Rust rows per reflection. The selected
one's-complement formula is independent of the widened implementation: adding
two 16-bit words produces at most one carry, so modular low-word addition plus
that carry is the exact single-fold result.

`TermArena::declare_internal` supplies the required user/internal namespace
firewall. The checked reflector already separates immediate undefined behavior
from lazy result poison. The missing representation is therefore one explicit
relational-assumption channel and its source/result metadata, not a new solver,
operator semantics, or executor.

## Observed result

The frozen experiment passes. `ScalarCallContract::new_relational` retains a
bounded, strictly sorted `ensures` expression, while
`reflect_scalar_into_checked_with_contracts` introduces one deterministic
internal result symbol and returns the relation in a distinct `assumptions`
channel. The ordinary checked reflector still rejects the call, exact
contracts are unchanged, and relational contracts fail precisely when offered
to the loop route.

The checksum gate classifies all 100,000 deterministic input rows twice:
100,000 real `sum16` result choices satisfy the relation and reproduce Rust,
MIR, and LLVM, while 100,000 deliberately different choices violate it. No row
is dropped or left unclassified, and both carry/no-carry populations are
nonempty. Under the exact relation the modular caller equals both inlined IRs
and re-proves the receiver identity. Under verified `ensures = true`, the
solver instead returns a replayed result countermodel, proving the caller did
not retain or substitute the callee body.

Every frozen negative passes: off-by-one relation, mutated body, forbidden
`Result` placements, ill-sorted equality/`ite`, missing and duplicate
contracts, signature and `noundef` drift, namespace collision, and a forced
verification `Unknown`. The standing manifest now owns 76 variants in 16
evidence groups across ten binaries; its 108 Rust tests plus ten checker tests
pass at a 2.7 GiB peak. The complete `axeyum-verify` package and two doctests
pass with one build job, one test thread, and test debug metadata disabled at a
2.5 GiB peak. Strict package Clippy, warning-denied rustdoc, formatting, links,
manifest mutation tests, and live Glaurung direct-call provenance also pass.

The resource gate exposed two validation-only failures that do not change the
semantic result. A full-package invocation without `CARGO_BUILD_JOBS=1`
triggered a 4 GiB cgroup OOM through simultaneous `rust-lld` processes. A
serialized full-debug retry was stopped cleanly at the cap before OOM. The
accepted no-debug test-profile route preserves all code and solver features,
completes below the same cap, and is the registered reproduction command:

```sh
CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 CARGO_PROFILE_TEST_DEBUG=0 \
  cargo test -p axeyum-verify --all-features --jobs 1
```

## Rejected alternatives

- **Substitute the body result while calling the API relational:** rejected;
  it never tests havoc and makes weak postconditions appear exact.
- **Put `ensures` inside `DefinedValue::defined`:** rejected; it conflates a
  logical assumption with LLVM poison and makes totality depend on an arbitrary
  unconstrained result.
- **Use an uninterpreted function application:** rejected for this slice; it
  expands the solver fragment and obscures the explicit result/relation that
  the contract checker must replay.
- **Add the result as loop state now:** deferred. Per-step renaming, path-local
  calls, PDR support, and untaken-path stuttering require their own frozen gate.
- **Require postconditions to be functional:** rejected. Relational contracts
  are sound over-approximations; proof strength is a caller concern.
- **Add Rust attributes or MIR call terminators now:** deferred until the
  runtime composition rule has executable evidence.

## Consequences

If the gates pass, Axeyum gains its first genuine body-independent relational
call result and advances the checksum-module half of T5.2.2/T5.2.4. Exact
contracts remain available and unchanged; weaker contracts honestly trade
proof strength for abstraction.

The full P5.2 exit will still require MIR-side modular calls, annotation
lowering, panic-contract composition, and the complete two-IR module gate. If
any frozen sort, body-check, havoc-teeth, relation, replay, mutation, or resource
gate fails, remove the implementation and retain ADR-0297 as the accepted
boundary.
