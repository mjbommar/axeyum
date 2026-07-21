# ADR-0315: Preregister modular MIR panic-contract propagation

Status: accepted
Date: 2026-07-21

## Context

[ADR-0299](adr-0299-preregister-checked-mir-relational-calls.md) accepts one
body-independent MIR call only after proving the selected `sum16` callee cannot
panic. That is deliberately sound but not yet compositional: a callee with a
real, input-dependent panic predicate is rejected instead of contributing that
predicate to its caller. [P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md)
therefore remains short of its panic-contract exit criterion.

The existing checked MIR route already has the two semantic channels this
increment needs. `CheckedMirScalar::panic` is a path-conditioned Rust panic
predicate, while a relational call's result constraint is retained separately
in `assumptions`. The missing rule is not new syntax: it is a verified summary
for the callee panic predicate and a precise normal-return guard for the
existing result relation.

This boundary must remain distinct from LLVM definedness. LLVM poison or
undefined behavior cannot certify Rust unwind behavior, and MIR panic does not
replace the LLVM-side value/definedness contract. Source attributes are also a
later presentation and lowering problem; this experiment first establishes the
runtime composition rule they would denote.

## Proposed decision

Preregister one opt-in scalar MIR panic-contract experiment over a two-function
chain. Extend the existing `ScalarCallContract` representation with one bounded
Boolean `panic_when(args)` component. Existing constructors remain
source-compatible and mean literal `false`, preserving ADR-0296--0299's total
contracts. A separately named constructor admits an explicit panic predicate;
it does not infer one from text, `unwind` spelling, LLVM attributes, or a failed
proof.

The implementation may land only with these semantics:

1. Resolver construction reflects the exact checked MIR callee body and proves
   `body_panic => panic_when`. For the frozen experiment it additionally proves
   equality, so the result measures exact composition rather than a vacuous
   `panic_when = true` over-approximation. Refutation, `Unknown`, timeout, or
   solver failure rejects the resolver.
2. The callee postcondition is required only on its normal-return population:
   `requires && !panic_when`. A panicking input has no usable return value. The
   verifier must not demand or fabricate a result on that population.
3. At a reached call, lowering computes the instantiated callee panic term
   before following the normal target. The caller panic becomes
   `prior_panic || callee_panic`. The fresh-result relation is guarded by that
   combined predicate, so it constrains only executions that reach and return
   normally from the call.
4. Call metadata exposes the source span, fresh result, result relation, and
   instantiated callee panic predicate as separate terms. A caller can replay
   whether a counterexample is a caller-local failure or a callee panic.
5. The ordinary checked scalar route continues to reject calls. Version one
   still admits exactly one direct scalar call, exact `unwind continue`, no
   cleanup execution, no nested/multiple/recursive calls, no memory or external
   effects, and no loops.
6. LLVM contract behavior is unchanged. The experiment compares the modular
   MIR route with a checked inlined MIR specification; it does not manufacture
   an LLVM panic channel or weaken LLVM definedness.

## Frozen experiment and evidence gates

Implementation is admitted only if one committed bundle passes every gate:

1. Freeze a checked scalar MIR callee whose exact panic condition is
   input-dependent and whose normal result is relationally specified, plus one
   direct caller using the already accepted assigned-call terminator. Both are
   parsed through the located MIR path; no legacy line executor is used.
2. Verify the declared panic predicate against the callee body in both
   directions. Mutating the body assertion or the declared predicate must fail
   resolver construction with `ContractDisproved`. Literal `false` must reject
   the panicking body, proving old total-contract behavior remains fail-closed.
3. Prove the modular caller's panic predicate equals an independently built
   inlined specification for all inputs. Prove the normal-return result equal
   under `!panic`, and replay at least one concrete callee-panic witness plus
   both boundary neighbors.
4. Exhaustively enumerate the complete input domain when its width is at most
   eight bits. Report exact normal/panic counts, zero disagreement, zero
   evaluation error, and zero dropped rows. A deliberately unguarded result
   relation must be refuted on a panicking input.
5. Add negative controls for wrong predicate sort, forbidden `Result` use in
   `panic_when`, signature drift, absent/duplicate contracts, wrong callee or
   unwind spelling, multiple/nested calls, explicit zero-resource `Unknown`,
   and symbol-alias attempts. Deterministic malformed input must not panic.
6. Register every added public contract component or call-site field in the
   source-derived reflection semantics manifest with proof, deterministic
   exhaustive replay, and mutation ownership. The standing checker must fail
   if any owner or evidence reference is omitted.
7. Focused panic-contract tests, the complete reflection semantics gate,
   complete `axeyum-verify` tests and doctests, strict Clippy, warning-denied
   rustdoc, formatting, links, and existing MIR provenance validation pass with
   one build/test job inside the 4 GiB cap.

The fixed experiment records correctness and mechanism counts only. It carries
no performance, general-call, source-annotation, or unwind-cleanup claim, and no
gate may be weakened after observing the implementation.

## Rejected alternatives

- **Keep requiring every callee to be panic-free.** Rejected as the permanent
  rule: it is sound but prevents modular verification of ordinary partial Rust
  functions and leaves T5.2.3 unimplemented.
- **Treat `unwind continue` as proof that a call returns.** Rejected: it names
  the exceptional control behavior; it does not establish its unreachability.
- **Conjoin the postcondition on panicking inputs.** Rejected: a Rust call that
  unwinds has no normal destination value, so this would add a fabricated
  semantic obligation.
- **Use LLVM poison/definedness as the panic summary.** Rejected: the two IRs
  expose different semantic channels, as ADR-0299 already requires.
- **Start with annotation parsing.** Deferred: attributes should lower to an
  already checked composition rule, not define that rule implicitly.
- **Model cleanup blocks now.** Deferred: the first slice propagates the panic
  predicate and proves the normal path; executing unwind cleanup is a separate
  control-flow/effects boundary.

## Consequences

- P5.2 gains a preregistered path from the accepted total checksum call to
  input-dependent modular panic-freedom.
- Existing total scalar contracts keep their exact behavior and API.
- If accepted, the runtime rule supplies the semantic target for later
  `#[requires]`/`#[ensures]` lowering; it does not itself complete annotations.
- A genuinely different second machine remains independently required for
  PLAN item 7. This local Track 5 work does not substitute for that evidence.

## Acceptance evidence

The accepted `ScalarCallContract::new_relational_with_panic` route keeps every
existing constructor at literal-false panic and is rejected by LLVM contract
verification. Checked MIR resolver construction lowers the declared predicate,
proves it exactly equal to the reflected body panic term, and proves the result
relation only under normal return. Caller lowering exposes the instantiated
callee panic in `MirRelationalCallSite`, joins it into caller panic, and guards
the fresh-result relation with the combined predicate.

The fixed `checked_inc` experiment passes all frozen gates:

- modular and independently inlined caller panic predicates are proved equal;
- all 256 `u8` inputs replay with exactly 255 normal rows, one panic row, zero
  disagreement, zero evaluation errors, and zero dropped rows;
- the panic witness at 255 and its boundary neighbors replay, while a deliberately
  unguarded postcondition rejects an arbitrary result on the panic row;
- body/predicate mutations, old literal-false total behavior, ill-sorted and
  result-dependent panic predicates, and a zero-node resource limit all fail
  closed with the registered classes; and
- the complete all-feature `axeyum-verify` package and doctests pass, as do the
  81-variant/17-group/ten-binary/117-test semantics gate, strict all-target
  Clippy, warning-denied rustdoc, formatting of every touched Rust file, links,
  and the OOM audit under the one-job 4 GiB profile.

This accepts only the runtime MIR panic-composition rule. Source annotations,
cleanup execution, general calls, memory/effects, recursion, loops, and any
performance claim remain outside the result.

## References

- `compiler/rustc_middle/src/mir/syntax.rs`, `TerminatorKind::Call` and
  `UnwindAction`.
- ADR-0288 and ADR-0296 through ADR-0299.
- P5.2 contracts and modular verification.
