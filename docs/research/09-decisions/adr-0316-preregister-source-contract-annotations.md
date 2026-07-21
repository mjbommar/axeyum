# ADR-0316: Preregister source scalar contract annotations

Status: proposed
Date: 2026-07-21

## Context

ADR-0315 accepts the checked-MIR runtime rule for modular panic propagation.
P5.2 still lacks its source-facing `requires`/`ensures` surface. The current
`#[verify]` macro cannot gain that surface through parsing alone: it evaluates a
tail expression only for panic side effects, `Program`/`Lowered` retain no
function result, and generated counterexample glue assumes every witness must
panic under `catch_unwind`. A postcondition violation instead returns normally
and must replay the returned value against the source predicate.

The macro already establishes a useful ordering convention: `#[verify]` is the
outer attribute and reads inert function-level attributes such as `#[unwind]`.
The first contract slice can reuse that seam without changing MIR capture,
calls, effects, or ADR-0315's checked-MIR contract representation.

## Proposed decision

Preregister one source-AST scalar annotation slice:

```rust
#[axeyum_verify::verify]
#[axeyum_verify::requires(x < 255)]
#[axeyum_verify::ensures(|result| result == x + 1)]
fn checked_inc(x: u8) -> u8 { x + 1 }
```

`verify` must be outermost. Standalone `requires` and `ensures` attributes are
inert markers, like `unwind`; the `verify` expansion strictly parses, consumes,
and removes them from the emitted original function. Duplicate, misplaced, or
malformed markers are compile errors rather than ignored text.

Version one has these boundaries:

1. Exactly one scalar return and scalar parameters are admitted. The body is
   straight-line with one tail expression; explicit/early `return`, arrays,
   branches, loops, calls, methods outside the existing scalar whitelist, and
   multiple exits remain rejected for the annotated route.
2. `requires` may reference parameters only. `ensures` is exactly a one-argument
   closure whose parameter denotes the retained result and whose body may also
   reference source parameters. Both use the existing strictly typed expression
   lowerer; no string parsing or implicit coercion is added.
3. `Program` and `Lowered` retain the typed tail result for annotated functions.
   Zero-annotation programs preserve their existing behavior and public
   constructors remain source-compatible.
4. The verification population is the precondition. Panic bad states become
   `requires && panic`; the postcondition bad state is
   `requires && !panic && !ensures(result)`. An unsatisfiable precondition is a
   precise contract error, not a vacuous proof.
5. A postcondition counterexample remains distinct from a panic counterexample.
   Generated replay calls the original function, confirms it returns normally,
   and evaluates the original typed `ensures` closure to false on the witnessed
   inputs/result. Panic witnesses retain the existing `catch_unwind` route.
6. This slice verifies one function against its own contract. It emits no
   `ScalarCallContract`, resolves no calls, and does not claim source-to-MIR
   identity. Later modular consumption must bind an authenticated compiler body
   to the annotation before using ADR-0315.

## Frozen evidence gates

Implementation is admitted only if all of these pass:

1. A safe `u8` checked-increment example verifies under `x < 255` and its
   result postcondition; the same body without the precondition retains the
   existing overflow witness.
2. A one-off mutated postcondition yields a concrete boundary witness, the
   original function returns normally, and the source closure replays false.
   Omitting result retention or guarding `ensures` by normal return must make a
   dedicated mutation test fail.
3. An implementation with a reachable panic under `requires` remains a panic
   counterexample; a panic cannot be mislabeled as a postcondition violation.
4. Exhaust all 256 `u8` inputs for the safe and mutated examples with exact
   admitted/precondition counts, zero disagreement, zero evaluation errors,
   and zero dropped rows.
5. UI/compile-fail tests cover duplicate attributes, wrong ordering, no scalar
   return, non-closure/wrong-arity `ensures`, unknown names, ill-sorted
   predicates, result use in `requires`, explicit return, branch/loop/call
   bodies, and an unsatisfiable precondition. No unsupported annotation is
   silently removed.
6. Existing zero-annotation macro fixtures remain byte-stable where committed
   and behavior-identical. Complete macro/runtime tests and doctests, the
   reflection semantics gate, strict Clippy/rustdoc, formatting, links, and OOM
   audit pass with one job inside 4 GiB.

No performance, modular-call, general-Rust, MIR-equivalence, or annotation-
ergonomics claim follows from this experiment.

## Rejected alternatives

- **Parse attributes but keep discarding the result.** Rejected: there is no
  term against which an `ensures` predicate can be checked.
- **Report postcondition failures as panics.** Rejected: the generated replay
  would be false and would weaken the existing DISAGREE=0 contract.
- **Use annotation strings.** Rejected: strings lose Rust spans and create a
  second untyped expression parser.
- **Emit modular summaries immediately.** Deferred: compiler-body
  authentication and source-to-MIR contract identity are separate gates.
- **Admit branches or loops in the first result-retention slice.** Deferred:
  joined return values and multiple exits need their own path-sensitive gate.

## Consequences

- T5.2.1 receives a bounded executable first slice with honest replay UX.
- The accepted no-annotation verifier stays the default.
- ADR-0315 remains the runtime target for later authenticated modular calls,
  not evidence that source annotations already compose.
- PLAN item 7 still independently requires a genuine second machine.

## References

- P5.2 contracts and modular verification.
- `crates/axeyum-verify-macros/src/parse.rs`.
- `crates/axeyum-verify/src/{ast,lower,verify}.rs`.
- ADR-0296 through ADR-0299 and ADR-0315.
