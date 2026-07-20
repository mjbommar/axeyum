# ADR-0296: Preregister verified scalar LLVM contract composition

Status: proposed
Date: 2026-07-20

## Context

[ADR-0295](adr-0295-preregister-checked-llvm-direct-body-calls.md) accepts an
exact checked-body interpretation of the two Glaurung PAC calls to `leaf`.
That route is deliberately an inlined baseline: the caller resolver retains
the callee body and executes it at every reflected call site. It supplies the
missing side of P5.2's modular-versus-inlined differential, but it is not a
contract rule.

[P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md) requires a
callee to be checked against an explicit contract once, after which callers
compose with the contract rather than the body. The first slice must preserve
LLVM value, poison, immediate-undefined-behavior, and `noundef` semantics. It
must also avoid an unsound shortcut: adding an unproved `requires` predicate to
a transition relation would erase violating executions and could make a buggy
caller look safe.

The exact PAC `leaf(i32) -> i32` is the smallest measured case with both an
accepted inlined baseline and nontrivial definedness (`mul nsw`, then
`add nuw nsw`). It can test the composition mechanism before annotation
syntax, general relational postconditions, or call-site precondition
obligations are designed.

## Decision

Preregister one opt-in verified scalar-contract experiment for the exact PAC
`leaf` call, compared against ADR-0295's checked-body baseline.

The experiment may add an explicit scalar contract and a contract-backed loop
resolver only under all of these boundaries:

1. A contract declares a stable callee name, ordered scalar argument widths,
   one scalar result width, and a deterministic term builder for `requires`,
   immediate definedness, result value, and result definedness. Every produced
   term is sort-checked. Contract construction and instantiation are fallible;
   malformed terms never panic or coerce.
2. A verified contract is created from one explicit contract plus one exact
   defined LLVM body. Construction independently reflects the body and proves,
   for all scalar inputs, that `requires` is true and that the contract exactly
   matches the body's immediate-definedness, result-definedness, and result
   value. A counterexample, `Unknown`, signature mismatch, malformed contract,
   or unsupported body fails closed with a stable distinct error class.
3. The accepted resolver stores only verified contract data, not the parsed
   callee body. Caller lowering instantiates that contract at the actual
   arguments and composes the existing argument-definedness/`noundef`
   boundary exactly as ADR-0295 does. This is the observable modular boundary:
   the caller cannot execute or inspect the callee body.
4. Version one admits only universally true preconditions and exact functional
   scalar postconditions. Nontrivial `requires`, havoc/existential results,
   relational postconditions, recursion, nested calls, memory, pointers,
   variadics, external effects, and annotations remain rejected. A later slice
   must represent call-site precondition violations as obligations/bad states;
   it may not prune them as infeasible transitions.
5. The existing default and direct-body entry points remain unchanged. Neither
   acquires an implicit contract, body, uninterpreted return, or fallback. The
   new contract route is separately named and opt-in, and `puts` remains
   rejected.
6. Contract inventories use deterministic ordering, reject duplicate names,
   and retain precise call-site locations for missing contracts, signature
   drift, and unsupported call attributes. No hash iteration may affect terms,
   state layout, or diagnostics.

This is the smallest T5.2.2/T5.2.4 composition rule. It is not yet
`#[requires]`/`#[ensures]`, general modular verification, a revised Glaurung
census, or a claim that an exact functional summary is more expressive than
the body it replaces.

## Frozen evidence gates

Implementation is admitted only if one committed evidence bundle passes all
of the following without weakening after result observation:

1. Revalidate ADR-0295's exact Glaurung revision, source/compiler command,
   source/module/function hashes, and the independent `x*x+1` specification
   before every exact contract test.
2. Verify the explicit `leaf` contract against the exact body once, then build
   `compute` and `main` transition systems from a resolver that retains no
   callee body. The unchanged default still fails at `@leaf`; the direct-body
   route remains independently usable as the inlined baseline.
3. Prove modular and inlined `init`, `trans`, and `bad` terms equivalent for
   both callers. Repeat ADR-0295's deterministic 100,000-tuple comparison with
   `DISAGREE = 0`, explicit multiplication/addition/counter overflow coverage,
   and source replay for every claimed reachable source state.
4. Exercise unbounded safety and replay-checked bounded reachability through
   both routes. Their verdicts and replay classification must agree; a solver
   `Unknown` is retained as `Unknown`, never treated as proof.
5. Mutate each semantic contract component independently: requirement,
   immediate definedness, result definedness, and result value. Each mutation
   must fail verification with a replayed counterexample. Also mutate the
   callee body and show that the frozen contract no longer verifies.
6. Negative tests cover duplicate/missing contracts; argument-count, argument-
   width, and result-width drift; non-Boolean `requires`/definedness; wrong
   result sort; contract-construction failure; verification `Unknown` under an
   explicit zero resource limit; and every direct-call boundary retained from
   ADR-0295. Failures keep stable classes and precise locations where source
   text exists.
7. Report body-resolver versus verified-contract construction time, reflected
   arena nodes/terms, and repeated transition-building time. These metrics
   characterize the mechanism; they are not a performance acceptance gate or
   a speed headline.
8. The standing reflection-semantics gate, complete `axeyum-verify` tests and
   doctests, strict all-target/all-feature Clippy, warning-denied rustdoc,
   formatting, and documentation links pass.

## Evidence before implementation

ADR-0295 already proves the exact body side independently and owns the full
call boundary. Its accepted `leaf` semantics are a pure function of one i32
argument plus three definedness predicates: signed multiplication overflow,
unsigned addition overflow, and signed addition overflow. No memory, nested
call, control flow, or hidden effect must be summarized.

The existing checked reflector exposes the needed internal decomposition:
returned value/poison are distinct from immediate undefined behavior. The loop
lowerer already conjoins actual-argument definedness at the call boundary.
Therefore the experiment can share those semantics and replace only the
resolver's body execution with a verified contract instantiation.

## Alternatives

- **Call a term builder a contract without verifying it:** rejected; that
  moves arbitrary Rust code into the trusted base and can prove a false caller
  property.
- **Keep the body beside the contract and choose either during lowering:**
  rejected for this gate; it does not establish that caller composition is
  independent of the body.
- **Start with a nontrivial precondition:** deferred until call-site obligation
  failures have an explicit safety representation. Conjoining `requires` to
  the transition is an unsound proof-by-path-deletion shortcut.
- **Start annotation parsing now:** deferred. A macro spelling should follow a
  checked runtime contract rule, not define its semantics accidentally.
- **Use an unconstrained result plus an `ensures` relation immediately:**
  deferred until per-step existential/havoc symbols and BMC renaming are
  explicit and tested. The exact functional contract is sufficient for the
  measured first case.

## Consequences

If the gates pass, Axeyum gains its first actual modular call: an exact callee
contract is verified once and caller reflection retains only the checked
summary. P5.2 can then proceed to explicit call-site precondition obligations,
relational `ensures`, and macro lowering with a concrete soundness baseline.

If any gate fails, remove the contract implementation and retain the result.
ADR-0295 remains the accepted inlined baseline, while annotations, nontrivial
preconditions, havoc, memory, recursion, and external calls stay deferred.
