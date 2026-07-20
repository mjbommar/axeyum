# ADR-0283: Preregister checked acyclic LLVM CFG execution

Status: proposed
Date: 2026-07-19

Result state: preregistered; implementation has not started

## Context

ADR-0280 establishes a located function boundary, ADR-0281 types the scalar
instruction fragment and exposes value definedness, and ADR-0282 validates
typed PHIs and terminators as one deterministic CFG. The remaining executor is
still the compatibility walker in `reflect::llvm`: it reparses strings, panics
on malformed or cyclic input, and drops an `unreachable` arm from a join. That
last behavior fabricates a value on an execution for which LLVM provides no
defined semantics.

The checked scalar lowerer already separates each SSA value's poison predicate
from immediate-UB obligations accumulated by an executed block. The
preregistration audit found one boundary that must be corrected before graph
execution reuses it: `binary_immediate_defined` currently requires both
division operands to be defined. LLVM makes a poison divisor immediate UB and
makes division by zero (plus signed `MIN / -1`) immediate UB, but an ordinary
poison dividend propagates poison to the result. If that result is never
consumed, it must not make the whole function undefined. This is observable in
CFGs because immediate UB is path-triggered while poison is use-triggered.

This slice therefore freezes execution and definedness together. It does not
broaden syntax, add memory, or route Glaurung through the parser.

## Decision

Add checked reflection entry points for the validated scalar CFG:

- `reflect_cfg_checked(&str) -> Result<CheckedCfgReflected, ReflectError>` owns
  a fresh arena, source parameters, and one returned `DefinedValue`; and
- `reflect_cfg_into_checked(&mut TermArena, &[TermId], &str) ->
  Result<DefinedValue, ReflectError>` binds caller-owned parameter terms.

`CheckedCfgReflected` does not expose one misleading function-wide map of
branch-local SSA values. The internal executor may retain per-path bindings,
but the public result is the joined return value and its exact checked
definedness predicate. The value term on an undefined path is a deterministic
same-sort placeholder and has no standalone semantic meaning; callers must
prove or assume `result.defined` before using `result.value` as an LLVM result.

Extend the structured function/CFG record with the scalar integer return width
from the `define` header. Every `ret` must match it. Reject duplicate SSA
definitions function-wide (including parameter, PHI, and body destinations)
before execution; sibling blocks do not make duplicate names legal.

Execute only acyclic graphs. Detect a cycle before lowering and return a new
stable `ReflectErrorKind::CyclicControlFlow` at a located edge. Bound the
accepted graph to at most 4,096 root-to-block executions, computed
deterministically before term construction; return
`ReflectErrorKind::ExecutionLimit` rather than recurse or allocate without a
bound. Loops remain the `TransitionSystem` route.

For each executed path:

- lower typed body instructions through ADR-0281's one scalar lowering path;
- accumulate only immediate UB from instructions actually executed;
- retain ordinary poison on its SSA value until a consuming operation,
  terminator, PHI, or return makes that value relevant;
- select a PHI incoming by the actual predecessor edge, including only that
  incoming value's definedness;
- require a conditional `br` or `switch` scrutinee to be defined even when all
  destinations are the same;
- join branch results with `ite(condition, true, false)` for both value and
  definedness, with condition-definedness conjoined outside the join;
- join `switch` cases in source order against the default, selecting exactly
  one path's value and definedness;
- transfer unconditional branches without inventing a condition; and
- interpret a reached `unreachable` as `defined = false`, never as a dropped
  arm or proof hypothesis.

Multiple reachable returns of the declared width are joined by their path
conditions. A function whose only reachable terminator is `unreachable`
reflects successfully to the typed placeholder with `defined = false`.
Undefined/non-dominating SSA uses still return a located `UndefinedValue`
error; no value is guessed across sibling paths.

Correct ADR-0281's immediate division bookkeeping as part of this slice:

- a defined zero divisor, a poison divisor, and signed `MIN / -1` remain
  immediate UB when the instruction executes;
- a poison dividend produces a poison result but is not immediate UB by
  itself; and
- `exact` violations and other poison-producing flags remain use-triggered,
  so an unconsumed poison result does not poison the function result.

Concretely, unsigned division/remainder immediate safety is
`rhs.defined && rhs != 0`; signed division/remainder additionally requires
`lhs.defined -> !(lhs == MIN && rhs == -1)`. Result definedness continues to
require both operands and every applicable poison-producing flag.

The compatibility `reflect_into`/`reflect_unary_into` executor remains
available but gains no new proof migration. New or migrated CFG proofs must use
the checked API and state the `defined` premise or prove it.

## Acceptance gates

Tests begin red and then require:

1. the unmodified clang 21 and rustc 1.97 division diamonds reflect through
   the checked CFG API; their value terms agree where defined, and their exact
   definedness is the selected divisor's nonzero predicate;
2. a conditional branch and an equivalent `select` produce provably equal
   values and definedness, including selected-arm poison behavior;
3. PHIs propagate only the incoming selected by the actual predecessor; poison
   in an unselected incoming does not affect the result;
4. an immediate-UB instruction in an unselected block does not affect the
   result, while selecting that block makes `defined` false;
5. unused poison is not immediate UB: an overflowing `add nsw`, an inexact
   `udiv exact`, and a poison dividend with a defined nonzero divisor leave a
   separate constant return defined; a zero or poison divisor does not;
6. a switch with a reached `unreachable` default is not assigned a fabricated
   value: its result is defined exactly on the admitted cases, and the existing
   `x < 3` hypothesis proves both definedness and equality to the total MIR
   function while unconditional definedness is refuted;
7. branch/switch scrutinee poison makes `defined` false even for repeated or
   identical destinations, and switch case/default roles remain exact;
8. scalar return-type mismatch, duplicate SSA definitions across sibling
   blocks, non-dominating uses, cycles, and one graph just over the 4,096
   execution bound return their stable located error kinds without panicking;
9. straight-line inputs are value+definedness equivalent between the existing
   checked scalar API and the checked CFG API;
10. at least the existing `br`+PHI diamond, `switch`+PHI dispatcher, and
    unreachable-default cross-IR proofs migrate from the legacy executor, with
    definedness explicit rather than an arm silently dropped;
11. deterministic graph-shaped noise cannot panic checked execution and
    repeated reflections have deterministic debug/term structure; and
12. the complete `axeyum-verify --all-features` suite, workspace formatting,
    strict Clippy, strict rustdoc, and the repository link checker remain green.

The gates may become stricter before implementation observes any new fixture
or external corpus. They may not be weakened after a failure.

## Consequences

The accepted scalar LLVM surface will finally have one fail-closed path from
text through syntax, graph validation, value semantics, and definedness. The
result is suitable for compiler-IR equivalence only under its explicit
definedness contract; it is not a source-Rust semantics theorem.

This still does not admit Glaurung lowering. Cycles, memory, pointers, calls,
exceptions, `freeze`, `undef`, parameter/return attribute semantics beyond the
selected scalar width, and module-wide symbol resolution remain separate
T5.1.2/T5.1.5 slices. ADR-0279's explicit-width/successor LLIR hardening and a
same-object binary-vs-IR differential remain prerequisites to a shared
consumer boundary.

## References

- [LLVM Language Reference](https://llvm.org/docs/LangRef.html), `phi`, `ret`,
  `br`, `switch`, `unreachable`, division/remainder, and poison semantics.
- [LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html).
- ADR-0279 through ADR-0282.

## Alternatives

- Continue dropping unreachable arms: rejected because it turns UB into an
  unconditional value and can prove a false equivalence without its required
  hypothesis.
- Enumerate cyclic paths to a fixed depth: rejected because a depth heuristic
  is not loop semantics; cycles belong in a `TransitionSystem`.
- Merge all branch-local SSA bindings into one public environment: rejected
  because existence and definedness are path-sensitive and such a map invites
  use without a reachability guard.
- Add memory or Glaurung lowering in this increment: deferred; neither changes
  the scalar CFG semantics required to make the existing proofs honest.
