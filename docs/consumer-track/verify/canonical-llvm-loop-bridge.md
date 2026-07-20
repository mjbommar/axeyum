# Checked LLVM loop bridge

Status: accepted self-loop and single-latch slices (ADR-0291/0292, 2026-07-20)

## Purpose

`axeyum_verify::reflect::llvm::loops` turns admitted typed, compiler-produced
LLVM loops into Axeyum's existing `TransitionSystem` contract. It is the cycle
route next to the checked acyclic executor: header PHIs become state, the entry
edge becomes `init`, one complete header-to-latch iteration becomes `trans`,
and one explicit unsigned PHI bound becomes `bad`.

The identity remains **untrusted fast search, trusted small checking**. The
bridge uses the checked LLVM syntax and value-plus-definedness lowering; it does
not trust a best-effort string parser or add implicit coercions. Solver SAT
models are replayed by the ordinary Axeyum backend. A source bug claim still
requires source replay because this first recurrence deliberately abstracts the
source exit edge.

## Accepted shapes

The constructor `reflect_canonical_loop_checked` accepts exactly:

- one typed scalar LLVM function;
- one reachable cyclic block and no other cycle;
- a conditional terminator with one self edge and one distinct exit edge;
- exactly the unlabeled function entry and the loop block as predecessors;
- one or more two-incoming PHIs, each with one entry and one self incoming;
- constant or scalar-parameter PHI initializers;
- existing checked scalar body instructions only; and
- `UnsignedPhiUpperBound { phi, bound }` over a non-Boolean loop PHI.

It rejects no cycle, multiple self loops, multi-block/nested/irreducible cycles,
self-only loops, malformed PHIs, pointer parameters, memory, external preheader
SSA state, duplicate definitions, unsupported body semantics, and invalid
properties with stable `LoopReflectErrorKind` classes and source spans.

ADR-0292 adds `reflect_single_latch_loop_checked`. It preserves the self-loop
route above and additionally accepts exactly one reachable header, one distinct
latch, one latch-to-header back-edge, entry+latch header predecessors, an
acyclic scalar internal region, branch-only internal control, no exit before
the latch, and at most 64 deterministic paths / 4,096 path block executions.
The latch must branch to the header and one distinct exit. Switches, multiple
latches/back-edges, early exits, external region predecessors, nested or
irreducible cycles, memory, and path overflow fail closed with located errors.

MIR loops, general rejected-loop fallback, general preheaders, arbitrary
properties, memory loops, and LLIR are not admitted by these slices. Existing
replay-checked BMC is the bounded unrolling route for every accepted relation;
it does not make a rejected loop supported.

## Implicit entry identity

LLVM unnamed arguments, instructions, and basic blocks share a numeric slot
namespace. The exact clang fixture has an unlabeled entry block referenced as
`%1` from PHIs. The structured parser previously represented the block as
`BlockId::Entry` but the PHI edge as undefined `Label("1")`.

`parse_scalar_cfg` now recovers that slot only when all of these are true:

1. the source entry is unlabeled and is an actual CFG predecessor;
2. the PHI predecessor sets differ only by replacing `Entry` with one undefined
   all-decimal label;
3. that label is not an explicit block; and
4. every PHI requiring the substitution agrees on the same label.

The graph retains `BlockId::Entry`; `ScalarCfg::implicit_entry_label` preserves
only the compiler spelling needed by canonical rendering. Named, conflicting,
duplicate, extant, unrelated, or structurally ambiguous labels still fail.
Parse-render-parse reproduces both the typed graph and the `%1` identity without
inventing a labeled source block.

## State and formulas

State order is deterministic:

1. loop PHIs in source order;
2. referenced function parameters in declaration order.

Parameters are immutable state so the same input is visible at every step.
`init` equates every PHI with its constant/parameter entry incoming. `trans`
seeds the checked environment with pre-state PHIs and parameters, executes the
typed body in source order, equates post-state PHIs with back-edge incoming
values, and preserves parameters.

For a multi-block loop, each deterministic header-to-latch path has a separate
checked environment. Internal PHIs select their actual predecessor
simultaneously. Internal conditional branches contribute both condition
definedness and selected polarity. Only the path's executed instructions
contribute immediate UB, and the full transition is the disjunction of its
path relations. Selected PHI poison is retained as definedness state rather
than promoted to immediate UB; it becomes constraining only when control or a
back-edge observes it.

The transition relation additionally conjoins:

- immediate-UB predicates from every executed body instruction;
- transitive poison-free/definedness predicates of every back-edge value; and
- the loop branch condition's definedness.

The branch Boolean value is intentionally not constrained. Either edge may be
taken by the abstract recurrence; only executing a poison/undefined branch is
forbidden. This makes the recurrence an exit-over-approximation.

## Result interpretation

For a property over modeled PHI state:

- `SafetyOutcome::Safe` is a sound source-loop invariant result. Proving the
  property on a recurrence that can execute extra iterations is conservative.
- `BmcOutcome::UnreachableWithinBound` is only the ordinary bounded statement.
- `BmcOutcome::Reachable` is an abstract recurrence witness, not yet a source
  bug. Re-execute an ordinary source input and match the reported state before
  making that claim.
- `Unknown` remains first-class and is never converted to safety.

The API exposes `exit_is_overapproximated() == true` and the omitted exit block
so a caller cannot reasonably mistake the profile for exact exit reachability.

## Accepted evidence

The committed `clang_capsum8.ll` fixture is the exact compiler text formerly
used by the manual prototype. Its automatic state is `%6:i8` (counter), `%7:i8`
(accumulator), then immutable `%0:i8` (input).

`llvm_checked_loop` establishes:

- exact implicit-entry normalization and canonical round-trip;
- deterministic metadata and state sorts/order;
- unbounded k-induction safety for `acc <= 100`;
- bounded unreachability of `acc > 100` through depth 8;
- abstract `acc > 2` reachability at step 3 plus separate source replay with
  `capsum8(3) == 3`;
- symbolic equivalence of automatic `init`/`trans`/`bad` formulas to an
  independently built recurrence;
- 20,000 deterministic concrete transition tuples with `DISAGREE = 0`;
- poison, immediate division UB, and undefined branch conditions excluded from
  transitions;
- precise negative coverage for all rejected shape/dependency/property classes;
  and
- deterministic malformed-input non-panic checks.

ADR-0292 adds the exact clang-21 `capdiv` module. Its state is `%7:i8`
(accumulator), `%8:i8` (counter), immutable `%0:i8` (`n`), then immutable
`%1:i8` (`d`). Its path inventory is `%6 -> %15` and `%6 -> %11 -> %15`.
The gate additionally establishes:

- exact implicit `%2` entry recovery, loop metadata, and render/reparse fixpoint;
- deterministic header/latch/exit/back-edge/path metadata;
- exact predecessor-selected, simultaneous latch PHIs;
- even-counter `d=0` acceptance and odd-counter `d=0` rejection, plus a
  concrete refutation of the wrong eager division-UB relation;
- independent multi-path `init`/`trans`/`bad` formula equivalence;
- 50,000 deterministic concrete transition tuples with `DISAGREE = 0`;
- unobserved poison preservation and observed branch-poison rejection;
- k-induction safety for `acc <= 100`, BMC unreachability through depth 8, and
  separate source replay of abstract step-2 reachability with
  `capdiv(2, 1) == 1`; and
- located rejection of the frozen cycle/region/path/type/dependency boundary.

ADR-0295 adds an opt-in checked direct-body resolver for the two exact Glaurung
PAC loops. Both call one registered scalar `leaf(i32) -> i32` body; the
unchanged default API still rejects the calls. Automatic call/loop
value-definedness formulas equal an independent `i*i+1` recurrence over
100,000 tuples at zero disagreement. Callee immediate UB is eager, an
unobserved poison return remains lazy, and missing/external/indirect/nested/
memory/signature/attribute boundaries fail closed. Exact source, module,
function, compiler, and command provenance reproduce live from the registered
Glaurung tree. This is the inlined baseline for a later P5.2
modular-versus-inlined differential, not itself a contract model.

ADR-0296 adds the first contract side of that differential. A bounded typed
expression tree states the exact `leaf` value plus poison/immediate-definedness
contract. `VerifiedContractResolver` checks it against the registered body,
then discards the body before caller reflection. The modular `compute`/`main`
relations have the same normalized conjunction atoms as the inlined route,
100,000 deterministic tuples have `DISAGREE = 0`, bounded/unbounded verdicts
match, and requirement/value/definedness/body mutations are refuted. The
universally true requirement is deliberate: a later call-site obligation route
must make failed nontrivial requirements bad states rather than silently prune
their transitions.

The ADR-0290 runner now owns nine binaries and runs 94 tests. Exact ownership
grows from 62 to 63 checked LLVM/MIR semantic variants; the direct-call form is
owned once by its independent formula, fuzz/replay, and mutation evidence.

Run the focused and standing gates with:

```sh
cargo test -p axeyum-verify --test llvm_checked_loop
cargo test -p axeyum-verify --test llvm_direct_calls
python3 scripts/check-reflection-semantics-gate.py --run
```

The old split/unwrap parser remains temporarily in `llvm_reflection` only as a
differential control against the typed bridge. It is not part of the standing
acceptance runner and is not an implementation dependency.
