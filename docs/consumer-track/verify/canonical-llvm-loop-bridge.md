# Canonical LLVM loop bridge

Status: accepted first T5.1.4 slice (ADR-0291, 2026-07-20)

## Purpose

`axeyum_verify::reflect::llvm::loops` turns one typed, compiler-produced LLVM
self-loop into Axeyum's existing `TransitionSystem` contract. It is the cycle
route next to the checked acyclic executor: PHIs become state, the entry edge
becomes `init`, the self edge becomes `trans`, and one explicit unsigned PHI
bound becomes `bad`.

The identity remains **untrusted fast search, trusted small checking**. The
bridge uses the checked LLVM syntax and value-plus-definedness lowering; it does
not trust a best-effort string parser or add implicit coercions. Solver SAT
models are replayed by the ordinary Axeyum backend. A source bug claim still
requires source replay because this first recurrence deliberately abstracts the
source exit edge.

## Accepted shape

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

MIR loops, bounded unrolling, general preheaders, arbitrary properties, memory
loops, and LLIR are not admitted by this slice.

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
typed body in source order, equates post-state PHIs with self-edge incoming
values, and preserves parameters.

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

The ADR-0290 runner now owns eight binaries and 70 tests. Adding this binary
does not change or duplicate the exact evidence ownership of the original 62
checked LLVM/MIR semantic variants.

Run the focused and standing gates with:

```sh
cargo test -p axeyum-verify --test llvm_checked_loop
python3 scripts/check-reflection-semantics-gate.py --run
```

The old split/unwrap parser remains temporarily in `llvm_reflection` only as a
differential control against the typed bridge. It is not part of the standing
acceptance runner and is not an implementation dependency.
