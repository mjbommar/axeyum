# ADR-0291: Preregister a typed canonical LLVM loop bridge

Status: proposed
Date: 2026-07-20

Result state: zero-row; no structured loop bridge, implicit-entry PHI
normalization, automatic transition system, or build-backed loop test exists
under this ADR

## Context

T5.1.4 requires reducible compiler loops to route into Axeyum's existing
`TransitionSystem` engines instead of stopping at the checked CFG cycle
boundary. A prototype in `tests/llvm_reflection.rs` already proves that the
architecture is viable: it finds one self-looping LLVM block, treats its PHIs
as state, lowers their back-edge dependencies, and proves `acc <= 100` for all
iterations with k-induction. BMC also finds the abstract recurrence state
`acc > 2` and agrees that `acc > 100` is unreachable within a bound.

That prototype is not an admissible frontend. It reparses text with unchecked
`split`/`unwrap`, uses the historical `lower_rhs` compatibility path, discards
LLVM flags and definedness, and silently drops the exit guard. The resulting
recurrence is a safety over-approximation: continuing after the concrete loop
would exit is sound for proving a state invariant, but an abstract reachable
state is not automatically a source counterexample. The current test does not
make that distinction explicit.

The exact compiler fixture also exposes a structured-syntax prerequisite. Its
unlabeled entry block is printed as implicit slot `%1` in loop PHIs. The typed
CFG currently represents that block as `BlockId::Entry` while parsing the PHI
predecessor as `BlockId::Label("1")`, so exact predecessor validation rejects
otherwise valid compiler output. Any normalization must be structural and
strict, not a general acceptance of undefined numeric labels.

This slice follows ADR-0290's correctness-first gate. It adds one canonical
LLVM self-loop profile only. MIR loops, multi-block/nested loops, memory,
bounded-unroll fallback, general bad predicates, and Glaurung LLIR lowering
remain separate work.

## Decision

Add a checked loop module under `reflect::llvm` and one public constructor for
a canonical scalar self-loop transition system. The first profile accepts:

- one typed scalar LLVM function parsed by the ADR-0280--0284 path;
- exactly one cyclic block, whose CFG has one self back-edge and one exit edge;
- one or more PHIs, each with exactly one self incoming and one non-self entry
  incoming;
- scalar function parameters, treated as immutable state components;
- constant or parameter entry values;
- only the existing typed scalar instruction families needed by PHI back-edge
  values and the loop branch; and
- one explicit unsigned upper-bound bad predicate over a named PHI.

The returned owned type implements `axeyum_solver::TransitionSystem`.
State order is deterministic: loop PHIs in source order followed by referenced
function parameters in declaration order. `init` binds PHIs to their entry
incoming values and leaves parameters universally unconstrained. `trans`
reuses the checked typed lowering, preserves parameters exactly, binds each
post-PHI to its self-edge incoming value, and conjoins every needed value's
poison-free predicate, every immediate-UB predicate, and the branch condition's
definedness. It may not fall back to the legacy string lowerer.

The exit edge is intentionally abstracted: the recurrence may take another
step after the source loop would exit. The API and documentation must label
this an over-approximation suitable for invariant proofs. A `Safe` result is a
sound source-loop safety result for a property over the modeled PHI state. A
`Reachable` result is an abstract recurrence witness until separately replayed
against source inputs; the bridge must not label it a source bug.

Extend typed CFG normalization only for the compiler's implicit entry slot. If
an unlabeled entry block is an actual predecessor, and a PHI's predecessor set
differs solely by one undefined all-decimal label in place of `BlockId::Entry`,
normalize that label to `Entry`. All PHIs for that edge must agree. Any named,
ambiguous, repeated, extant, or otherwise unmatched label remains a located
error. Canonical rendering uses the structured entry identity and reparses to
the same graph.

Expose stable, located loop failure classes for syntax, no/multiple cycles,
noncanonical/multi-block shape, invalid PHIs, unsupported init/body/memory,
external SSA dependency, bad-property target/bound, and internal IR building.
No source input may panic the constructor.

The first acceptance fixture remains the exact `capsum8` compiler text already
used by the manual prototype. Move the reusable fixture and automatic tests to
the library-facing checked route; do not mutate it into hand-labeled LLVM. The
manual parser may remain temporarily only as a differential control and must be
removed from the accepted proof path.

## Pre-implementation acceptance gates

Implementation begins only after this zero-row ADR is committed. It must then
satisfy all of the following:

1. the exact existing `capsum8` LLVM text parses through the structured function
   and typed CFG paths without adding a synthetic source label;
2. implicit-entry normalization accepts only the unique structural numeric-slot
   substitution described above; named, ambiguous, duplicate, and unrelated
   undefined PHI predecessors retain precise located errors;
3. parse-render-parse yields the same typed graph and deterministic loop-system
   metadata/state order;
4. automatic detection selects exactly one self-loop block with one back-edge,
   one exit edge, and one or more two-incoming PHIs; no loop, two loops,
   multi-block/nested cycles, malformed PHIs, or self-only loops fail closed;
5. the automatic system reproduces the accepted unbounded `acc <= 100`
   k-induction proof and bounded `acc > 100` unreachability result;
6. `acc > 2` is reported only as abstract recurrence reachability, and one
   explicit ordinary-source input separately replays a matching concrete state;
   no un-replayed abstract witness is called a source bug;
7. function parameters used by the loop remain immutable state, entry PHIs bind
   only accepted constant/parameter operands, and external preheader SSA values
   fail closed in this slice;
8. transition terms preserve the checked scalar value plus definedness
   semantics, including `nuw`/`nsw` on the fixture; injected poison, immediate
   UB, undefined branch conditions, or unsupported memory cannot become a
   permitted transition;
9. one-step automatic init/transition/bad formulas are equivalent to an
   independently constructed specification over the fixture, and deterministic
   concrete recurrence fuzz reports `DISAGREE = 0`;
10. deterministic malformed/noise inputs never panic and every rejection has a
    stable class plus source span where source exists;
11. ADR-0290's source-owned manifest and runner add the loop evidence binary
    without weakening or duplicating ownership of any of the 62 semantic
    variants; all prior 60 tests remain mandatory; and
12. focused loop/parser/semantics tests, the complete
    `axeyum-verify --all-features` suite, workspace formatting and strict
    Clippy, warning-denied rustdoc, exact MIR fixture replay, and repository
    links pass without a dependency, feature, unsafe, MSRV, native, or WASM
    surface change.

The gates may be strengthened before the first structured loop result is
observed. They may not be weakened afterward.

## Consequences

If accepted, T5.1.4 gains its first reusable automatic compiler-loop route and
the historical proof moves onto typed, definedness-aware syntax. The recurrence
abstraction becomes explicit enough for reviewers to distinguish sound invariant
proofs from abstract reachability.

T5.1.4 remains in progress. A later ADR must add bounded-unroll fallback and
either MIR or multi-block reducible loops before the phase can claim general
cycle routing. Memory loops, nested/irreducible control flow, arbitrary
properties, source-level loop contracts, and LLIR consumption remain open.
