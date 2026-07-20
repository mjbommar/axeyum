# ADR-0292: Preregister a checked single-latch LLVM natural loop

Status: proposed
Date: 2026-07-20

Result state: zero-row; the exact compiler module is registered, but no
multi-block loop discovery, internal-path semantics, latch-PHI lowering, or new
public constructor exists under this ADR

## Context

ADR-0291 accepts one typed scalar LLVM self-loop. That proves the
`TransitionSystem` architecture, strict implicit-entry identity, checked
value/definedness lowering, exit-over-approximation contract, and source replay
discipline. T5.1.4 still lacks ordinary reducible loops whose header, internal
body, and latch are distinct blocks.

The roadmap also names bounded unrolling as a fallback. Axeyum's
`bounded_model_check` already performs a replay-checked k-unrolling once a
trustworthy one-step transition exists. Building a second direct textual-CFG
unroller now would duplicate PHI, branch, poison, and immediate-UB semantics
before the frontend can derive that one-step relation. The next architectural
gap is therefore multi-block transition extraction; the existing BMC engine is
the bounded route for every accepted system. A general unroll fallback for
still-rejected cycles remains open.

Ubuntu clang 21.1.8 provides a compact real input. `capdiv` has header `%6`, an
odd-counter division block `%11`, latch `%15`, one `%15 -> %6` back-edge, a
latch PHI, and an exit to `%4`. Its even path must remain executable when the
divisor is zero because `udiv` is not executed; its odd path must be forbidden
for zero. Flattening both paths or conjoining every block's UB predicate would
be a soundness/completeness bug. The accumulator is capped with `llvm.umin`, so
`acc <= 100` remains an independently checkable invariant.

The complete compiler module is committed before implementation at
`crates/axeyum-verify/tests/fixtures/llvm/clang21_capdiv_natural_loop.ll`, SHA-256
`1592057004b6db95281a96f8a24835cd8fbeade5a297a70ec2a76988fc2bc8e7`. It
passes `llvm-as-21` unchanged and retains exact compiler attributes and loop
metadata. This freezes the input shape; it is not an observed implementation
result.

## Decision

Add `reflect_single_latch_loop_checked` beside the self-loop constructor. It
returns the existing owned `CanonicalLoopSystem`, generalized internally to a
deterministic list of iteration paths. `reflect_canonical_loop_checked` remains
self-loop-only and source-compatible. Add read-only latch/path metadata without
changing the `TransitionSystem` trait.

The first multi-block profile accepts exactly one scalar natural loop with:

- one reachable header and one distinct latch;
- exactly one latch-to-header back-edge and no other cycle;
- header predecessors consisting only of the unlabeled entry and the latch;
- one or more two-incoming header PHIs selecting entry or latch state;
- an acyclic internal region from header to latch;
- only unconditional and conditional branches internally;
- no exit before the latch, and one latch branch with a header back-edge plus a
  distinct exit;
- typed scalar instructions and internal/latch PHIs from the existing checked
  fragment; and
- at most 64 deterministic header-to-latch paths and 4,096 total path block
  executions.

Switches, multiple latches/back-edges, early exits, nested/irreducible cycles,
memory, calls outside admitted intrinsics, external SSA, and paths that do not
reach the latch fail with stable located loop error classes. These are explicit
profile boundaries, not an attempt to recognize arbitrary reducibility.

Each transition path starts with pre-state header PHIs and referenced immutable
parameters. It executes blocks in source order along that CFG path. Internal
PHIs select the incoming value for the actual predecessor and bind
simultaneously. Conditional internal edges conjoin both condition definedness
and the selected Boolean polarity. Only instructions executed on that path
contribute immediate-UB constraints. Back-edge values and the latch branch must
be defined. The path then binds post-state header PHIs and unchanged parameters.
The complete transition relation is the disjunction of all path relations in
deterministic CFG successor order.

As in ADR-0291, the latch branch value is abstracted while its definedness is
required. The recurrence can continue after source exit, which is conservative
for invariants. Any reachable result remains abstract until source replay.
`bounded_model_check` is the accepted bounded unrolling of this relation; this
ADR does not claim fallback coverage for a loop rejected by the profile.

For `capdiv`, state order must be `%7:i8` (accumulator), `%8:i8` (counter), then
referenced parameters `%0:i8` (`n`) and `%1:i8` (`d`). The exact path inventory
is `%6 -> %15` and `%6 -> %11 -> %15`, with latch `%15` and exit `%4`.

## Pre-implementation acceptance gates

Implementation begins only after this zero-row ADR and fixture are committed.
It must then satisfy all of the following:

1. the registered module retains the exact SHA-256 above, passes `llvm-as-21`,
   parses through the structured function/CFG paths, recovers implicit entry
   slot `%2`, preserves loop metadata, and reaches a canonical render/reparse
   fixpoint;
2. discovery deterministically reports header `%6`, latch `%15`, exit `%4`, one
   back-edge, and exactly the two registered iteration paths;
3. the self-loop constructor remains self-loop-only, while the new constructor
   accepts both the registered natural loop and the prior canonical self-loop
   without changing the prior state/formulas/results;
4. no cycle, two loops, multiple latches/back-edges, a multi-block cycle without
   one natural header, early exits, internal `switch`, unreachable region blocks,
   path-count/block-execution overflow, memory, and malformed PHIs fail closed
   with stable classes and source spans;
5. internal/latch PHIs select the actual predecessor simultaneously; missing
   dominance, external preheader SSA, duplicate definitions, or width mismatch
   cannot be hidden by another path;
6. path conditions are exact: even-counter `d=0` can take `%6 -> %15` because
   division is not executed, while odd-counter `d=0` cannot take
   `%6 -> %11 -> %15`; poison, immediate UB, and branch definedness remain
   path-conditioned rather than globally conjoined or discarded;
7. header PHIs and referenced parameters use the frozen deterministic state
   order, parameters are immutable, and entry initialization remains
   constant/parameter-only;
8. the automatic system proves `acc <= 100` unbounded by k-induction and reports
   `acc > 100` unreachable through a fixed BMC depth;
9. abstract reachability of `acc > 0` is labeled as such and separately replayed
   by the ordinary source case `capdiv(2, 1) == 1`;
10. automatic `init`/multi-path `trans`/`bad` formulas are solver-equivalent to
    an independently built specification, at least 50,000 deterministic
    concrete recurrence tuples report `DISAGREE = 0`, and a deliberately eager
    division-UB relation is refuted on the even `d=0` path;
11. ADR-0290 retains exact ownership of all 62 source-derived semantic variants;
    the loop binary expands without weakening any prior test, refutation,
    mutation, self-loop, or source-replay gate; and
12. focused loop/parser tests, the full reflection gate, complete
    `axeyum-verify --all-features` suite and doctests, workspace formatting and
    strict Clippy, warning-denied rustdoc, exact MIR replay, `llvm-as-21`, and
    repository links pass without dependency, feature, unsafe, native, MSRV, or
    WASM surface changes.

The gates may be strengthened before the first multi-block semantic result is
observed. They may not be weakened afterward.

## Consequences

If accepted, T5.1.4 will cover the first real reducible natural loop with an
internal branch and path-sensitive UB, not merely a syntactically split
self-loop. The same checked one-step relation will support both unbounded
invariant proving and bounded BMC unrolling without a second semantics engine.

T5.1.4 remains in progress. General rejected-loop unrolling, MIR loops,
multi-latch loops, early exits, switches, memory, and nested/irreducible control
flow still require separately preregistered routes.
