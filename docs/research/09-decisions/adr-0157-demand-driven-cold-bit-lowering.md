# ADR-0157: Demand-driven cold bit lowering

Status: deferred
Date: 2026-07-14

## Context

The Glaurung client profile re-establishes term-to-AIG lowering as the largest
native-driver stage and reports a register-slice-heavy workload. Axeyum already
has three pieces of infrastructure for relevant-bit lowering:

- `BitDemandStats` and exact structural demand propagation;
- dense term IDs plus deterministic term-bit lift ranges; and
- original-query model replay in `SatBvBackend`.

The production lowerer nevertheless lowers every bit of every reachable child.
For `(= ((_ extract 7 0) x64) c8)`, the diagnostic demands 25 term bits and
eight symbol bits while production materializes 81 term bits and all 64 symbol
bits. ADR-0143 correctly removed the old observational `BTreeSet` walk from
normal timing; simply running that expensive pass before the unchanged full
lowerer would not implement GQ4.

Partial lowering changes both the circuit and model-lift boundary. It therefore
needs an explicit exactness, fallback, missing-bit completion, and replay
contract before it can become a solver policy.

## Proposed decision

Add an off-by-default, additive cold lowering route. It computes demand with
dense arena-indexed bitsets, then materializes only the demanded bits for the
first exact structural class.

Demand begins at every bit of every supplied root. The first production class
propagates exactly through:

- Boolean not/and/or/xor/implies;
- BV not/and/or/xor/nand/nor/xnor;
- `extract`, `concat`, zero/sign extension, and constant rotations;
- BV/Boolean `ite`, always demanding its condition and both selected output
  bits; and
- floating-point bit reinterpretation (`FpFromBits`).

Every other operator is a conservative barrier: demanding any output bit
demands every bit of every operand, and lowering materializes its complete
output with the existing verified circuit builder. Equality, comparisons,
arithmetic, division, symbolic shifts, and all future unclassified operators
therefore preserve the current circuit semantics. Low-prefix arithmetic can be
added only in a later ADR after this structural slice is measured.

The demand planner uses `Vec<Vec<bool>>` keyed by dense `TermId` and `SymbolId`,
not ordered sets. It reports complete request/available/demanded counts and its
own elapsed time. Lowering iterates demanded reachable terms in increasing
arena ID; this is topological because an application can reference only terms
that already exist. Per-term bits are processed in increasing LSB-first index,
preserving deterministic AIG and lift-map order.

Roots remain complete `LoweredTerm` values. The term-bit lift map may be sparse;
`literal_for_term_bit` returns `None` exactly for an unmaterialized bit and
finds materialized bindings by their explicit bit index rather than assuming
that range offset equals bit index.

Only the demand-driven route permits partial symbol inputs. During model lift,
materialized symbol bits take their SAT/AIG values and omitted bits are filled
with deterministic `false` (numeric zero). A symbol with no materialized bits
is supplied by the solver's existing well-founded model completion. This is not
trusted as a semantic shortcut: every SAT candidate must still evaluate every
original assertion. A failed replay remains a soundness error or `Unknown`
under the existing evaluator-failure rules; it is never accepted as SAT.

The ordinary full lowerer and incremental lowerer retain their missing-bit
invariant and behavior. The first implementation exposes explicit lowering
functions and a benchmark-only solver configuration. It does not change the
default path until the real-corpus acceptance gate passes.

## Acceptance gate

- Exhaustive widths 1--4 compare demand-lowered roots with the ground evaluator
  and the full lowerer for every input over nested extract/concat/extension,
  bitwise, rotation, and ITE shapes.
- Focused tests cover disjoint demands of one shared term, high zero-extension
  bits with no source demand, sign-bit sharing, sparse lift lookup, deadline
  behavior, and deterministic omitted-bit model completion.
- The 8-of-64 equality regression lowers exactly the 25 demanded term bits and
  eight demanded symbol bits rather than 81/64, while SAT and UNSAT variants
  replay against the untouched source terms.
- Existing full and incremental lowering suites remain unchanged and green;
  strict Clippy and docs pass under the 4 GiB cap.
- The benchmark artifact records whether production slicing was applied and
  reports demanded/lowered bits, AIG nodes, CNF variables/clauses, stage times,
  decisions, disagreements, and replay failures by Glaurung family.
- Artifact v29 and its configuration hash distinguish this production policy
  from the unchanged full lowerer and the observational demand profiler.
- Five representative and full comparisons are 100% decided with zero errors,
  disagreements, or replay failures. `register-slice` and the whole corpus must
  improve AIG/CNF size and end-to-end time before the policy is accepted or
  enabled by default.

## Alternatives

- **Rewrite every demanded bit into a separate IR formula.** Rejected: it
  duplicates the lowering semantics in the term builder, loses the direct
  term-bit map, and expands the arena before the AIG can share gates.
- **Use the observational `BTreeSet` profile and then lower fully.** Rejected:
  it pays the measured diagnostic cost without removing a gate.
- **Make every operator partially aware in the first change.** Rejected:
  arithmetic carry, comparison, division, and symbolic-shift cones need
  separate exact proofs. Conservative barriers make the first public slice
  complete and falsifiable without narrowing the requested end state.
- **Assign arbitrary values to omitted model bits.** Rejected: model completion
  must be deterministic. Zero completion plus mandatory original replay is
  simple, stable, and checkable.
- **Change incremental lowering simultaneously.** Deferred: the cold Glaurung
  gate is the immediate target, while incremental partial memos add a separate
  later-demand and scope contract. The cold representation is chosen so that a
  later incremental extension can add missing bits monotonically.

## Consequences

The first candidate can remove wide discarded register bits without changing
the existing arithmetic circuits or weakening replay. Demand planning becomes
real production work only when the explicit policy is selected, and its cost is
charged to bit blast. Sparse lift maps become an intentional representation,
while full and incremental paths retain their stronger complete-map invariant.

An accepted result will close GQ4 only for the exact structural class above.
Low-prefix add/sub/multiply, symbolic shifts, comparison-specific relevance,
and warm incremental partial-bit growth remain measured follow-ups rather than
implicit claims.

## Glaurung measurement and disposition (2026-07-14)

The Glaurung acceptance measurement is semantically green but rejects this
implementation as a default performance policy:

- the unchanged default remains about **1.42x** Z3;
- unconditional demand lowering regresses that ratio to about **4.49x**;
- all queries are decided with zero disagreements; and
- bit blast rises from about **47%** to **83%** of Axeyum time because the
  backward demand analysis costs more than the circuit construction it avoids.

Therefore the implementation remains explicit, off by default, and useful as
correctness/telemetry infrastructure, but ADR-0157 is deferred rather than
accepted. No default or automatic policy may select it.

The next GQ4 design needs a separate admission contract. A cheap syntactic
precheck must reject ordinary/full-demand queries before allocating per-term
bitsets; the exact demand pass must be memoized and bounded; and slicing may be
admitted only when a conservative savings estimate clears a deliberately wide
threshold. The bound must fall back to the ordinary full lowerer before paying
the current unbounded analysis cost. Thresholds and budgets must come from the
`register-slice` family and whole Glaurung corpus, not the focused 8-of-64
microcase. The required outcome remains an end-to-end win at unchanged decided,
agreement, and replay rates.
