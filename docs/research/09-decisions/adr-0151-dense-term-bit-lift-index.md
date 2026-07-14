# ADR-0151: Dense term-bit lift index

Status: proposed
Date: 2026-07-14

## Context

After accepted ADR-0150, bit blasting is the largest full Glaurung stage at
5.884 seconds. One-shot lowering appends every materialized bit to the
deterministic `Vec<TermBitBinding>` and also inserts the same literal into a
`BTreeMap<(TermId, u32), AigLit>`. The full canonical tier creates 23,029,676
term-bit bindings; `register-slice` and `slice-partial` account for 22,797,529
(99.0%).

Term IDs are dense arena indices, and `record()` appends all bits for one term
contiguously. The map's only read consumer is `BitLowering::literal_for_term_bit`;
interpolation iterates the existing binding vector, while model replay uses the
separate symbol-input map. The ordered map therefore adds millions of tree
insertions without contributing output order or ownership.

## Decision

Replace the term-bit ordered lookup map with a dense per-term range index,
subject to the Glaurung acceptance benchmark.

- Keep `Vec<TermBitBinding>` as the authoritative, deterministic binding owner.
- Record `(start, length)` for each lowered dense `TermId`; resolve a requested
  bit by bounds-checking its range and indexing the binding vector.
- Preserve `term_bits()` order and `literal_for_term_bit()` behavior, including
  `None` for unknown terms or out-of-range bits.
- Grow the range vector when an incremental arena grows, preserving already
  assigned term ranges and stable IDs.
- Do not change AIG construction, term memoization, symbol inputs, root bits,
  CNF, model lifting, interpolation, or replay.
- Add focused lookup-boundary and incremental-growth tests in addition to the
  existing end-to-end lowering/evaluation suite.

The decision becomes accepted only if all BV/CNF/SAT integration tests and
strict Clippy pass, then five clean representative processes improve both bit
blast and end-to-end medians with identical AIG/CNF counters, decisions, and
replay. A 4 GiB full-tier confirmation is required; otherwise restore the
ordered map and defer this ADR.

## Evidence

The artifact-v27 counts and consumer audit above select the experiment. The
implementation passes all 20 `axeyum-bv` tests, including explicit unlowered
term/out-of-range lookup and incremental arena-growth coverage; all 10 BV
interpolant tests; 31 SAT-BV integration tests; strict Clippy; formatting; and
documentation-link checks under the 4 GiB cap. Performance evidence remains
pending the representative/full gates.

## Alternatives

- **Replace the term memo at the same time.** Deferred: its dense-index
  opportunity is separate, and this experiment isolates the 23.03 million
  per-bit inserts first.
- **Remove term-bit bindings entirely from ordinary SAT solving.** Rejected for
  now: they are public lift metadata and consumed by BV interpolation.
- **Use a hash map.** Rejected: dense IDs and contiguous bindings admit direct
  indexing with deterministic bounded lookup and no hashing.
- **Change incremental lowering only.** Rejected: the measured target is the
  cold Glaurung path; the representation can support both without diverging
  semantics.

## Consequences

One range entry replaces all ordered-map nodes for a term while the existing
binding vector remains authoritative. Lookup becomes two bounds checks and one
direct index. Memory scales with arena terms plus required bindings rather than
with a tree node per materialized bit; the real corpus decides whether this is
material end to end.
