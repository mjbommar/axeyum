# ADR-0152: Range-backed term-lowering memo

Status: proposed
Date: 2026-07-14

## Context

Accepted ADR-0151 makes dense per-term ranges point into the authoritative
`Vec<TermBitBinding>`, but `LoweringBuilder` and `IncrementalLowering` still
retain `BTreeMap<TermId, Vec<AigLit>>`. Each completed term therefore owns a
second bit vector containing the same literals.

The accepted full Glaurung artifact has 982,044 unique post-word DAG terms and
23,029,676 materialized term-bit bindings. `register-slice` and
`slice-partial` account for 973,313 terms (99.1%). Range presence already says
whether a term completed, and its `(start, length)` recovers every literal in
bit order. The ordered memo contributes neither output order nor distinct
semantic ownership.

## Decision

Use dense range presence plus authoritative bindings as the term-lowering memo,
subject to the Glaurung acceptance benchmark.

- Treat `term_bit_ranges[term.index()].is_some()` as the completed-term test.
- Reconstruct the same owned `Vec<AigLit>` for child operands and returned roots
  by mapping the term's authoritative binding range.
- Remove the ordered `TermId -> Vec<AigLit>` owner from one-shot and incremental
  lowering.
- Preserve binding order, root/operand bit order, incremental arena growth,
  deadline behavior, public lookup, interpolation, AIG construction, CNF, model
  lifting, and replay.
- Keep the current per-parent operand-vector cloning in this ADR. Any borrowing
  or scratch-buffer redesign is a separate experiment.
- Add batch-vs-incremental, shared-subterm, repeated-root, interrupted-lowering,
  and lookup-boundary coverage.

The decision becomes accepted only if BV/interpolation/SAT integration tests and
strict Clippy pass, then five clean representative processes improve bit blast
and end-to-end medians with identical AIG/CNF counters, decisions, and replay. A
4 GiB full-tier confirmation is required; otherwise restore the ordered memo
and defer this ADR.

## Evidence

The artifact-v27 counts and ownership audit above select the experiment.
Implementation and performance evidence are pending.

## Alternatives

- **Borrow child slices directly.** Deferred: mutating AIG construction while
  borrowing binding storage requires a broader ownership refactor and would
  confound this representation test.
- **Replace only `BTreeMap` with a dense `Vec<Option<Vec<AigLit>>>`.** Rejected:
  it removes tree probes but preserves the duplicate per-term vectors already
  made redundant by ADR-0151.
- **Drop public term-bit metadata.** Rejected: interpolation and public lift-map
  consumers require the authoritative bindings.
- **Change operator encodings simultaneously.** Rejected: structure must remain
  identical so the client gate attributes only memo ownership.

## Consequences

Completed-term state and bit ownership have one dense representation. Operand
and root reads still allocate the same owned vectors, so the experiment does
not claim to solve clone cost. Incremental reuse remains keyed by stable dense
term IDs and grows with the arena; the real corpus decides whether removing the
ordered duplicate owner is material end to end.
