# ADR-0246: Model-independent Glaurung stack-region classification

Status: accepted
Date: 2026-07-18

## Context

ADR-0245's v2 sweep failed closed at maximum's positive-control precision
gate. Both sole-authority backends and both repetitions retained all 14 expected
source-backed findings, but also labeled the arbitrary destination of
`RtlCopyMemory` in `test_physical_memory.sys` as a stack overflow. The old
detector separately concretized `dst` and `rsp` and treated proximity within
plus or minus 64 KiB as semantic stack membership. Maximum unsigned could place
unrelated values next to each other and manufacture that label.

The correction also had to preserve the genuine stack overflow in
`test_stack_overflow.sys`, where the destination is the local frame expression
`rbp - 0x70` and the attacker controls the copy length.

## Decision

Accept Glaurung's structural stack-origin correction on the isolated
`axeyum-concretization-policy-a0` branch. A destination may reach the existing
bounded numeric refinement only when it is the current stack/frame expression,
contains a non-leaf current stack/frame expression in its interned expression
DAG, or shares a free symbolic ancestor with it. A common constant or free
symbol leaf alone is not structural proof.

Keep arbitrary-read, arbitrary-write, and null-dereference classification
independent. A model-selected scalar witness may drive execution, but must not
create a semantic memory-region label.

## Evidence

The correction deliberately retained three successive real-fixture controls:

1. Glaurung `52bd3c0` removed the attacker-pointer false positive by requiring
   `rsp` symbolic ancestry, but lost the genuine `[rbp-0x70]` row (13/14).
2. Glaurung `3d0e2aa` admitted `rbp`, but its fresh-symbol unit fixture did not
   match the real constant-base expression DAG; the exact control still returned
   13/14.
3. A temporary environment-gated expression trace showed `rbp = 0 - 8`,
   `rsp = rbp - 0x90`, and `dst = rbp - 0x70`. The replacement regression failed
   before DAG ancestry and passes after Glaurung `0581f57`; the trace was removed.

The exact N=2 maximum-policy authority control at `0581f57` accepts all 14
expected findings with precision and recall 1.0, zero false negatives, zero
unexpected high-confidence rows, stable repetitions, and exact Z3/Axeyum
parity. Its preserved hashes are:

- authority report: `8ff7eef2738c51c78de2576807fa7c27a1b8cf5c0c77e77951f0912f6392cc6e`;
- source-backed validation: `281ccf95a5ca1ecf176f5b9bfddcddf6fb2bd4e098549b7a8844caf599d32dc8`.

The focused positive/negative structural tests pass with both solver features.
The final dual-backend Glaurung library suite passes 992/994 tests; the two
remaining WinAPI prototype-rendering assertions reproduce on the untouched
baseline and are outside the changed symbolic/IOCTL path. Glaurung documents
the accepted correction at final clean revision `7f682e5`.

## Consequences

The v2 maximum failure is a repaired detector-classification bug, not validated
coverage headroom. V2 remains rejected evidence and its unobserved site-hash
cells cannot be combined with a later run. A new preregistered five-policy sweep
must rerun every cell from the corrected revision.

This correction does not select a preferred concretization policy, establish
real-world recall, or justify symbolic memory. A0 remains a configuration knob;
symbolic memory remains conditional on a separately measured validated coverage
gap.

## Alternatives

- Suppress the one instruction address: rejected as fixture-specific.
- Accept 14/15 precision: rejected because the source-backed control is exact.
- Treat an untainted destination as sufficient: rejected because stack origin
  and attacker control are different facts.
- Continue v2 after repair: rejected because it would mix source revisions.
