# Lean Rado sharpness witness result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1;
[ADR-0399](../research/09-decisions/adr-0399-quotient-free-rado-sharpness-witness.md).

## Result

The zero-axiom Nat prelude checks bounded multiplication over subtraction. A
dedicated Rado development then replaces `N/b` by an explicit factor witness
`N=b*q` and checks the paper identity for

```text
u = q-a,  X = N-a*b+1,  Y = 1,  Z = a*u:
a*(X-Y) = b*Z.
```

The generic package inventory is eight definitions and 41 theorems. Its 17th
mutation changes the scaled subtrahend. The Rado integration suite adds a
concrete `18=18` witness control and rejects the false `16=18` endpoint
mutation.

All 216 kernel library tests, every integration suite and doctest, strict
all-target/all-feature Clippy, strict rustdoc, the unchanged 65-row axiom
ledger and eight controls, foundational resources, PLAN authority, and links
pass locally.

## Boundary

This checks the witness equation, not the witness's closed-form quotient,
ranges, valuation, colours, or `thm:sharp`. Euclidean division remains absent
and unneeded for this increment. Publication and hosted CI are not claimed
from local evidence.
