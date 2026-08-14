# Lean Nat conditional subtraction result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.2 / R7.1;
[ADR-0398](../research/09-decisions/adr-0398-order-conditioned-subtraction-restoration.md).

## Result

The zero-axiom Nat prelude now checks `succ_sub_succ`, `sub_self`, and
`sub_add_cancel`. The last theorem consumes explicit `Le m n` evidence and
proves `n-m+m=n`; it does not erase the truncation side condition.

The focused suite checks equal and strict bounds, deterministic package
construction, all 48 promised definitions/theorems, and a mutation that tries
to restore the wrong minuend. Sixteen broken-proof controls are now required to
reject without insertion.

All 215 kernel library tests, every integration suite and doctest, strict
all-target/all-feature Clippy, strict rustdoc, the unchanged 65-row axiom
ledger and eight controls, foundational resources, PLAN authority, and links
pass locally.

## Boundary

This is a checked witness dependency, not `thm:sharp`. Multiplicative
cancellation, the explicit quotient/witness connection, range bounds, and
colour obligations remain. Publication and hosted CI are not claimed from
local evidence.
