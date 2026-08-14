# Lean Rado closed-form witness result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1;
[ADR-0400](../research/09-decisions/adr-0400-closed-form-rado-sharpness-witness.md).

## Result

The Rado integration development now constructs the factorized geometric
quotient `q=a+a*u'`, shell length `N=b*q`, and the exact paper endpoints. It
checks the universal witness equation by composing the finite-sum
factorization with the quotient-free identity.

The six-test integration suite covers the universal factorization, abstract
quotient-free witness, closed-form composition, the `k=3` computation at 36,
and separate false mutations of the factorization, endpoint, and shell length.

All 216 kernel library tests, every integration suite and doctest, strict
all-target/all-feature Clippy, strict rustdoc, the unchanged 65-row axiom
ledger and eight controls, foundational resources, PLAN authority, and links
pass locally.

## Boundary

Witness range bounds, the `Z<=N` equivalence, valuation/divisibility, colours,
and `thm:sharp` remain unproved. Publication and hosted CI are not claimed from
local evidence.
