# Lane: testbit-codomain — decide the `Nat.testBit` codomain question

<!-- plan-section: lane-status -->

**testbit-codomain (`WIP`, testbit-codomain, 2026-09-02).** Starting from the
`shape-census` finding: the largest raw bucket on the ready frontier is six
`Nat.testBit` ml430 mirrors, all `DIVERGENCE-BLOCKED` because our
`Nat.testBit` returns `Nat` where Mathlib's returns `Bool`. This lane makes
the one-time construction decision (ADR-1545) with each option costed from the
tree, implements it, and flips whatever the ledger's own rules allow. Held-out
facts are checked first and left alone.
