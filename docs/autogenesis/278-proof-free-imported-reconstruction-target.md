# Proof-free imported reconstruction target

Date: 2026-08-26

`Nat.testBit_bitwise` has an exact proof-free diagnostic capsule that contains
its generalized proposition but not its assumption-bearing proof. The materializer imports the
audited theorem, takes only its type, generalizes the two contaminated
transparent definitions (`Nat.testBit` and `Nat.bitwise`), emits a fresh
root-selected `definition : Prop`, and imports that stream again through the
ordinary proof-isolated statement boundary.

The external capsule is 10,087 bytes, contains 12 declarations, performs zero
normalization rewrites, and has an empty measured axiom footprint. Its goal is
the generic theorem over explicit `testBit` and `bitwise` parameters. The
source theorem name is rejected if it remains in the output bytes.

This is not a valid reconstruction goal. Fresh inspection found that
generalizing the definitions without also carrying their semantic laws makes
the two functions arbitrary. A concrete countermodel sets `testBit n i` to
`n = 1`, `bitwise` to constant zero, `f` to Boolean conjunction, and
`x = y = 1`: the required premise holds, while the conclusion is
`false = true`. The audit therefore records
`logical_status = refuted-unconstrained-abstraction` and
`execution_eligible = false`.

The empty footprint remains useful evidence about proof isolation, but it is
not evidence of provability. A producer must instead receive a law-bearing
interface or reconstruct the concrete definitions before any specialization or
sibling theorem may receive credit.

The committed candidate audit binds the external path, size, digest, goal
digest, target identity, abstraction count, and empty footprint. Run
`just autogenesis-imported-testbit-bitwise-statement` to reproduce the
diagnostic capsule and verify its fail-closed countermodel receipt.
