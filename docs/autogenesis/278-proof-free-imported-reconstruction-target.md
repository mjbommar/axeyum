# Proof-free imported reconstruction target

Date: 2026-08-26

`Nat.testBit_bitwise` now has an exact reconstruction target that contains its
proposition but not its assumption-bearing proof. The materializer imports the
audited theorem, takes only its type, generalizes the two contaminated
transparent definitions (`Nat.testBit` and `Nat.bitwise`), emits a fresh
root-selected `definition : Prop`, and imports that stream again through the
ordinary proof-isolated statement boundary.

The external capsule is 10,087 bytes, contains 12 declarations, performs zero
normalization rewrites, and has an empty measured axiom footprint. Its goal is
the generic theorem over explicit `testBit` and `bitwise` parameters. The
source theorem name is rejected if it remains in the output bytes.

This is not a proof. It is the clean goal a reconstruction producer may attack.
After proving the generalized goal, a checked specialization receipt must bind
the two abstract parameters back to the exact imported definitions before any
of the three sibling facts can receive credit.

The committed candidate audit binds the external path, size, digest, goal
digest, target identity, abstraction count, and empty footprint. Run
`just autogenesis-imported-testbit-bitwise-statement` to reproduce it.
