# Bitwise semantic-law reconstruction gap

Date: 2026-08-26

The first proof-isolation pass generalized `Nat.testBit` and `Nat.bitwise` as
two unconstrained function parameters. That preserved an empty kernel footprint
but discarded the very semantics from which `Nat.testBit_bitwise` follows. The
resulting proposition is refuted by a four-line finite countermodel recorded in
the candidate audit and is permanently execution-ineligible.

This closes a measurement loophole: an empty-footprint statement is not a
reconstruction target merely because it imports. Before dispatch, generalized
operations need either checked defining equations or a typed law package strong
enough to imply the target. The gate must test semantic sufficiency separately
from importability and axiom footprint.

The pinned Lean 4.30 source proves the concrete theorem by strong induction on
the observed bit index. Its relevant reusable interface consists of:

- the zero and nonzero branches of `Nat.bitwise`;
- the zero-bit behavior of `Nat.testBit`;
- successor-bit reduction through division by two;
- `Nat.mul_add_div` for the recursive branch; and
- the side condition `f false false = false`.

The next implementation should derive a typed semantic-law capsule containing
only those equations, independently import it, and prove that its hypotheses
exclude the committed countermodel. Only then may reconstruction run. The
original imported proof remains candidate metadata and must never be copied
into the executable capsule.

The first machine-readable demand is
[`bitwise-semantic-law-demand-v1.json`](../../artifacts/autogenesis/bitwise-semantic-law-demand-v1.json).
It binds the exact `Nat.testBit` and `Nat.bitwise` content identities from the
implementation graph, the candidate's alpha-stable type identity, five required
laws, and the pinned Lean source revision. Its checker also evaluates the
`testBit_succ` witness at `n = 2, i = 0`, proving that the required interface
excludes the previously admitted countermodel. The artifact remains
`reconstruction_eligible = false` until those laws have independently checked
evidence rather than assumption-bearing imported dependencies.

Run `just autogenesis-bitwise-semantic-law-demand` to validate the join and its
negative controls.
