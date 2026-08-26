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
implementation graph, the candidate's alpha-stable type identity, six required
laws, and the pinned Lean source revision. Its checker also evaluates the
`testBit_succ` witness at `n = 2, i = 0`, proving that the required interface
excludes the previously admitted countermodel. The artifact remains
`reconstruction_eligible = false` until those laws have independently checked
evidence rather than assumption-bearing imported dependencies.

The native library already contains axiom-free `Nat.testBit_zero` and
`Nat.testBit_succ` analogues. They are not direct solutions: native `testBit`
returns an `AxNat` constrained to zero or one, while imported Lean `testBit`
returns `Bool`. The demand therefore records both exact native types and a
sixth, currently missing `boolean_numeric_observation_transport` obligation.
Same-name retrieval cannot cross that result-sort boundary without a checked
bridge.

The native side of that bridge is now constructive. The
`nat_testbit_bool_bridge` example defines `testBitBool` by mapping native
zero/positive bit values to `Bool.false`/`Bool.true`, then admits
`testBitBool_succ` by reflexivity over the existing numeric recursion. Its
measured footprint is empty. This proves the result-sort adaptation itself is
available; equivalence with the exact imported `Nat.testBit` definition remains
missing and is still denied credit in the artifact.

Definition-level inspection now binds both imported operations beyond their
graph hashes: alpha-stable type and value hashes, direct declaration
dependencies, and measured footprints. Both `Nat.testBit` and `Nat.bitwise`
carry `propext` through their concrete implementation closures. For
`testBit`, the 13 direct dependencies expose the typeclass-expanded
`HAnd`/`HShiftRight`/`BEq` route; for `bitwise`, the direct seam is the private
unary worker plus `PSigma`. This rules out a cheap exact-definition graft as
the clean bridge and makes target-owned semantic reconstruction the next step.

The target-owned observation algebra is now also explicit and axiom-free:
`bitwiseObservation f x y i` computes
`f (testBitBool x i) (testBitBool y i)`, and its application theorem closes by
reflexivity. This cleanly isolates what remains: construct a natural number
whose Boolean observations equal that function. The artifact records
the reification state separately; the observation-level theorem alone cannot
receive credit for `Nat.testBit_bitwise`.

Bounded Nat reification is now constructive too. `reifyBits bits k` sums
`boolToBit (bits i) * 2^i` below `k`, and `bitwiseReifyBounded` applies that
packer to the pointwise algebra. The zero-length theorem checks by reflexivity
with an empty footprint. The remaining theorem is no longer “invent a
reifier”; it is the bounded round trip: for `i < k`, observing
`reifyBits bits k` at `i` returns `bits i` (under the Boolean/numeric bridge).
That theorem is still missing and receives zero credit.

The reifier now exposes an axiom-free successor equation as well:
`reifyBits bits (k+1)` is the prefix plus
`boolToBit (bits k) * 2^k`. Base and step both close by computation. This is the
induction interface for the missing round trip; consumers no longer need to
unfold `sumRange` or depend on its implementation shape.

The Boolean digit seam itself now round-trips too:
`testBitBool (boolToBit b) 0 = b`, proved constructively by the two `Bool`
cases with an empty footprint. An attempted jump directly to
`reifyBits bits 1` was correctly rejected because weighted-sum normalization is
not definitional for a symbolic bit. That arithmetic bridge is now proved from
the named reifier equations plus `pow_zero`, `zero_add`, and `mul_one`.
Transporting the Boolean digit theorem across it yields the genuine one-bit
weighted-sum round trip, also axiom-free. The remaining status is precisely the
general bounded round trip.

The next induction leaf is also closed: `boolToBit b ≤ 1`, by constructive
case analysis on `b`, with an empty footprint. This is exactly the coefficient
bound needed to show each newly appended weighted digit contributes at most
`2^k` in the reifier-bound induction.

That universal bound now checks in the kernel:
`reifyBits bits k < 2^k` for every `bits` and `k`, with an empty footprint. The
proof inducts on `k`, uses the coefficient bound for the new term, and closes
the power step through explicit addition/multiplication normalization. This
removes the sufficient-size uncertainty from bounded reification; the remaining
universal theorem is observation round-trip/uniqueness below the bound.

The established bound composes with the existing native
`Nat.sum_testBit_lt`: summing the first `k` native numeric observations of
`reifyBits bits k` reconstructs that exact number, because the modulus by
`2^k` is removable. This universal numeric round trip is kernel-checked and
axiom-free. What remains is componentwise uniqueness—showing the reconstructed
numeric digit at each `i < k` equals `boolToBit (bits i)`—then transporting
through the Boolean digit bridge.

A bounded oracle exhausts every Boolean vector through width 12: 8,191 vectors,
90,114 in-range observations, and 8,191 first-out-of-range zero observations.
It confirms the weighted-sum construction has the intended finite semantics.
The artifact labels this computational observation only; it does not replace or
receive credit for the universal kernel proof.

Run `just autogenesis-bitwise-semantic-law-demand` to validate the join and its
negative controls.
