# Imported generic bitwise candidate audit

Date: 2026-08-26

## Result

Pinned Lean 4.30 already contains the exact generic theorem the three bitwise
siblings need:

```lean
theorem Nat.testBit_bitwise
    (of_false_false : f false false = false) (x y i : Nat) :
    (bitwise f x y).testBit i = f (x.testBit i) (y.testBit i)
```

Pinned Mathlib defines `testBit_lor`, `testBit_land`, and `testBit_ldiff` as
specializations of that theorem. This corrects the previous next step: Axeyum
should not invent a new generic interface before testing the exact upstream
one. The theorem was absent from Axeyum's native lemma index and from the
proof-free target capsules because neither contains the imported Init theorem
population needed for premise retrieval.

A root-selected export was generated on s5 from:

- Lean 4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`; and
- lean4export commit `a3e35a584f59b390667db7269cd37fca8575e4bf`.

The 2,222,315-byte stream is not vendored. It is read-only at
`/nas3/data/axeyum/autogenesis/reference-packs/imported-candidates-v1/Nat.testBit_bitwise.ndjson`;
the committed
[`candidate audit`](../../artifacts/autogenesis/imported-testbit-bitwise-candidate-v1.json)
binds its path, byte count, SHA-256, toolchain identities, declaration identity,
and independent kernel result.

## Trust result

The import succeeds, but the candidate is **not axiom-free**. Its measured
footprint is:

- `propext`;
- `Quot.sound`;
- `Quot`, `Quot.mk`, and `Quot.lift`.

It also has 29 direct theorem dependencies. Consequently, the theorem is
excellent search guidance but cannot become a semantic-contract witness under
the current empty-footprint authority. Specializing it would merely propagate
the assumption-bearing proof into the three targets.

This is not evidence that the mathematical proposition requires those axioms.
The upstream proof uses tactic-generated simplification and strong induction;
the footprint describes that exported proof term. A separate constructive
reconstruction may establish the same type without those assumptions.

## Correct next sequence

1. Add imported theorem candidates as a separate, exact-identity search
   population. Never silently mix them with native axiom-free lemmas.
2. Carry the measured footprint into ranking and require an explicit
   `reconstruct-required` disposition for this candidate.
3. Reconstruct `Nat.testBit_bitwise` inside the imported target kernel from its
   transparent `Nat.bitwise`/`Nat.testBit` definitions and axiom-free arithmetic
   and decision lemmas. The imported proof may guide strategy but may not be
   admitted as evidence.
4. If the reconstructed generic theorem has an empty footprint, specialize the
   same checked term to and/or/difference and run all three targets through one
   unchanged producer operation.
5. Keep `testBit_eq_inth` separate: it needs the list/bits projection law and is
   not a specialization of the binary bitwise theorem.

Run `just autogenesis-imported-testbit-bitwise-candidate-replay` on a host with
the external stream to re-hash and independently import it. The ordinary
knowledge gate checks the committed negative result without requiring the
external mount. Neither route grants contract, proof, transport, operation, or
fact-transition authority.
