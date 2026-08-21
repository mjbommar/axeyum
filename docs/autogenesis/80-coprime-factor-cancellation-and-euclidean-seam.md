# Coprime-factor cancellation and the Euclidean seam

Date: 2026-08-20

## Result

The second support frozen for `Nat.gcd_fib_add_self` reconstructs twice in
fresh native kernels:

```text
forall a c b d,
  gcd a c = 1 -> d divides a -> d divides (c * b) -> d divides b
```

The theorem
`Axeyum.Autogenesis.NatCoprimeFactorDivisibilityCancellation` has identical
fresh goal, proof, declaration, dependency, and empty-footprint identities:

| Object | SHA-256 |
|---|---|
| Goal | `4b22a4c4d2a11ef915e033e6d2c66996e8b46de9594ee45bcb7501ee2e5612d4` |
| Proof | `796d456daab359175f298d9b5d47c76a8f11a6261c206c98218ce8323f1f1f8c` |
| Declaration | `879325e939a6ae474dcb7ec2041942547a3eea8b427fd35abe54274e70f66bd9` |

Both mathematical supports are therefore real. Only the Fibonacci addition
theorem is currently portable into the exact official r091 kernel.

## Proof

The proof is the preregistered balanced-natural Bézout construction. From
`gcd a c = 1`, it transports `Nat.gcd_bezout a c` to a certificate

```text
(1 + a*mn) + c*nn = a*mp + c*np.
```

Multiplying by `b` makes every term except the leading `b` divisible by `d`:
the `a` terms use `d ∣ a`, while the `c` terms use `d ∣ c*b` plus multiplication
and reassociation. `Nat.dvd_add_iff_right` removes the known divisible tail.
No subtraction, classical axiom, proof search, or unproved arithmetic rule is
used.

The kernel derives exactly ten direct theorem dependencies: additive
associativity and commutativity, divisibility closure and cancellation,
right-multiplication closure, balanced gcd Bézout, multiplicative
associativity and commutativity, `one_mul`, and right distributivity.

## Typed composition decline

Composing this theorem into the exact r091 target fails closed first at
`Nat.div_mod_exec`. The native balanced-Bézout proof reaches Axeyum's theorem
combining a Euclidean division equation and remainder bound. Official Lean
4.30 uses the same name for a different computational declaration with a
different type. Same-name similarity therefore grants no transport authority.

This is not a failure of the cancellation theorem. It is a representation seam
between the native Euclidean foundation and the official target environment.
The composition API published no partial kernel, and the run made zero exact
target submissions, executor invocations, retries, semantic receipts,
evaluation claims, or ledger writes.

## Statement-only horizon

Without inspecting any proof body, the pinned Mathlib 4.30 statement inventory
identifies two official target-side formulations:

- `Nat.Coprime.dvd_mul_left`
- `Nat.Coprime.dvd_of_dvd_mul_left`

They demonstrate that the desired target-side interface exists. They do not
authorize importing its proof or crediting the result. The next bounded plan
must choose between independently reconstructing that official interface or
building the missing constructive official Euclidean equation that makes the
native balanced-Bézout closure portable. The latter is the broader foundation;
the former is the narrower representation adapter.

## Immutable evidence

The read-only pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/3acb61ef5-nat-coprime-factor-cancellation-v1/manifest.json`

Its manifest SHA-256 is
`1937d3abaabf56302ced49806d7132e4b1e329b17f6e3da152295476a58e2a63`.
The tracked checker binds the producer blobs, proof identities, direct
dependencies, exact inputs, failure boundary, statement-only inventory, file
modes, and all no-credit counters.

## Verification

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-support-result.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_support_result
```

## Next

Record a revised bridge plan before another construction. Preserve the two
accepted native theorem identities and the remaining two exact-target
submissions. Do not graft `Nat.div_mod_exec`, inspect Mathlib proof bodies, or
treat statement availability as theorem evidence.
