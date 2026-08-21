# Native Fibonacci coprimality

Date: 2026-08-20

## Result

The bounded induction selected in the Fibonacci-coprimality premise plan is now
an independently accepted theorem in the completed native Nat kernel:

```text
forall n,
  Nat.gcd (Nat.fib n) (Nat.fib (Nat.succ n)) = 1
```

Two fresh reconstructions produce the same goal, proof, theorem declaration,
empty kernel-derived axiom footprint, and direct theorem dependency set.

| Object | SHA-256 |
|---|---|
| Goal | `36a50e432178b2a22463e13ace748a078b989f6670eb97638fb7884a3df2ba86` |
| Proof | `e4af20e137001895506d5ccc11e2f4aa5186fe575c9b0ce61bd3fa51c6ca9efe` |
| Theorem declaration | `72edaaed9362afed68cfc03ff99b619435130bb16c8229e41b1c3188091a3e6a` |

The theorem is `Axeyum.Autogenesis.NatFibCoprimeSucc`. This is a real native
library theorem, but it is not yet the durable Mathlib fact described by r082.

## Proof

The proof is the preregistered induction, expressed directly as a kernel term.

At zero, imported `Nat.fib` computes to zero and one, and native
`Nat.gcd_zero_left` closes the goal definitionally.

For the successor step, write:

```text
a = fib n
b = fib (n + 1)
c = fib (n + 2)
d = gcd b (b + a)
```

The admitted Fibonacci recurrence and `Nat.add_comm` give `c = b + a`, hence
`gcd b c = d`. The native gcd projections show `d ∣ b` and `d ∣ b + a`.
`Nat.dvd_add_iff_right` cancels the known divisible `b`, giving `d ∣ a`.
`Nat.dvd_gcd` gives `d ∣ gcd a b`; transporting across the induction hypothesis
gives `d ∣ 1`; `Nat.eq_one_of_dvd_one` gives `d = 1`.

The kernel reports exactly these direct theorem dependencies:

1. `Axeyum.Autogenesis.NatFibAddTwo`
2. `Nat.add_comm`
3. `Nat.dvd_add_iff_right`
4. `Nat.dvd_gcd`
5. `Nat.eq_one_of_dvd_one`
6. `Nat.gcd_dvd_left`
7. `Nat.gcd_dvd_right`
8. `Nat.gcd_zero_left`

The first is the sole previously admitted fact premise. The other seven are
the exact axiom-free native surface frozen before execution. No search ran.

## Why the r082 fact remains open

The r082 target definition renders as:

```text
forall n, Nat.Coprime (Nat.fib n) (Nat.fib (n + 1))
```

Its exact goal digest is
`a053d8f483f2cc1e79c53924baf5f79e4897ce992ca77722168cee20a6f5150f`.
In the official environment, `Nat.Coprime` unfolds through the official
`Nat.gcd` definition. The accepted theorem unfolds through Axeyum's separately
constructed native `Nat.gcd` definition.

Those constants have the same name and compatible type, but that does not make
their values or dependency closures identical. Under ADR-0524, same-name type
compatibility authorizes an independent target check; it does not authorize
definition substitution or theorem credit. Treating the native proof as the
r082 proof now would erase the exact semantic boundary the flywheel is meant
to police.

## Immutable evidence

The generated observations are stored outside Git in the read-only pack:

`/nas3/data/axeyum/autogenesis/reference-packs/8403e6f65-native-fibonacci-coprimality-v1/manifest.json`

Its manifest SHA-256 is
`e068326d75717014d5425ff4566e4e3d0cc355a77fbf2b898fda004f037a86e6`.
The tracked checker binds the exact inputs, historical implementation blobs,
two-reconstruction theorem identities, dependency set, target statement,
zero-receipt boundary, and immutable file modes.

## Verification

```sh
cargo run -p axeyum-lean-import \
  --example nat_fib_iterate_recurrence -- \
  --native-coprime-control --stream /path/to/r080.ndjson

cargo run -p axeyum-lean-import \
  --example nat_fib_native_definition_probe -- \
  /path/to/r082.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next

The first explicit bridge is now complete: a target-specific pointwise fuel
proof reconstructs official `Nat.gcd_succ` without `Quot.sound`, and
`Nat.dvd_gcd` composes over that checked target leaf. See
[Axiom-free official `Nat.gcd_succ`](71-axiom-free-official-nat-gcd-succ.md).

All seven planned support roots now compose together; see
[Official Fibonacci coprimality support surface](72-official-fibonacci-support-surface.md).
Reconstruct this exact official target statement next. Same-name reuse,
quotient assumptions, and unproved computation equations remain forbidden.

Only after that bridge lets the target statement pass an ordinary kernel gate
may Autogenesis issue a semantic theorem receipt and attempt the crash-safe fact
transition.
