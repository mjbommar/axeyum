# Exact official Fibonacci coprimality

Date: 2026-08-20

## Result

The completed official Lean 4.30 support environment now accepts an ordinary
kernel theorem with the exact frozen r082 statement and official name:

```text
Nat.fib_coprime_fib_succ :
  forall n, Nat.Coprime (Nat.fib n) (Nat.fib (n + 1))
```

The target goal SHA-256 is
`a053d8f483f2cc1e79c53924baf5f79e4897ce992ca77722168cee20a6f5150f`,
exactly matching `Axeyum.Autogenesis.Coverage.r082`. The admitted theorem has
proof SHA-256
`baa3313f7b40ad1c73ae29de08deb9f0368e9fcf06fd318fea9c73822c7d6827`
and declaration SHA-256
`7fd9a1e811b93f8021ded1e34de5a816a0e9b23940e15cfcd5cbe81309daede9`.
Its kernel-derived axiom footprint is empty.

This closes the semantic gap left by the earlier native control. The proof is
checked against the official imported `Nat.fib`, `Nat.gcd`, and `Nat.Coprime`
definitions; it does not transport the native theorem by name or replace an
official definition with a compatible local definition.

## Axiom-free recurrence

Official `Nat.fib_add_two` reaches `propext` and `Quot.sound` through the
generic iterator equation. The exact route instead proves only the needed
pointwise iterator step and derives:

```text
Axeyum.Autogenesis.fibAddTwo (n : Nat) :
  Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)
```

Pinned Lean 4.30 reports both authored theorems axiom-free. The focused
lean4export stream contains 53 admitted declarations and no axioms. Axeyum's
independent importer assigns the recurrence declaration identity
`982c676b0656664e807c5e195bbdbd43376d78dec029bb3c409df661de39edb4`.

## Exact dependency boundary

The final theorem has exactly eight direct theorem dependencies:

1. `Axeyum.Autogenesis.fibAddTwo`
2. `Nat.add_comm`
3. `Nat.dvd_add_iff_right`
4. `Nat.dvd_gcd`
5. `Nat.eq_one_of_dvd_one`
6. `Nat.gcd_dvd_left`
7. `Nat.gcd_dvd_right`
8. `Nat.gcd_zero_left`

The recurrence closure composes with receipt
`1c073ec45fa0af03f8d2318afea9d8b106f8b65c86b69d7d3677587c5a36775b`.
The seven-root support environment retains receipt
`c4cedfbc21119852cd885829601434015971582165103f2580f29ea4e677ec67`.

Two fresh full executions are byte-identical. Each execution reconstructs the
final theorem twice in distinct target clones and compares its proof,
declaration, footprint, and dependency identities. Four ordinary final-theorem
kernel submissions therefore agree; no search or ledger write occurred.

## Immutable evidence

The generated Lean export remains outside Git in the read-only pack:

`/nas3/data/axeyum/autogenesis/reference-packs/d12736b63-lean430-exact-fibonacci-coprimality-v1/manifest.json`

Its manifest SHA-256 is
`69a99345f384dc906b34196958fe5a1863665da7fc27eb1c62054f57fffff109`.
The directory is mode `0555`; all seven files are mode `0444`. The repository
checker binds the historical implementation blobs, authored source, focused
export, Lean and importer audits, all upstream inputs, two byte-identical
results, exact target identities, dependency set, and zero-credit boundary.

## Reproduction

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_gcd_succ_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  /path/to/nat-gcd-bridge.ndjson \
  --exact-target /path/to/fib-recurrence.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Authority boundary and next step

An accepted theorem is the candidate evidence required for a semantic receipt;
it is not the receipt itself. ADR-0504 and ADR-0505 require preregistration,
fresh reconstruction, exact receipt replay, and only then the ordinary
crash-safe fact transaction. Accordingly this increment issues no semantic
receipt, claims no evaluation credit, changes no fact status, and writes no
ledger state.

Next, bind the exact target, proof, declaration, dependency, source, and
observation identities in the preregistered authority; issue the semantic
theorem receipt twice from fresh reconstructions; then attempt the fact
transition with the checked receipt as its sole evidence authority.
