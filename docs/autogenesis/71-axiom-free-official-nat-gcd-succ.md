# Axiom-free official `Nat.gcd_succ`

Date: 2026-08-20

## Result

The official r082 `Nat.gcd` implementation now has an independently accepted
successor computation theorem with an empty kernel-derived footprint:

```text
Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m)
```

This is not the earlier native theorem transported by name. The authored proof
unfolds the exact official `Nat.gcd`/`WellFounded.Nat.fix` implementation, and
the target kernel checks the translated term against that official definition.

## Removing the hidden quotient dependency

Lean's generic fuel-congruence theorem compares complete recursive functions.
It uses function extensionality and reaches `Quot.sound`. Euclid's algorithm
needs much less: equality at one pair `⟨m,n⟩` and, in the nonzero case, at its
single recursive successor `⟨n % m,m⟩`.

The replacement therefore inducts pointwise over the two fuel values:

- impossible zero-fuel branches eliminate the contradictory decrease proof;
- the `m = 0` branch reduces definitionally to `n`; and
- the nonzero branch applies the induction hypothesis only to the concrete
  modulo successor.

No equality between recursive functions is constructed. Pinned Lean 4.30 and
the independent Rust importer both report an empty footprint.

## Checked specialization chain

The authored theorem keeps the modulo decrease fact explicit. The checked
pipeline then performs two named specializations:

1. `Axeyum.Autogenesis.modLtSucc` receives the established target theorem
   `Nat.mod_lt`, producing `Axeyum.Autogenesis.ModLtSucc` with receipt
   `a605a5db994eecefef2c5061126c7e472072dcf37b481d4590b23f991ece63f2`.
2. `Axeyum.Autogenesis.nat_gcd_succ` receives that theorem, producing
   `Nat.gcd_succ` with receipt
   `993468eba57cf6f789f11019d9a2b83194822d5e98f71cceb371d22a7d663a93`.

The final declaration SHA-256 is
`e41996f98e01e15b88e11773bb42db825bf271888ece2d002c193627a8392727`.
Its type is checked as translated-definitional-equality compatible with the
native `Nat.gcd_succ`; compatibility authorizes the subsequent target check and
does not substitute definitions.

## The frontier moved

With these explicit target-owned leaves:

```text
Nat.dvd_mod_iff
Nat.mod_lt
Nat.gcd_succ
```

the 57-declaration native `Nat.dvd_gcd` closure now composes successfully into
the official target. It adds five theorems and four definitions, has empty
added footprints, and replays with receipt
`5be80180f535cce7a42d9ac9b87f2e7fe716479a3aaf3f2108fdc00fe40a3261`.

Two fresh complete executions produce byte-identical observations. No proof
search, fact transition, evaluation credit, or ledger write occurred.

## Immutable evidence

The sealed pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/f94489c74-lean430-nat-gcd-succ-bridge-v1/manifest.json`

Its manifest SHA-256 is
`7190676a198599fd7d4f14bb5cb0a83f2a8d9806be7d5803e3de920cf8e77637`.
The directory is mode `0555`; all eight files are mode `0444`.

## Reproduction

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_gcd_succ_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  /path/to/nat-gcd-bridge.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next

Compose the remaining six required gcd/divisibility support theorems over this
new target, then reconstruct the exact official r082 Fibonacci-coprimality
statement. A semantic theorem receipt and fact-ledger transition remain
forbidden until that exact target passes an ordinary kernel gate.
