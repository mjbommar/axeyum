# Mathlib reflexivity coverage census

Date: 2026-08-19

Tooling commit: `cacc8f700f328a745250caf564bdcec9e03920a1`

## Result

The first sealed bottom-up census classified all 138 train/development facts
and opened no held-out fact. Every row received its own minimal-module,
proof-free transparent `Prop` definition and isolated `lean4export` stream. The
independent importer and bounded reflexivity producer then ran from a fresh
kernel per row. No executor budget was consumed and no ledger write occurred.

| Boundary | Rows |
|---|---:|
| Adapter rejected a proof-bearing/trusted dependency | 114 |
| Adapter admitted; terminal goal was not exact equality | 15 |
| Producer emitted `Eq.refl`; independent kernel rejected it | 7 |
| Independently checked, dependency-free reflexivity proof | 2 |

Two complete observations—one exploratory and one from clean commit
`cacc8f700`—are byte-identical at
`4515d41797f37bd4282feb1fedc85fa7246e9929be491b4f452f698439e7e202`.
The read-only external archive and all 138 streams are bound by
[`mathlib-reflexivity-coverage-v1.json`](../../artifacts/autogenesis/mathlib-reflexivity-coverage-v1.json).

## The reusable success

The already-admitted `Nat.ascFactorial` zero fact reproduced its original goal
and proof identities. More importantly, the same generic producer independently
checked a second frozen train fact:

```lean
∀ (n : ℕ), n.descFactorial 0 = 1
```

| Property | Result |
|---|---:|
| Fact | `F:ml430-nat-descfactorial-zero-966b01df` |
| Goal SHA-256 | `84c2cb6ba48868786799c28aef4104a845cf9d238ff6786285645562570c5d23` |
| Proof SHA-256 | `15725b2125daf99a7f779d218f36de67fe85dc42eaae4e1db23f55e5b628856a` |
| Binders / constructed nodes | 1 / 4 |
| Axioms / theorem dependencies | 0 / 0 |
| Target-definition dependency | false |
| Ledger writes | 0 |

This is the first evidence that the operation family, rather than only one
exact fact, is reusable. The row remains open: a checked diagnostic candidate
is not a registered authoritative execution or proof credit.

## What the 114 rejections mean

They do **not** mean 114 propositions require those theorems, and they are not
proof-search failures. The current exporter follows full definition bodies
reachable from constants in a statement. Many such bodies contain theorem,
axiom, opaque, or quotient declarations irrelevant to merely presenting the
target type. The strict adapter correctly refuses that stream rather than
smuggling assumptions into the producer environment.

The first attempted all-target stream made this coupling worse: one
proof-bearing closure contaminated every row. It was rejected before coverage
and is retained as a negative probe. Per-target streams exposed 24 genuinely
clean adapter paths and made the stage counts falsifiable.

## Sequencing over the horizon

Bottom-up, generalize the registered operation from one exact fact to the
smallest source-bound natural-factorial zero family, then run the ordinary
crash-safe admission protocol for the still-open `descFactorial` fact.

Top-down, the next high-leverage capability is a checked **type slice**: export
or reconstruct exactly the declarations required to type a proposition while
excluding irrelevant proof-bearing implementation closure. Its contract must
still fail closed on any proposition-valued assumption, bind every abstracted
constant's type identity, and preserve enough transparent computation for the
kernel to decide definitional equality. Broadening search before this seam is
closed would leave 114 of 138 rows unreachable.

The seven kernel rejections and fifteen producer declines are the next honest
search curriculum only after their adapter paths remain proof-isolated. Held-out
rows stay sealed until a family operation and type-slice policy are frozen.

## Reproduction

```sh
python3 -m unittest scripts.tests.test_create_autogenesis_reflexivity_coverage_input
cargo test -p axeyum-lean-import --example statement_reflexivity_coverage
python3 -m unittest scripts.tests.test_check_autogenesis_reflexivity_coverage
python3 scripts/check-autogenesis-reflexivity-coverage.py
```
