# Semantic abstraction debt census

Date: 2026-08-19

## Result

The 114 generalized Mathlib train/development slices contain 152 definition
bindings, representing 244 source occurrences. A fresh kernel imported each
exact definition identity once, verified its canonical source identity, and
measured its type, transparent body, normalization, and trusted implementation
closure. The census generated no contract, proof, operation, or ledger credit
and did not inspect held-out.

| Contract shape derived from checked type | Exact identities | Bindings |
|---|---:|---:|
| Predicate equivalence | 5 | 73 |
| Pointwise function equation | 15 | 50 |
| Nullary observational projections | 12 | 29 |
| **Total** | **32** | **152** |

The most important result is an identity warning: **30 rendered names denote
32 exact source identities**. `Int.gcd` and `Nat.gcd` each occur with two
different source-content identities across export contexts. A semantic
contract registry or cache keyed by a printed name would silently conflate
different checked declarations. The complete content, instantiated type, and
universe identity must be the key.

The exact observation has semantic identity
`3c2a5d670255f9911ba96e4219803dbe7a61838407610785ca82cec78b5c3c6a`
and file identity
`215372dc525a6467b51e598c9ca54d18540cf538a45e4119f8f9bb6098c1ba00`.
It reproduces the exploratory run byte-for-byte.

## What the closure counts mean

Across the 32 independently imported identities, the normalized transitive
implementation closures contain 6,346 theorem, 27 axiom, 20 quotient, and 7
opaque name occurrences. These are diagnostic costs, not proposed premises.
Twenty-nine identities have zero direct theorem dependencies. The large count
mostly arises below transparent helpers and generated structures, supporting a
narrower design: residualize the behavior actually needed as an explicit local
obligation and discharge it against the exact source definition.

Copying the transitive closure into a producer would import upstream answers.
Treating a behavior equation as an axiom would merely hide the missing proof.
Both would improve apparent yield while weakening the trusted result.

## Sequenced next state

ADR-0488 settles the boundary before implementation:

1. key contracts by exact source content, instantiated type, and universes;
2. add contracts as local Pi-bound premises, never global axioms;
3. derive proposals only from transparent source behavior without target proofs
   or held-out outcomes;
4. independently check a source-specialization witness and bind its complete
   dependency footprint in the receipt; and
5. grant concrete fact credit only when the witness is axiom-free or every
   premise is independently established under ordinary ledger policy.

The first bottom-up prototype is one small pointwise function equation with
wrong-identity, wrong-equation, circularity, and dependency controls. Top-down,
proof-plan work can proceed independently on the 24 exact slices. Only after
both controls pass should broader producers consume semantic contracts across
the 114 generalized goals. Predicate equivalence is the next contract family;
nullary instances require projection-level demand analysis and remain later.

## Reproduction

```sh
cargo run -p axeyum-lean-import --example semantic_abstraction_census -- \
  --archive /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1 \
  --observation /nas3/data/axeyum/autogenesis/producer-census/10ab370a9-mathlib-v4.30.0-reflexivity-v1/observation.json \
  --output observation.json
python3 -m unittest scripts.tests.test_check_autogenesis_semantic_abstraction_census
python3 scripts/check-autogenesis-semantic-abstraction-census.py
```
