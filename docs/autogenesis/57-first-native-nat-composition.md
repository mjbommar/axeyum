# First checked native-library composition

Date: 2026-08-20

## Result

Axeyum has admitted its first native axiom-free theorem slice into a real
proof-isolated Mathlib environment. Starting from the checked `r082` import, a
probe-local transaction:

1. built the native Nat library in a separate kernel;
2. selected the root closure of `Nat.add_comm`;
3. compared every reused declaration with the binder-insensitive kernel-type
   identity;
4. translated only the three absent theorem declarations into a cloned imported
   kernel;
5. submitted each translated proof through the ordinary independent trusted
   gate; and
6. published the clone only after all three admissions succeeded.

The reused declarations were `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Eq`,
`Eq.refl`, `Eq.rec`, and `Nat.add`. The admitted declarations were
`Nat.zero_add`, `Nat.succ_add`, and `Nat.add_comm`. Each admitted theorem has an
empty kernel-derived axiom footprint. The environment digest changed from
`798b19a16b1e6937d4fc9eb6f0c2f5f58c5544d5ea58641c7aa04119dc6b0982` to
`68d95b32414757044ce3433fbf8c069b9304eca42d3d261ecff8ef6bb9131085`.

This matters beyond one commutativity lemma. It demonstrates the missing arrow
between imported statements and Axeyum's bottom-up theorem library: compatible
imported declarations can remain authoritative while fresh native proof terms
are independently rechecked against their actual definitions.

## Fail-closed control

The same transaction was rooted at `Nat.eq_one_of_dvd_one`, whose closure
reaches structurally different imported order declarations. It declined at
`Nat.zero_le` before admission. The caller environment digest was identical
before and after the failed attempt:
`798b19a16b1e6937d4fc9eb6f0c2f5f58c5544d5ea58641c7aa04119dc6b0982`.

The trusted gate is stronger than the compatibility diagnostic. Type-shape
agreement merely authorizes an attempt; each translated proof must still infer
to its declared proposition in the actual imported environment. The transaction
does not replace or mutate any imported declaration.

## Boundary and next step

At this historical checkpoint the implementation remained inside the
measurement example. ADR-0523 and the subsequent
[public checked theorem composition](58-public-checked-theorem-composition.md)
have now promoted the exact theorem-only, completed-clone boundary and added the
required incompatible-type, unsupported-kind, free-variable, partial-staging,
receipt-replay, and unchanged-caller controls. This document retains the first
probe-local observation rather than rewriting its evidence identity.

No Fibonacci theorem was submitted, no proof search ran, no proof body was
displayed, and no ledger row changed. Three native library proofs were submitted
to the probe-local imported kernel and independently accepted.

## Evidence

The immutable observation is
`/nas3/data/axeyum/autogenesis/probes/9caac0bf5-nat-add-comm-composition-v5/observation.json`.
It is read-only inside a read-only directory and binds the exact source stream,
probe, declaration receipts, environment transition, axiom footprints, and
negative-control transition.

Verify it with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```
