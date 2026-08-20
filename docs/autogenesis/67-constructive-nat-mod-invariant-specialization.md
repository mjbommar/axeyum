# Constructive Nat.mod invariant specialization

## Result

The missing target-side remainder theorem now exists as an independently
checked, axiom-free theorem over the imported Lean 4.30 `Nat.mod`:

```text
Nat.dvd_mod_iff :
  forall k d x, Nat.dvd k (Nat.succ d) ->
    (Nat.dvd k (Nat.mod x (Nat.succ d)) <-> Nat.dvd k x)
```

Its declaration identity is
`7f785ea99cdfd9ca1e5e4a7044f2c53bc3a0255fa4143532ebcb26bef4d671a8`.
Its kernel-derived axiom footprint is empty. Its type-shape identity is
`82789b0e69792f3d2308a32b4c6f108fef63bbded868e066fed2422a1b49019e`,
exactly equal to the native Axeyum theorem's type shape.

This closes the construction problem isolated by the 92-declaration
`Nat.dvd_gcd` closure. It does not yet close `Nat.dvd_gcd`: the current
source-root closure algorithm still walks through the native proof behind an
already compatible target theorem and therefore unnecessarily rediscovers the
incompatible native `Nat.div_mod_exec` path.

## Constructive proof

The authored source is
[`scripts/lean/autogenesis_nat_mod_invariant.lean`](../../scripts/lean/autogenesis_nat_mod_invariant.lean).
It imports only `Init` and proves three layers:

1. `modCoreGo_invariant` performs induction on the explicit fuel of
   `Nat.modCore.go`. Each recursive subtraction preserves an arbitrary
   predicate `D` through an explicit step equivalence.
2. `modSucc_invariant` lifts that fuel theorem through `Nat.modCore` and the
   official successor equation `Nat.mod.eq_2`.
3. `modSucc_dvd_iff` instantiates `D` as divisibility by `k`. It keeps the
   divisibility predicate, additive cancellation theorem, subtraction
   restoration theorem, and addition commutativity theorem as explicit
   parameters.

The proof does not import official `Nat.dvd_mod_iff`, `Nat.mod_add_div`, or
`Nat.div_add_mod`. Those convenient high-level Lean 4.30 proofs reach
`propext`; the new proof follows the two empty-footprint generated computation
equations directly.

## Independent import and composition

The pinned Lean 4.30 toolchain compiles the module, and lean4export commit
`a3e35a584f59b390667db7269cd37fca8575e4bf` exports its final root as a
6,971-line stream. Axeyum independently admits 211 declarations and reports no
axioms. The three authored theorem identities are:

| Theorem | Declaration identity | Footprint |
|---|---|---|
| `Axeyum.Autogenesis.modCoreGo_invariant` | `d2c5b7f22ba8be2944cf3a4a864250b40410de6bda746b026023f555efa66b14` | empty |
| `Axeyum.Autogenesis.modSucc_invariant` | `3edbf74b7eb077da928a8ca499823419449791a72e654b885e1920e15df2952e` | empty |
| `Axeyum.Autogenesis.modSucc_dvd_iff` | `cc6cb4ce64e5c30b3f8ff36cbc5c6c14f19dae1b57c51a6df095a07e9851a43e` | empty |

Composing the generic final root into r082 selects all 211 source declarations,
reuses 184, and independently adds 16 theorems plus eight definitions and one
singleton inductive package. Every added theorem has an empty footprint. The
V5 composition receipt digest is
`95774f7e022659cb41f792e3049d533035dee561c50064bab5e33f9e2f254b3e`.

A second native-helper composition selects 49 declarations rooted at
`Nat.dvd_add_iff_right`, `Nat.sub_add_cancel`, and `Nat.add_comm`. It reuses 23,
adds 21 empty-footprint theorems and two definitions, and replays receipt
`df4704110bd0458ce772302fd3eca5a873c6704cec12de7451363e26aeae6e07`.

## Checked specialization boundary

ADR-0530 introduces `specialize_checked_theorem`. The operation:

- accepts one checked generic theorem and ordered named declaration arguments;
- applies and infers them in a private clone;
- admits the inferred proposition through the ordinary theorem gate;
- rejects a non-empty axiom footprint;
- publishes only a completed owned kernel; and
- binds source, arguments, target, footprint, and both environment identities
  in a replayable receipt.

For this proof the ordered arguments are:

```text
Nat.dvd
Nat.dvd_add_iff_right
Nat.sub_add_cancel
Nat.add_comm
```

The specialization receipt digest is
`f03cd55d79467478528e24cdc347e6f9945a3eb1c49064e075176068451e358d`.
Controls reject a wrong-typed argument, an existing target, and receipt
mutation. All failure paths leave the caller environment unchanged.

## Immutable evidence

The generated stream is intentionally not vendored. The immutable external
pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/667201932-lean430-nat-mod-invariant-v1/manifest.json`

| Artifact | SHA-256 |
|---|---|
| Pack manifest | `ba31490c95fbd9b08005fcc0517fe6c09645d63c216005be0a795be85a15ef0e` |
| Authored source copy | `6afdadc9efae226348d73e6c4024608a1566973d16d24a29ab3e8176424f07bc` |
| Lean export | `5d945b100f3e2939d6ea3ffa67e10b4d78ff9efb7782a56f3d67468aa167ebf9` |
| Theorem audit | `f67c50e0faafd5dcad1ba418b5442763ae8d7eb8db7de1987007997541c479fb` |
| Specialization result | `54d2a0805cf41f3c1e5c9cf9592848e665d6341d5ff5e23bdd14d1889b330575` |

The directory is mode `0555`; all five files are mode `0444`. The tracked
checker verifies the complete file set, hashes, modes, tool and source
identities, source/target axiom inventories, theorem audit coverage,
composition counts and receipts, explicit arguments, native type
compatibility, and the empty specialized footprint. Mutation tests alter each
authority class and require a nonzero result.

## Reproduction

```sh
export PATH=/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH
lean scripts/lean/autogenesis_nat_mod_invariant.lean

cargo run -p axeyum-lean-import \
  --example nat_mod_invariant_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next bounded increment

Define a target-leaf theorem composition contract: when the source closure
reaches a theorem already present in the target, require explicit compatibility
and stop traversing the unrelated source proof behind that theorem. Add
positive and mutation controls proving that the cut is exact, target-owned,
and replayable. Then retry the unchanged `Nat.dvd_gcd` root with the newly
specialized `Nat.dvd_mod_iff` as the leaf. No ledger credit is due until the
downstream theorem and its intended fact transition independently close.
