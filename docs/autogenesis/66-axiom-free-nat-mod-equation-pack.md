# Axiom-free Nat.mod equation pack

## Result

The first bottom-up primitives for the target-side `Nat.dvd_mod_iff` proof now
compose into the exact Mathlib 4.30.0 r082 target:

| Theorem | Role | Declaration identity | Axiom footprint |
|---|---|---|---|
| `Nat.mod.eq_2` | exposes the official wrapper's successor equation | `47a0f25d2575086bb8d8ad687beca4e69ef71644bb6057f55ec052d5c2084610` | empty |
| `Nat.modCore.go.eq_1` | exposes one checked fuel-recursion step | `aaf85a61edef7f6416bfccd8d817ca53c88cf7fe3d5b34bfbf166287e485448d` | empty |

These are generated equation theorems from Lean's definitions, not the
assumption-bearing high-level `Nat.mod_add_div` proof. They expose exactly the
computation needed for an induction over the official remainder
implementation while preserving the empty trusted footprint.

## Why this is the right layer

The previous audit found `propext` in official `Nat.dvd_mod_iff`,
`Nat.mod_add_div`, and `Nat.div_add_mod`. Their direct dependency audits locate
the assumption in tactic-generated proposition rewrites such as `Nat.div_eq`,
`Nat.mod_eq`, and simplification lemmas. That does not make the arithmetic
principle nonconstructive; it means those compiled proof terms are unsuitable
for Axeyum's empty-footprint library path.

The generated computation equations are different. The Lean kernel reports no
axiom in their complete 183-declaration export, and Axeyum independently
rechecks both roots. This permits a constructive proof to proceed bottom-up:

1. induct over `Nat.modCore.go` fuel;
2. use divisibility cancellation after each checked subtraction step;
3. lift the invariant through `Nat.modCore` and the `Nat.mod` wrapper; and
4. publish the resulting general `Nat.dvd_mod_iff` only after a fresh target
   kernel measures an empty footprint.

No equation is inferred from source text, and no theorem is trusted because
Lean labeled it generated.

## Exact composition evidence

The proof-isolated composition runner is commit
`dd79317c5495ba42bac14d855923b1f1cb40aad5`. It imports two streams, refuses a
non-empty source or target axiom inventory, composes only explicit theorem
roots into a private clone, replays the V5 receipt, and rejects any added
theorem whose kernel footprint is non-empty.

The immutable pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/dd79317c5-lean430-nat-mod-equations-v1/manifest.json`

| Artifact | SHA-256 |
|---|---|
| Pack manifest | `a41348a8fed7ebf1a877e5a48d86287c25a3216291da6c586909884f5f28c658` |
| Lean export | `bbb1136fef6c4dacd737ace4d797e3512dd85f290506f6d635cc069ec36035fb` |
| Audit report | `1969f848566fe3351a502f802ad098fd5ab1f5d84be9b40789fb61ba6e1a8db8` |
| Composition receipt file | `e5835c9e5f73548567de84c1ef127d6d009c5c712811938cdbd119f39f925d21` |
| Composition receipt | `804aabcf8a72f9ae5f4df04c7868d02b691472481917d5ff856bc02b987d1108` |

The source export has 183 admitted declarations and no axioms. Against the
261-declaration r082 target, the selected closure reuses 181 declarations and
adds exactly the two equation theorems. Source and independently admitted
target identities match for both; both footprints are empty. The target
environment moves from
`82ac7b0143bdd9891b666a37220fb91b86afc4af4b920d68773d80b5c9348855`
to
`52f7944c1b497460196465da64d170632aff481c97924e4fc36a8e2cb5fefda5`.
The directory is mode `0555` and all four files are mode `0444`.

## Authority and controls

The run admits 183 source declarations and 261 target declarations, then
admits two theorems during issuance and the same two during independent replay.
It performs zero proof search and zero ledger writes, and displays no proof
bodies. The tracked checker binds:

- the external manifest and every file hash and mode;
- Lean, lean4export, and composition-tool identities;
- the source and target axiom inventories;
- both theorem identities and empty footprints;
- the 183/181/2 closure partition;
- both target environment identities; and
- the exact replayed V5 receipt.

Mutation tests reject a changed footprint, closure size, or manifest identity.
The CLI also rejects either input stream before composition if its imported
axiom inventory is non-empty.

## Reproduction

```sh
cargo run -p axeyum-lean-import \
  --example lean4export_composition -- \
  /path/to/nat-mod-equations.ndjson \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson \
  Nat.mod.eq_2 Nat.modCore.go.eq_1

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Next bounded increment

Build the target-side fuel invariant
`k ∣ Nat.modCore.go y hy fuel x hfuel ↔ k ∣ x` under `k ∣ y`, using the
composed step equation and already checked native divisibility/subtraction
lemmas. Lift it through `Nat.modCore` and `Nat.mod`, then generalize the native
`Nat.dvd_mod_iff` signature to match official Lean before replaying
`Nat.dvd_gcd`. The equation pack alone does not establish any divisibility
theorem and receives no ledger credit.
