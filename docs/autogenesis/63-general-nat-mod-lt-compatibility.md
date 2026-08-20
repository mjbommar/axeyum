# General Nat.mod_lt compatibility

## Result

Native `Nat.mod_lt` now states and proves Lean's general positive-denominator
contract:

```text
forall x y, 0 < y -> Nat.mod x y < y
```

The native kernel checks the proof by induction on `y`. At zero, the positivity
witness is impossible; at a successor, the proof projects the remainder bound
from the existing checked `Nat.div_mod_exec` relation. GCD and Bezout consumers
construct `0 < succ k` explicitly and apply the general theorem.

The unchanged Mathlib r082 `Nat.dvd_gcd` composition control now passes
`Nat.mod_lt` and stops at the missing recursive inductive `Acc` package.

Follow-on result [64](64-canonical-acc-composition.md) closes that exact
package boundary and advances the unchanged control to target-kernel rejection
of `Nat.div_mod_exec`.

## Exact evidence

The implementation commit is `a5a1114989077b7254a5dec0daa048aa5d2793ba`.
The read-only compatibility API and evidence commit is
`ac33a0a2d8508d2123b23cfc9959da38d1b9ad37`.

The immutable observation is:

`/nas3/data/axeyum/autogenesis/probes/ac33a0a2d-nat-mod-lt-compatibility-v13/observation.json`

| Artifact | SHA-256 |
|---|---|
| Mathlib r082 stream | `6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd` |
| Composition probe | `51b896dfc78747aa36d3903c8a25be8ebc7956c910ea2e574fd326704e657698` |
| Compatibility/composition API | `d2a6e191ca8d517b5cae74eb5b273f454389c3140eaeed1c07c3938cabcaf654` |
| Native prelude surface | `0f158d8ba4e2ed9d18bf618002ce2584188cbefeb17d7ab82297a76c9819acec` |
| Native Nat operations | `85e0c9e5e0cde8a6014a950baf44f764265c041d391b1cb9c7e54005a718b139` |
| Native GCD proof | `52ab374341afb28ec2940b6381697d6959097f74afbef3ab99fae0f8d75d8309` |
| Native Bezout consumer | `27bbdf48b8703304ee85b1294b519f6558aa259fd9701844a35dd5ce8d5c1ed4` |
| Observation | `29fc6b096e28e7f99b8005e86673259b3b1e3686778af6b0e452d4f31be079c1` |

Two warm executions were byte-identical. The observation directory is mode
`0555` and the file is mode `0444`.

## Compatibility receipt

The overlap census remains intentionally coarse: `Nat.mod_lt` stays among the
seven wrapper-level type-shape mismatches. Its native statement uses direct
`Nat.lt` and `Nat.mod`; the import uses `LT.lt`, `OfNat.ofNat`, `HMod.hMod`, and
their instances. That bucket alone cannot establish reuse.

The new read-only named check runs the actual composition compatibility policy
and records:

| Field | Value |
|---|---|
| Name | `Nat.mod_lt` |
| Compatibility | `translated-definitional-equality` |
| Native declaration | `4dcd688e98a17ae946a8f7def4bcc5cb590edac930b3fa5e9de9e2babd3060f7` |
| Imported declaration | `34e06b0574c094ba8dc2e317ef541822292b21cd0295e0f8126af92e4ab0f305` |
| Native type shape | `bab8f0787af5b6f65728ff310696471b6fe776754fdd8e16d199c2ade1976171` |
| Imported type shape | `22c2f033e81299ffa23212d921c3e90552bfc1e5d310fbc7c12cfde5a6af6bc2` |

The different identities are important: this is not exact reuse. Translation
reconstructs the native type in a target clone, the target kernel infers that it
is a type, and target definitional equality compares it with the imported type.
That result only authorizes the later composition attempt.

## Validation and trust boundary

The generalized theorem has an empty kernel-derived axiom footprint. Its exact
rendered type, concrete application, and old-order rejection are pinned. All
393 pre-existing kernel unit tests passed, followed by the new focused test.
The theorem-composition suite has direct controls for translated equality,
real mismatch, and missing target names; all ten tests pass. All-target importer
and kernel Clippy pass with warnings denied, as does formatting.

[ADR-0528](../research/09-decisions/adr-0528-native-nat-mod-lt-uses-the-general-positive-denominator-contract.md)
makes the distinction explicit: named compatibility is read-only attempt
authority. It performs no kernel submission and cannot publish a declaration.
Only completed target-kernel composition can add durable library material.

## Next measured gap

The unchanged `Nat.dvd_gcd` control now declines with:

```text
UnsupportedMissingDeclaration { name: "Acc", kind: "recursive-inductive" }
```

Its target environment digest is unchanged before and after. The next
bottom-up increment should inspect the complete native/imported `Acc` family,
constructor, and generated recursor, then define an atomic reconstruction gate
for exactly that recursive singleton package. Recursive/mutual inductives must
remain unsupported until the target kernel independently checks the complete
package and rollback/mutation controls prove partial publication impossible.

## Reproduction

```sh
CARGO_TARGET_DIR=/data0/axeyum/codex-nat-mod-lt-target \
  cargo run -p axeyum-lean-import \
  --example nat_prelude_composition_probe -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson \
  /path/to/observation.json

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```
