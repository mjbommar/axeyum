# Lane: top-three-focus — autonomous production, connected knowledge, honest integration

<!-- plan-section: lane-status -->

**Turn the architecture review into executable product increments** (`WIP`,
top-three-focus, 2026-08-25). The durable plan is
[`../../top-three-focus-plan-2026-08.md`](../../top-three-focus-plan-2026-08.md);
the full lane history is in
[`../notes/126-top-three-focus.md`](../notes/126-top-three-focus.md).

Current boundary: one unchanged imported `Nat.mod` contract family advances the
frozen arithmetic `Nat.ModEq` siblings from 0/3 to 3/3. It rebuilds fuel
congruence, modulo recurrence, addition periodicity, and self-modulus over the
exact imported implementation. Every transport and independent admission has
an empty footprint and no hidden-target dependency. Public shortcuts carrying
`propext` remain rejected. It is the 27th authoritative registered operation,
and the full executor path now preserves each target's immutable stream hashes,
proof identity, and one named retained theorem dependency through execution,
transaction construction, and settled-fact replay. Zero facts are settled.
Its three historical assay/contract gates are correctly lifecycle-stable, and
the operation explicitly reviews their coupling. The first production episode
settled `Nat.add_modEq_left`: the intent-boundary fault changed no fact,
recovery performed exactly one write, settled replay passed, and the frontier
advanced to `addRight`. A second independently commit-bound episode has now
settled `Nat.add_modEq_right` through the same crash/recovery discipline and
advanced the frontier to `modulusZero`. The third fresh episode settled
`Nat.mod_modEq`/`modulusZero`; the family is now 3/3 durable, and the machine
frontier honestly returns no admissible registered target. Next: use the
measured zero-admissible boundary to select and register the next reusable
family, rather than adding one-off proof code. The three manually orchestrated
episodes have also been converted into a generic one-command runner: callers
choose only an external receipt directory; the frontier, registry, transaction,
intent fault, recovery, and settled checker choose and police everything else.

Priority 3 also repaired the CI-observed sub-millisecond budget escape: policy
now compares an unrounded monotonic duration while receipts retain integer
milliseconds. The focused 29-test tier-C suite and Ruff pass. Product health
still reports the older failed ancestor until a completed provider run is
captured.

Detail and older landed rows moved to [`../notes/126-top-three-focus.md`](../notes/126-top-three-focus.md).

<!-- plan-section: landed-changes -->

| 2026-08-26 | `98628e363` | Replace manual per-fact episode orchestration with a generic frontier-selected authoritative runner that retains crash-safe receipts and permits exactly one machine-selected ledger path to change. |
| 2026-08-26 | `aff331097` | Settle `Nat.mod_modEq` through the third fresh crash-safe episode; the imported Nat.mod family reaches 3/3 durable admissions and the frontier returns zero admissible registered targets. |
| 2026-08-26 | `04f75cdf9` | Settle `Nat.add_modEq_right` through a fresh crash-safe episode; exact `addModRight` dependency replay passes and `modulusZero` becomes the sole admissible target. |
| 2026-08-26 | `9db19bb4d` | Settle `Nat.add_modEq_left` through one clean crash-safe autonomous episode; exact proof/dependency replay passes and the durable frontier advances to `addRight`. |
| 2026-08-26 | `05553bd14` | Remove mutable-ledger coupling from immutable Nat.mod assay receipts, review the exact three gate mentions, and make all three registered targets frontier-admissible without bypassing the safety interlock. |
| 2026-08-26 | `cbaef1a1f` | Authorize the imported Nat.mod candidate family end to end: exact dependency names and immutable input/proof identities now survive execution receipts, fact transactions, and settled replay. |
| 2026-08-26 | `490c45ac3` | Add held-out-safe reviewed semantic coverage to the generated product-health authority while preserving separate autonomous-yield and runtime-status boundaries. |
| 2026-08-26 | `681a9b4be` | Add three reviewed local concept families and twelve proposition-level mappings; restore held-out-safe topic, fact-formalization, and kernel-anchor coverage in one checked projection. |
| 2026-08-26 | `8b3ef15bd` | Restore an actionable semantic-review path with three self-contained local concepts and three strictly qualified empty-footprint kernel anchors, without reviving any sibling-repository dependency. |
| 2026-08-26 | `f5695d52b` | Synchronize the semantic-review JSON and human census at 1,287 unreviewed theorems, and replace a deleted-link-dependent control with synthetic active/candidate mutations. |
| 2026-08-26 | `2b943b2e7` | Generate a hash-bound product-health snapshot from kernel, fact, connectivity, operation, producer-outcome, episode, and aggregate-gate authorities without converting static wiring into a runtime-green claim. |
