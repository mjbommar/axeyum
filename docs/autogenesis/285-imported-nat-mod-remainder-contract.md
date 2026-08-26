# Imported Nat.mod remainder contract

Date: 2026-08-26

## Result

The first implementation-local remainder contract converts one of the three
frozen arithmetic `Nat.ModEq` siblings. The proof-free modulus-zero target,
the independently exported candidate, source-to-source transport, bounded
application, and final target admission all succeed with an empty measured
axiom footprint and no dependency on the target declaration.

This is the first positive conversion after the 0/3 imported bridge assay. It
does **not** settle the fact or authorize an operation: the reusable-producer
bar remains one unchanged contract family converting at least three siblings
through the authoritative transaction path.

The durable receipt is
[`nat-modeq-remainder-contract-v1.json`](../../artifacts/autogenesis/nat-modeq-remainder-contract-v1.json).
The 419 KiB candidate capsule and 380 KiB proof-free target capsule remain
outside Git under the hash-bound `/nas3/data/axeyum/autogenesis/reference-packs/`
path recorded there.

## Why this proof matters

Lean 4.30 reports that the tempting public theorems `Nat.mod_self`,
`Nat.add_mod_left`, and `Nat.add_mod_right` all depend on `propext`. The new
`modSelf` candidate does not wrap any of them. It reduces the exact imported
`Nat.mod` definition, unfolds `Nat.modCore`, and follows the two required
`Nat.modCore.go` steps directly. Lean reports no axioms, and Axeyum independently
repeats that footprint measurement after transport and admission.

This confirms the earlier diagnosis: the sound route is behavior over the
actual imported implementation, not a same-name bridge to Axeyum's different
native definition.

## Next falsifiable step

Construct one implementation-local periodicity contract for `Nat.mod` that
specializes to both addition siblings. Then rerun the unchanged transport probe
and require 3/3 independent admissions before operation registration.

That bar is now met by the expanded
[`imported Nat.mod remainder family`](286-imported-nat-mod-remainder-family.md).
This 1/3 receipt remains the immutable first checkpoint.
