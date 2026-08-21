# agent-retire-real — the last 30 axioms: what moved, what did not, and why

Detail behind [`docs/plan/status/64-retire-real.md`](../status/64-retire-real.md).
The decision is [ADR-0509](../../research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md);
the measurement is `F:shipped-front-door-reaches-no-real-axiom`.

## Re-measured, 2026-08-18

The brief carried numbers from an earlier survey. What is actually there:

| quantity | brief | measured |
|---|---|---|
| `.rs` files naming the `Real` package | 22 | **30** |
| non-test `src` call sites building it | — | **4** (`LraReconstructCtx::try_new` + the ℤ/ℚ/`CReal` models) |
| shipped routes reaching it | 0 (implied) | **1** (`ProofFragment::IntFarkas`) |
| trusted surface | `real: 30`, rest 0 | confirmed, `total=30 retired=35 axiom_free=7` |

The brief's claim that "the shipped front door reconstructs over `CReal` with
zero carrier axioms" is true of `Lra`/`DisjunctiveLra`/`Sos` and was **false of
`IntFarkas`**, which is also on `prove_unsat_to_lean_module`. That arm built the
`Real` package, refuted there, λ-abstracted all 30 constants out with
`generalize_over_ordered_ring`, and instantiated at ℤ via
`build_int_model_of_arith` — which builds the package a second time. Because the
scan trial-builds the module to classify (`int_farkas_reconstruction_certifies`),
an integer query paid for the whole trusted surface twice before the front door
returned.

Nothing could see it. Every check for this claim reads the finished term's
`axiom_footprint`, and that footprint was genuinely empty. The gate named for the
claim, `examples/front_door_carrier.rs --require-axiom-free`, has three fixtures
and all three are real-typed, so they route to `Lra` and `Sos` and never reach
the integer arm — the repository's standing trap, a correct empty answer to a
question the tool was never asked.

## The fix needed no new mathematics

`IntPrelude` already carried all 30 signature fields under the same names, every
law proved, with the kernel's own `Eq` as ring equality — `Int` is a
one-constructor inductive with no setoid over it. `RingSignature:
From<IntPrelude>` is therefore the third instance of the interface and the only
one that is both axiom-free and at kernel equality (`Real` has `Eq` at 30
axioms; `CReal` is free but its equality is the defined `CReal.Equiv`).

`build_int_model_of_arith` reports `identical: true` for all 22 laws, i.e. the
interpreted `Real` axiom is *syntactically* the `Int` theorem after renaming, so
the mapping was already kernel-checked. The signature test asserts exactly that,
field for field, which is what makes it catch a transposition.

## Mutation checks (both required "exactly one test dies")

1. `le_refl := Int.le_trans` in `From<IntPrelude>`: **1 test dies**, the
   field-for-field cross-check. Without that cross-check **0** die — the
   transposition validates (both are propositions in the ring language) and the
   baby-Farkas fixture never uses `le_refl`. That is why the cross-check exists.
2. Restore the pre-change body of `reconstruct_int_farkas_to_lean_module`:
   **1 test dies**, the new reach test. All **9** tests of
   `tests/farkas_over_the_integers.rs` — the suite named for that route — pass
   under the mutation, because they assert on the module and the footprint and
   both were already clean.

## What was NOT done, and the two things that block it

Declared surface is still 30. Retiring it means deleting `build_arith_prelude`,
and two consumers make that a migration rather than a deletion:

- the three relative-consistency models (ℤ, ℚ, `CReal`) are statements **about**
  the package, computed from the axioms as they stand in the environment;
  `F:real-axioms-modelled-by-constructed-setoid` would become unstatable;
- the package is the **negative control** in `front_door_carrier
  --require-axiom-free`, `ordered_ring_refutation --require-empty` and
  `signature_tests`. Each of those fails if the `Real` column comes back empty.
  Deleting it removes the only thing that can make an axiom-freedom measurement
  here fail.

ADR-0509 records the bounded route out of both: pin the ledger's digests onto the
axiom-free 30-binder telescope `generalize_over_ordered_ring` already produces
(it *is* the interface, stated in the kernel, assuming nothing), and shrink the
control from 30 axioms to one declared for the purpose. Then
`--accept-population-change` publishes the 30 rows as retired.

## Incidental

`rustup run stable cargo clippy --workspace --all-targets --all-features
-- -D warnings` was **red on `main`** before this lane started: `minted_axioms_of`
and `is_query_local` are `pub fn` in the private `ordered_ring` module, called
only from `#[cfg(test)]` code, and re-exported nowhere. `ebb56ec5c` tried to
unbreak it by naming the function in a `capabilities.rs` doc comment, which does
not make it live. `minted_axioms_of` now sits beside `carrier_axioms_of` in all
three re-export lists.

Also worth knowing: `LraReconstructCtx` over `CReal` costs ~98 s of test time per
binary against ~1 s over `Int`, so a test that only needs *an* axiom-free ordered
ring should take the integer context.
