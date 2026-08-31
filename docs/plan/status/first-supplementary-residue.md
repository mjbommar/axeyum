# Lane: first-supplementary-residue

<!-- plan-section: lane-status -->

Status: DONE — the residue half of the first supplementary law is proved,
axiom-free. With ADR-1230's non-residue half, **both halves of the law are
proved**; the biconditional is not carried by any single declaration.

## Target

`p ≡ 1 (mod 4) ⟹ −1 IS a quadratic residue mod p`, the half ADR-1230 left
open. Its route note held: Wilson's theorem supplies the witness (`m!`) with no
converse of Euler's criterion anywhere.

## Landed

| declaration | fact | file |
| --- | --- | --- |
| `Nat.sub_sub_self` | `F:nat-sub-sub-self` | `nat_prelude/order.rs` |
| `Int.wilsonHalfSplit` | `F:int-wilsonhalfsplit` | `int_prelude/first_supplementary_residue.rs` |
| `Int.firstSupplementaryLawResidue` | `F:int-firstsupplementarylawresidue` | `int_prelude/first_supplementary_residue.rs` |

All three: `Kernel::axiom_footprint` empty.

- [ADR-1235](../../research/09-decisions/adr-1235-wilson-supplies-the-residue-witness-and-the-first-supplementary-law-closes.md)
  — the route, the three-column mutation table, and what the controls do not
  catch.
- `docs/research/09-decisions/adr-1235-first-supplementary-residue-checks.py`
  — thirteen numeric claims, one per proof step, each with a mutation that must
  be refuted; exits 1 if any survives.

## Measured

- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 65 passed, 0 failed.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 299 passed, 0 failed.
- `python3 scripts/validate-facts.py` — 2457 facts, 0 errors.
- `python3 scripts/check-settled-fact-statements.py` — PASS, drifted=0.
- Nine mutations, none surviving: five rejected by the kernel (two of them
  because the mutated STATEMENT is false, exhibited independently), three
  ADMITTED and TRUE but not the law (ADR-1230's M5 shape), and one control
  inversion proving the M5 assertion is not vacuous.

## Corrections to the handoff

- ADR-1230 said to promote `nat_prelude/transposition.rs`'s
  `injective_of_involutive`. That helper takes an **unbounded** involution law
  and the reflection is not a global involution (`Nat.sub` truncates), so it
  does not apply. `int_prelude/wilson.rs`'s private
  `injective_of_involutive_local` takes the **bounded** law and was reused
  verbatim. "Promote, do not re-derive" was right; the named helper was not.
- Everything else in the handoff held, including the claim that
  `count_range_reversal.rs` has nothing to reuse despite its name.

## Next

- `Int.wilsonHalfSplit` is stated for both parities. The odd-`m` reading —
  `(m!)^2 ≡ 1 [p]` for `p ≡ 3 (mod 4)` — is one `pow_neg_one_of_odd` away and
  is not landed.
- `Nat.sub_sub_self` plus `injective_of_involutive_local` is the general
  reflection kit; the `sumRange`/`countRange` reversals should use it rather
  than re-derive.
