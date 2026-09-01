# Lane: constant-canonicity — one canonical definition per mathematical object

<!-- plan-section: lane-status -->

**Status:** landed. One canonical definition per mathematical object is now a
gate, registered in all four aggregate contexts.

## The question

"Will we end up with ten or twenty definitions of pi?" Measured 2026-08-31:
nothing objected to a second one.

- `check-shape-duplicates.py` groups declarations by admitted TYPE. Every
  `CReal`-valued constant has the identical type `CReal`, so a type-based
  detector over constants is either useless or blind. It is blind -- 15
  duplicate groups, zero containing a constant.
- `CReal.Equiv` is undecidable, so no mechanical "same real" test exists.
- `Kernel::add_declaration` admits a `Definition` on well-typedness alone.

Measured population: **16** nullary data-valued definitions over
`CReal`/`Complex`/`Int`/`Rat` -- not a `CReal`-only problem. 366
function-valued definitions are deliberately out of scope; a 366-row
hand-adjudicated registry is the shape of gate lanes turn off.

The discipline is already the practice and was simply unenforced:
`CReal.expFn_one_equiv_e`, `CReal.cosFn_one_equiv_cosOne` and
`CReal.cosFnWide_one_equiv_cosOne` are three alternative constructions that
landed as THEOREMS rather than second definitions.

## What it guarantees, and what it does not

A new constant cannot land silently: its author must register it as a new
mathematical object (visibly, attributably) or as an `alternate` naming a
bridge theorem whose STATED TYPE the kernel confirms mentions both constants.
The population is derived from the kernel in both directions, so the registry
cannot rot.

It cannot check that a "these are different objects" claim is TRUE. `Equiv` is
undecidable. What changes is that a duplication stops being a silent omission
and becomes a written, reviewable, attributable claim.

## Landed changes

| commit | what |
| --- | --- |
| `bad9b8162` | open the lane |
| `07964ed6b` | `scripts/check-constant-canonicity.py` + `artifacts/trust-closure/canonical-constants.tsv` (16 rows) |
| `c92bb1488` | 32 controls, 19 mutations each killing EXACTLY one test; registered the CHECKER in `check.sh`, `local-ci.sh`, `ci.yml`, `justfile` |
| (this) | ADR-1320 |

## Proof it fires

End to end against a real kernel: a `lane-snapshot.sh` scratch copy declaring
`CReal.pi` and `CReal.piMachin` as real `Definition`s (the kernel admitted
both -- projection 14,137 -> 14,143 rows) makes the gate exit 1 naming both.
Six further registry variants against that same mutated projection each
produced exactly their own guard (G10, then OK with `distinct-from:pi`, then
G6, G8, G7, G4).

## For the `creal-pi` lane

Nothing here depends on `CReal.pi` existing. When it lands it needs one
registry row and the gate will fail until it does.

## Next

- A `separation` column, checked the way `bridge` is. Five constant pairs
  already carry kernel-checked distinctness (`CReal.apart_zero_one`,
  `Complex.Equiv.not_zero_one`, `Complex.Equiv.not_zero_I`,
  `Int.Characterization.zero_ne_one`, `Rat.one_ne_zero`); they are cited in
  reasons today but not machine-checked as evidence.
- The function-valued duplication hazard (366 definitions) is unaddressed and
  needs a different instrument -- proof-skeleton retrieval, not a registry.
