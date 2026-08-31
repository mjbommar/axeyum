# Lane: unblock-index-three

<!-- plan-section: lane-status -->

Status: complete (2026-08-31). Index 3 is filled; no draw authored.

## What this lane did

ADR-1220 measured that draw 16 needs two viable held-out slots, cycle index 0
and cycle index 3. ADR-1240 filled index 0 with `Nat.casesOn` and the inductive
`Nat.Primrec`. This lane fills index 3 with `Nat.floorRoot` and `Nat.ceilRoot`,
opening `Mathlib.Data.Nat.Factorization.Root` — **construction only**
(ADR-0653), no theorem about either, no fact registered.

Two conditions came with the candidate and both were discharged:

1. **The 3-of-10 boundary count was re-measured, not inherited.** ADR-1220's
   figure was relative to Mathlib's `Finsupp` body, which this kernel cannot
   build. Against the bounded-search construction actually written the count is
   **1 of 10**, and it is now a gated assertion rather than a reading.
2. **Draw 11's `natural-nth-root` review was redone**, because the two new
   names take the recorded `root` sweep from 11 declarations to 13.
   `check-holdout-adjacency.py` refused the frozen family until it was; it does
   not now.

## The substantive findings

- **`ceilRoot`/`floorRoot` are DIVISIBILITY roots, not the numeric root.**
  `floorRoot n a` is the greatest `b` with `b ^ n ∣ a` and `ceilRoot n a` the
  least `b ≥ 1` with `a ∣ b ^ n`; `Nat.nthRoot n a` is the greatest `m` with
  `m ^ n ≤ a`. They disagree at `(2, 12)`: `2`, `6` and `3`. That is what makes
  the adjacency review resolve, and it is asserted in the test suite rather than
  argued in prose.
- **The boundary count dropped from 3 to 1** because a bounded search does not
  special-case `n = 1`. `Nat.ceilRoot_one_left : ∀ a, ceilRoot 1 a = a` is a
  real theorem here — exactly what ADR-1220 predicted a search would do.
- **Two mutants SURVIVED, and both are reported.** One is extensionally
  identical and should survive; the other lowers `ROOT_HEIGHT` below `Nat.pow`
  and `Nat.mod`, changes no value, and is invisible to every test in the file.
  That is the definition-shaped form of ADR-1230's third outcome: admitted,
  computing the right thing, and not the declaration meant.
- **One predicted survivor did not survive, and the prediction was wrong in the
  write-up before it was measured.** A `floorRoot` scanning to `n` rather than
  to `a` was expected to pass the original four tests; it is caught at `a = 0`
  by a test written for a different purpose. The doc comment now says so.

## Landed changes

| change | where |
| --- | --- |
| `Nat.floorRoot` and `Nat.ceilRoot`, definitions only | `crates/axeyum-lean-kernel/src/nat_prelude/factorization_root.rs` |
| the evaluation suite and the gated boundary reading, 6 tests | `crates/axeyum-lean-kernel/src/nat_prelude/factorization_root_tests.rs` |
| wiring, field docs and `definition_names` coverage | `crates/axeyum-lean-kernel/src/nat_prelude.rs`, `.../nat_prelude_tests.rs` |
| the reproducible screen against the real machinery | `docs/research/09-decisions/adr-1245-index-three-screen.py` |
| draw 11's `natural-nth-root` review, redone | `artifacts/autogenesis/holdout-adjacency-review-v1.json` |
| environment snapshot 2706 -> 2708 | `artifacts/autogenesis/kernel-environment-snapshot-v1.json` |
| the decision | `docs/research/09-decisions/adr-1245-index-three-is-filled-and-a-boundary-count-is-definition-relative.md` |

## Verification

- `--lib nat_prelude::factorization_root` 6 passed / 0 failed (nonzero,
  confirmed). `--lib nat_prelude::` **309 passed / 0 failed**, up from 303.
- `clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
- Environment **2708**, exactly +2 (`definition 372 -> 374`); `axiom=30`,
  `inductive`, `constructor` and `recursor` all unchanged.
- `gen-autogenesis-nursery-refill.py --check`: 420 entries,
  `development=160 held-out=150 train=110`, manifest byte-identical under the
  refreshed snapshot.
- Five gates green: `check-autogenesis-nursery.py`,
  `check-autogenesis-holdout-isolation.py` (`held_out=166 settled=0 PASS`,
  before and after), `check-holdout-closed-evaluation.py`,
  `check-holdout-adjacency.py` (16 families, 0 refused), and
  `create-autogenesis-nursery-dispatch-baseline.py --check`.
  `check-shape-duplicates.py` and `validate-facts.py` also exit 0.
- No fact moved partition, none was registered, and `nursery-v1.json` was never
  touched. No `FAMILY_MODULES`/`FAMILY_ROUTES` edit is committed — that is the
  draw lane's.

## What the next lane inherits

Draw 16 is now authorable on layout RP, and the only remaining refusal is
**R11's authorable disclosure for the two new held-out families** — a review
that must be performed, not asserted. This lane deliberately did not write it.

One caution recorded in the redone review and repeated here: the supporting
theorems for `factorization_root` are safe to land from `development`, but
`Nat.pow_dvd_iff_dvd_floorRoot` is the divisibility adjunction and the held-out
`Nat.le_nthRoot_iff` is the order adjunction, so their proof skeletons rhyme.
Re-run `check-holdout-adjacency.py` before landing them.
