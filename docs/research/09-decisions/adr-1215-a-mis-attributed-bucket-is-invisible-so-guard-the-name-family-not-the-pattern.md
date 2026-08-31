# ADR-1215: a mis-attributed bucket is invisible, so guard the name FAMILY, not the pattern

Status: accepted
Date: 2026-08-31
Index-summary: The curriculum classifier's residual counter catches a
declaration attributed to NOTHING and structurally cannot catch one attributed
to the wrong REAL bucket, which happened twice in two days (ADR-1140, ADR-1205).
Three ratcheted guards over name FAMILIES make it loud; both incidents are
replayed red against a slice of the real projection, and the checker itself --
not only its tests -- is now registered in both aggregate gates.

## Context

`scripts/measure-curriculum-kernel-coverage.py` attributes every kernel
declaration to one of the 23 `docs/curriculum/curriculum.toml` nodes using an
ORDERED pattern table matched against the declaration NAME. The last entries —
`naturals`, `integers`, `rationals`, `reals`, `complex`, and the two logic
nodes — are catch-alls: anything no topic pattern claims lands there.

The script prints a `residual` count, which catches a declaration attributed to
**nothing**. Nothing catches a declaration attributed to the **wrong real
bucket**, because such a declaration is attributed, counted, and entirely
plausible — and the node's pinned `kernel_decls` in `curriculum.toml` stays
*unchanged and wrong*, so a drift check comparing totals passes clean.

That failed twice in two days, both times on a pattern that named INSTANCES
rather than a family:

- **ADR-1140.** `linear-algebra`'s pattern carried the literal `det2|det3`.
  ADR-1120's general-`n` determinant (`Rat.det`, `det_zero`, `det_succ`,
  `det_eq_det2`, `Rat.matSkip`, `Rat.matMinor`, `Rat.altSign`,
  `Rat.sumRange_matSkip`, …) matched none of them, so 22 declarations fell into
  the `rationals` catch-all. `linear-algebra` stayed at 59.
- **ADR-1205.** `number-theory`'s only Gauss alternative was the literal
  `gauss_fold_injective`. The whole ADR-1130 / ADR-1150 quadratic-residue
  family — `gaussFold`, `gaussNegCount`, `gaussSignNeg`, `leastResidue`,
  `gauss_neg_count_*`, `gauss_residue_*`, `secondSupplementaryLaw` — fell into
  `naturals` / `integers`. `number-theory` stayed at 108.

Both were found only because a lane had been told to verify by name that its
new declarations landed in the intended bucket. Both were fixed by widening one
pattern, which treats the symptom: a pattern naming instances goes stale the
moment the family grows, and the table is full of such patterns.

Measured while writing this: **the classifier was registered in neither
`scripts/check.sh` nor the `justfile`.** It ran only when a lane typed it.

## Decision

Guard the **name family**, ratcheted against a committed pin, and register the
checker itself in both gates.

A *family* is the first word of the local name, with camelCase and snake_case
folded into one vocabulary and trailing digits stripped — so `Nat.gaussFold`
and `Nat.gauss_neg_count_succ` are one family, and `Rat.det2`, `Rat.det3` and
`Rat.det` are one family. Both foldings are load-bearing and each is
mutation-controlled: without the digit strip, ADR-1140's exact shape (a pattern
naming the NUMBERED instances while the general construction grows past them)
never produces a comparison at all; without the camel fold, this kernel's two
spellings of one mathematical family look like two families and neither
incident fires. (Measured over 447 `CReal` names: 315 carry an underscore, 225
an internal capital, 117 both.)

Three guards, all in `cohesion_findings`:

- **G1 SPLIT** — a family attributing to a node SET the pin does not carry.
  This is both incidents' shape: the pattern still matches the instances it was
  written for, so the family straddles its destination node and a catch-all.
  The pin holds the SET, not counts, so growth inside nodes a family already
  occupies is free.
- **G2 FAMILY** — a family of at least 8 declarations landing ENTIRELY in a
  catch-all, unpinned. This is the case G1 structurally cannot see: a family
  with no partial match never splits. Neither historical incident had this
  shape, but the next one can.
- **G3 STALE** — a pinned row matching no measured family. Without it the pin
  rots into a list of things that used to be true and G1/G2 weaken with nothing
  reporting it.

Two input refusals, because a guard is only as good as what it reads:

- `parse_rows` refuses a projection under 2,500 distinct declarations. A short
  index makes a newly-landed family look like it was always in the catch-all —
  the same failure arriving through the input rather than the table. Same
  device as `check-absence-claims.py`'s `authority_declaration_floor`.
- `--require-pin` (checked before the projection is read) refuses a missing pin
  file. An absent pin makes every guard examine an empty table and exit 0.

## Why this over the alternatives

**The source module was the first candidate and it does not carry.**
`kernel_declaration_projection` emits `kernel.environment()`, and the `Kernel`
stores name, type, value and kind — no provenance. The projection *cannot*
supply a module without a change to the trusted kernel API.

It can be RECOVERED from the Rust source, and I measured how well. Mapping each
declaration's registry field (`kernel.name_str(nat, "leastResidue")` in
`nat_prelude.rs`) to the module that uses that field in a DECLARING position
resolves **2,022 of 2,636 declarations, 76.7%**. The gap is per-prelude helper
vocabulary: `name: p.x` and `.theorem(p.x` cover nat; rat and int declare
through `.lemma(p.x`… except `.lemma` is a term *reference*, not a
declaration — I included it, coverage read 57.3% with 628 spurious
ambiguities, and I got the answer wrong in one command. That is the argument
against the design, not an anecdote about it: a module scan needs a hand-kept
table of which helper declares and which consumes, in a repository whose
recurring defect is exactly a hand-kept table going stale.

**And module cohesion would have missed ADR-1140 anyway.** `Rat.det2` is
declared in `rat_prelude/matrix.rs` and `Rat.det` in
`rat_prelude/matrix_det.rs`. Before the fix, `matrix_det.rs` was 100%
`rationals` and `matrix.rs` was 100% `linear-algebra` — perfectly cohesive,
green, wrong. Turning module into a bucket needs a module→node table, which has
the same staleness problem one level up.

**Exhaustiveness over a namespace** (every `Nat.*` matching no specific pattern
is an anomaly) is the design this decision rejects for false-positive cost: it
requires a table edit for every new declaration, and per the brief that gets it
disabled within a week. G2 is the same idea with a family floor of 8, which
bounds the cost to a table edit per new *family*.

**Per-node count deltas** against `curriculum.toml` are implemented as
`--expect-node-counts` but deliberately NOT wired into the gate: they redden on
every ordinary declaration. They are useful for a re-measure pass, and their
first run found `curriculum.toml` is internally inconsistent — pinned
`rationals` 206 against a measured 221 and `linear-algebra` 90 against 96,
while `naturals` matched exactly at 518, so the committed pins are not a
snapshot of any single tree state.

## Evidence

Both incidents are reconstructed in
`scripts/tests/test_curriculum_bucket_cohesion.py` from the two pattern tables
as `git show`n at `d2bb38a1e^` and `bd382566b^`, run against a 124-row slice of
the REAL projection (`scripts/tests/fixtures/curriculum-projection-slice.tsv`),
not a synthetic fixture:

    ADR-1140, pre-fix linear-algebra pattern:
      G1 SPLIT Rat.det* attributes to linear-algebra,rationals (pinned
        (unpinned)) -- linear-algebra: Rat.det2, Rat.det2_eq_zero_of_lin_dep,
        ...; rationals: Rat.det, Rat.det_congr, Rat.det_eq_det2, ...
      G1 SPLIT Rat.mat* attributes to linear-algebra,rationals ...

    ADR-1205, pre-fix number-theory pattern:
      G1 SPLIT Nat.gauss* attributes to divisibility-and-euclid,naturals,
        number-theory (pinned divisibility-and-euclid,number-theory) --
        naturals: Nat.gaussFold, Nat.gaussNegCount, Nat.gaussSignNeg, ...
      G1 SPLIT Int.gauss* attributes to divisibility-and-euclid,integers ...
      G1 SPLIT Nat.least* attributes to naturals,number-theory ...

    CONTROL, shipped table, same slice: 0 findings

The control is what makes the two red cases mean anything: a guard that fired
on everything would pass both.

Mutation sweep, `python3 scripts/tests/mutation_controls.py
curriculum-bucket-cohesion`: **nine mutations, all KILLED, no survivors.** The
first run had three survivors and each was a real hole — the family-floor test
built `range(FAMILY_FLOOR - 1)` and so adapted to any floor value; the
`--require-pin` test passed on the projection floor's refusal instead;
and `first = local.split("_", 1)[0] -> first = local` is an equivalent mutant,
since the word regex already splits on underscores.

**False positives on the current tree: zero, measured rather than argued.**
The pin was cut from a projection of 2,636 declarations. A projection built
from `main` an hour later carries **2,675** — 39 new declarations from ordinary
lane work (`naturals` 500→518, `rationals` 206→221, `linear-algebra` 90→96),
none of it aware of these guards. The gate reports **0 findings** on it, and
regenerating the pin changes only two informational counts, adding and removing
no rows.

The pin is 27 split rows and 59 catch-all-family rows over 433 measured
families, so ~94% of families never span a node boundary and only 14% of
carrier-bucket families reach the floor. Accumulated over the kernel's whole
history that is 86 rows per 2,675 declarations — roughly one pin edit per 31
declarations landed, which at the observed pace is a line every day or two.

## Consequences

- `just check` and `scripts/check.sh` run the CHECKER against the live kernel
  (`--run-projection --require-pin`), plus its controls. `shape-duplicates` and
  `absence-claims` have already warmed the release build; the run itself is
  ~45 s.
- A lane landing a new mathematical family in a carrier bucket will see a
  finding. The remedy is a decision, not a rubber stamp: widen the destination
  node's pattern if the declarations belong to a destination, and only then
  `--update-cohesion-pin`. The script says so in its own failure output.
- `--update-cohesion-pin` is a real hazard — a mechanical refresh of a WRONG
  attribution is how this table stops being evidence. It is not automated
  anywhere and the pin file's header says why.
- G2's floor of 8 is a judgement. Below it, ordinary new work in a carrier
  bucket is silent, which is deliberate: a guard that reddens on every new
  `Nat` lemma would be disabled, and a disabled guard catches nothing at all.
- Not addressed here: `artifacts/autogenesis/kernel-dependency-projection-v1.json`
  is badly stale (1,644 declarations, missing `Rat.det`, `Nat.gaussFold` and
  `CReal.integral`), so it is not usable as a cheap gate input for anything.
