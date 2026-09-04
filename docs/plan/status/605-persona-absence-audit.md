# Lane: persona-absence-audit — check every absence claim in the twelve persona reviews

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, persona-absence-audit, 2026-09-04).** Every claim
of absence in `docs/math-department/`'s twelve persona files was re-checked
against a freshly rebuilt kernel index (`declarations=3575`, positive control
`AlgS.Hom.firstIso`, which landed the same day). **76 claims checked: 11 are
FALSE — the thing is proved — 12 more overstate the gap, 51 are confirmed
absent, and 2 could not be settled by search and are recorded as did-not-run.**
Findings in [`docs/math-department/AUDIT-2026-09-04.md`](../../math-department/AUDIT-2026-09-04.md),
worst-first, each row carrying the evidence command, the declaration name, and
the landing commit. The twelve persona files and `00-roadmap.md` are NOT
touched; the coordinator applies the findings.

The worst false absences are the reviewers' own number-one items: `02`'s FTC
(both directions, `1b91195d0`/`d1bdae9e7`, 2026-08-27), `08`'s weak law of
large numbers (`Rat.weak_law_of_large_numbers`, `54592604a`, 2026-08-24),
`02`'s uniform convergence with both interchange theorems (`edb2feb7b`,
2026-08-27), `01`'s primitive roots (`f04f3eaf4`, the same day the file was
written), `01`'s unique factorization as a multiset identity (`340dd568d`),
`07`'s "no Stirling numbers" against ten proved theorems (`33cae3575`), `01`'s
"totient multiplicativity is not general" against `Nat.totient_mul_of_coprime`
(`05ad19d54`), `02`'s constructive Rolle/MVT (`db7c56936`/`3a7f3d1e8`), and
`04`'s "no kernels or images" against twelve `AlgS.Hom.*` declarations
(`5337d192b`). **Seven of the eleven landed on 2026-08-27**, one week before
the reviews.

Root cause, re-measured independently of lane `ftc` and decided in
[ADR-1605](../../research/09-decisions/adr-1605-the-ledger-cannot-tell-uncharacterised-from-absent.md):
the ledger cannot distinguish "no prose has been written" from "there is
nothing here". 1,054 of 2,764 facts carry the generator's `[generated]` title
(64.2% of the `CReal` shelf), and a class nobody had counted — 499 proved facts
titled "Mathlib v4.30 source proposition `<Name>`", which the landmark rule
scores as characterised and where the Stirling false absence hid. Together
**1,553 of 2,493 proved facts (62.3%) carry no characterisation of their own.**
A second, larger axis nobody had measured: **430 kernel theorems and 762 of 789
definitions have no ledger fact at all**, including `AlgS.Hom.firstIso`.

Implemented rather than left proposed: `scripts/check-fact-characterisation.py`
(three-way split, two hard guards, and a per-fragment RATCHET on the curated
count rather than the exact pin next door), its 17-test control suite with a
full mutation table in the ADR, and registration in both `scripts/check.sh` and
the `justfile`. Deliberately NOT done: a `characterisation_status` schema field
(derivable, would drift, 1,054 file edits against a gated schema) — the ADR
argues that alternative down. The kernel-vs-ledger coverage gate is sized at
half a day in the ADR and left proposed; it needs a committed declaration index
and a staleness guard, which is the load-bearing part.

**Two off-lane findings.** (1) `scripts/count-landmark-facts.py --check` was
RED on `main` at `182d0dd7d` — `baseline=2758 measured=2764` — because two
lanes landed six facts on 2026-09-04 and neither bumped the generated baseline;
re-baselined here. (2) `artifacts/facts/F-int-euler-totient-theorem.json`
carried a full curated statement of Euler's totient theorem under a "prose not
curated" title, so both the landmark count and the new checker scored a
characterised fact as uncharacterised; the title is corrected, and it is the
one live violation the new `PROSE_DISAGREEMENT` guard found on its first run.

<!-- plan-section: landed-changes -->

| 2026-09-04 | persona-absence-audit | `AUDIT-2026-09-04.md`: 76 absence claims checked, 11 false, 12 partial, 51 confirmed, 2 did-not-run |
| 2026-09-04 | persona-absence-audit | ADR-1605 (proposed): characterisation is a derived three-way ratcheted measurement, not a stored schema field |
| 2026-09-04 | persona-absence-audit | `check-fact-characterisation.py` + 17-test control suite, registered in `check.sh` and the `justfile` |
| 2026-09-04 | persona-absence-audit | re-baselined the red `count-landmark-facts.py` pin and fixed one mistitled fact |
