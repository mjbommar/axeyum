# Lane: draw-14 — the draw is declined, and the gate that should have said so was blind to the shape

<!-- plan-section: lane-status -->

**Draw 14 is DECLINED, and the finding is mechanised rather than argued**
(`DONE`, draw-14, 2026-08-31). ADR-1100 enabled two four-family layouts and left
the R11 disclosure to a draw lane. Both sweeps were performed.
`natural-avg-pair` is clean and its review is recorded and live. The other
held-out family — `natural-factorisation-properties`, the only late-sorting
held-out-viable candidate in the space, re-confirmed by running the real
`select()` over all 38 un-owned modules — draws `Nat.Abundant 12` and
`Nat.Deficient 1`, which the committed `abundant_evaluates_at_twelve` `def_eq`
test already shows unfold to `Lt 24 28` and `Lt 1 2`. Decided by reduction the
instant ADR-1100's construction landed, so not blind.

**R12 said `0 of 10` because `is_closed_evaluation` required an `=`, and a
ground PREDICATE application has none.** Every family the gate had screened
stated its ground rows as equations, so the `=` looked like part of the
definition of "closed evaluation" rather than an artefact of the sample. Widened
to a disjunction of `_is_ground_equation` and `_is_ground_predicate`; blast
radius measured at **0 of 146** committed held-out rows before any code was
written, mutation-verified, and the redundant `"=" not in text` guard removed
because zero fixtures die without it. With the gap closed R12 names both rows.

Accepting and recording the spend was considered and rejected on the empirical
record: draw 11's `natural-bit-decode` was drawn at the same 2-of-10 and then
amended **out of held-out entirely** (ADR-0542, `7296730d6`). Enlarging the
family so the two rows fall outside the alphabetical ten is available and is
disqualified on principle — it is choosing the family set to obtain an outcome.

Also repaired en route: **`gen-autogenesis-nursery-refill.py` was RED on `main`**
and nothing reported it. `nursery-v2-extension.json` did not match its own
`extension_sha256`, so `frozen_partitions()` raised before a single row was
selected and no draw lane could have got past step one. Bisected to `b81f22780`,
each candidate checked with that commit's own copy of the generator.

Held-out isolation `held_out=146 files_scanned=1110 settled=0 references=0
PASS` before and after; no fact moved partition and no manifest row changed.
Full reasoning and every number: [ADR-1115](../../research/09-decisions/adr-1115-draw-14-is-declined-r12-could-not-see-a-ground-predicate.md).

<!-- plan-section: landed-changes -->

| 2026-08-31 | `e6c3f1265` | Repair `nursery-v2-extension.json`'s self-digest. The generator could not run at all on `main` — not `--check`, not a regeneration. `b81f22780` hand-edited the `cross_population_component_split_exemptions` reason string without re-pinning the digest, and the guard fired exactly as its docstring says it should. One line; the writer asserts the reloaded body equals the body it read, and the exemption list is an authored key `stored_cross_population_exemptions()` carries across a regen, so the content is preserved verbatim. Generator now reproduces the manifest: `entries=380 env=2593 development=150 held-out=130 train=100`. |
| 2026-08-31 | `fab0bd201` | R12 could not see a ground PREDICATE, only a ground equation. `is_closed_evaluation` split into `_is_ground_equation` (unchanged) + `_is_ground_predicate` (new), with the numeral requirement separating `Nat.Abundant 12` from the genuinely blind `Monotone Nat.fermatNumber`. Mutation-verified on a scratch copy with `__pycache__` cleared: numeral guard killed by 2 fixtures, head guard by exactly 1, whole branch by 3, baseline 0. Discriminating evidence, R12's body called directly on the candidate entries: REFUSED with both rows named, against `no violation` from the pre-extension classifier. Gate stays `held_out=146 closed_shaped=0 violations=0 PASS`. |
| 2026-08-31 | `9d45cb5b4` | Draw 14's two disclosure sweeps, recorded with what was actually found. `natural-avg-pair` is a `reviews` row (clean; verified live both ways — `clean` as recorded, `refused` when the count is perturbed to 2), and it records two things the stem mechanism structurally cannot reach: `Nat.pair` is a subject of one drawn row but sits below `SUBJECT_FRACTION` so no `pair` stem is swept (16 declarations enumerated by hand), and all ten rows carry binders. `natural-factorisation-properties` is deliberately NOT a review row — a review row is a licence to draw — and goes in a new top-level `refused` list that `load_reviews` ignores by construction, recording that the sweep does not reach `Nat.sumDivisors` (through which all three predicates are defined; `Nat.sumDivisors_prime` makes three drawn rows cheap rather than open). `Mathlib.Data.Nat.Count` recorded there too, labelled as carried forward from ADR-1100 rather than verified here. |
