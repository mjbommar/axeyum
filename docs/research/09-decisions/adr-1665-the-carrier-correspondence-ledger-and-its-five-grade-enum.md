# ADR-1665: The carrier correspondence ledger and its five-grade enum

Status: accepted
Date: 2026-09-05
Index-summary: `docs/math-department/14-lean-lang.md` Next Ten item 4, closed. `artifacts/carrier-correspondence/carrier-correspondence-v1.json` holds 16 rows, one per (Axeyum carrier, Mathlib counterpart) pair, each graded exactly one of `same-statement` / `constructively-stronger` / `constructively-weaker` / `different-object` / `no-counterpart`, with a verified source location on both sides and a witness theorem pair for every grade except `no-counterpart`. `scripts/check-carrier-correspondence.py --check` resolves every name marked kernel-projection-verified against the live projection and enforces the grade/witness/coverage rules; nine independent guards, each mutation-verified to kill exactly one control test. Going forward, a "shares this theorem with Mathlib" sentence anywhere in the docs must cite a row here.
Index-status: accepted

## Context

Reviewer 03 (`docs/math-department/03-classical-analysis.md`) writes that a
theorem this library shares with Mathlib "may be a different theorem" because
`CReal` is a Bishop setoid (ADR-0512) and Mathlib's `Real` is a classical
Cauchy quotient. Reviewers 05 (geometry), 07 (combinatorics) and 08
(probability) each record the same complaint for their own carrier: a name
match with nothing written down saying whether the two objects, or the two
theorems stated over them, are actually the same.

Before this ADR, exactly one gate protected statement identity across the Lean
boundary: `scripts/check-mirror-statement-fidelity.py`, which hash-pins the
`F:ml430-*` mirrors' Mathlib-surface `formal.statement` text against a
preregistered catalog. That gate is scoped to the ℕ/ℤ mirror programme and
checks that a mirror states what it claims to mirror -- it says nothing about
whether the *carrier itself* corresponds to anything in Mathlib, or at what
cost. `docs/math-department/14-lean-lang.md`'s Next Ten item 4 named the gap
directly and assigned it a name: **a carrier correspondence ledger**, "gated
the way the ℕ/ℤ mirror-fidelity check already is."

The measured comparisons that exist -- ADR-1030's IVT/EVT verdict, the
per-statement Pareto argument in
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` -- are
both real and both about *facts*, not carriers, and both live in prose no
tool reads. `artifacts/correspondences/*.json` (ADR-0546) is the closest
existing machinery, but it is scoped to pairs of *facts already in the
ledger* and refuses a pair the ledger already connects by `depends_on`; a
carrier is not a fact and most carrier pairs here have no ledger connection to
refuse in the first place.

## Decision

**A new artifact, a new schema, and a new gate, sibling to the theorem
correspondence machinery rather than an extension of it.**

- `artifacts/ontology/carrier-correspondence.schema.json` defines the ledger
  document: `{schema_version, kind, rows: [...]}`, where each row names both
  carriers, their verified source locations, the equality regime on each side,
  a grade, a one-sentence reason, a witness array, and provenance.
- `artifacts/carrier-correspondence/carrier-correspondence-v1.json` holds
  **16 rows**, covering every pair `docs/math-department/14-lean-lang.md`
  Next Ten item 4 named (`CReal`↔`Real`, `Nat.Finset`↔`Finset`,
  `Nat.Multiset`↔`Multiset`, `AlgS.Group`↔`Group`, `AlgS.CommRing`↔`CommRing`,
  an honest substitute row for `AlgS.Field`↔`Field`, `CPoint`↔`EuclideanSpace
  ℝ (Fin 2)`, `Nat.Graph`↔`SimpleGraph`, `Complex`↔`Complex`, Rat matrices
  ↔`Matrix`, the ℚ probability shelf↔`PMF`, `Metric`↔`MetricSpace`,
  `IntSpace`↔the Bochner integral, `Nat.RM`↔Mathlib's computability library,
  and the `ipc_*`/`Provable` logic↔Mathlib's Heyting/ModelTheory) plus one
  bonus row (`Nat.Rado`, `no-counterpart`) found while verifying the
  combinatorics rows.
- `scripts/check-carrier-correspondence.py --check` validates structure
  (`jsonschema` when importable, a hand-rolled subset otherwise, matching
  `validate-docir.py`'s fallback) and nine independent semantic guards
  (G0-G8: unique ids, closed grade enum, witness required/forbidden by grade,
  `no-counterpart`'s mathlib side is null, every `verified-in-kernel-projection`
  name actually resolves in `artifacts/autogenesis/kernel-dependency-projection-v1.json`,
  ledger non-vacuity, kernel-projection-citation non-vacuity, the Next Ten
  item 4 coverage floor, and `mathlib_theorem`/`mathlib_location`
  null-pairing). `scripts/tests/test_check_carrier_correspondence.py` carries
  one clean fixture and one failing fixture per guard (12 tests);
  `scripts/tests/mutation_controls.py carrier-correspondence` confirms each of
  the 11 registered mutations (nine guards plus the witness-forbidden/-required
  split plus the kernel-projection-missing fallback) kills **exactly** its own
  test, none survive, none unmeasured.
- `docs/plan/generated/carrier-correspondence.md` is generated from the ledger
  by `scripts/gen-carrier-correspondence-md.py`, `--check` gated.
- Both checks are registered in `scripts/check.sh` and the `justfile`,
  immediately beside `mirror-statement-fidelity`.

### The five-grade enum, and what each means

- **`same-statement`** -- stripping the carrier from both formal statements
  leaves the identical proposition (the `carrier-transport` shape from
  `theorem-correspondence.schema.json`, applied to a carrier pair as a
  whole). Used for `AlgS.Group`↔`Group` and `AlgS.CommRing`↔`CommRing`: their
  own module doc records that `app2(k, equiv, lhs, rhs)` beta-reduces to
  `Eq carrier lhs rhs` exactly when `equiv := @Eq carrier`, so every law is,
  up to that one substitution, the identical string.
- **`constructively-stronger`** -- the Axeyum side proves a strictly
  stronger or more computational statement over the same content. Used for
  `CReal`↔`Real` (IVT: an approximate root with an explicit witness, footprint
  `0`, against pure existence under three classical axioms -- ADR-1030) and
  `Complex`↔`Complex` (`Complex.no_compatible_order` constructively derives
  `False` from the order axioms, where Mathlib simply never registers a
  `LinearOrder ℂ` instance).
- **`constructively-weaker`** -- the reverse; not used by any row in this
  draw, kept in the enum because a future row (or a future re-grading of the
  `IntSpace` or `Nat.RM` rows, both currently `different-object`) may need it.
- **`different-object`** -- not comparable on one axis, either because
  hypotheses and conclusions differ in the same direction (ADR-1030's EVT
  verdict, cited as this row's second witness rather than a second row) or
  because the carriers serve different purposes despite a name match. Ten of
  the sixteen rows land here, including the three combinatorics-adjacent rows
  (`Nat.Finset`, `Nat.Multiset`, `Nat.Graph`) where the representation choice
  documented in ADR-1608/ADR-1623 -- a computed bounded predicate whose own
  `Eq` is not set-extensional -- is genuinely a different object from
  Mathlib's `nodup`-`Multiset` quotient, not merely a weaker one.
- **`no-counterpart`** -- nothing in the pinned Mathlib checkout plays this
  role. One row (`Nat.Rado`'s partition-regularity Rado numbers) uses it,
  backed by a clean negative search distinguished from the unrelated "Rado
  selection lemma" that shares the mathematician's name.

### A finding this ADR records rather than silently substitutes

The brief that commissioned this ledger named `AlgS.Field`↔`Field` and
`Nat.RM`↔no counterpart as two of the required rows, and this lane's own first
pass on `AlgS.Field` was ALSO wrong, for a different reason than a brief error:
a stale merge base.

- **`AlgS.Field` does exist, and this lane's own draft first got that wrong.**
  The lane's worktree branched before `53c851e5b` (ADR-1627) landed `AlgS.Field`
  on `main`, so its first pass measured `AlgS.Field*` absent from
  `structures_setoid.rs`'s nine-record list and graded `Alg.Field` (the older
  Eq-based spine) instead. The coordinator caught the staleness before merge.
  After `git merge --no-edit main` and a FRESH release build of `shape_search`
  (declarations `4291 -> 4379`), `AlgS.Field` is confirmed live: `--name
  AlgS.Field` returns `FOUND 1` (positive control `--name AlgS.Group` also
  `FOUND 1`), and `--name-contains Field` (67 matches) confirms
  `AlgS.Field.mulInvEx`, `.apart`, `.IsTight`, `.ofCommRing`,
  `.mul_left_cancel` as live declarations; a follow-up `--name-like fieldS`
  confirms `CReal.fieldS`, `Rat.fieldS` and `Rat.fieldS_isTight`. None of this
  is in `artifacts/autogenesis/kernel-dependency-projection-v1.json`, which was
  not regenerated across the merge — so every `AlgS.Field`-related name in the
  ledger is `verified-in-source-only` (shape_search + direct source read), not
  `verified-in-kernel-projection`, the same distinction already used for this
  session's other post-projection landings.

  `CC:algs-field-field` now grades the REAL `AlgS.Field` against Mathlib's
  `Field`, as **`different-object`** rather than the withdrawn
  `same-statement` grade its first (stale) draft gave `Alg.Field`: `AlgS.Field`'s
  inverse is existential (`mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one`)
  over an apartness hypothesis not proved tight for `CReal`, while Mathlib's
  `Field` commits to a total function under a bare inequality — hypothesis
  stronger, conclusion weaker, the same two-asymmetries-in-opposite-directions
  pattern ADR-1030 used for EVT. `CReal.no_total_inverse` (verified by direct
  source read; a dedicated shape_search query for this one name was not run in
  this session, reported as such rather than guessed) proves the functional
  shape is impossible for `CReal`, not merely unbuilt, which is the strongest
  single fact in the row.
- **`Nat.RM` has a Mathlib counterpart.** Mathlib's `Computability` library
  states the general halting problem (`halting_problem`,
  `Mathlib/Computability/Halting.lean:65`) and Rice's theorem over its own
  `Nat.Partrec.Code`/Turing-machine apparatus. The `CC:nat-rm-computability`
  row is graded `different-object` (a bespoke, unconnected shallow embedding
  refuting one self-referential instance, versus a general universal-code
  result) rather than `no-counterpart`, with the correction stated in the
  row's own `reason` field.

Both are recorded as findings, per this repository's own discipline that an
absence must be a measured negative and a brief's — or a lane's own first
pass's — "blocked on" or "assumed absent" is a claim about one route (or one
worktree's merge base) rather than a verified fact. **Merge local `main`
before measuring an absence, and re-measure after merging** is the general
lesson ADR-1030 already recorded from a 22-commit-stale worktree; this ADR is
a second, independent instance of the same failure mode, caught before merge
rather than after.

### Counts per grade (measured 2026-09-05, `check-carrier-correspondence.py --check`)

| Grade | Rows |
|---|---:|
| `same-statement` | 2 |
| `constructively-stronger` | 2 |
| `constructively-weaker` | 0 |
| `different-object` | 11 |
| `no-counterpart` | 1 |
| **Total** | **16** |

### The rule going forward

**A "shares this theorem with Mathlib" sentence anywhere in the docs must
cite a ledger row.** Not a fact id, not an ADR, not a curriculum note's prose
-- a `CC:` row, because that is the only object in the repository that pairs a
verified Axeyum name with a verified Mathlib name and a grade a referee can
check independently of the sentence itself. `docs/math-department/14-lean-lang.md`,
`03-classical-analysis.md` and `07-combinatorics.md` are updated in this
change to cite the rows that answer their own stated stakes; their verdict
lines are otherwise unchanged.

## Evidence

- `python3 scripts/check-carrier-correspondence.py --check` --
  `CARRIER_CORRESPONDENCE|rows=16|witnesses=25|kernel_verified_names=20|kernel_declaration_ids=4291|grades=constructively-stronger:2,constructively-weaker:0,different-object:11,no-counterpart:1,same-statement:2|violations=0|verdict=PASS`.
- `python3 -m unittest scripts.tests.test_check_carrier_correspondence` -- 12
  tests, all passing, bare, nonzero count confirmed (re-run after the
  `AlgS.Field` regrade).
- `python3 scripts/tests/mutation_controls.py carrier-correspondence` -- 11/11
  registered mutations KILLED, each by exactly the test named for its guard;
  zero survivors, zero unmeasured (re-run after the regrade).
- `python3 scripts/gen-carrier-correspondence-md.py --check` -- clean against
  the committed `docs/plan/generated/carrier-correspondence.md`.
- A FRESH `shape_search` release build after `git merge --no-edit main`
  (declarations `4291 -> 4379`, build cost ~210-350s per query since
  `--include-constructed` rebuilds the `creal`/`complex`/`cpoint`/`metric`/
  `intspace` preludes in memory each run): `--name AlgS.Field` -> `FOUND 1`;
  positive control `--name AlgS.Group` -> `FOUND 1`; `--name-contains Field`
  (67 matches) confirms `AlgS.Field.mulInvEx`, `.apart`, `.IsTight`,
  `.ofCommRing`, `.mul_left_cancel`; `--name-like fieldS` confirms
  `CReal.fieldS`, `Rat.fieldS`, `Rat.fieldS_isTight`.
- Every Axeyum name cited as `verified-in-kernel-projection` was cross-checked
  against `artifacts/autogenesis/kernel-dependency-projection-v1.json`
  (4,291 declarations, unregenerated across the `main` merge) by exact `id`
  lookup; names that postdate that projection's last regeneration (the
  2026-09-05 binomial/Hall-singleton landings, and now the entire
  `AlgS.Field`/`fieldS` family) are marked `verified-in-source-only` rather
  than guessed present.
- Every Mathlib name and `file:line` was read directly from the pinned
  mathlib4 checkout at `c5ea00351c28e24afc9f0f84379aa41082b1188f` (Lean
  4.30.0), located via `scripts/provision-lean-import-toolchain.sh --verify`,
  never from memory -- including three clean negatives (Menelaus/Varignon,
  the 3-3 Ramsey number, Rado's partition-regularity theorem) each backed by
  a positive control confirming the search methodology was not silently
  broken.

## Alternatives considered

**Extend `artifacts/correspondences/*.json` (theorem-correspondence) instead
of a new artifact.** Rejected: that schema's `endpoints` are exactly two fact
ids, and a fact is a proposition, not a carrier -- most rows here (e.g.
`Nat.RM`↔Mathlib's computability library, or `Metric`↔`MetricSpace`) have no
natural fact-id endpoint on either side, since the object being compared is a
type or a typeclass spine rather than a specific proved proposition. Forcing
a carrier pair through a fact-shaped schema would have meant inventing
placeholder facts with no independent reason to exist.

**One file per row under `artifacts/carrier-correspondence/`, mirroring
`artifacts/correspondences/`'s one-file-per-edge convention.** Rejected: the
brief specified a single file (`carrier-correspondence-v1.json`), and a
carrier-pair count in the tens rather than the hundreds does not need the
per-file convention's main benefit (avoiding merge contention on one shared
file across many concurrent lanes).

**Score the rows with a single weighted number.** Rejected for the same
reason ADR-1030 rejected it: a weighted score would hide the per-row detail
that is the entire content of this ledger, and would invite exactly the kind
of "0 against 3" over-generalization ADR-1030 found and corrected.

## Consequences

- Reviewer 03's "may be a different theorem" is now a citable row
  (`CC:creal-real`) rather than a sentence; reviewers 05, 07 and 08 likewise
  have rows for `CPoint`, `Nat.Finset`/`Nat.Multiset`/`Nat.Graph`, and the ℚ
  probability shelf respectively.
- `CC:rat-matrix-matrix`'s witness array corrects ADR-1030's rank-absence
  measurement in place (`Rat.rank` now exists at symbolic dimension) without
  editing ADR-1030 itself, which stays the record of what was true when it
  was measured.
- The coverage-floor guard (G7) means a future edit that silently deletes a
  required row fails the gate even though the row *count* alone would not
  obviously look wrong -- the same failure mode CLAUDE.md's "a stable number
  can be stably wrong" note warns about, applied here before it happens
  rather than after.
- One follow-on item this ADR does NOT close: a specific grading of the
  `Rat.rank`↔`Matrix.rank` pair on its own, now that it is no longer
  fixed-size-vs-general-n (flagged in `CC:rat-matrix-matrix`'s witness note).
- `CC:algs-field-field`'s `notes` field records that `Alg.Field` and
  `Rat.IsField`/`Rat.rat_isField` (the Eq-based spine `AlgS.Field` sits beside)
  remain real, landed, and closer in shape to Mathlib's `Field` than
  `AlgS.Field` is -- a future lane could reasonably want a second row for that
  pair specifically, since this row now grades the setoid record the brief
  named rather than its Eq-based cousin.
