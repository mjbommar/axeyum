# Held-out contamination: the real count, the detector, and the repair

Date: 2026-08-25

Plan: [`263-holdout-contamination-by-ordinary-development.md`](263-holdout-contamination-by-ordinary-development.md) (finding)
Decision: [ADR-0542](../research/09-decisions/adr-0542-held-out-partition-breach-repair.md) (repair mechanism, reused)

## The measurement

Doc 263 found "at least 4" of the 57 pre-repair held-out nursery propositions
already proved in the kernel by ordinary hand development, and asked for the
real number across all 57. Method: for each held-out fact, generate name-level
candidates from `nat_theorem_inventory` / `int_theorem_inventory --release`
(the debug build SIGABRTs on stack depth), then decide MATCH/NO-MATCH by
comparing quantifier structure, hypotheses, argument order, and equation/iff
direction — never by name alone.

Two of the three held-out families (`natural-logarithm`, `natural-square-root`,
37 rows) have **zero** kernel presence: grepping both inventories for
`sqrt|clog|log|multichoose|ascfactorial|descfactorial|isSquare` across the full
unfiltered dump returns nothing. Every row in those families is NO-MATCH
categorically — the concepts do not exist yet, so no proposition about them can
be already proved.

`natural-binomial` (20 rows) is the only family with candidates. Name-level
sweep against `nat_theorem_inventory`'s `choose`-containing rows produced
**8 candidates**; statement comparison against the live rendered types
confirmed **5**:

| Held-out fact | `formal.statement` | Kernel theorem | Kernel rendered type |
|---|---|---|---|
| `F:ml430-nat-choose-zero-right-1ed2802a` | `∀ (n : ℕ), n.choose 0 = 1` | `Nat.choose_zero_right` | `choose x0 0 = 1` |
| `F:ml430-nat-choose-self-25bb9fb8` | `∀ (n : ℕ), n.choose n = 1` | `Nat.choose_self` | `choose x0 x0 = 1` |
| `F:ml430-nat-choose-succ-succ-671856b6` | `∀ (n k : ℕ), n.succ.choose k.succ = n.choose k + n.choose k.succ` | `Nat.choose_succ_succ` | `choose (succ x0) (succ x1) = choose x0 x1 + choose x0 (succ x1)` |
| `F:ml430-nat-choose-zero-succ-62c6520b` | `∀ (k : ℕ), Nat.choose 0 k.succ = 0` | `Nat.zero_choose_succ` | `choose 0 (succ x0) = 0` |
| `F:ml430-nat-choose-succ-self-e396f6c2` | `∀ (n : ℕ), n.choose n.succ = 0` | `Nat.choose_succ_self_eq_zero` | `choose x0 (succ x0) = 0` |

The fifth (`choose-succ-self` ↔ `choose_succ_self_eq_zero`) is new: doc 263's
table listed only the other four. **5 of 57 pre-repair held-out rows (5 of 20
`natural-binomial` rows) were already proved**, all with empty axiom footprint
(`nat` prelude measures axiom-free).

The other 3 candidates were REFUTED by statement comparison, confirming doc
263's warning that a name match is usually wrong:

| Held-out fact | `formal.statement` | Candidate | Why it fails |
|---|---|---|---|
| `F:ml430-nat-choose-symm-add-e4b68161` | `(a+b).choose a = (a+b).choose b` | `Nat.choose_symm` | kernel form is `k ≤ n → n.choose k = n.choose (n-k)` — different hypothesis, different argument (subtraction, not an additive decomposition) |
| `F:ml430-nat-choose-symm-of-eq-add-9b5f9a20` | `n = a+b → n.choose a = n.choose b` | `Nat.choose_symm` | same mismatch |
| `F:ml430-mutation-edb05acf07d9ef3f9f8232fc` | `n.choose n = 0` (deliberately falsified) | `Nat.choose_self` | kernel proves `choose n n = 1`, not `0` |

The remaining 9 `natural-binomial` candidates that generated no kernel name hit
at all (`choose-eq-zero-of-lt`, `choose-le-add`, `choose-le-choose`,
`choose-le-succ`, `choose-mono`, `choose-ne-zero`, `choose-one-right`,
`factorial-dvd-ascfactorial`, `factorial-dvd-descfactorial`) and the 3
`multichoose` rows (`Nat.multichoose` is not declared) are NO-MATCH.

**Total: 5 confirmed contaminated of 57 pre-repair held-out rows.**

## The detector

`scripts/check-autogenesis-holdout-contamination.py`, registered in
`scripts/check.sh` and the `justfile`'s `autogenesis-nursery` recipe (which
`check` depends on). It:

1. Re-derives each of the 5 reviewed matches against a **fresh, live**
   `--release` kernel build every run — the pinned `expected_line` is the exact
   `name<TAB>arity<TAB>type` row copied from a real run, not transcribed by
   hand. A row whose fact id is no longer held-out is SKIPPED, not checked,
   so the kernel is never even asked about a fact this population does not
   call held-out.
2. Runs an advisory word-set candidate sweep over every held-out fact NOT in
   the reviewed table, so a NEW theorem added later (a sixth contaminating
   `choose` lemma, or the day `Nat.sqrt`/`Nat.log` are declared) surfaces as
   `needs-review` before anyone builds an amendment for it.
3. **Reports, never fails the build**, on a finding — exit is nonzero only for
   the detector's own infrastructure (missing/unreadable nursery, empty
   held-out population). Failing the build on a proof landing would pressure a
   lane into not proving a theorem it needs.

Discrimination, demonstrated two ways:

*Synthetic* (`scripts/tests/test_check_autogenesis_holdout_contamination.py`,
13 tests): `test_a_matching_kernel_line_is_reported_contaminated` and
`test_a_non_matching_kernel_line_is_not_reported_contaminated` run the same
fixture through the same code path and differ only in the fake kernel output;
the verdicts differ (`CONTAMINATED` vs not).

*Real*, run against real cargo output on the same tree:

```text
# pre-repair nursery (57 held-out, read from git HEAD before this repair)
held_out=57  contaminated=[choose-zero-right, choose-self, choose-succ-succ,
                            choose-zero-succ, choose-succ-self]  skipped=[]

# post-repair nursery (37 held-out, committed)
AUTOGENESIS_HOLDOUT_CONTAMINATION|held_out=37|reviewed=5|contaminated=0|
  skipped=5|candidates=0|verdict=CLEAN
```

The same 5 facts the table names are exactly what it finds against the old
population, and it correctly reports nothing once they graduate.

## The repair

Per ADR-0542, the repair for a held-out family whose blind-evaluation value
has been spent is a whole-family move to `development`, recorded in an
amendment ledger, never a deletion or a per-row split — the ADR explicitly
rejected a per-shape split because "a proof route for one member is evidence
about its siblings," and that reasoning applies here too: the `choose.rs`
machinery the 5 confirmed matches sit on (Pascal's rule, `choose_symm`, the
sum identities) is shared scaffolding for the other 15 `natural-binomial`
rows.

`natural-binomial` moves to `development` as a whole family. Held-out
re-freezes at **37 rows across two families** (`natural-logarithm` 21,
`natural-square-root` 16); development rises to 99, train stays at 78.

Mechanism (mirrors the `natural-gcd` repair exactly):

```text
held-out before   57   natural-binomial 20 · natural-logarithm 21 · natural-square-root 16
spent             20   natural-binomial (ordinary development, not an autogenesis operation)
held-out after    37   natural-logarithm 21 · natural-square-root 16
```

Files touched, same shape as the `natural-gcd` repair (`227-held-out-partition-
breach-result.md`):

- `artifacts/autogenesis/mathlib-nursery-split-policy-v1.json` — second
  `amendments` entry (`natural-binomial`, held-out → development), and
  `family_partitions["natural-binomial"]` flips to `development`.
- `artifacts/autogenesis/nursery-v1.json` — regenerated by
  `create-autogenesis-mathlib-nursery-split.py`.
- `scripts/create-autogenesis-mathlib-nursery-split.py` — `PARTITION_COUNTS`
  now `{train: 78, development: 99, held-out: 37}`.
- `scripts/create-autogenesis-nursery-dispatch-baseline.py` — the
  train+development tripwire, 157 → 177; `mathlib-nursery-dispatch-
  baseline-v1.json` regenerated.
- `scripts/create-autogenesis-reflexivity-coverage-input.py` —
  `LIVE_POPULATION` 157 → 177 (not gated in `check.sh`/`justfile`, fixed for
  correctness). `scripts/check-autogenesis-reflexivity-coverage.py` is
  untouched and unaffected: since the `natural-gcd` repair it reads the
  nursery at the historical commit its own manifest pins, not the live file.
- `docs/plan/generated/autogenesis-baseline.{json,md}` — regenerated
  (`gen-autogenesis-baseline.py`); this file also picked up unrelated drift
  from the wider fact ledger's growth since it was last regenerated (523 → 696
  facts) — a pure function of already-committed source data, not new content.
- Pinned test literals updated:
  `scripts/tests/test_create_autogenesis_mathlib_nursery_split.py`,
  `scripts/tests/test_check_autogenesis_holdout_isolation.py` (`held_out=57`
  → `held_out=37`), `scripts/tests/test_create_autogenesis_nursery_dispatch_
  baseline.py` (`candidates` and the `expected 157`/`177` regex).

**Amendment field mapping, adapted from the `natural-gcd` schema.** That
breach had an autogenesis operation registration to name (`operation_id`,
`registered_commit`); this one has none — the contamination is ordinary
library development. `breach.fact_id` names one exemplar row
(`F:ml430-nat-choose-zero-right-1ed2802a`); `breach.operation_id` is set to
`no-operation-ordinary-nat-prelude-choose-development` rather than left blank,
since the schema requires a nonempty string and the value should say plainly
that no operation exists; `breach.registered_commit`/`registered_date` name
the commit that added `nat_prelude/choose.rs` (`8b9ddb7c5`, 2026-08-23), not an
operation-registration commit. All five confirmed matches are named in
`reason` rather than only the exemplar, since the whole-family move is what
the ADR requires — the breach record identifies the mechanism, not an
exhaustive list.

**Not flipped**: no held-out fact's `epistemic_status` was touched. All 20
`natural-binomial` facts, including the 5 already-proved ones, remain `open`
in the ledger — establishing them by crediting the ledger is a separate,
future step, and doing it now would be exactly the settled-held-out-fact
violation the isolation gate exists to catch.

## Gate summary lines

```text
$ python3 scripts/validate-facts.py
<quoted in the task report — see below>

$ python3 scripts/check-autogenesis-holdout-isolation.py
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=37|files_scanned=1029|settled=0|references=0|verdict=PASS

$ python3 scripts/check-autogenesis-holdout-contamination.py
AUTOGENESIS_HOLDOUT_CONTAMINATION|held_out=37|reviewed=5|contaminated=0|skipped=5|candidates=0|verdict=CLEAN
```

## What this does not fix

Same caveat as the `natural-gcd` repair: the detector's reviewed table only
re-derives the 5 matches this audit already found, plus an advisory word-set
sweep for anything new. It is not a general Lean-statement equivalence
checker — none exists — so a future contamination whose kernel theorem name
shares no word with its held-out slug will not surface automatically. The
candidate sweep narrows that gap; it does not close it.

## Known pre-existing, unrelated gate drift found while running this repair

Two test failures were found already broken at `HEAD`, before any edit in this
document, confirmed by reverting each touched file and re-running:

- `scripts/tests/test_create_autogenesis_nursery_dispatch_baseline.py::
  test_current_population_separates_admitted_row_from_pre_execution_declines`
  — `eligible_for_dispatch` is 2, not 0. Both dispatchable rows
  (`F:ml430-nat-modeq-symm-0a3d4d18`, `F:ml430-nat-modeq-trans-ef9d1c46`) are
  `natural-modular-equivalence`, unrelated to this repair; a concurrent lane
  registered matching operations against them.
- `scripts/tests/test_create_autogenesis_reflexivity_coverage_input.py` (2
  failures, 2 errors) — its fixture always builds a synthetic 138-row nursery
  but calls `build()` without `expected=`, so it silently depended on
  `LIVE_POPULATION` matching 138 exactly; it was already broken at 157 before
  this repair moved the constant to 177.

Neither is caused by or repaired by this document; both are left for whichever
lane is investigating that drift.
