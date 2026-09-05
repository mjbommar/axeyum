# lean-import-composition

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, lean-import-composition, 2026-09-05).**

`docs/math-department/14-lean-lang.md` Next Ten **item 8** — the imported-axiom
composition ADR — is landed as
[ADR-1664](../../research/09-decisions/adr-1664-an-originated-theorem-may-rest-on-an-import-on-a-route-of-its-own.md),
decided by building the composed theorem rather than weighing the options.

**The decision.** An originated theorem MAY depend on an imported one. It lands
on a distinct `proof_route: kernel-lean-over-import`, its `axiom_footprint` is
`Kernel::axiom_footprint` of the composed theorem **plus** the import route's
three assumptions, and it counts toward the axiom-free headline never and toward
a separately reported composed tier always. Option (1) (forbid) and option (3)
(allow when the composed footprint is `[]`) were both rejected on measurements,
not preferences.

## What was measured

`crates/axeyum-lean-import/tests/imported_composition_footprint.rs`, four tests,
every number on an `AXEYUM-COMPOSE|` marker line.

| case | stream | admitted | measured footprint |
|---|---|---|---|
| Init-only import | `bool-and-comm.ndjson` | 48 | `EMPTY` |
| …composed over (`Bool.and_comm x true`) | | | `EMPTY` |
| classical import | `classical-em.ndjson` | 106 | `Classical.choice, Quot, Quot.lift, Quot.mk, Quot.sound, propext` |
| …composed over (`fun p h => Classical.em p`) | | | the same six, exactly |
| …**sibling of the same type** (`fun p h => h`) | | | `EMPTY` |
| Mathlib import | `ivt-intermediate-value-icc.ndjson` | 3,585 | eight names |

The discriminating pair is the whole decision. Two originated theorems of the
**same type** in the **same kernel**, differing only in whether the proof term
reaches the import: one inherits the import's whole closure, the other measures
`[]`. So propagation is transitive **and per proof term**, not per environment —
which is what makes the tier decidable per theorem, and what means a lane that
loads an import does not contaminate everything it proves beside it.

Cost: `add_declaration` 0.194 ms composed against 0.091 ms for the sibling. The
import itself costs 51.7 ms (48 declarations), 122.5 ms (106), 17.5 s (3,585).
**The trusted gate is not where composition is expensive; the import is.**

**Why option (3) is wrong.** `Kernel::axiom_footprint` walks *declarations* and
keeps the ones admitted on trust. The import route's three assumptions
(`lean4export-3.1.0-stream-faithfulness`,
`axeyum-lean-import-wire-translation`,
`lean4export-3.1.0-delivered-bytes-are-the-intended-export`) are not
declarations — they are claims about how the declarations reached the
environment — so no walk can reach them. An Init-only composition measures
`EMPTY` and rests on all three; option (3) would file it on `kernel-lean` with
`[]` and put it in the axiom-free headline.

## Three things this lane corrected rather than added

- `14-lean-lang.md` said imports carry `[propext, Classical.choice,
  Quot.sound]`. That is Lean's own `#print axioms` vocabulary. This kernel
  reports **eight** names for `intermediate_value_Icc` and **EMPTY** for the
  three Init-only streams.
- The same row said "largest closure 3,142 declarations". 3,142 is the wire
  **record** count; 3,585 is the declaration count. ADR-1090 has both columns.
- `scripts/count-landmark-facts.py` read only `epistemic_status` and `title`,
  so **all 7 `imported-kernel-lean` facts were counted as landmarks**, Mathlib's
  IVT and EVT among them — the rows ADR-0601 calls "labeled scaffolding, never
  headline". Fixed: `landmark` 1,523 → 1,516, `imported=7` now printed beside it
  so the exclusion is visible rather than subtracted, baseline bumped.

## What is enforced, and how each guard was verified

Five mutation controls, **each measured to kill exactly one test**
(`python3 scripts/tests/mutation_controls.py <name>`):

| control | rule |
|---|---|
| `fact-composed-route-import-assumptions` | the three import-route assumptions must be in `axiom_footprint` (this is what makes option (3) impossible) |
| `fact-composed-route-prior-art` | `provenance.prior_art` on the composed route |
| `fact-import-route-prior-art` | the pre-existing imported-route rule, which had no control until its sibling was written beside it |
| `fact-composed-route-traceability` | ≥1 `depends_on` edge to a fact on an imported route, so the tier is walkable |
| `landmark-excludes-import-dependent-routes` | an import is not a landmark |

The two prior-art rules are deliberately **separate branches** rather than one
widened route set: a shared branch could not tell a control which of the two
rules it had deleted.

## What did NOT happen, stated plainly

- **Zero composed facts exist.** ADR-1664 decides how one is recorded; the
  first one is not built. `K = 0`, and the validator's composed-tier line prints
  nothing, which is the honest report.
- **One environment cannot yet hold both.** `import_ndjson` builds its own
  staging kernel (the fail-closed contract), so import-then-prelude is the only
  reachable order, and `build_nat_prelude` into a kernel holding the
  48-declaration `Init` slice is **rejected at `False`** — 17 names are shared
  (`Bool`, `Bool.false`, `Bool.rec`, `Bool.true`, `Decidable`, …, `Eq`,
  `Eq.rec`). This is a name-space obstacle, not a trust one, and Next Ten item 4
  (the carrier correspondence ledger) is what removes it. Until then a composed
  proof term must live wholly in the imported vocabulary.
- **Not registered in `scripts/check-kernel-suites.sh`, and it should not be.**
  Checked rather than assumed: that script is `axeyum-lean-kernel`-only and
  *discovers* its membership from the source (`#[path = "support/lean_probe.rs"]`)
  rather than listing it, so there is nothing to append. `axeyum-lean-import`'s
  suites are named individually in `scripts/check.sh` and the `justfile`, and
  the crate is not run wholesale anywhere — so the new suite is registered in
  **both**, under `lean-gate`. Registering it is not tidiness: it is the
  evidence for ADR-1664, and the numbers the ADR quotes stop being verifiable
  the moment it rots. Note for a future lane: `imported_fact_evidence`, which
  re-derives all seven imported facts, is registered in **neither** gate and is
  run only by the facts' own `checker_command`s.

## Red found and NOT fixed

- `python3 scripts/tests/mutation_controls.py --check-anchors` exits **1** with
  `stale=1`: `MISSING SUBJECT creal-migrate-consumers: M7 a stale shape census
  fails the gate, and exit 2 does not`. Pre-existing and unrelated — this lane
  touched neither `scripts/creal-migrate-registry.py` nor that suite's entry.
  The five anchors added here all resolve and were each run.
- `scripts/check-aggregate-scope.sh` exits **1** with **17** unrecorded
  one-sided steps between `check.sh` (498) and `just check` (563) — all
  pre-existing, from other lanes' recipes (`check-proof-plan.py`,
  `check-structural-index.py`, `check-module-baseline.py`, …). This lane's own
  step was one-sided for one run and was then added to both, so the count went
  18 → 17. Recording the other 17 with `--update` would be adopting other lanes'
  divergences as accepted, which is not this lane's call.
- The three Lean gates `14-lean-lang.md` already records as red on `main` since
  `792224e73` were not re-checked and were not touched.

## How to re-measure

```sh
cargo test -p axeyum-lean-import --test imported_composition_footprint \
  -- --nocapture --test-threads=1      # confirm "3 passed", 1 ignored
cargo test -p axeyum-lean-import --test imported_composition_footprint \
  -- --nocapture --ignored             # the Mathlib endpoint, ~18 s

python3 -m unittest scripts.tests.test_validate_facts        # 44
python3 -m unittest scripts.tests.test_count_landmark_facts  # 22
python3 scripts/validate-facts.py            # 2,848 facts, 0 errors
python3 scripts/count-landmark-facts.py --check
```

<!-- plan-section: landed-changes -->

| 2026-09-05 | lean-import-composition | `imported_composition_footprint.rs` — 4 measurements of whether an originated theorem inherits an import's axioms, each on an `AXEYUM-COMPOSE|` marker line |
| 2026-09-05 | lean-import-composition | ADR-1664: composition allowed on `kernel-lean-over-import`, footprint = kernel walk + the import route's three assumptions, axiom-free headline never |
| 2026-09-05 | lean-import-composition | `validate-facts.py` + `fact.schema.json`: the new route, its assumption-transcription rule, its `prior_art` rule, and a cross-fact traceability pass |
| 2026-09-05 | lean-import-composition | five mutation controls, each measured to kill exactly one test; the imported-route `prior_art` guard had none before |
| 2026-09-05 | lean-import-composition | `count-landmark-facts.py`: 7 imports were being counted as landmarks (IVT and EVT included); `landmark` 1,523 → 1,516, `imported=7` reported, baseline bumped |
| 2026-09-05 | lean-import-composition | `14-lean-lang.md` item 8 closed and two of its numbers corrected; `03-classical-analysis.md` progress row (verdict line unchanged) |
| 2026-09-05 | lean-import-composition | the measurement suite registered under `lean-gate` in BOTH `scripts/check.sh` and the `justfile`, so the ADR's evidence cannot rot unnoticed |
