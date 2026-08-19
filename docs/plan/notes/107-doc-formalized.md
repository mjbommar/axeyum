# doc-formalized — bringing `docs/formalized-math-2026-08/` into line with what happened

**Method.** Correct specific claims in place; keep the reasoning that still
holds visible; where a passage is falsified, say what falsified it and when.
Nothing was rewritten and no file was deleted. Every number added below was
measured on this host on 2026-08-19 unless it is explicitly cited to an ADR.

## What was measured, and with what

| what | command | result |
|---|---|---|
| trusted surface, all eight preludes | `cargo run --release -p axeyum-lean-kernel --example nat_axiom_inventory -- --include-constructed` | `complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30`, exit 0 |
| Nat theorem count (this strand's rate metric) | `--example nat_theorem_inventory` | **139**, 31 naming `dvd` |
| Int theorems | `--example int_theorem_inventory` | 57 derived, 57 empty footprint, 0 asserted |
| shipped front door | `cargo run --release -p axeyum-solver --features full --example front_door_carrier -- --require-axiom-free` | 1,304,276 / 1,330,091 / 1,442,247 B over `CReal`, **0** carrier axioms; `Real` control 12 / 17 / 8; exit 0 |
| the three autogenesis facts | `python3 scripts/check-autogenesis-fact-operation.py --fact …` ×3 | `AUTOGENESIS_FACT_OPERATION_OK|…|label=…-axiom-free`, exit 0 each |
| Lean pin | `scripts/check-lean-gate.sh --print-toolchain` | 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, matches `lean-toolchain` |
| gate shape | read from `scripts/check-lean-gate.sh` | 21 suites listed, `CHECK_FLOOR=219`, `THEORY_FAMILY_FLOOR=37` |
| ledger / decisions | `ls | wc -l` | 340 facts, 523 ADRs |

`front_door_carrier` and the autogenesis checkers were chosen over reading the
committed artifacts precisely because **their exit status depends on the
finding** — `--require-axiom-free` fails if the `Real` control comes back empty,
which is the failure mode where the measurement is broken rather than the result
being good.

## The claims corrected

1. **`README.md` and `05-throughput.md`: "that number is currently zero."**
   Written 2026-08-17 (`56f4c2b23`), falsified 2026-08-18. Replaced with three
   named facts and three qualifications: the first two are `Eq.refl` from a
   target-independent bounded producer (2 admissions out of 138 candidate rows);
   `Nat.fib_add_two` came from a program written for that goal and repaired by
   hand across two failed runs (ADR-0496 → 0500 → 0502), so by
   `docs/autogenesis/04-metrics-and-evaluation.md`'s own definition it is not
   autonomous. **C2 — dispatch a DAG goal to the solver, reconstruct, admit —
   has produced nothing.** The count moved by a different, narrower route, and
   that distinction is worth more than the count.

2. **`05-throughput.md`: the rate.** The 2026-08-17 re-measurement (10.3/day
   against 149 projected) stands and is extended, not replaced: the counter is
   **flat at 139** two days later, so the realized figure over 5.16 days is
   6.4/day and `f ≈ 0.043`. The larger correction is that the *instrument* is
   now wrong — `nat_theorem_inventory` reads one prelude, and ℤ, ℚ, `creal` and
   ℂ were proved out elsewhere. A single-prelude counter cannot rise when the
   work is elsewhere and cannot fall meaningfully either, so the honest statement
   is that **nobody can currently measure this project's theorem-production
   rate**. Recorded explicitly that nothing measured today moves C4's figures
   (26 ms / 6.6 µs, 5.4x / 5.6x / 55x / 86x) — they are cited as they stood.

3. **The cross-check, everywhere it appears.** "Lean's own kernel accepted the
   result from an empty environment" was true and read wider than it was:
   emission is reachability driven, a refutation reached 343 of 465 declarations
   (ADR-0511), and **122 had never been handed to any Lean**. ADR-0517's finding
   — kernel takes all 470 in 1.4 s, elaborator refuses 4 in 14.1 s, mechanism
   isolated to one token per line, our kernel *not* the permissive one — is now
   a section of `03-integrate.md` with the coverage hole and its fix beside it.
   ADR-0518's decision not to flip the default is recorded with its reason (the
   shipped surface already elaborates clean; flipping it makes the divergence
   suite report a false all-clear).

4. **The two limitations, stated at their true width.** The shipped `.lean`
   artefact still does not carry the whole carrier — each of the three fixtures
   is the closure of its own refutation. Four carrier declarations are
   kernel-checkable but not elaborator-checkable, and no shipped artefact
   contains them. Written to be neither softened nor inflatable into "Lean
   rejects our reals."

5. **The artefact size.** ~2.6 MB → ~1.3 MB by scope-aware `let` sharing, which
   is the writer's ceiling because 99.84% of a module is a development identical
   for every query; the split layout (ADR-0511) takes the per-query half to
   5,056 / 14,567 / 1,954 B (257x / 91x / 738x), shared half 1,715,764 B
   compiling once in 14.4 s, each query then 0.102 s. **Not the default**, and
   the reason — a strictly weaker artefact for a third party — is recorded with
   it, because the numbers alone argue for flipping it.

6. **C1 landed and did not deliver, which nothing in the strand said.**
   `nat_prelude.rs` is **845** lines and its content lives in eleven topic
   modules under `src/nat_prelude/` — almost exactly the split C1 proposes. The
   first two landed 2026-08-14 (`bc094a3dd`, `55a366a1b`), the same day as the
   burst the rate extrapolates from. Five days of sharded, collision-free
   library then produced +33 theorems, none in the last ~2.1 days. So `N ×
   149/day` is **falsified by its own remedy**: the single-file lock was not the
   binding constraint on `f`, or removing it was not sufficient. The shard was a
   real multi-agent-hygiene win; the strand conflated that with a throughput win.
   The useful residue is a question nobody has measured — *if not the file lock,
   what is `f` spent on?*

7. **Stale status blocks left standing with their correction.**
   `03-integrate.md`'s "13 of 40 admitted / population UNSTARTED / L3 0/12" (all
   three false by 2026-08-17); `04-implement.md`'s tier table putting ℚ and ℝ on
   the **import** side (both were built, both axiom-free); and its "today it is
   one `#print axioms` line run by hand", which `front_door_carrier
   --require-axiom-free` closed.

## What was deliberately left alone

- **`02-synthesize.md`** — nothing today falsifies it. The interchange-format
  survey and the alignment argument are unaffected by a Lean checker split.
- **`01-collect.md`** — already rewritten 2026-08-15 and updated 2026-08-17 with
  the 1,500-declaration census; its figures carry sources and dates.
- **The six diaries** — they are dated records of what a lane did. Correcting
  them would destroy the thing they are for.
- **The `N × 149/day` table** — kept, because the re-measurements read as
  corrections *of* it. Removing it would hide what was wrong.
- **`lean_crosscheck`'s family count** — the gate script comments say 70 / 73 /
  74 at different dates and ADR-0511 says 77. Not re-derived here, so no family
  count was asserted in the strand.

## Anything in the brief that was wrong

- The brief said `check-parity-docs.py` has **17** inherited errors; it reports
  **19** today. All 19 are `docs/reference/examples.md` missing-example rows —
  two more examples landed since (`autogenesis_apply_plan_check.rs`,
  `autogenesis_induction_plan_check.rs`). None relate to this lane's files, so
  the gate gained nothing.
- The brief said `lean_crosscheck` is "77 of 77"; the gate script's own comment
  says 70 of 70 families and a nearby comment says 41 of 73. Not asserted.
- The brief did not mention the "theorems the system proved without a human
  writing the proof: **currently zero**" claim, which appears in two files and is
  the single largest correction in this pass. It was found by asking whether the
  autogenesis lane's landings had falsified anything the strand asserts, not by
  following the brief.
