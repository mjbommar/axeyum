# evt-row1-land-and-register

<!-- plan-section: lane-status -->

**Status: DONE.** Acted on an independent audit's finding that the published
"EVT row 1 — there is none" claim (`08-ivt-and-evt-measured-against-mathlib.md`
§2, ADR-0692) was stale and wrong: `CReal.supOn_ub` and `CReal.supOn_approx_lub`
already existed under those exact names, and both documents' absence probes
had searched for a guessed name, `CReal.supOn_upper_bound`, that never existed.

## What landed

1. **`CReal.evt_approx_max`** — `crates/axeyum-lean-kernel/src/creal/evt_row1.rs`.
   Pure composition of `CReal.supOn_approx_lub` (the witness) and
   `CReal.supOn_ub` (the bound) through `CReal.le_trans`. `∀ n, ∃ x ∈ [a,b],
   ∀ y ∈ [a,b], F y ≤ F x + 1/(n+1)` — the exact structural mirror of
   `CReal.ivt_approx`, ADR-0603 row 1 for EVT. Axiom-free, wired into the
   `STEPS` dispatch table and its own inventory shard
   (`crates/axeyum-lean-kernel/src/creal/inventory/evt_row1.rs`).
2. A negative control, `evt_approx_max_needs_the_slack_term` (same file):
   the exact (epsilon-dropped) form is a different, false proposition and is
   rejected by the kernel — confirmed non-vacuous (`!def_eq`) and confirmed
   rejected, both in one test.
3. **Four facts registered**: `F:creal-supon`, `F:creal-supon-ub`,
   `F:creal-supon-approx-lub`, `F:creal-evt-approx-max`. Before this lane,
   zero facts named any `CReal.supOn` law — `grep -rl "sup_on\|supOn"
   artifacts/facts/` returned nothing.
4. **Corrections**, both citing what was measured rather than asserted:
   - [`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md) —
     a top-level correction block, the §2 "Row 1" heading, the summary
     table's EVT row, the §4 EVT axis discussion, and §5 items 1-2 marked
     DONE, all pointing at ADR-0895. Historical prose left verbatim and
     labeled STALE rather than rewritten, matching the doc's own existing
     correction pattern.
   - [ADR-0692](../../research/09-decisions/adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md) —
     a correction note plus an annotation on "What survives unchanged".
     ADR-0692's own DECISION (cite IVT, not EVT, for the headline claim) is
     untouched and still correct.
5. **[ADR-0895](../../research/09-decisions/adr-0895-evt-row-1-lands-and-two-absence-claims-were-wrong.md)** —
   the full history, the generalizable lesson (an absence probe searching a
   guessed name proves nothing about the thing, only the spelling), and what
   this landing does NOT change.

## What this does NOT change

- EVT still does not conclude an attained maximum. `evt_approx_max` does not
  narrow `CReal.evt_attained_max_decides_sign` at all — the witness moves
  with `n` and never converges.
- `F` is still required `UniformlyContinuousOn [a,b]` with an explicit
  modulus carried as `Sort 1` data.
- **The dominance verdict does not flip to "EVT dominates".** The comparison
  against Mathlib's `IsCompact.exists_isMaxOn` is now RUNNABLE (there is a
  genuine positive statement on our side for the first time), but it is an
  approximate bound against an exact attained maximum. Whether that counts
  as dominance, a narrower-but-comparable result, or something else is left
  for whoever next revisits `08-…`'s axis tables — deliberately out of this
  lane's scope, argued in ADR-0895.

## Re-verification performed

- `cargo test -p axeyum-lean-kernel --lib creal::` — 201 passed, 0 failed
  (406.29 s), after fixing one pinned-build-order regression the first run
  caught (`steps_table_matches_recorded_extraction`).
- `cargo test -p axeyum-lean-kernel --lib creal::evt_row1::` — 1 passed
  (116.28 s), the negative control.
- `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.
- `rustfmt --edition 2024 --check` on every touched Rust file — clean.
- Every `checker_command` in the four new facts executed by hand and
  confirmed to print the expected discriminating output (not merely assumed
  from the JSON).
- `python3 scripts/validate-facts.py` — 2322 facts, 0 errors.
- `python3 scripts/check-fact-depends-derived.py --fix` — added 33 missing
  edges across the two `supOn` law facts.
- `python3 scripts/check-settled-fact-statements.py --write` — pinned the
  four new facts (additive; picked up 4 unrelated already-settled facts from
  other lanes in the same pass, no existing pin's digest changed).
- `python3 scripts/check-autogenesis-holdout-isolation.py` — run before and
  after: `held_out=136|files_scanned=1110|settled=0|references=0|verdict=PASS`
  both times, unchanged (this lane never touches `artifacts/autogenesis/`).
- `bash scripts/check-links.sh` — all links ok.
- `python3 scripts/gen-adr-index.py --check` — exit 0
  (`duplicate_numbers=0166,0167` is pre-existing and grandfathered).

## Paths cited in the brief that were not visible in this worktree

`docs/research/09-decisions/adr-0875-*.md` and
`crates/axeyum-lean-kernel/src/creal/examples/ivt_evt_vacuity_probe.rs` were
both absent (push race, as the brief warned might happen). Proceeded from
primary sources: the kernel itself, ADR-0692 (which WAS visible, and carries
the same claim ADR-0875 apparently also made), and
`08-ivt-and-evt-measured-against-mathlib.md`.

## One honest sentence for a Mathlib maintainer

`CReal.evt_approx_max` gives an approximate maximum with an explicit,
computable error bound and zero trusted axioms; Mathlib's
`IsCompact.exists_isMaxOn` gives an exact attained maximum over an arbitrary
compact set in an arbitrary topological space, has nothing computable to
extract, and did not need eighteen months of a bespoke real-number
construction to state.
