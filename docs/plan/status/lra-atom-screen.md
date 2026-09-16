# Lane: `lra-atom-screen` — does raising the LRA online admission screen decide any of ADR-2111's 32 `lra.rs` rows

<!-- plan-section: lane-status -->

**Lane LRA-ATOM-SCREEN (`IN PROGRESS`, lra-atom-screen, 2026-09-16.)**
Reads: [ADR-2111](../../research/09-decisions/adr-2111-qf-lra-what-the-same-simplex-does-differently.md)
(the atom screen, § 5b, its A/B left unrun), [ADR-2122](../../research/09-decisions/adr-2122-lra-bound-propagation-into-the-sat-core.md),
[ADR-2125](../../research/09-decisions/adr-2125-a-warm-simplex-basis-across-sat-decisions.md),
[ADR-2132](../../research/09-decisions/adr-2132-a-builds-per-file-screen-for-the-warm-basis.md).
Artifacts: `bench-results/lra-atom-screen-20260916/`.
Compute: s5, physical core pairs `1,9` and `3,11` (confirmed free: zero
`smtcomp_cli` processes, no `nra-clause-loop` harness dir at all on s5).

### The mechanism, confirmed live before any sweep

`AXEYUM_LRA_ATOM_SCREEN` (`crates/axeyum-solver/src/lra_theory.rs`) is a
multiplier on `admitted_atoms` in ONE comparison,
`atom_terms.len() > admitted_atoms`, inside
`check_qf_lra_online_cdclt` — nothing downstream reads the multiplier again
(`CdcltLraTheory::new` is built from the real atom list and `budget_bytes`,
not from the allowance). So for a fixed file, raising the multiplier is a
**step function**: refused (bit-identical to shipped) below the file's own
threshold, bit-identical to one measured "admitted" run at or above it. That
is the measurement design this lane is using — see `run-ladder.sh`'s header
and `derive_ladder.py` — and it was checked live, not just read from source,
on `QF_LRA/2017-.../_standard_init5_ground.i_3_2_2.bpl_7.smt2` (one of the
32): at `AXEYUM_LRA_ATOM_SCREEN=1` it is refused by the admission screen
(`online_probe=admission-screen`); at `=65536` it now **enters** the online
CDCL(T) engine (`lazy-smt reading=not-reached`, `theory-layer` populated,
`simplex_rows=1839`) and comes back `unknown` again via
`online_probe=model-did-not-replay` — live confirmation of the wall ADR-2111
and ADR-2045 already named: opening the screen without fixing "model did not
replay" repeats that result. This is one file, not the finding; the full
sweep is running.

### Status at last update

- Binary built (`target/release/examples/smtcomp_cli`,
  sha256 `6261a505ea6767af32873bfc897ae64f8879b6388e5ea1074d27a6d3e12218e3`),
  deployed to `/nas3/data/axeyum/harness/lra-atom-screen/` (self-contained:
  `bin/`, `scripts/ledger-run-one.sh` + its two Python deps, `rss-wrap.sh`,
  `run-ladder.sh`, the five population lists).
- **Running in background on s5**: `shipped` pass (multiplier 1, `--trace`,
  24 s / 8 GiB) over all 200 `QF_LRA` rows on core 1 (this establishes the
  loss control AND recovers each refused row's exact atom count from the
  admission screen's own decline detail, which is what lets the ladder be
  derived rather than brute-force swept — see `run-ladder.sh`); and, on core
  3, the same `shipped` pass over `QF_UFLRA`, `QF_LIA`, `QF_RDL`, `QF_IDL`
  (200 each), which decides whether any of those divisions can even reach
  this screen before spending time on an "open" arm there.
- Not yet run: the "open" (admitted) arm on whichever files the shipped
  passes refuse; the 3x mover recheck; the README verdict.

<!-- plan-section: landed-changes -->

| 2026-09-16 | (pending) | Lane start: mechanism confirmed live, baseline sweeps launched. |
