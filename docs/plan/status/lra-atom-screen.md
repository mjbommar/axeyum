# Lane: `lra-atom-screen` — does raising the LRA online admission screen decide any of ADR-2111's 32 `lra.rs` rows

<!-- plan-section: lane-status -->

**Lane LRA-ATOM-SCREEN (`MEASURED, DOES NOT SHIP`, lra-atom-screen, 2026-09-16.)**
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

### Final result

**Does not ship at any tested level (2x, 4x, 16x, off/65536x). No
config_registry change, no ADR-2137, no Rust touched.**

Every level fails "≥1 stable gain" (0 newly decided `QF_LRA` rows at any
multiplier, over the full 200-row population, the 70-row admission-screen-
refused subset, and the specific 32-row `lra.rs` bucket this census was
about). 16x and off additionally fail "0 aborts introduced": 6 and 8 new
allocator aborts respectively (`exit=134`, `SIGABRT`), each confirmed
STABLE 3/3 on a follow-up recheck (24 of 24 runs across the 8 aborting
files return exit 134). Peak RSS on one such file: 120.6 MiB shipped →
7.38 GiB at 65536x, killed at the 8 GiB `ulimit -v` ceiling — the exact
"screen is a conservative stand-in for an allocation nobody has found"
failure mode ADR-2111's own doc predicted, still present after the sparse
tableau (ADR-2125/2132).

**Why**: the 32-row bucket's true wall is "online CDCL(T) LRA model did not
replay", not atom count. 10 of 32 are already admitted at the shipped
multiplier and stuck behind that wall; the 22 the screen does refuse
(thresholds 2–13, all admitted by 16x) mostly walk into the SAME wall from
the other side once admitted (18 of 22), with the remaining 4 becoming new
aborts. Reproduces ADR-2045's finding under a different lever, matches
ADR-2111 §6 item 2 ("model did not replay" is prior/separate work).

Cross-division (all measured, none reverses the QF_LRA verdict): QF_UFLRA
8 admission-screen hits, 0 gains/losses/aborts. QF_RDL 36 hits, 0
gains/losses/aborts, max RSS only 1.27 GiB (no memory blowup there). QF_LIA
and QF_IDL: 0 candidates each — the lazy-SMT offline loop this screen
guards entry to is never reached at all on either population
(`reading=not-reached` on every row), so the lever provably cannot affect
either division. (QF_LIA's board TSV has only 140 distinct corpus paths of
200 data rows — 60 exact duplicates — recorded so "checked all 200" isn't
overstated; the other three cross-division boards are clean.)

Full numbers, method (why two passes suffice for a five-level ladder — the
screen gates one boolean and the multiplier value is never read again after
that check passes, so a file's admitted behaviour doesn't depend on WHICH
admitting multiplier was used), and the worked mechanism example:
`bench-results/lra-atom-screen-20260916/README.md`.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `0ac3fed2b` | Lane start: harness, population lists, mechanism confirmed live. |
| 2026-09-16 | `eb327f569` | QF_LRA/QF_UFLRA/QF_LIA measured: 0 gains at every level, 16x/off introduce new allocator aborts. |
| 2026-09-16 | `e8733acb0` | QF_RDL measured: 36 admission-screen hits, 0 gains/losses/aborts. |
| 2026-09-16 | (pending) | QF_IDL measured (0 candidates), abort stability 3x (24/24 stable), final README + ship decision. |
