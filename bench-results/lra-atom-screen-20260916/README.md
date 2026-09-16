# The LRA atom screen: does raising it decide any of ADR-2111's 32, now that the tableau is sparse?

Status: **IN PROGRESS** — sweeps running, this file is a skeleton pending the
measured tables (see `docs/plan/status/lra-atom-screen.md` for live status).

## The question

ADR-2111's census found `QF_LRA`'s largest ADDRESSABLE undecided bucket is 32
rows that die inside `lra.rs`'s offline Fourier–Motzkin fallback (86–91%
addressable against reference solvers), not the dense tableau that lane fixed.
Those 32 rows get there because the online CDCL(T) engine's own admission
screen (`AXEYUM_LRA_ATOM_SCREEN`, `crates/axeyum-solver/src/lra_theory.rs`)
refused them for having too many atoms, and the route policy falls through to
the much weaker offline loop. The screen's own doc names why raising it is a
trap and not just an opportunity: three replacement cost models were built and
falsified by the corpus, the last of which bounded Fourier–Motzkin's own
allocations correctly and still let `danoint-266.smt2` reach 7.8 GB with no
simplex involved. ADR-2125 and ADR-2132 have since made the tableau sparse
(measured fill-in up to 21x). So: **does raising the screen decide any of the
32 now, and what does it cost in memory and time?**

## Method

See `run-ladder.sh` and `derive_ladder.py` for the full reasoning. Short
version: the screen gates one boolean comparison and nothing downstream reads
its value again, so for a fixed file the outcome is a step function of the
multiplier — refused (bit-identical to shipped) below the file's threshold,
bit-identical to one measured "admitted" run at or above it. So this lane runs
exactly two passes over the population (`shipped`, and one "open" admitted arm
on whichever files `shipped` refuses, interleaved per file), not a brute-force
sweep at five multiplier values, and derives every ladder level's table from
those two measured passes. Every number below is a real measured run; nothing
is extrapolated across code that did not execute.

Envelope: 24 s budget, 8 GiB `ulimit -v` (soft), pinned core, `--trace`, peak
RSS captured via `/usr/bin/time -v` (`rss-wrap.sh`). Population: the 93
undecided + 107 decided (loss control) `QF_LRA` rows from
`bench-results/board-ab-20260915/QF_LRA.tsv` (confirmed to match
`bench-results/lra-trace-20260915/{undecided-93,decided-107}.txt` exactly).

## The mechanism, confirmed live

On `QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_standard_init5_ground.i_3_2_2.bpl_7.smt2`
(one of the 32): at the shipped multiplier the online CDCL(T) probe is refused
by the admission screen (`online_probe=admission-screen`, 1,839 atoms against
a 1,024 allowance) and the query falls through to the offline loop, which
burns the whole budget on Fourier–Motzkin and returns `unknown`. At multiplier
65536 the SAME file now enters the online engine directly
(`lazy-smt reading=not-reached`, the offline loop never runs;
`theory-layer` populated: 428,277 decisions, `simplex_rows=1839`) — and comes
back `unknown` again, this time via `online_probe=model-did-not-replay`. This
is the wall ADR-2111 and ADR-2045 already named (opening the screen without
fixing model reconstruction repeats ADR-2045's "0 newly decided, 19 dying at
model-did-not-replay" result), now confirmed live on this lane's own binary
and corpus. It is one file, not the finding — the full sweep is what decides
the finding.

## [PENDING] The ladder table

## [PENDING] The memory curve

## [PENDING] The 32's enter/refuse/fail split

## [PENDING] Cross-division check (QF_LIA, QF_UFLRA, QF_RDL, QF_IDL)

## [PENDING] Ship decision
