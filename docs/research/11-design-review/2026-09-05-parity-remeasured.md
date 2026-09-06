# Parity board re-measured at one commit on idle hosts, 2026-09-05

All eleven committed benchmark lists under `bench-results/parity-lists/` were
run through `scripts/parity-run.sh` on the same day, at the same solver commit,
on idle fleet hosts. Entries are in [`bench-results/PARITY.md`](../../../bench-results/PARITY.md)
under the 2026-09-05 and 2026-09-06 UTC timestamps; per-file sidecars are the
gitignored `bench-results/parity-details/<DIV>.tsv` on each measuring host.

## Protocol

| field | value |
|---|---|
| solver commit | `9914a1c0e` (main after ADR-1703 native CDCL core as default, ADR-1701 widened theory interface with DL and LRA opted in, ADR-1702 opt-in wide rationals in the simplex) |
| hosts | s5, s6, s7: 16-thread i5-class boxes, otherwise idle, load 0.0 to 1.6 throughout |
| pinning | `taskset -c 0-7`, one division at a time per host |
| budget | 24 s wall, 8 GiB, per file (SMT-COMP single-query convention) |
| references | Bitwuzla 0.9.1 for QF_BV and QF_ABV; cvc5 1.3.4 (`f3b21c4`), plain invocation, for the rest |
| knobs | none: no `PARITY_BUDGET_S`, `PARITY_REFERENCE_OPTS`, `PARITY_ALLOW_DIRTY`, `PARITY_ALLOW_WEAK_REFERENCE` |
| resume | five divisions reused rows from a sweep the same binary began minutes earlier on the same idle host after the driving agent was cut off; each entry records the count |
| build | one `git bundle` of `9914a1c0e` shipped to each host, detached worktree, `cargo build --release -p axeyum-bench --example smtcomp_cli`, 41,090,616 bytes on all three |

## The board

Previous = latest earlier entry for the division, sorted by solver commit per
the 2026-08-21 batch note. All August entries ran on a loaded 16-thread box.

| Division | Reference | Previous | 2026-09-05 | Ours | Theirs | both / ours only / theirs only |
|---|---|---:|---:|---:|---:|---|
| QF_SLIA | cvc5 | 193 / 193 = 100.0% | 193 / 194 = 99.5% | 0 | +1 | 187 / 6 / 7 |
| QF_BV | Bitwuzla | 187 / 194 = 96.4% | 188 / 194 = 96.9% | +1 | 0 | 188 / 0 / 6 |
| UF | cvc5 | 83 / 93 = 89.2% | 85 / 93 = 91.4% | +2 | 0 | 61 / 24 / 32 |
| QF_ABV | Bitwuzla | never run | 179 / 197 = 90.9% | new | | 178 / 1 / 19 |
| QF_LIA | cvc5 | 113 / 139 = 81.3% | 114 / 139 = 82.0% | +1 | 0 | 112 / 2 / 27 |
| QF_UF | cvc5 | never run | 162 / 200 = 81.0% | new | | 162 / 0 / 38 |
| QF_RDL | cvc5 | 102 / 148 = 68.9% | 107 / 154 = 69.5% | +5 | +6 | 107 / 0 / 47 |
| QF_UFLIA | cvc5 | 113 / 180 = 62.8% | 122 / 180 = 67.8% | +9 | 0 | 122 / 0 / 58 |
| QF_LRA | cvc5 | 88 / 134 = 65.7% | 91 / 145 = 62.8% | +3 | +11 | 91 / 0 / 54 |
| QF_IDL | cvc5 | 66 / 118 = 55.9% | 70 / 123 = 56.9% | +4 | +5 | 69 / 1 / 54 |
| QF_NIA | cvc5 | 39 / 83 = 47.0% | 39 / 87 = 44.8% | 0 | +4 | 26 / 13 / 61 |

Totals over the nine re-measured divisions: axeyum 1,009 decided (was 984,
+25); references 1,309 (was 1,282, +27). Disagreements: 0 in 11 of 11
divisions, 2,200 files, three reference solvers.

## What moved, and why

**Soundness held through an engine replacement.** ADR-1703 put the native CDCL
core under every division on the same day these were measured. Zero
disagreements anywhere is the row the board depends on.

**Our count rose in six of nine re-measured divisions and held in three.**
Nothing regressed. QF_UFLIA +9 is the largest gain and is the division the
August core-minimisation fix (ADR-0538) and today's widened theory interface
(ADR-1701) both touch. QF_RDL +5 and QF_IDL +4 are the difference-logic
divisions whose theory opted into the new interface. QF_BV +1 is the division
that ran on BatSat for months; with the native core as default it gained a
file, and Bitwuzla's six exclusive files are the same six.

**Three ratios fell, and all three fell because the reference got stronger on
an idle host, not because we got weaker.** QF_LRA: ours 88 to 91, cvc5 134 to
145. QF_NIA: ours 39 to 39, cvc5 83 to 87. QF_SLIA: ours 193 to 193, cvc5 193
to 194. cvc5's QF_NIA count on this list has now read 89, 76, 76, 81, 83 and 87
across six sweeps. The ledger's 2026-08-21 note already says to read the
`axeyum solved` count when the reference count moves; these three rows are
that case.

**Two never-run lists have first entries.** QF_ABV 90.9% against Bitwuzla with
one file we decide that it does not; QF_UF 81.0% against a cvc5 that solves
the full list.

**UF has the widest axeyum-only column on the board**: 24 files we decide that
cvc5 does not, against 32 the other way. The composition shift first seen on
2026-08-21 is real.

**The shape of the deficit is unchanged and now cleanly measured.**
Bit-vectors, arrays and uninterpreted functions: 81 to 97%. Linear arithmetic:
57 to 70%. Nonlinear integers: 45%. The
[ADR-1701 slice-1 measurement](2026-09-05-adr-1701-slice-1-measured.md) shows
the IDL timeouts spend 18 to 20 s of 24 in the CDCL(T) driver's own Boolean
propagation with the theory under 0.1 s, and the
[micro-benchmarks](../08-planning/microbenchmarks-2026-09-05.md) put that driver
at about 7x the native core on identical CNF. Unifying the two engines (ADR-1701
slice 2) is the lever; its hook cost and design are being measured as this
note is written.

## What this does not establish

- Comparability with the August entries is by count, not ratio: the August box
  was loaded and these hosts were idle, which is why every reference count
  either held or rose.
- Five entries carry a `resumed` row. The reused rows came from the same binary
  on the same idle host minutes earlier, so the mixture is of moments, not of
  machines or builds.
- The 24 s budget is the competition convention; nothing here says what a
  60 s or 1200 s budget would show.
- cvc5 ran plain, not with its competition portfolio, per the ledger's standing
  rule; UF in particular would read differently against `--finite-model-find`.
