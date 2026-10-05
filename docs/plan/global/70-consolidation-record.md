## Consolidation record

### 2026-10-05

`PLAN.md` had grown to 75,717 lines and its global sections were three to seven
weeks stale. The 770 lane files moved to `docs/plan/archive/lanes/`; the replaced
sections are kept verbatim in `docs/plan/archive/global-2026-09-17/`; A1–A13
and L0–L4 became five tracks. Stale claims corrected, each checked against the
tree at `a38d5f5da`:

- The header said "last consolidated 2026-08-13" and cited A5-era SHAs.
- Status and Workstream quoted 2026-08-21 and 2026-09-05 parity numbers; every
  division has a 2026-09-11 ledger entry, and the 09-17 board is newer still.
- A13 read `PAUSED` with items 1–4 open; all four closed on 2026-09-17
  (`f7cd4195f`, `aa4ea0b6b`, `aab5d2db7`, `4d7c61ad5`). Its item 5 said the
  frame was 313 commits behind; it is now 425.
- A12 asked for a `CdclT` ADR and BatSat retirement; ADR-1908 and ADR-1910 are
  both accepted, and BatSat is out of `Cargo.lock`. Only phase B4 is left.
- L0–L4 read `TODO`; the phase lane files report S0–S6, C0–C3, G0–G5, D0–D5
  done on 2026-08-30/31. Only D6, C4 and C5 remain.
- A9 listed four open Lean items; `14-lean-lang.md` ticks all ten.
- Families said QF_RDL had "fourteen" unexplained files; the ledger gap is 2.
- The math chair's "Next Five" landed on 2026-09-06 and was never ticked.

### 2026-08-05

Removed two conflicting append-only root journals and one subsidiary live
tracker, made this file the only project-level authority, and corrected five
stale claims (CAS wave 24, an August-1 resume block, seven-vs-eleven divisions,
T3.5 ordering, PLAN-vs-STATUS authority). Detail is in Git history.
