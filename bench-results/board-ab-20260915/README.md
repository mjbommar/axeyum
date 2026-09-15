# Nine ADRs moved no canonical verdict — the regression check that mattered

**2026-09-15.** Interleaved per-file A/B of **`2611e14b0`** (where the board last
read 2,417) against **`054104068`**, across all **16 divisions × 200 files**.
Both arms back to back on the same file on the same pinned core, order
alternating, 24 s wall / 8 GiB `ulimit -v`, 4 shards on s5/s6 cores `5,13`+`6,14`
while other lanes used the rest.

| | |
|---|---:|
| base arm | **2,419** |
| current main | **2,419** |
| net | **+0** |
| gains / losses / sat↔unsat flips | **0 / 0 / 0** |
| divisions that moved at all | **NONE** |
| soundness | **4,356 comparisons vs declared `:status`, 0 disagreements** |

## This was a regression check first, and it passed

Between those two commits, nine ADRs landed: three parser soundness fixes that
changed **wrong verdicts to right ones** ([ADR-2010]), a model-rendering fix
([ADR-2070]), the LRA sparse simplex entry ([ADR-2055]), opaque Real atoms
([ADR-2065]), the give-up variant split ([ADR-2060]), the round-cap null
([ADR-2035]) and the lemma-refresh null ([ADR-2080]). Several touch code every
division's queries pass through — the parser, `lra.rs`, the dispatch ladder.

**Nobody had measured any of it against this board.** Now it is measured: not one
canonical verdict moved in either direction.

## It also confirms each lane's own post-merge prediction

Each of those ADRs predicted its own effect here, and each was right:

- ADR-2055 predicted `QF_LRA` stays at 107 — it does.
- ADR-2065's 14 gains were all `AUFLIRA`, which is **not on this board** — and
  indeed nothing here moved.
- ADR-2080, ADR-2075 and ADR-2035 all ship `Off`, and all measure 0 here.

That matters after a week in which a lane's `+22` became `+6` once merged. The
per-lane predictions have become reliable, and this is the check that says so.

## Why interleaved rather than a single-arm sweep

The same binary scored **77, 79 and 85** on one division in a single day purely
on ambient load. A single-arm level is only comparable against another single-arm
run at similar load; the *difference* survives contention, which is why this ran
four shards beside two other lanes without the result being a hostage to them.

## The one population caveat, unchanged from 2026-09-14

`bench-results/session-20260911-smtlib/head-to-head/*.tsv` records **basenames,
not paths**, and 370 of 3,200 resolve to more than one corpus file. A documented
deterministic tie-break keeps every division at exactly 200 and both arms on
identical files, so the delta is unaffected. Lane `core-select` independently hit
the same thing from the other side: the `QF_NIA` board row is
`20170427-VeryMax/SAT14/106.smt2` where the pinned list has `mcm/106.smt2`.
**Both exist; it is a basename collision in the board's own runner.** The fix for
the next board is still to record the corpus-relative PATH.
