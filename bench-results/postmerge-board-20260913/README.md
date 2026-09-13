# Post-merge board — a lane's A/B arm is not the landed result

**2026-09-13, on `f234017e1`.** Every division re-measured on **merged `main`**
with a **freshly built binary**, full 200 files, one arm: *what does main
actually decide?*

This exists because a lane's A/B measures **its branch**. Nine lanes landed
today and I recorded each lane's arm as the board value without re-measuring
after the merge. Seven survived closely. One did not.

| division | original board | recorded from lane arm | **re-measured on main** | vs recorded | vs board |
|---|---:|---:|---:|---:|---:|
| AUFLIRA | 10 | 164 | **160** | −4 | **+150** |
| AUFNIRA | 3 | 122 | **120** | −2 | **+117** |
| AUFDTLIRA | 0 | 110 | **96** | **−14** | +96 |
| UFDTNIRA | 5 | 92 | **86** | −6 | **+81** |
| UFDTLIRA | 66 | 105 | **105** | 0 | +39 |
| QF_NIA | 41 | 80 | **77** | −3 | +36 |
| UFLIA | 71 | 76 | **73** | −3 | +2 |
| UF | 90 | 90 | **90** | 0 | 0 |
| UFNIA | 53 | 53 | **47** | −6 | **−6** |
| **total** | | **892** | **854** | **−38** | **+515** |

**The work is real: +515 against the original boards. The recorded total was
overstated by 38 (4%).**

## The one that actually failed to land

`ADR-1966` recorded **AUFDTLIRA 90 → 110 (+22 re-checked)**. On main it is **96**,
measured twice at different loads. That `+22` was worth about **+6** once merged.

**It is not a regression, and I checked rather than assumed.** I first suspected
ADR-1965 had cost AUFDTLIRA 14 files, proposed a mechanism (it made array routes
decline nested sorts, and its controls were QF_ABV/QF_BV which could not have
shown it), and said so. Then I built a binary at `9c24786d0` — pre-ADR-1965 —
and ran it against main over all 104 files main returns `unknown` on:

    104 unknown -> unknown,  0 losses

Nothing was lost. The mechanism was a story built around a number difference
before the number was tested, which is the same error this repository's ADRs
keep recording in censuses.

## Caveats — read these before quoting a row

- **This run was single-arm at load ~10 with 12 concurrent solvers.** The lanes
  used pinned cores and interleaved arms precisely so ambient load cancels in
  the difference. These numbers are therefore a **lower bound**, and the small
  deltas (−2, −3, −4) are consistent with load alone. AUFDTLIRA's −14 is the one
  to trust: it reproduced at low load twice.
- **UFNIA at 47 is below its own board's 53 and is NOT being called a
  regression.** It needs a quiet-box re-run first. An hour earlier I called a
  14-file difference a regression, named a cause, and was wrong.
- The original-board column mixes boards taken at different times; see
  `bench-results/winnable-polarity-20260913/README.md` for why a board is a
  snapshot.

## The practice this changes

**After merging a lane, re-measure the affected division on `main` before the
number goes anywhere.** One 200-file run. Every verification I did per lane —
re-tallying its TSVs, live spot-checks of its gains — confirms *the lane's arm*,
which is exactly what was already true. None of them tests the merge.
