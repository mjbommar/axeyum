# What our work is worth on the canonical board, measured immune to load

**2026-09-14.** Interleaved per-file A/B of the canonical board commit
**`1446a809c`** (2026-09-11, the tree that produced the 2,309 head-to-head row)
against **`2611e14b0`**, over all **16 divisions × 200 files**. Both arms run
back to back on the **same file** on the **same pinned physical core**, order
alternating per file, 24 s wall / 8 GiB `ulimit -v`, four shards on s7 only,
divisions serial within a shard.

## Why this exists rather than another single-arm board

**The same code scores 77, 79 or 85 on `QF_NIA` depending only on machine load.**
Measured the same day, one binary:

| conditions | QF_NIA |
|---|---:|
| single-arm, load ~10 | 77 |
| interleaved A/B, 2x oversubscribed | 79 and 79 |
| single-arm, quiet box | 85 |

That is a 10 % swing at fixed code, and it is why every cross-day board
comparison in this repository is suspect: the 2026-09-11 row was measured with a
careful interleaved protocol and the 2026-09-13 re-measures were single-arm under
load, so their difference contained both our work and the machine. **The level
moves with load; the difference does not** — the 2x-oversubscribed run above
reads 79 in *both* arms and its delta is still exactly the delta.

## Result

| division | board arm | main | net | gains | losses | tie-broken | A-arm vs canonical |
|---|---:|---:|---:|---:|---:|---:|---:|
| QF_DT | 114 | **170** | **+56** | 57 | 1 | 0 | +0 |
| QF_NIA | 41 | **82** | **+41** | 41 | 0 | 1 | +0 |
| QF_UFLRA | 141 | 148 | **+7** | 7 | 0 | 0 | −3 |
| QF_ABV | 186 | 188 | +2 | 2 | 0 | 0 | +0 |
| QF_RDL | 148 | 150 | +2 | 2 | 0 | 0 | −4 |
| QF_IDL | 111 | 112 | +1 | 1 | 0 | 1 | −2 |
| QF_NRA | 117 | 116 | **−1** | 0 | 1 | 0 | +0 |
| QF_BV | 179 | 179 | +0 | 0 | 0 | 129 | −7 |
| QF_FP | 199 | 199 | +0 | 0 | 0 | 0 | +0 |
| QF_LIA | 127 | 127 | +0 | 0 | 0 | 142 | +8 |
| QF_LRA | 107 | 107 | +0 | 0 | 0 | 0 | +0 |
| QF_S | 186 | 186 | +0 | 0 | 0 | 1 | +0 |
| QF_SLIA | 196 | 196 | +0 | 0 | 0 | 49 | +3 |
| QF_UF | 199 | 199 | +0 | 0 | 0 | 37 | −1 |
| QF_UFLIA | 161 | 161 | +0 | 0 | 0 | 0 | −1 |
| UF | 91 | 91 | +0 | 0 | 0 | 10 | +1 |
| **total** | **2,303** | **2,411** | **+108** | **110** | **2** | | **−6** |

**Against the published canonical row of 2,309, this is 2,309 → 2,417 of 3,200.**
References on the same 3,200: z3 **2,790**, cvc5 **2,652**.

## Soundness

**4,232 comparisons against the files' declared `:status`, across both arms,
0 disagreements.** The comparable denominator is published beside the zero
deliberately: two verifiers in this repository have reported confident zeros from
comparing nothing — one `$`-anchored grep that never matched any file, and one of
mine on this very run that read the `first` column instead of `status` and
printed `comparable=0, disagreements=0`. **A disagreement count without its
denominator is not evidence.**

## The A-arm is the control, and it caught a reproducibility defect

The board arm re-measures the *same commit* the canonical row was measured at, so
where it reproduces the canonical number the population reconstruction is
confirmed and the delta beside it is trustworthy.

**It does not always reproduce it, and the reason is a defect in the committed
artifact: `bench-results/session-20260911-smtlib/head-to-head/*.tsv` records
BASENAMES, not paths.** Against the real corpus, **370 of the 3,200 basenames
resolve to more than one file** — `QF_LIA` 142, `QF_BV` 129, `QF_SLIA` 49,
`QF_UF` 37. The exact population that produced 2,309 is **not reconstructible
from what is in the repository.**

Rather than drop ambiguous rows — which would silently shrink the denominator,
the precise failure this frame exists to prevent — a **documented deterministic
tie-break** (lexicographically first candidate path) keeps every division at
exactly 200. The A/B delta is unaffected: both arms see identical files.

The divergences line up with ambiguity exactly as predicted: every division with
≤1 tie-break reproduces the canonical value to within 2 files, while `QF_BV`
(−7, 129 tie-breaks) and `QF_LIA` (+8, 142) do not. **On the 11 low-ambiguity
divisions the reconstruction is off by 10 of 1,521 files (0.7 %).**

**Fix for the next board: record the corpus-relative PATH, not the basename.**

## Caveats

- **The `−1` on `QF_NRA` is not called a regression.** A single file is inside
  the noise band measured today: three passes of identical code on `UFLIA` gave
  **+1 / −2 / +0** with every moved row UNSTABLE, and a separate lane measured a
  band of 2 files on a 200-file division. It needs a 3x re-check per arm before
  anyone uses the word.
- **`QF_DT`, `QF_NIA` and `QF_UFLRA` were not re-checked 3x either.** They are
  far outside any measured noise band, so the direction is not in doubt, but the
  exact values are single-pass.
- A sweep's **shard configuration** moved a count by more than repeating the
  sweep did (ADR-2000: 69 under 8 shards on 4 pairs vs 72–74 under 6 on 6). This
  run held 4 shards on 4 pinned pairs of one host for every division and both
  arms.
- The binaries were confirmed distinct by digest, and the board binary was
  **force-rebuilt** after a snapshot handed back a cached artifact dated three
  days earlier from a 0.85 s "build".
