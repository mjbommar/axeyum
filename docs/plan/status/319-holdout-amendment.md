# Lane: holdout-amendment -- repair a spent blind-evaluation population

<!-- plan-section: lane-status -->

**Lane block (`DONE -- holdout-isolation green at held_out=96, two ADR-0542
amendments recorded, R10 binds the ledger to the v2 manifest, brief-step0
refuses a held-out target, holdout-amendment, 2026-08-30`).**

## Headline

`check-autogenesis-holdout-isolation.py` was `held_out=127|settled=10|FAIL` on
`main` and is now `held_out=96|settled=0|references=0|PASS`. No fact was
reopened; all ten are genuinely proved. The guard gap that produced the
incident is closed in three places, and the amendment is now machine-enforced
rather than recorded in a file nothing read.

Commits: `81c1aef5a`, `6f4b1e62b`, `137451362`, `1093e02f9`, `876ba7c47`,
plus the ADR commit below. **Not pushed.**

## 1. The dating -- the brief's reading held for 4 rows and not for 6

Declaration dates are the first commit introducing each
`<leaf>: kernel.name_str(nat, "<leaf>")` registration under `crates/`.

| fact | kernel theorem | declared | manifest | preregistered | blind then? |
| --- | --- | --- | --- | --- | --- |
| `F:ml430-nat-log-zero-left-9ec8541e` | `Nat.log_zero_left` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 `2d65f19d8` | YES |
| `F:ml430-nat-log-zero-right-8ea186db` | `Nat.log_zero_right` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-of-lt-89eaf42e` | `Nat.log_of_lt` | 2026-08-28 `1dd090dff` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-le-self-da387172` | `Nat.log_le_self` | 2026-08-28 `722d9c204` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-left-1c61a5bf` | `Nat.clog_zero_left` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-right-d42d47b1` | `Nat.clog_zero_right` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-dvd-add-0c5bcc91` | `Nat.dvd_add` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 `94b3e61ee` | **NO** |
| `F:ml430-nat-dvd-mul-right-a87a83c4` | `Nat.dvd_mul` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-add-iff-right-bf79c0cd` | `Nat.dvd_add_iff_right` | 2026-08-14 `eccaf84ac` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-antisymm-507f9026` | `Nat.dvd_antisymm` | 2026-08-24 `7de26df70` | v2-ext | 2026-08-29 | **NO** |

**Did anything leak? Not because of the sweep, and the two families differ.**

Detail moved to [`../notes/319-holdout-amendment.md`](../notes/319-holdout-amendment.md).

