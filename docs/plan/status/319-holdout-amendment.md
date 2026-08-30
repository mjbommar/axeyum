# 319 — held-out amendment: repairing a spent blind population

**Lane:** `holdout-amendment` · **Status:** in progress

## Step 1 — the dating (DONE, and it corrects the brief's reading)

`scripts/check-autogenesis-holdout-isolation.py` is FAIL on `main`:
`held_out=127, settled=10`. The ten settled rows split into TWO families with
DIFFERENT causes, and lumping them would misreport both.

Declaration dates are the first commit introducing each
`<leaf>: kernel.name_str(nat, "<leaf>")` registration under `crates/`.

| fact | kernel theorem | declared | manifest | preregistered | blind when preregistered? |
| --- | --- | --- | --- | --- | --- |
| `F:ml430-nat-log-zero-left-9ec8541e` | `Nat.log_zero_left` | 2026-08-28 `3707c6040` | nursery-v1 | 2026-08-18 `2d65f19d8` | YES |
| `F:ml430-nat-log-zero-right-8ea186db` | `Nat.log_zero_right` | 2026-08-28 `3707c6040` | nursery-v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-of-lt-89eaf42e` | `Nat.log_of_lt` | 2026-08-28 `1dd090dff` | nursery-v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-le-self-da387172` | `Nat.log_le_self` | 2026-08-28 `722d9c204` | nursery-v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-left-1c61a5bf` | `Nat.clog_zero_left` | 2026-08-28 `2ccf6322c` | nursery-v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-right-d42d47b1` | `Nat.clog_zero_right` | 2026-08-28 `2ccf6322c` | nursery-v1 | 2026-08-18 | YES |
| `F:ml430-nat-dvd-add-0c5bcc91` | `Nat.dvd_add` | 2026-08-13 `46b47f869` | nursery-v2-ext | 2026-08-29 `94b3e61ee` | **NO** |
| `F:ml430-nat-dvd-mul-right-a87a83c4` | `Nat.dvd_mul` | 2026-08-13 `46b47f869` | nursery-v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-add-iff-right-bf79c0cd` | `Nat.dvd_add_iff_right` | 2026-08-14 `eccaf84ac` | nursery-v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-antisymm-507f9026` | `Nat.dvd_antisymm` | 2026-08-24 `7de26df70` | nursery-v2-ext | 2026-08-29 | **NO** |

### What this means

The brief's reading was that the declarations predate preregistration, so the
repair is accounting. That is **true for the four `natural-divisibility` rows
and false for the six `natural-logarithm` rows**, and the two need different
amendment reasons:

* **`natural-logarithm` (v1, 21 held-out rows).** Preregistered 2026-08-18 when
  no `Nat.log`/`Nat.clog` existed at all — genuinely blind. Contaminated
  2026-08-28 by ordinary `nat_prelude/log.rs` + `clog.rs` development that never
  mentions the mirror programme. This is a REAL breach of a blind population,
  the same shape as the 2026-08-25 `natural-binomial` amendment already in the
  ledger (contamination by ordinary development), not an accounting artifact.
* **`natural-divisibility` (v2 extension, 10 held-out rows).** Preregistered
  2026-08-29, by which time all four theorems had been admitted for 5 to 16
  days. These rows were **never blind**; the refill generator assigned held-out
  to propositions the kernel already proved. Nothing was spent because there
  was nothing to spend.

Either way the sweep (`92a61164e`) did NOT cause a leak: every declaration
predates it. It recorded a fact rather than creating one. The brief's
conclusion about the sweep holds; its premise about the dating does not.
