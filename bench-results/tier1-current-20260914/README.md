# Tier 1 on current main — the goal table's rates are stale by a wide margin

**2026-09-14, on `78ca906c2`.** All seven Tier 1 divisions, 200 files each,
single arm, fresh binary, 24 s wall / 8 GiB `ulimit -v`, one pinned physical core
per shard, 12 shards across s5/s6/s7, divisions **serial** within a shard.

| division | goal table | **measured** | decided | prior measure | delta |
|---|---:|---:|---:|---:|---:|
| AUFLIRA | 4 % | **82 %** | 164/200 | 160 | +4 |
| UFNIA | 20 % | **26 %** | 53/200 | 53 | +0 |
| UFLIA | 36 % | **42 %** | 85/200 | 73 | **+12** |
| AUFDTLIRA | 45 % | **60 %** | 121/200 | 118 | +3 |
| QF_NIA | 40 % | **42 %** | 84/200 | 82 | +2 |
| UF | 45 % | **45 %** | 90/200 | 90 | +0 |
| UFDTLIRA | 51 % | **72 %** | 144/200 | 143 | +1 |
| **total** | | **53 %** | **741/1,400** | 719 | +22 |

**700 comparisons against the files' declared `:status`, 0 disagreements.** The
comparable denominator is published beside the zero because two verifiers in this
repository have reported confident zeros from comparing nothing.

## Only ONE of the seven deltas is a claim

**`UFLIA` +12 is real**: it is [ADR-2025]'s boolean-skeleton rung landing on
merged `main`, slightly above the **+9** its own interleaved A/B measured
on-branch, and that A/B carried 9/9 STABLE-GAIN over three passes per arm with a
noise floor of 0.

**The other four (+4, +3, +2, +1) are NOT claims.** Every one is inside the
noise band measured repeatedly this week: a same-arm band of **1 of 129**
(ADR-2020), **2 of 129** (ADR-2015), and three passes of *byte-identical* code
giving **+1 / −2 / +0** with every moved row UNSTABLE (ADR-2005). This is a
single-pass sweep, so it cannot separate them from zero. They need 3x per arm
before anyone quotes them.

## What the table is actually for

The goal table's rates predate this week entirely. The correction that matters:
**`AUFLIRA` is not 4 % — it is 82 %**, on the division ranked first by undecided
mass. `UFDTLIRA` is 72 % rather than 51 %, and `AUFDTLIRA` 60 % rather than 45 %.

Gaps to the per-division reference, on these same 200-file samples:

    UFNIA 61 · QF_NIA 60 · UFLIA 59 · AUFDTLIRA 55 · UFDTLIRA 37 · AUFLIRA 33 · UF 3

`UF` is effectively closed. The four largest gaps are now `UFNIA`, `QF_NIA`,
`UFLIA` and `AUFDTLIRA`.

## Method note

Divisions run **serially** within a shard. Launching them concurrently on one
pinned core pair oversubscribes it and biases every number DOWN — caught on an
earlier sweep before any row was recorded, and the reason that run was discarded
and relaunched. The same code has scored 77, 79 and 85 on one division in a
single day purely on ambient load, so a single-arm level is only comparable
against another single-arm run at similar load.
