# 275 — autogenesis refill: the selection mechanism, not just the queue

Lane: `autogenesis-refill`. Status: **in progress** (this commit records the
re-measurement only; nothing else has landed yet).

## Step 0 — re-measurement (2026-08-29, this worktree, after `git merge main`)

The numbers in
[`docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md`](../../research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md)
reproduce exactly. Measured from `artifacts/facts/*.json` and
`artifacts/autogenesis/nursery-v1.json` directly, not from the note:

| | measured |
| --- | --- |
| facts total | 1,949 |
| `ml430` population | 214 |
| `ml430` proved | 155 (72.4%) |
| `ml430` open | 59 |
| open, all facts | 64 — so the **non-mirror open set is 5** |
| nursery entries | 216 (train 78 / development 99 / held-out 37 / longitudinal 2) |

Decomposition of the 59 open `ml430` rows by nursery partition:

| partition | rows | of which mutation controls |
| --- | --- | --- |
| held-out | 37 | 0 |
| development | 16 | 4 |
| train | 6 | 8 |

12 mutation controls total, 37 held-out, **12 dispatchable**:

```
F:ml430-nat-coprime-of-lt-minfac-0f79bdba     development  natural-primes
F:ml430-nat-fastfib-eq-cde11774               train        natural-fibonacci
F:ml430-nat-lt-of-testbit-72f64ab8            development  natural-bitwise
F:ml430-nat-lt-xor-cases-c43a1e85             development  natural-bitwise
F:ml430-nat-multichoose-one-b210386a          development  natural-binomial
F:ml430-nat-multichoose-one-right-7755072d    development  natural-binomial
F:ml430-nat-multichoose-zero-right-6ef827c8   development  natural-binomial
F:ml430-nat-testbit-eq-inth-ffa07392          development  natural-bitwise
F:ml430-nat-testbit-land-dfef7ca4             development  natural-bitwise
F:ml430-nat-testbit-ldiff-16f94162            development  natural-bitwise
F:ml430-nat-testbit-lor-7644e067              development  natural-bitwise
F:ml430-nat-zero-of-testbit-eq-false-e244c9a1 development  natural-bitwise
```

**One thing the note does not say, and it sharpens the finding.** The 37 open
held-out rows are *not* spread across the population — they are exactly two
families:

```
natural-logarithm  21
natural-square-root 16
```

Every other held-out family is fully closed. So the blind evaluation population
is not merely off-limits; what remains of it tests exactly two capabilities.
A refill that does not add held-out breadth leaves the evaluation narrow even
if it never spends a row.

## Remaining work in this lane

1. Diagnose the selection mechanism (what would have reported "the dispatchable
   set is structurally empty"; fill the hole if nothing would).
2. A mechanised screen for the four divergence classes, run before
   preregistration.
3. Written proposal for refilling population without disturbing the split.
4. Name the measurement drift (local analogues landed *because* a mirror is
   unclosable) and propose how the ledger should count them.
