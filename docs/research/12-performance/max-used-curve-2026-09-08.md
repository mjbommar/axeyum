# The `max_used` curve: does a smaller tier database pay for itself?

Lane `binary-watch-arena`, 2026-09-08, on s7. Subject:
`ClauseDbPolicy::max_used` — how many reduce rounds a tier1 clause survives
after its last use, and therefore how large the tier clause database grows.

## Why this was measured

The three-tier clause database gets **~14% fewer conflicts** than the
pre-2026-09 database and pays **~25% more watch visits** for them, and that
watch cost is why it is not the shipped default. The
[binary-watch change](../02-ecosystems/pipeline-survey-2026-09/cdcl-core-engine.md)
(findings R9/R10) was expected to unblock it and does not: it removes arena work
*inside* a watch visit, while the tier policy's cost is the *number* of visits.
That left `max_used` as the cheapest remaining lever — it is the one knob that
directly sets database size, it was already A/B-able, and its value of 31 was
copied from Kissat and has never been measured here.

## Method, and what is and is not reportable

Arms are `SearchPolicies` objects inside **one binary** (`cargo run --release -p
axeyum-cnf --example clause_db_policy_ab`), so no build, compiler or mtime
variance enters the comparison. `legacy` — the pre-2026-09 clause database — is
the denominator throughout.

**Wall clock is not reported, and the control is the reason.** Five identical
repetitions of one arm on the measurement host, with nothing changed between
them:

| instance | min s | max s | max/min |
| --- | ---: | ---: | ---: |
| bitblast_20x14 | 0.220 | 0.560 | **+154.5%** |
| vdw-2-3-10 | 1.566 | 2.249 | +43.6% |
| rado-r4-a3-b1 | 0.989 | 1.714 | +73.3% |
| rado-r4-a2-b2 | 0.981 | 1.673 | +70.5% |

s5/s6/s7 were each running an unrelated `smtcomp_cli` sweep (2 to 6 processes
at 100% CPU), so no host on the fleet had a usable clock that evening. In the
same five repetitions the **deterministic counters were bit-identical** —
conflicts, decisions, propagations, watch visits, clause visits and ticks, all
six, on all four instances. So conflicts, watch visits and ticks are the result
here and wall clock is not quoted at all. A reader who wants a duration should
re-run the control first.

Rows are restricted to instances that decided under **every** arm and ran at
least one reduce round under some arm: an undecided run's conflict count is a
budget rather than a measurement, and an instance that never reduces has no
clause-database policy to measure. That leaves **7 of 14**.

## The curve, to verdict

Geometric mean over the 7 kept instances, each arm against `legacy`:

| `max_used` | conflicts | watch visits | ticks |
| --- | ---: | ---: | ---: |
| legacy (no tiers) | 1.000 | 1.000 | 1.000 |
| **31** (current) | 0.860 | 1.254 | 1.088 |
| 16 | 0.857 | 1.246 | 1.083 |
| 8 | **0.851** | 1.210 | 1.070 |
| 4 | 0.859 | 1.182 | 1.055 |
| 2 | 0.880 | 1.151 | 1.046 |
| **1** | 0.879 | **1.003** | **0.954** |

Two things in that table are worth more than the endpoints.

**The conflict column is non-monotone, and 31 is not its optimum.** It improves
from 31 down to 8 (0.860 → 0.851) and then degrades (0.880 at 2). So the
reference's value is not even the best point for the metric the tier policy
exists to improve; a shorter lease is *better* on conflicts down to about 8. The
middle of the curve is the informative part and it is why the whole curve is
here rather than the best point.

**The jump at `max_used = 1` is structural, not a longer slide down the same
slope.** `classify` floors the tier2 grace at `max(max_used - 1, 1)`, and tier1
keeps on `used_before > 0`, i.e. `>= 1`. At `max_used = 1` those two predicates
are the same, so tier1 and tier2 **collapse into one rule**: keep if
`glue <= tier2` and the clause was resolved since the previous round. So
`max_used = 1` is not "the shortest lease on the three-tier policy" — it is a
different, two-tier policy that the knob happens to reach. Anyone reading the
1.003 as the limit of a trend is reading it wrong.

## The same knob at fixed work

To verdict, a policy that needs fewer conflicts can reach parity on *total*
watch visits while still being more expensive per conflict. Under a fixed
conflict budget every arm analyses the same number of conflicts, so watch visits
per conflict is per-conflict cost with the search length held constant:

| instance | legacy | `max_used`=31 | =8 | =1 |
| --- | ---: | ---: | ---: | ---: |
| vdw-2-3-11 (150k) | 1396 | 3283 (2.35x) | 2850 (2.04x) | 1664 (1.19x) |
| rado-r4-a2-b2 (150k) | 1124 | 2198 (1.96x) | 2062 (1.83x) | 1410 (1.25x) |
| bitblast 32-bit (120k) | 2977 | 3564 (1.20x) | **3406 (1.14x)** | 3670 (1.23x) |

**Per-conflict cost never reaches parity.** The total-work parity at
`max_used = 1` in the previous table comes from the search being *shorter*, not
from propagation being cheaper. That is still a real win — time to verdict is
total work — but it is a different claim, and the two tables are the two halves
of it.

And on the one genuinely hard bit-blasted instance the curve **runs the other
way**: 8 is the best point and 1 is worse than the 31 it was supposed to
improve on.

## Answer

**Yes, `max_used` moves the 1.254, and at `max_used = 1` the tier database is
net-positive on total deterministic work** — 12% fewer conflicts, watch visits
at parity, and 4.6% *fewer* ticks than the pre-2026-09 database. That is the
first setting at which the tier policy is not paying for its conflict win.

**It is not enough to flip the default on**, for three reasons that are in the
data above rather than in caution:

1. The corpus is 7 decided instances and 5 of them are combinatorial.
2. On the hard bit-blasted instance — the family that matches our real workload
   — the curve is non-monotone in the opposite direction and `max_used = 1` is
   worse than the current 31.
3. `max_used = 1` is a policy change (tier1 and tier2 collapse), not a
   parameter setting, so it deserves to be argued as one.

The two candidates worth a wider corpus are **1** (best total work, combinatorial)
and **8** (best conflicts everywhere, best per-conflict cost on bit-blasted). A
run over the public QF_BV slice would settle it; that is a bench-corpus job, not
a unit-test one.

## A hazard in the fixture this lane added

`clause_db_policy_ab`'s `bitblast:<width>x<count>` generator has two properties
that will mislead anyone who reaches for it, both found here:

* **`count` buys size, not difficulty.** The conjuncts are independent, and
  within a conflict budget the search never leaves the first one's cone.
  `bitblast:32x6` and `bitblast:32x12` differ by **372 watch visits out of 357
  million** — the same search, on formulas of very different size. Raising
  `count` to get a harder instance does not work.
* **`width < 32` is not a factoring instance at all.** The generator masks its
  primes to `width` bits, which destroys their primality, so the "semiprime"
  has small factors. Measured: 20, 24 and 28 bits are all `sat` inside 1600
  conflicts, while 32 bits exhausts every budget tried.

So the only hard member of the family is `width = 32`, and this lane's earlier
binary-share figures of 13.7% / 14.1% (on `24x8` and `20x14`) were taken on
*easy satisfiable* instances; the figure on the hard one is **6.8%**. The fix is
to chain the factor pairs so the constraint graph is connected — not done here,
because it would invalidate the fixtures this sweep ran on.

## What I did not verify

- Anything about wall clock. The control says the host could not measure it.
- Whether `max_used` interacts with `DeleteFraction` or `ReduceSchedule`. Only
  `max_used` was swept; the harness has `tiered-frac<N>` and
  `tiered-tuned<used>-<frac>` arms for the joint sweep.
- Any instance outside this repository's committed CNF plus the generated
  factoring fixtures.
