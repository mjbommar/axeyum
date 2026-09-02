# Lane: nursery-draw-19 — draw 19 REFUSED, the partition gate is held green by a growing exemption

<!-- plan-section: lane-status -->

**Done (`DONE`, nursery-draw-19, 2026-09-02).** Draw 19 was **not authored**.
Two of the seven partition gates are red at baseline, and the standing rule is
that a draw on top of a red partition gate is a contamination, not a refill.
`artifacts/autogenesis/nursery-v2-extension.json` is unchanged at 500 entries;
no candidate was screened, no partition assigned, no row written, no held-out
outcome named, nothing dispatched. A refused draw is a valid result
(precedent: draw 17, ADR-1450).

**Re-measurement at start** (`1ba3ae705`, after `git merge main`; main at
`b4b2f96c6`). Each gate run bare, exit captured before any `grep`:

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=500 development=180 held-out=190 train=130 env=2838 screen_drift=31` |
| `check-autogenesis-nursery.py` | **1** | 3 violation types; a component of **305** crosses 4 partitions |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=206 files_scanned=1111 settled=0 references=0 PASS` |
| `check-holdout-adjacency.py` | 0 | 20 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-development-partition.py` | **1** | 1 violation; `open train=6 development=16 held-out=16` |
| `check-dispatchable-frontier.py` | **1** | G7, **2** dispatchable against a floor of 10 |
| `check-draw7-frozen-families.py` | 0 | `frozen=50 moved=0 new=0 control=FIRES PASS` |
| `validate-facts.py` | 0 | 2576 facts, 0 errors |

There is no "after" table: nothing was authored, so every number above is also
the number at the end. `check-dispatchable-frontier.py` stays at **2**.

**The frontier's red is the condition the draw repairs, not a contamination** —
draw 18 recorded the same exit 1 at the same count of 2 at its own start. The
other two reds are the finding.

**`check-development-partition.py` has been red every day sampled since
2026-08-26** (eight days, one commit per day, each measured by running the
checker over a `git archive` snapshot of that tree), on one unchanged
violation: `authoritative-mathlib-nat-modeq-remainder-family-v1` references
three development facts and no train fact. Already recorded as a known
pre-existing red in `198-modeq-producer.md` on 08-28. **Draw 18 never measured
this gate** — its baseline table omits it — so the precedent "author once the
gates are green" was never actually satisfied.

**`check-autogenesis-nursery.py` was green at draw 18's own commit and went red
the same day**, bisected to two producer commits: `42847d62c` (a **development**
fact `depends_on` a **train** fact) and `ac1d00fd7` (a **train** fact
`depends_on` a **development** fact). Both edges read directly out of
`artifacts/facts/`; the gate's query is exactly `depends_on`, so it is right
about its subject. Resulting components: **305** facts (development 172, train
126, **held-out 5**, longitudinal 2), plus 10 and 4. **319 distinct drawn facts
now sit in a component that crosses an evaluation boundary.**

**The structural finding, and the reason "wait for green, then draw" is also
refused.** The v2 draw assigns partitions by Mathlib module and runs **no
dependency-component analysis** — the generator publishes that caveat itself,
and emits every new row with `"depends_on": []` — while the union gate enforces
`no-declared-component-may-cross-evaluation-partitions` against a live ledger
that producers keep adding crossing edges to. Neither gate runs in
`hooks/pre-push`, so a producer fuses two partitions and pushes without the
gate ever executing. What has kept it green is one hand-maintained exemption
re-scoped upward four times in four days — **228 → 230 → 258 → 274**, each
figure read from the JSON at that commit, not from the commit message — now 31
short of the 305 it must cover. A gate whose largest subject is waved through
by an exemption enlarged to fit whenever it fails cannot fail on that subject.
Drawing 40 more rows adds 40 more surfaces for the same breakage.

**Not run:** anything needing a workspace build. No `.rs` file touched, no
`cargo` invocation, `shape_search` never rebuilt — candidate blindness
screening was not reached, because the refusal happens before candidate
selection. `just check` / `check.sh` not run.

Full reasoning, the three repair options and their costs:
[ADR-1546](../../research/09-decisions/adr-1546-draw-19-is-refused-and-the-partition-gate-is-held-green-by-a-growing-exemption.md).

<!-- plan-section: landed-changes -->

| 2026-09-02 | nursery-draw-19 | draw 19 refused; `check-autogenesis-nursery.py` red on a 305-fact component crossing 4 partitions, bisected to two producer commits |
| 2026-09-02 | nursery-draw-19 | `check-development-partition.py` measured red on all 8 days sampled since 08-26; draw 18 never measured it |
| 2026-09-02 | nursery-draw-19 | the v2 partition exemption measured growing 228 → 230 → 258 → 274 in four days, now 31 short of the live component |
