# ADR-1546: Draw 19 is refused, and the reason is not two bad commits — the v2 partition design cannot hold the property its gate enforces

Date: 2026-09-02
Status: Accepted
Lane: `nursery-draw-19`

Index-summary: Draw 19 was not authored. Two of the seven partition gates are
red at baseline. `check-development-partition.py` has been red every day
sampled since 2026-08-26 on one unchanged violation, and draw 18 shipped over
it without measuring it. `check-autogenesis-nursery.py` is red on a
declared-dependency component of **305** facts that crosses development (172),
train (126), held-out (5) and longitudinal (2) — bisected to two producer
commits on 2026-09-01 that closed facts whose `depends_on` reach across the
split. The structural finding is that this is the steady state, not a
regression: the v2 draw assigns partitions by Mathlib module and runs **no
dependency-component analysis** — the generator's own published caveat says so
— while the union gate enforces `no-declared-component-may-cross-evaluation-
partitions` against a live ledger that producers keep adding crossing edges to.
The gate has been held green by one hand-maintained exemption re-scoped upward
four times in four days (228 → 230 → 258 → 274) and now 31 facts short of the
component it must cover. Drawing 40 more rows adds 40 more surfaces for the
same breakage and cannot improve the gate.

Index-status: Accepted

## What this lane was sent to do

Author nursery refill draw 19. `check-dispatchable-frontier.py` reports **2**
dispatchable against a floor of 10; lane `shape-census` measured the ready
frontier at 217 dependency-ready open facts, 186 held-out, 31 visible, 4
genuinely targetable. The queue a producer can work on is empty and a
preregistered draw is the mechanism that refills it. Draw 18 (ADR-1465) is the
template; draw 17 (ADR-1450) is the refusal precedent.

The brief's standing rule: re-measure every partition gate first, and if any is
red, stop — a draw on top of a red partition gate is a contamination, not a
refill. Two are red. This ADR records the refusal and what the measurement
found underneath it.

## Re-measurement, before anything

Each gate run bare, exit status captured before any `grep`. Worktree at
`1ba3ae705`, after `git merge main` (main at `b4b2f96c6`).

| gate | exit | headline |
| --- | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | `entries=500 development=180 held-out=190 train=130 env=2838 attested=409 screen_drift=31` |
| `check-autogenesis-nursery.py` | **1** | 3 cross-population violation types; component of 305 crosses 4 partitions |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=206 files_scanned=1111 settled=0 references=0 PASS` |
| `check-holdout-adjacency.py` | 0 | 20 held-out families, 0 refused, 4 undisclosed (advisory) |
| `check-development-partition.py` | **1** | 1 violation; `open train=6 development=16 held-out=16` |
| `check-dispatchable-frontier.py` | **1** | G7, **2** dispatchable against a floor of 10 |
| `check-draw7-frozen-families.py` | 0 | `frozen=50 moved=0 new=0 control=FIRES PASS` |
| `validate-facts.py` | 0 | 2576 facts, 0 errors |

`check-dispatchable-frontier.py`'s red is the condition the draw exists to
repair, not a contamination — draw 18 recorded the same exit 1 at the same
count of 2 at its own start. The other two reds are the finding.

## The two reds, dated

Both gates are registered (`scripts/check.sh:688`, `justfile:235`). **Neither
runs in `hooks/pre-push`**, which runs `check-settled-fact-statements.py` and
`check-holdout-closed-evaluation.py` but not these; so a producer can close a
fact that fuses two partitions and push it without the gate ever executing.

Gate state sampled one commit per day, each run over a `git archive` snapshot
of that tree:

| commit | date | `check-autogenesis-nursery` | `check-development-partition` |
| --- | --- | ---: | ---: |
| `d3ab093c1` | 08-26 | 0 | **1** |
| `f8a54fd42` | 08-27 | 0 | **1** |
| `9342701f2` | 08-28 | 0 | **1** |
| `203712454` | 08-29 | **1** | **1** |
| `63f1179a4` | 08-30 | 0 | **1** |
| `69a6d09c6` | 08-31 | **1** | **1** |
| `524df45e2` | 09-01 | **1** | **1** |
| `1ba3ae705` | 09-02 | **1** | **1** |

`check-development-partition.py` is red at every point sampled, on the same
single violation throughout: the operation
`authoritative-mathlib-nat-modeq-remainder-family-v1` references three
development facts and no train fact — a producer authored against the
evaluation set. This was already recorded as a known pre-existing red in
`docs/plan/status/198-modeq-producer.md` on 2026-08-28 ("was already failing on
`main` … it still is"). **Draw 18 did not measure this gate at all**; its
baseline table omits it. So the precedent that draw 18 established — "author
once the partition gates are green" — was never actually satisfied.

The nursery gate's green days before 08-29 mean nothing: `nursery-v2-extension.json`
was created on 2026-08-29 (`94b3e61ee`) and the component-split gate was
extended to cover it on 2026-08-30 (`5f2664b5a`). It went red essentially as
soon as it began looking.

## What broke it this time

Bisected within `0c13e80f8..HEAD` (draw 18's own commit was **green**, so draw
18 did not cause this). Two independent producer commits, both 2026-09-01:

- `42847d62c` `chore(l0): pin the fib corollary statement` —
  `F:ml430-int-fib-two-mul-add-one-eq-natfib-natabs-61a8342b` is **development**
  (v2) and its `depends_on` names `F:ml430-int-fib-of-odd-66560495`, which is
  **train** (v1). One edge, development → train.
- `ac1d00fd7` `feat(nat): six log/clog ml430 mirrors` —
  `F:ml430-nat-clog-anti-left-d72bd6cd` is **train** (v2) and its `depends_on`
  names `F:ml430-nat-clog-antitone-left-44a87771`, which is **development**
  (v1). One edge, train → development.

The gate's query is exactly `depends_on` over `artifacts/facts/`
(`components()`, line 170), and the policy literal it enforces is
`split_component_authority: declared-dependency-weak-component` /
`split_leakage: no-declared-component-may-cross-evaluation-partitions`. Both
edges are real and present in the ledger. The gate is right about its subject;
this is not a checker manufacturing a finding.

The resulting weak components, counted from the gate's own report:

| component | distinct facts | partitions |
| --- | ---: | --- |
| `f5f596f2791f…` | **305** | development 172, train 126, **held-out 5**, longitudinal 2 |
| `25a802dff13a…` | 10 | development 8, train 2 |
| `57d5ed927fd6…` | 4 | development 3, train 1 |

319 distinct drawn facts now sit in a component that crosses an evaluation
boundary. Five held-out facts share a declared-dependency component with 172
development facts.

## The structural finding

This is not two careless commits. **The v2 draw cannot establish the property
the gate enforces, and says so itself.** From
`scripts/gen-autogenesis-nursery-refill.py`, in the text it publishes into the
manifest:

> v1 freezes partitions against declared dependency weak components
> (`policy.split_component_authority`); here `source_group` is the Mathlib
> defining module and no dependency-component analysis was run, so a held-out
> row can share a component with a dispatchable one and nothing in this
> manifest sees it. […] Any `depends_on` on these facts is ledger-owned and
> accrued after the fact (ADR-0615), never the preregistered component analysis
> above.

So: draws assign partitions by module with no component analysis; new rows are
emitted with `"depends_on": []`; producers then accrue the real edges by
proving things; and the union gate checks components over that live ledger.
Every closed v2 fact is a fresh opportunity to fuse two partitions, and nothing
at draw time can prevent it.

The mechanism that has kept the gate green is a single hand-maintained
`cross_population_component_split_exemptions` entry, re-scoped upward every
time it goes stale:

| commit | date | largest exemption | gate |
| --- | --- | ---: | ---: |
| `203712454` | 08-29 | (none) | red |
| `e72bb1b28` | 08-30 | 228 | — |
| `63f1179a4` | 08-30 | 230 | green |
| `69a6d09c6` | 08-31 | 258 | red |
| `ced416a4c` | 09-01 | 258 | — |
| `bd99ed696` | 09-01 | 274 | green |
| `0c13e80f8` | 09-01 | 274 | green (draw 18 authored here) |
| `1ba3ae705` | 09-02 | 274 | red |

228 → 230 → 258 → 274 in four days — the 08-30 commit message is literally
"re-scope the cross-population exemption **again**". The live component is now
**305**, so the exemption is 31 short, which is precisely the gate's second
violation type ("matches no live crossing component … the component it was
reviewed against has changed shape").

A gate whose largest subject is waved through by an exemption that is enlarged
to fit whenever it fails is a checker that cannot fail on that subject. That is
the failure mode CLAUDE.md names: at N lanes the ledger IS the product, and a
checker that cannot fail is worse than no checker, because it manufactures
unfalsifiable partition-integrity claims at full speed.

## Decision

**Draw 19 is refused.** No candidate family was screened, no partition was
assigned, no row was written, and `nursery-v2-extension.json` is unchanged at
500 entries. Refusing is the cheap half; the expensive half is that the obvious
alternative — wait for someone to re-scope the exemption to 305, then draw — is
**also refused**. That does not repair anything. It times the draw to the lull
between two producer commits and publishes 40 more rows into a design that has
demonstrated, four times in four days, that it cannot hold them.

What a repair would have to choose between, stated so the next lane does not
have to re-derive it:

1. **Make the draw do component analysis.** Assign v2 partitions against the
   declared-dependency graph the way v1 does, instead of by Mathlib module.
   This is the honest fix and it is expensive: it needs a dependency graph over
   statements that are not yet proved, which is the thing ADR-0615 says is not
   available at draw time.
2. **Gate the producer, not the draw.** Refuse at close time any `depends_on`
   edge that crosses an evaluation partition, and run that check in
   `hooks/pre-push` where producers will actually hit it. This turns a
   post-hoc, exemption-managed property into an enforced one, at the cost of
   telling producers which partition a fact is in — which is itself a
   disclosure that needs its own review.
3. **Retire the property.** Concede that v2 partitions are module-scoped, not
   component-scoped, drop `split_leakage` from the v2 policy, and stop
   reporting v2 held-out results as if they carried v1's isolation guarantee.
   Cheapest, and the most honest of the three if 1 and 2 are both unaffordable
   — but it downgrades what a held-out score means and must be said out loud
   rather than absorbed.

This lane does not choose between them; each is a larger decision than a refill
draw and at least one changes what a held-out score is worth.

## Consequences

- The dispatchable frontier stays at **2** against a floor of 10. The producer
  queue remains empty. That cost is real and is the price of not contaminating
  the evaluation population further.
- `check-development-partition.py` remains red on
  `authoritative-mathlib-nat-modeq-remainder-family-v1`, untouched by this lane
  and now dated: at least eight days, 2026-08-26 to 2026-09-02.
- Draw 18's authorization is retrospectively weaker than its status doc reads.
  It measured six gates and found five green; the sixth
  (`check-development-partition.py`) was red and unmeasured, and the one it did
  record green (`check-autogenesis-nursery.py`) was green only because an
  exemption had been enlarged to 274 eleven commits earlier. Draw 18's rows are
  not withdrawn — nothing here shows them individually unsound — but "the
  partition gates were green" should not be quoted from it as evidence.
- No held-out row's outcome was named, nothing was dispatched, and no existing
  row moved partition. `check-draw7-frozen-families.py` reports `moved=0 new=0`
  with its control firing, before and after.

## Method notes

- Gate state per commit was measured by extracting each tree with `git archive`
  into a scratch directory and running the checker there, never by reading a
  commit message or a status doc. The two commit-message-derived claims in this
  ADR (the exemption re-scopes) are each confirmed against the JSON at that
  commit.
- The per-partition counts come from parsing the gate's own report, not from
  re-deriving its component algorithm, so they cannot disagree with it.
- Both breaking edges were read out of `artifacts/facts/` directly and are
  quoted above, so the claim "the gate is right about its subject" is checkable
  without re-running it.
- Not run: anything requiring a workspace build. No `.rs` file was touched, no
  `cargo` invocation was made, and `shape_search` was never rebuilt — candidate
  blindness screening was not reached, because the refusal happens before
  candidate selection.
