# Lane: nursery-draw-author — author the nursery refill draw that clears the frontier floor

<!-- plan-section: lane-status -->

Status: COMPLETE (2026-09-01). **The draw is NOT authorable, and that is the
result.** R5 requires two NEW held-out families and only one can be formed from
the whole remaining supply — one two-row module gates every candidate. Recorded
in [ADR-1420](../../research/09-decisions/adr-1420-the-refill-draw-is-not-authorable-one-two-row-module-blocks-it.md).
No draw was authored, nothing in `FAMILY_MODULES`/`FAMILY_ROUTES` was touched,
and no already-drawn row moved.

## Step 1 — re-measure

The worktree started **13 commits behind local `main`** and its copy of
`gen-autogenesis-nursery-refill.py` still carried the four-element
`HELD_OUT_CONSTRUCTIONS = {Nat.log, Nat.clog, Nat.log2, Nat.sqrt}`. Measured on
that stale tree the proposer reported 3 ready families with `Mathlib.Data.Nat.Log`
at **37** — wrong in the direction that overstates headroom. Merged `main`
(a6c531eab) and re-ran.

```
python3 scripts/propose-nursery-refill.py --remeasure          exit 0
  pinned inventory   9729 records, 4285e551680abf3b…
  screened out       7673   (5173 not-statable-here, 1699 hygienic-or-generated,
                             662 already-drawn, 125 divergence-registry,
                             14 held-out-construction)
  survivors          2056 across 85 module(s)
  READY FAMILIES     2
        17  Mathlib.Data.Nat.Log
        15  Mathlib.NumberTheory.FactorisationProperties
```

`artifacts/autogenesis/refill-headroom-v1.json` regenerates with a **zero diff**
against what `main` committed, so nothing moved under the concurrent
divergence-registry lane and both counts match ADR-1405 exactly.

```
python3 scripts/check-dispatchable-frontier.py                 exit 1
  FAIL: G7 queue-below-floor: 3 dispatchable mirror(s), floor 10
  open ml430 216 -> 211;  held-out 185;  mutation controls 12;
  divergence-blocked 11;  DISPATCHABLE 3
```

(The frontier read **8** on the stale tree; the five `F:ml430-int-prime-dvd-mul-*`
mirrors that merge closed are the difference, not anything this lane did.)

## Step 2 — the two-family draw is refused before yield is ever considered

`dispatchable_yield(2) = 10·(2 − ⌈2/3⌉) = 10` is arithmetically right and is not
the binding constraint. Run against the real `select()` + `guard()`:

```
  [0] natural-logarithm-base            Mathlib.Data.Nat.Log                          -> held-out
  [1] natural-factorisation-properties  Mathlib.NumberTheory.FactorisationProperties  -> development
select OK: 480 entries
GUARD_REFUSED: R5 the refill adds 1 held-out families; the blind population is
               already down to two capabilities
```

`_with_cycle` restarts the cycle at index 0 per draw, so held-out families =
`⌈n/3⌉`, and **R5's two needs n ≥ 4**.

## Step 3 — R9 / R11 / R12 per family, with the real machinery

Screened as if held-out, using `screen_family()` and `is_closed_evaluation()`:

| candidate | R9 | R12 | R11 |
| --- | --- | --- | --- |
| `Mathlib.Data.Nat.Log` | 0/10 | clean | **refused** topic `Log` (natural-logarithm) + vocab 10/10 |
| `Mathlib.NumberTheory.FactorisationProperties` | 0/10 | **2** (`abundant_twelve`, `deficient_one`) | vocab 4/10; disclosure only |
| bit representation (3 modules) | **3/10** | clean | **refused** topic `Bitwise` + vocab 9/10 |
| binomial bounds (4 modules) | **1/10** | clean | **refused** topic `Choose`,`Dvd` + vocab 10/10 |
| prime-power decomposition (4 modules) | 0/10 | clean | **refused** vocab 9/10 |
| prime distribution (5 modules) | 0/10 | clean | **refused** topic `Prime` + vocab 10/10 |

## Step 4 — the exhaustive result

Topic collision is per-MODULE, vocabulary is per-ROW, so a held-out family must
be built entirely from topic-clean unowned modules: **18** of them, **57**
survivors, **19** vocabulary-clean. Over all `2^18` subsets, drawing the first
ten by name as `select()` does:

```
modules 18, viable subsets 36868
modules present in EVERY viable subset: ['Mathlib.Tactic.IntervalCases']
EXACT answer -- two disjoint viable held-out families: NO
```

Exact, not sampled — a subset-sum DP over the 18-bit module universe, so every
one of the 36,868 viable subsets is checked against every other. A first run
capped its stored module-sets at 40 per drawn-ten and would have reported the
same "NO" from a sample; that reading was discarded and re-derived.

`Mathlib.Tactic.IntervalCases` holds two rows, both vocabulary-clean and both
sorting near the front of the pool, so they enter every drawn ten and supply two
of the five clean rows a family needs. A module belongs to one family, so **at
most one viable held-out family can exist**. R5 needs two.

## The unblock

Declare a construction that opens a module which is **topic-clean against every
development/train family** and has **at least five of its alphabetically-first
ten rows about constants no development/train family publishes**. Definition
only — declaring theorems about it spends the family through R9 (ADR-0653).

## Gate results (all run in this worktree, foreground)

| command | exit | note |
| --- | --- | --- |
| `propose-nursery-refill.py --remeasure` | 0 | 17 / 15, snapshot zero-diff |
| `check-dispatchable-frontier.py` | 1 | G7, 3 dispatchable, floor 10 |
| `gen-autogenesis-nursery-refill.py --check` | 0 | entries=460, env=2711, dev 170 / held-out 170 / train 120 |
| `check-autogenesis-holdout-isolation.py` | 0 | `held_out=186 settled=0 PASS` |
| `check-holdout-adjacency.py` | 0 | 18 held-out families, 0 refused |
| `validate-facts.py` | 0 | |
| `gen-adr-index.py` | 0 | `rows=739` |
| `check-autogenesis-nursery.py` | **1** | pre-existing red on `main`; cross-population `depends_on` component spanning development/train/longitudinal. Same failure recorded by `unblock-draw-16` on 2026-08-31. |

## Landed changes

| commit | what |
| --- | --- |
| `bdf6291d0` | early commit: the re-measurement, before any screening |
| (this) | ADR-1420 + regenerated ADR index + this status |
