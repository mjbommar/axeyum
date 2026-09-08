# How CaDiCaL and Kissat Afford Inprocessing

**Lane:** `research-inproc-sched` · **Date:** 2026-09-08 · **Status:** research note, read-only

Reference sources read for this note (fresh shallow clones under the gitignored
`references/`, so line numbers are pinned to these commits):

| source | version | commit |
|---|---|---|
| `references/kissat` | 4.0.4 | `8af8e56f174b778aef3aa45af9f739b2a5f492c2` (2025-10-16) |
| `references/cadical` | 3.0.1 (main) | `c60730422e758ef1cebe7aeddf2dda31c996bf04` (2026-07-19) |

Every claim is tagged **[C]** (read from the C/C++ source, with `file:line`),
**[P]** (from a paper or solver description), or **[I]** (my inference). An
inference is never presented as a fact. Where I could not establish something, I
say "did not verify".

---

## 0. The question, and the one-sentence answer

We have vivification, BVE and subsumption in
`crates/axeyum-cnf/{vivify,bve,simplify,inprocess}.rs`. They work, they are
proof-carrying, and they are **off by default** (`InprocessOptions::default()`
is `Self::OFF`, `inprocess.rs:113-155`) because on a 24 s budget they cost more
than they save; the benefit was measured to appear near 5x the competition limit.

The algorithms are not the difference. The difference is that **we run them once,
on the whole formula, against an absolute budget; Kissat runs them many times, on
a shrinking marked subset, against a budget that is a fixed fraction of the
search work already spent.**

Four structural facts, each of which independently removes a large constant from
the cost, and none of which we currently have:

1. **[C] Learned clauses do not schedule any inprocessing work.** In Kissat,
   both `kissat_mark_added_literals` and `kissat_mark_removed_literals` — the
   only ways a variable enters the BVE or subsumption schedule — are called
   *only on the irredundant branch* (`src/clause.c:97-99`, `src/clause.c:153-154`).
   The search learns millions of redundant clauses and **not one of them touches
   a variable flag.** Between two inprocessing rounds the irredundant formula
   changes only through units, vivification strengthening, and BVE's own
   resolvents. So round *n+1* re-examines a tiny fraction of what round 1 did.
2. **[C] The budget is a per-mille slice of the search effort spent since the
   last round** (`src/kimits.h:135-170`), measured in a deterministic,
   machine-independent unit. Inprocessing therefore cannot outgrow search:
   spending is proportional to what search already spent, not to formula size and
   not to wall clock.
3. **[C] CaDiCaL refuses to run an expensive pass until the accrued budget
   exceeds a multiple of the formula size**, and says why in a source comment
   (`references/cadical/src/limit.hpp:151-157`, rationale at
   `src/probe.cpp:902-907`): *"vivify, sweep and factor can also have a big
   initial overhead in setting up the datastructures … since inprocessing is done
   frequently, this overhead is too expensive to pay. So instead, we accumulate
   the budget of 'ticks' and delay the technique until it passes a certain
   threshhold, which depends on the the cost of initialization."* **This is our
   measured problem, diagnosed and solved in the reference solver's own words.**
   The answer is not a bigger or smaller budget; it is not running the round
   until you can afford the `O(|F|)` setup *plus* useful work. See §2A.2.
4. **[C] The strength bound starts at zero and ratchets up only after a level is
   completed** (`src/eliminate.c:339-372`; CaDiCaL `src/elim.cpp:963-996`).
   Kissat's first BVE round is strictly non-growing (`bound = 0`, exactly our
   `growth: 0`); it reaches `eliminatebound = 16` only after five completed
   sweeps. We pay the expensive setting or the cheap setting once and forever;
   they pay cheap-then-expensive, and the expensive levels only run on formulas
   where the cheap ones already converged.

The rest of this note gives the data structures, the formulas and the constants,
separated into *essential*, *tuning constant*, and *do not copy*. §1-§2 and
§3-§5 are read from Kissat; §2A is CaDiCaL, which shares the design and differs
in three instructive ways.

---

## 1. The cost model: what a "tick" is

### 1.1 The definition

**[C]** A tick is **one expected cache line touched during propagation**, not a
propagation and not a microsecond.

`references/kissat/src/utilities.h:19-34`:

```c
#define ASSUMED_LD_CACHE_LINE_BYTES 7u

static inline word kissat_cache_lines (word n, size_t size) {
  if (!n) return 0;
  assert (size == 4);
  const unsigned shift = ASSUMED_LD_CACHE_LINE_BYTES - 2u;   // 7 - 2 = 5
  const word mask = (((word) 1) << shift) - 1;               // 31
  const word masked = n + mask;
  return masked >> shift;                                    // ceil(n / 32)
}
```

`sizeof(watch) == 4`, so `2^(7-2) = 32` watches fit an assumed **128-byte** cache
line and `kissat_cache_lines(n, 4) == ceil(n/32)`. **[I]** 128 bytes is 2x a
typical x86 line; the constant is an *assumption baked into the model*, not a
measurement of the host — which is exactly what makes the count portable.

### 1.2 How ticks are counted

**[C]** All charging happens in one inlined function,
`references/kissat/src/proplit.h:34-187`, which is `#include`d four times with
different macros to produce the search / probing / dense / beyond-conflict
propagators. The charges (`src/proplit.h:64,92,98,148,174`):

| event | ticks | line |
|---|---|---|
| entering a literal's watch list of `n` watches | `1 + ceil(n/32)` | `proplit.h:64` |
| assigning from a binary clause | `+1` | `proplit.h:92` |
| dereferencing a large clause in the arena | `+1` | `proplit.h:98` |
| moving a watch to a new list (watch replacement) | `+1` | `proplit.h:148` |
| assigning with a large-clause reason | `+1` | `proplit.h:174` |

and `solver->ticks += ticks;` once at `proplit.h:178`.

**[I]** Read the table as a cost model, not as bookkeeping: the base term is the
*sequential* scan of one contiguous watch list (cheap per element, so amortised
over 32), and every `+1` is a **pointer chase to somewhere else in memory** — the
arena, another watch list, the assignment array. That is the right shape: the
count tracks the thing that actually dominates SAT runtime.

One charge lives outside propagation: `src/analyze.c:158` charges
`INC (search_ticks)` per large reason clause walked during conflict analysis
(gated by the `minimizeticks` option, default 1, `src/options.h:83`).

### 1.3 Where ticks accumulate

**[C]** `solver->ticks` is a scratch accumulator zeroed before each propagation
run and drained into named statistics counters afterwards:

- `src/propsearch.c:21-32` → `ticks`, `search_ticks`, and `stable_ticks` or
  `focused_ticks`;
- `src/proprobe.c:31-32` → `probing_ticks` and `ticks` (plus `vivify_ticks` /
  `backbone_ticks` under `METRICS`);
- `src/propinitially.c:22` → `ticks` only.

**`search_ticks` is the numeraire.** It is the only counter that measures search,
and every inprocessing budget is denominated as a fraction of it.

### 1.4 Determinism — why this matters for us

**[C]** Nothing in the tick computation reads a clock, an allocator address, or
the host cache geometry: `ASSUMED_LD_CACHE_LINE_BYTES` is a compile-time
constant and all inputs are watch-list lengths and control flow. **[I]** A fixed
formula plus fixed options therefore produces a fixed tick count and hence a
fixed schedule, on any machine — which is exactly the property our determinism
promise needs and which a wall-clock deadline cannot give. Our current
`inprocess.rs` `deadline: Option<Instant>` is explicitly documented as "the one
input that can change the result" (`inprocess.rs:64-67`). A tick budget removes
that caveat entirely.

### 1.5 The budget unit is per-pass, and it is not always ticks

**[C]** The budget macro is generic over which counter it limits. Call sites:

| pass | counter budgeted | file:line |
|---|---|---|
| vivification | `probing_ticks` | `src/vivify.c:1422` |
| SAT sweeping | `kitten_ticks` | `src/sweep.c:143` |
| transitive reduction | `transitive_ticks` | `src/transitive.c:320` |
| backbone | `backbone_ticks` | `src/backbone.c:344` |
| bounded variable addition (factor) | `factor_ticks` | `src/factor.c:1108` |
| **BVE** | **`eliminate_resolutions`** | `src/eliminate.c:428` |
| **forward subsumption** | **`forward_steps`** | `src/forward.c:539` |
| local search (walk) | `walk_steps` | `src/walk.c:413` |

**[I]** This is the design lesson, not an accident: a pass is budgeted in *its
own natural unit of work*. Propagation-driven passes pay in ticks; BVE pays in
**resolution attempts** (`INC (eliminate_resolutions)` at `src/resolve.c:157`,
charged per candidate resolvent *including tautologies*); subsumption pays in
occurrence-list steps. All are deterministic integers. Forcing everything into a
single unit would be worse — the abstraction is "a counter you can compare
against a limit", not "ticks".

---

## 2. The budget formula

**[C]** One macro, `SET_EFFORT_LIMIT`, `references/kissat/src/kimits.h:135-170`:

```c
#define SET_EFFORT_LIMIT(LIMIT, NAME, START) \
  uint64_t LIMIT; \
  do { \
    const uint64_t OLD_LIMIT = solver->statistics.START; \
    const uint64_t TICKS = solver->statistics.search_ticks; \
    const uint64_t LAST = solver->probing ? solver->last.ticks.probe \
                                          : solver->last.ticks.eliminate; \
    uint64_t REFERENCE = TICKS - LAST; \
    const uint64_t MINEFFORT = 1e6 * GET_OPTION (mineffort); \
    if (REFERENCE < MINEFFORT) REFERENCE = MINEFFORT; \
    const double EFFORT = (double) GET_OPTION (NAME##effort) * 1e-3; \
    const uint64_t DELTA = EFFORT * REFERENCE; \
    LIMIT = OLD_LIMIT + DELTA; \
  } while (0)
```

In words:

```
reference = search_ticks_now - search_ticks_at_end_of_last_round     // work search did since
reference = max(reference, mineffort * 1_000_000)                    // floor so early rounds can run
delta     = (<pass>effort / 1000) * reference                        // per-mille slice
limit     = <pass's own counter now> + delta                         // absolute stop value
```

Then the pass loops `while (its_counter <= limit)`.

### 2.1 The per-mille table

**[C]** `references/kissat/src/options.h` (default, min, max):

| option | default (per mille) | line |
|---|---|---|
| `mineffort` | **10** (i.e. 10 million, absolute floor) | `options.h:80` |
| `eliminateeffort` | **100** = 10 % | `options.h:44` |
| `vivifyeffort` | **100** = 10 % | `options.h:161` |
| `forwardeffort` | **100** = 10 % | `options.h:72` |
| `sweepeffort` | **100** = 10 % | `options.h:143` |
| `factoreffort` | **50** = 5 % | `options.h:57` |
| `walkeffort` | **50** = 5 % | `options.h:168` |
| `backboneeffort` | **20** = 2 % | `options.h:12` |
| `transitiveeffort` | **20** = 2 % | `options.h:156` |
| `substituteeffort` | **10** = 1 % | `options.h:135` |

**[I]** The sum over the passes reachable in one `probe()` round
(vivify 100 + sweep 100 + backbone 20 x2 + transitive 20 + factor 50 +
substitute 10 x2) is ~330 per mille, i.e. probing is allowed roughly a third of
the search ticks spent since the last probe; BVE separately gets 10 %. So
**inprocessing's steady-state share of total work is bounded at design time by a
number you can read off a table**, not discovered empirically per instance.

### 2.2 Four properties of this formula worth stealing

**[I]** all four:

1. **Self-limiting.** Spend is a fraction of *search* spend. A formula the search
   blows through gets little inprocessing; one it grinds on gets more, and the
   ratio never inverts.
2. **Self-warming.** `REFERENCE` uses ticks *since the last round of this
   family*, not lifetime ticks, so a round that produced nothing does not earn a
   larger budget next time merely by the clock advancing.
3. **A floor, not a ceiling, on the first round.** `mineffort = 10` million ticks
   guarantees the very first round has something to spend before any search has
   happened. **[I]** This is the piece that makes "preprocess before search" a
   *special case of the same code path* rather than separate machinery.
4. **The limit is absolute in the pass's own counter**, so a pass never needs to
   subtract or reset anything — it just compares a monotone counter to a number.

### 2.3 Budget splitting with carry-over across sub-passes

**[C]** `references/kissat/src/vivify.c:1405-1458`. One `SET_EFFORT_LIMIT` yields
`total`; four weighted sub-passes consume it, and **`limit` is cumulative, so an
under-spending sub-pass hands its remainder to the next**:

```c
double irr_budget   = DELAYING (vivifyirr) ? 0 : GET_OPTION (vivifyirr);   // 3
double tier1_budget = GET_OPTION (vivifytier1);                           // 3
double tier2_budget = GET_OPTION (vivifytier2);                           // 3
double tier3_buget  = GET_OPTION (vivifytier3);                           // 1
double sum = irr_budget + tier1_budget + tier2_budget + tier3_buget;       // 10
...
SET_EFFORT_LIMIT (limit, vivify, probing_ticks);
const uint64_t total = limit - solver->statistics.probing_ticks;
limit = solver->statistics.probing_ticks;
if (tier1_budget) { limit += (total * tier1_budget) / sum; vivify_tier1 (&vivifier, limit); }
if (tier2_budget) { limit += (total * tier2_budget) / sum; vivify_tier2 (&vivifier, limit); }
if (tier3_buget)  { limit += (total * tier3_buget)  / sum; vivify_tier3 (&vivifier, limit); }
if (irr_budget)   { limit += (total * irr_budget)   / sum; vivify_irredundant (&vivifier, limit); }
```

Defaults `vivifytier1/2/3 = 3/3/1` and `vivifyirr = 3` (`options.h:104,106-108`)
→ a **30 / 30 / 10 / 30** split over tier1, tier2, tier3, irredundant.

**[I]** Carry-over is essential, not cosmetic: without it, a tier with few
candidates wastes its slice, and the pass systematically under-spends its
allowance while still paying full setup cost.

### 2.4 The failure-backoff counter

**[C]** `references/kissat/src/kimits.c:155-194` plus the `delays` struct at
`src/kimits.h:68-78`. A `delay` is two `unsigned`s, `{count, current}`:

- `kissat_delaying`: if `count > 0`, decrement and **skip this round**;
- `kissat_bump_delay`: `current += 1; count = current;` (linear growth);
- `kissat_reduce_delay`: `current /= 2; count = current;` (halving).

Applied to `bumpreasons`, `congruence`, `sweep`, `vivifyirr`. The vivification
use is the clearest, `src/vivify.c:1454-1457`:

```c
if (kissat_average (vivifier.vivified, vivifier.tried) < 0.01)
  BUMP_DELAY (vivifyirr);
else
  REDUCE_DELAY (vivifyirr);
```

**A success rate below 1 % causes the sub-pass to be skipped for an increasing
number of rounds; any better rate halves the skip count.** Additive-increase /
multiplicative-decrease on *skips*.

**[I]** This is the cheapest possible answer to "the pass does not pay off on
this instance", and it is per-instance and adaptive rather than a global on/off.
For us it is more valuable than for them, because our measurement says the passes
*do not pay off inside 24 s on our workload* — a 1 %-success backoff would have
turned themselves off on the instances where they lose, instead of us turning
them off everywhere.

---

## 2A. CaDiCaL's variant — and the one idea that directly answers our question

CaDiCaL's tree (`references/cadical` @ `c607304`, `VERSION` says 3.0.1 but the
tree carries `sweep.cpp`, `congruence.cpp`, `factor.cpp`, `elimfast.cpp` and a
ticks model, so treat the label as stale) has **two coexisting cost models**.

### 2A.1 The same tick idea

**[C]** `references/cadical/src/internal.hpp:739-742`:

```cpp
int64_t cache_lines (size_t bytes) { return (bytes + 127) / 128; }
int64_t cache_lines (size_t n, size_t bytes) { return cache_lines (n * bytes); }
```

Same 128-byte assumed line as Kissat, charged at
`src/propagate.cpp:244` (`ticks += 1 + cache_lines (ws.size (), sizeof *i);`),
`+1` per watch replacement and per unit found (`propagate.cpp:384, 397`),
drained at `propagate.cpp:468` into `stats.ticks.search[stable]` — **indexed by
stabilization mode**, and `analyze.cpp:370` charges one per conflict.

### 2A.2 The accumulate-and-delay gate — the headline finding

**[C]** `references/cadical/src/limit.hpp:136-164`, verbatim:

```cpp
#define SET_EFFORT_LIMIT(LIMIT, NAME, THRESHHOLD) \
  int64_t LIMIT; \
  do { \
    const int64_t OLD_LIMIT = stats.ticks.NAME; \
    const int64_t TICKS = stats.ticks.search[0] + stats.ticks.search[1]; \
    const int64_t LAST = last.NAME.ticks; \
    int64_t REFERENCE = TICKS - LAST; \
    if (!REFERENCE || !stats.conflicts) { \
      VERBOSE (2, ...); \
      REFERENCE = opts.preprocessinit; \
    } \
    const double EFFORT = (double) opts.NAME##effort * 1e-3; \
    const int64_t DELTA = EFFORT * REFERENCE; \
    const int64_t THRESH = opts.NAME##thresh * clauses.size (); \
    if (THRESHHOLD && DELTA < THRESH) { \
      VERBOSE (2, "delaying %s with ticklimit %" PRId64 \
               " and threshhold %" PRId64, #NAME, DELTA, THRESH); \
      return false; \
    } \
    last.NAME.ticks = TICKS; \
    const int64_t NEW_LIMIT = OLD_LIMIT + DELTA; \
    LIMIT = NEW_LIMIT; \
    ... \
  } while (0)
```

Same shape as Kissat's, with **one decisive difference**. Kissat clamps the
reference from below with a constant floor (`mineffort`). CaDiCaL instead
**refuses to run the pass at all until the accrued budget exceeds a multiple of
the formula size** — `THRESH = <pass>thresh × clauses.size()` — and, crucially,
**on the delay path `last.NAME.ticks` is not written**. So the reference window
keeps growing and `DELTA` keeps growing until it clears the bar.

**The developers state the rationale explicitly.** `references/cadical/src/probe.cpp:902-907`
**[C]**, verbatim:

> *"Additionally 'vivify', 'sweep' and 'factor' can also have a big initial
> overhead in setting up the datastructures. This has to be accounted for with
> the 'ticks', however, since inprocessing is done frequently, this overhead is
> too expensive to pay. So instead, we accumulate the budget of 'ticks' and delay
> the technique until it passes a certain threshhold, which depends on the the
> cost of initialization."*

and, four lines earlier (`probe.cpp:887-892`):

> *"We want to be able to run inprocessing frequently, without it dominating
> runtimes."*

**[I] This is our measured problem, named and solved in the reference solver's
own comments.** Our finding was "running the passes costs more time than they
save inside 24 s". CaDiCaL's diagnosis is that the *fixed setup cost* — building
occurrence lists, which is `O(|F|)` and cannot be amortised or made incremental
— is what makes a small round uneconomic. The fix is not a smaller budget and not
a bigger one: it is **not running the round until you can afford the setup plus
useful work**, with the affordability test scaled to formula size.

Two properties fall out that a plain budget does not have:
- A pass with a large setup cost runs **rarely and thoroughly** rather than often
  and pointlessly. The threshold multiple *is* the encoded setup cost.
- The mechanism is self-tuning across instance sizes: `THRESH` is proportional to
  `|clauses|`, so a big formula demands a proportionally bigger accrued budget.

**[C]** Thresholds and efforts, `references/cadical/src/options.hpp`:

| pass | `<pass>effort` (per mille) | `<pass>thresh` (multiple of clause count) | gated? | line |
|---|---|---|---|---|
| `sweep` | 100 (10 %) | 5 | `!opts.sweepcomplete` | `options.hpp:230,236` |
| `vivify` | **50** (5 %) | **20** | yes | `options.hpp:259,267` |
| `factor` | 50 (5 %) | 7 | after first call | `options.hpp:123,126` |
| `backbone` | 20 (2 %) | 5 | **no** (threshold arg is `false`) | `options.hpp:29,32` |
| `ternary` | 8 (0.8 %) | 6 | yes | `options.hpp:241,245` |
| `probe` | 8 (0.8 %) | **0** | yes, but `THRESH = 0` so never fires | `options.hpp:165,167` |
| `preprocessinit` | 2e6 (bootstrap reference) | — | — | `options.hpp:162` |

**[I]** Vivification carries the highest threshold (20× clause count) and one of
the lower efforts (5 %) — i.e. exactly the pass we found most expensive is the
one CaDiCaL delays hardest. `backbonethresh` is dead code (the macro is invoked
with `THRESHHOLD = false`), and `probethresh = 0` makes probe's gate vacuous.

**Unspent budget is forfeited at the limit level:** `OLD_LIMIT` is
`stats.ticks.<pass>`, the *actual* cumulative spend, not the previous limit
(`limit.hpp:139`) **[C]**. Only the *delay* path accumulates. Contrast Kissat,
where budget carries over between sub-passes of one round (§2.3) but not between
rounds.

### 2A.3 The legacy propagations model, still live

**[C]** `references/cadical/src/elim.cpp:778-791`:

```cpp
if (opts.elimlimited) {
    int64_t delta = stats.propagations.search;
    delta *= 1e-3 * opts.elimeffort;              // elimeffort = 1e3
    if (delta < opts.elimmineff) delta = opts.elimmineff;   // 1e7
    if (delta > opts.elimmaxeff) delta = opts.elimmaxeff;   // 2e9
    delta = max (delta, (int64_t) 2l * active ());
    resolution_limit = stats.elimres + delta;
} else resolution_limit = LONG_MAX;
```

`subsume.cpp:350-362` is the same shape with `subsumeeffort/mineff/maxeff` and
`check_limit = stats.subchecks + delta`. The `mineff`/`maxeff` clamp pattern the
task brief expected is here, on the *older* passes (elim, subsume, transred,
condition, cover, walk); the newer ones use §2A.2 instead.

**[I]** Two things to notice. First, the reference is **absolute lifetime
`propagations.search`**, not a delta since the last round — so this budget grows
monotonically over a run whether or not the pass is earning it, which is exactly
the weakness §2.2's property 2 avoids. Second, the units are not commensurate:
`delta` is derived from *propagations* and spent on *resolutions* (`elimres`) or
*subsumption checks* (`subchecks`). **[I]** It works as a dimensionless allowance,
but it is not a cost model — the tick model is, and it is visibly the direction of
travel. **Port the tick model, not this one.**

### 2A.4 Schedule: two entry points, not seven

**[C]** `references/cadical/src/internal.cpp:280-346`, `cdcl_loop_with_inprocessing`:

```cpp
} else if (restarting ())    restart ();
else if (rephasing ())       rephase ();
else if (reducing ())        reduce ();
else if (inprobing ())       inprobe ();
else if (ineliminating ())   elim ();
else if (compacting ())      compact ();
else if (conditioning ())    condition ();
else                         res = decide ();
```

Only `inprobe()` and `elim()` are inprocessing entry points; `subsume`, `vivify`,
`ternary`, `sweep`, `probe`, `transred`, `factor` are **sub-passes with an effort
share but no interval of their own** — there is no `opts.subsumeint` or
`opts.vivifyint`. **[I]** That is a cleaner factoring than "every pass has its
own schedule", and it is the one to copy: *one* schedule decision, *many* budget
shares.

Growth laws **[C]**:

- `elim`, `src/elim.cpp:1165-1166`:
  `delta = scale (opts.elimint * (stats.elimphases + 1))` with `elimint = 2e3`,
  and `scale` (`src/limit.cpp:9-16`) multiplying by
  `log2(irredundant/active)` when that ratio exceeds 2.
  **[I]** Gaps 2000·s, 4000·s, 6000·s … so cumulative conflicts grow as Θ(n²) and
  elim phases ≈ √conflicts.
- `inprobe`, `src/probe.cpp:981-983`:
  `delta = 25 * opts.inprobeint * log10 (stats.inprobingphases + 9)` with
  `inprobeint = 100`, i.e. ≈ 2500·log10(phases+9) — 2384 at phase 0, ~4250 at
  phase 100.

**[C]** The two "worth it" gates, which match Kissat's design closely:

```cpp
bool Internal::ineliminating () {                    // src/elim.cpp:60-82
  if (!opts.elim) return false;
  if (!preprocessing && !opts.inprocessing) return false;
  if (lim.elim >= stats.conflicts) return false;
  if (last.elim.fixed  < stats.all.fixed)  return true;   // new units
  if (last.elim.marked < stats.mark.elim)  return true;   // new marked vars
  return false;
}

bool Internal::inprobing () {                        // src/probe.cpp:16-26
  ...
  if (stats.inprobingphases && last.inprobe.reductions == stats.reductions)
    return false;                                    // at most one per reduce
  return lim.inprobe <= stats.conflicts;
}
```

**[C]** `last.elim.marked` is advanced **only when the round completed**
(`elim.cpp:908-911`: `if (!completed) last.elim.marked = marked_before;`).

**[C] Stabilization does not gate inprocessing.** Neither predicate reads
`stable`. The coupling is indirect: `stats.ticks.search[]` is indexed by mode and
mode switching is itself ticks-driven (`src/restart.cpp:18-84`, with the interval
growing **quadratically** in `stabphases` and the base interval *measured* from
the first unstable phase rather than configured). `SET_EFFORT_LIMIT` sums
`search[0] + search[1]`, so inprocessing budgets pool across both modes
(`limit.hpp:140`). **[I]** Confirms the Kissat reading in §3.5: keep the two
policies separate.

### 2A.5 Incrementality: same idea, different bookkeeping

**[C]** `references/cadical/src/flags.hpp:21-25` — per-variable dirty bits
(`elim`, `subsume`, `ternary`, `sweep`, `blockable`, `factor:2`, `block:2`),
initialised **set** so the first round is unrestricted, with global counters
maintained by the setters (`internal.hpp:1084-1141`):

```cpp
void mark_subsume (int lit) { Flags &f = flags (lit); if (f.subsume) return;
                              stats.mark.subsume++; f.subsume = true; }
```

**[C]** `src/clause.cpp:59-66` — and note the redundancy split, matching Kissat:

```cpp
inline void Internal::mark_added (int lit, int size, bool redundant) {
  mark_subsume (lit);
  if (size == 3) mark_ternary (lit);
  if (!redundant) mark_block (lit);
  if ((!redundant || size == 2)) mark_factor (lit);
}
```

**[I]** Here `mark_subsume` is called for redundant clauses too — so CaDiCaL's
subsumption *does* see learned clauses, unlike Kissat's (§4.2). It compensates
with the `subsume < 2` candidate filter and `likely_to_be_kept_clause`.
Both designs converge on "do not let the redundant DB drive expensive work",
by different routes.

**[C]** Per-clause bits, `src/clause.hpp:41-58`: `conditioned`, `covered`,
`transred`, `subsume`, `swept`, `instantiated`, `vivified`, `vivify`. The
`vivify` leftover marker works as in Kissat (`vivify.cpp:1322-1327`,
`vivify.cpp:1629-1632`); `transred` is a full-cycle round-robin that clears every
flag and restarts when all are marked (`transred.cpp:44-69`).

**[C]** Occurrence lists are **allocated and freed every round** —
`init_occs`/`reset_occs`/`init_noccs`/`reset_noccs` in `src/occs.cpp:9-50`, with
`erase_vector` releasing the memory. Watches and occurrences are mutually
exclusive (`internal.hpp:466-467`). Nothing is cached across rounds. **[I]** This
`O(|F|)` rebuild is precisely the setup cost §2A.2 exists to amortise, and
confirms that trying to keep occurrence lists live through search is the wrong
answer.

**[C]** `elim_schedule` is a binary heap (`src/elim.hpp:16`,
`typedef heap<elim_more> ElimSchedule`) keyed by
`compute_elim_score` (`elim.cpp:21-35`):

```cpp
double pos = noccs (lit), neg = noccs (-lit);
if (!pos) return -neg;
if (!neg) return -pos;
sum  = opts.elimsum  * (pos + neg);      // elimsum  = 1
prod = opts.elimprod * (pos * neg);      // elimprod = 1
return prod + sum;
```

ordered **larger first**, tie-broken by index for determinism (`elim.cpp:39-47`).
**[I]** Note this is `prod + sum`, where Kissat uses `prod − sum` (§4.3), and the
sort direction differs; the two solvers do not agree on the sign of the linear
term. Treat the *shape* (a product term dominating, an activity/size tiebreak) as
the finding and the exact expression as tuning.

**[C]** Rescheduling is asymmetric (`elim.cpp:104-119` vs `88-103`): a **removed**
literal re-adds its variable to the heap if absent; an **added** literal only
updates a variable already in the heap. **[I]** Removing occurrences can only make
a variable more eliminable, so it deserves a fresh look; adding cannot.

### 2A.6 CaDiCaL's per-pass bounds

**[C]** All from the tree above.

| bound | default | meaning | site |
|---|---|---|---|
| `elimocclim` | 100 | reject if the *larger* side exceeds this (pure literals bypass) | `elim.cpp:696-700` |
| `elimclslim` | 100 | reject on the first oversized resolvent | `elim.cpp:510-516` |
| `elimboundmin`/`max` | 0 / 16 | ladder 0→1→2→4→8→16 | `elim.cpp:963-996` |
| `elimrounds` | 2 | rounds per phase | `elim.cpp:1067-1103` |
| `elimint` | 2000 | base conflict interval | `elim.cpp:1165` |
| `subsumeclslim` | 100 | candidate length cap | `subsume.cpp:386` |
| `subsumeocclim` | 100 | do not connect on a literal above this | `subsume.cpp:525` |
| `subsumebinlim` | 10000 | binary path occurrence cap | `subsume.cpp:549` |
| `vivifyschedmax` | **5000** | **hard cap on candidates per tier per round** | `vivify.cpp:1331` |
| `vivifytier1/2/3eff` | 4 / 2 / 1 | tier budget weights | `options.hpp:269-273` |
| `vivifyirredeff` | 3 | irredundant weight → split **40/20/10/30** | `options.hpp` |
| `vivifyonce` | **0** | once-only filtering **off by default** | `options.hpp:264` |
| `vivifyretry` | 0 | do not retry a successfully vivified clause | `options.hpp:265` |
| `vivifycalctier` | 0 | tier boundaries hardcoded to glue 2 / 6 | `vivify.cpp:1717-1726` |
| `inprobeint` | 100 | probing interval base | `probe.cpp:981` |

**[C]** `increase_elimination_bound` (`elim.cpp:963-996`) re-marks **every active
variable** when it raises the bound — same deliberate discard of the incremental
saving as Kissat (§4.5), bounded to five occurrences.

**[C]** Two extras worth stealing outright:

- **The setup cost is charged and shared.** `vivify_initialize` accumulates
  `init_ticks`, adds them to `stats.ticks.vivify`, and computes
  `shared_effort = init_ticks / 4.0` which is subtracted from each of the four
  tier limits (`vivify.cpp:1792-1795`). A tier that cannot clear its share of the
  setup cost is skipped with a log line (`vivify.cpp:1804-1810`). **[I]** This is
  the honest accounting: the round's fixed cost is not free, so it is billed to
  the sub-passes that caused it.
- **The same delay/backoff loop as Kissat.** `vivify.cpp:1864-1874`: below a 1 %
  strengthening rate on irredundant clauses, `bump_delay()`; otherwise
  `reduce_delay()` (`Delay` at `limit.hpp:55-86`).

**[C]** Clauses are processed **smallest first** in subsumption
(`rsort` by `smaller_clause_size_rank`, `subsume.cpp:425`) so any subsuming clause
is already indexed when a larger candidate is checked.

### 2A.7 Determinism caveat CaDiCaL introduces and Kissat does not

**[I]** (originating from a systematic grep by the CaDiCaL sub-lane; I confirmed
the arithmetic sites but did not exhaustively re-grep):
no wall clock enters any budget in either solver — `seconds()`, `process_time()`,
`time()` appear only in termination callbacks and reporting. But CaDiCaL's
schedules call **libm**: `log` in `scale()` (`limit.cpp:9-16`), `log10` in
`inprobe` (`probe.cpp:981`), `sqrt`/`log` in `reduce` (`reduce.cpp:233-254`).
libm `log`/`log10` are **not bit-identical across implementations**, so a
schedule *boundary* could differ by a conflict across libcs. Kissat has the same
exposure (`kissat_logn` is `log10`, `src/kimits.c:13-18`).

**[I] For us this is a real constraint, not a footnote.** Determinism is a public
API promise. If we adopt a `log10`-shaped growth law we must either use a
fixed-point/integer approximation, or pin our own implementation, or restrict the
law to integer arithmetic (`Sqrt` via integer isqrt, `NLogN` via a table on
`ilog2`). Recommend an integer-only `Growth` enum from the start.

### 2A.8 A suspected defect — do not copy

**[I]**, flagged by the CaDiCaL sub-lane, derived algebraically from **[C]** code
and **not verified by execution** (this was a read-only task; neither of us built
CaDiCaL). `references/cadical/src/ternary.cpp:394-395`:

```cpp
// approximation of ternary ticks.
// TODO: count with ternary.ticks directly.
int64_t steps_limit = stats.ticks.ternary - limit;
stats.ticks.ternary = limit;
```

`limit` comes from `SET_EFFORT_LIMIT (limit, ternary, true)` at `ternary.cpp:373`,
i.e. `limit == stats.ticks.ternary + DELTA` with `stats.ticks.ternary` unchanged
in between — so `steps_limit == −DELTA`, and the round loop opens with
`if (steps_limit < 0) break;` (`ternary.cpp:416-417`). If the reading is right,
hyper ternary resolution never runs in this build while still being charged its
budget. The operands look reversed. **Do not copy this line**, and do not treat
this tree's ternary results as a baseline without checking.

---

## 3. The schedule

### 3.1 The search loop is a strict priority chain

**[C]** `references/kissat/src/search.c:194-224`:

```c
while (!res) {
  clause *conflict = kissat_search_propagate (solver);
  if (conflict)                              res = kissat_analyze (solver, conflict);
  else if (solver->iterating)                iterate (solver);
  else if (!solver->unassigned)              res = 10;
  else if (TERMINATED (search_terminated_1)) break;
  else if (kissat_reducing (solver))         res = kissat_reduce (solver);
  else if (kissat_switching_search_mode (solver)) kissat_switch_search_mode (solver);
  else if (kissat_restarting (solver))       kissat_restart (solver);
  else if (kissat_reordering (solver))       kissat_reorder (solver);
  else if (kissat_rephasing (solver))        kissat_rephase (solver);
  else if (kissat_probing (solver))          res = kissat_probe (solver);
  else if (kissat_eliminating (solver))      res = kissat_eliminate (solver);
  else if (conflict_limit_hit (solver))      break;
  else if (decision_limit_hit (solver))      break;
  else                                       kissat_decide (solver);
}
```

**[C]** Every trigger is checked **only when the trail is fully propagated and no
conflict is pending** — inprocessing happens at a quiescent point, at decision
level 0 after `kissat_backtrack_propagate_and_flush_trail`
(`src/probe.c:27`, `src/eliminate.c:580`).

**[I]** Two design points transfer directly: (a) the triggers are *predicates
over counters*, so they are pure and cheap to evaluate every loop iteration;
(b) the chain is an explicit total order, so "which pass runs first when two are
due" is decided once, in one readable place, rather than emerging from
interleaved conditionals.

### 3.2 The conflict-interval growth law

**[C]** `references/kissat/src/kimits.h:112-131`:

```c
#define UPDATE_CONFLICT_LIMIT(NAME, COUNT, SCALE_COUNT_FUNCTION, SCALE_DELTA) \
    uint64_t DELTA = GET_OPTION (NAME##int); \
    const double SCALING = SCALE_COUNT_FUNCTION (statistics->COUNT); \
    DELTA *= SCALING; \
    const uint64_t SCALED = !(SCALE_DELTA) ? DELTA \
                          : kissat_scale_delta (solver, #NAME, DELTA); \
    limits->NAME.conflicts = CONFLICTS + SCALED;
```

with (`src/kimits.h:104-110`, `src/kimits.c:13-37`), where `logn(c) = log10(c+9)`:

```
LOGN(n) = log10(n+9)      LINEAR(n) = n
NLOGN(n) = n·log10(n+9)   NLOG2N(n) = n·log10(n+9)²   NLOG3N(n) = n·log10(n+9)³
```

The registered laws (**[C]**, one call site each):

| pass | base interval | growth in *n* = times run | formula-scaled? | file:line |
|---|---|---|---|---|
| `reduce` | `reduceint` = 1000 | `SQRT` | no | `src/reduce.c:193` |
| `rephase` | `rephaseint` = 1000 | `NLOG3N` | no | `src/rephase.c:119` |
| `reorder` | `reorderint` = 10000 | `LINEAR` | no | `src/reorder.c:214` |
| `randec` | `randecint` = 500 | `LOGN` | no | `src/decide.c:82` |
| **`probe`** | `probeint` = **100** | **`NLOGN`** | **yes** | `src/probe.c:85` |
| **`eliminate`** | `eliminateint` = **500** | **`NLOG2N`** | **yes** | `src/eliminate.c:600` |

**[I]** Note the ordering: BVE has both the larger base (500 vs 100) and the
faster-growing law (`n log² n` vs `n log n`), so probing runs several times per
BVE round and the gap between BVE rounds widens fastest. That matches the cost
asymmetry — BVE has to rebuild full occurrence lists (§4.4), probing does not.

### 3.3 The formula-size scaling factor

**[C]** `references/kissat/src/kimits.c:39-57`, applied to `probe` and
`eliminate` only:

```c
uint64_t kissat_scale_delta (kissat *solver, const char *pretty, uint64_t delta) {
  const uint64_t C = BINIRR_CLAUSES;              // binary + irredundant clauses
  double f = kissat_logn (C + 1) - 5;             // log10(C+10) - 5
  const double ff = f * f;
  const double fff = 4.5 * ff + 25;
  return fff * delta;
}
```

`BINIRR_CLAUSES` is `BINARY_CLAUSES + IRREDUNDANT_CLAUSES`
(`src/statistics.h:338`). The factor is a **parabola in log10(size) with its
minimum of 25 at 10^5 clauses**:

| irredundant+binary clauses | scale factor | first BVE at (conflicts) | first probe at |
|---|---|---|---|
| 10^3 | 42.9 | 21,461 | 4,292 |
| 10^4 | 29.5 | 14,748 | 2,950 |
| **10^5** | **25.0** | **12,500** | **2,500** |
| 10^6 | 29.5 | 14,750 | 2,950 |
| 10^7 | 43.0 | 21,500 | 4,300 |

(computed from the source formula; **[I]** the arithmetic is mine, the formula is
**[C]**.)

Successive intervals at 10^5 clauses (**[I]**, computed from the **[C]** formulas):

| round *n* | BVE gap (conflicts) | probe gap |
|---|---|---|
| 1 | 12,500 | 2,500 |
| 2 | 27,112 | 5,207 |
| 3 | 43,674 | 8,094 |
| 4 | 62,043 | 11,139 |
| 8 | 151,400 | 24,609 |

**[I]** Both very small and very large formulas are *delayed*: small ones because
search will likely finish first, large ones because a round is expensive. The
sweet spot at 10^5 is where inprocessing has the best expected return. This is a
per-instance policy expressed as a closed-form function of one measurable
quantity, which is far easier to port than a table of hand-tuned thresholds.

### 3.4 The change-driven gate on BVE

**[C]** `references/kissat/src/eliminate.c:21-39` — the conflict interval is
**necessary but not sufficient**:

```c
bool kissat_eliminating (kissat *solver) {
  if (!solver->enabled.eliminate) return false;
  if (!statistics->clauses_irredundant) return false;
  const uint64_t conflicts = statistics->conflicts;
  if (solver->last.conflicts.reduce == conflicts) return false;
  if (limits->eliminate.conflicts > conflicts) return false;
  if (limits->eliminate.variables.eliminate < statistics->variables_eliminate) return true;
  if (limits->eliminate.variables.subsume  < statistics->variables_subsume)  return true;
  return false;
}
```

`variables_eliminate` and `variables_subsume` are **monotone counters of how many
variables have ever been marked**; `limits->eliminate.variables.*` is the
watermark saved at the last *completed* round (`src/eliminate.c:352-354`).
**If no new variable has been marked since the last completed sweep, BVE does not
run at all — even though the conflict interval has elapsed.**

**[I]** This is the schedule-level half of the incrementality story, and it is
almost free to implement: two `u64` counters and two watermarks.

### 3.5 Mode switching, and its (non-)relation to inprocessing

**[C]** `references/kissat/src/mode.c:69-101, 186-199`. Kissat alternates focused
and stable search with an **equal-work** rule:

- focused→stable is triggered on a **conflict** limit:
  `limits->mode.conflicts = conflicts + modeint · NLOGPOWN(count, 4)`
  where `count = (switched + 1) / 2` and `modeint = 1000` (`options.h:26`),
  i.e. `1000 · count · log10(count+9)^4`;
- stable→focused is triggered on a **tick** limit:
  `limits->mode.ticks = search_ticks + delta_ticks`, where `delta_ticks` is
  *exactly the ticks the just-finished focused period consumed*
  (`src/mode.c:78`, `src/mode.c:115`).

**[C]** `kissat_switching_search_mode` selects which limit applies by the parity
of `limits->mode.count` (`src/mode.c:195-198`).

**[I]** So: focused mode is measured in conflicts, stable mode is given the same
*tick* budget focused just used. Conflicts are the useful output of focused
search; ticks are the fair way to give stable search an equal share of machine
work. Two different units for two different questions, in the same policy.

**[C] Inprocessing is not tied to mode switching.** `kissat_probing` and
`kissat_eliminating` read only `conflicts` and the marked-variable watermarks;
neither reads `solver->stable`. Mode switching merely sits *above* them in the
priority chain (`search.c:206` before `search.c:214,216`).

**[C]** The one place mode does leak in is *scoring*, not *scheduling*:
`variable_score` uses the VSIDS heap score in stable mode and the VMTF queue
stamp in focused mode (`src/eliminate.c:57-62`), and vivification's tier limits
default to the **focused** tiers regardless of current mode
(`vivifyfocusedtiers = 1`, `options.h:103`; `src/vivify.c:128-134`).

**[I] Recommendation: do not couple our inprocessing schedule to any mode
notion.** It buys nothing here and creates a dependency between two policies that
Kissat deliberately keeps separate.

---

## 4. Incrementality — where the 5x almost certainly goes

This is the section that matters most for us.

### 4.1 One bitfield per variable

**[C]** `references/kissat/src/flags.h:8-19`:

```c
struct flags {
  bool active : 1;      bool backbone0 : 1;   bool backbone1 : 1;
  bool eliminate : 1;   bool eliminated : 1;  unsigned factor : 2;
  bool fixed : 1;       bool subsume : 1;     bool sweep : 1;
  bool transitive : 1;
};
```

Ten bits, one byte-ish per variable, indexed by variable id. `eliminate` = "this
variable may now be eliminable, it was not considered since it last changed";
`subsume` = "a clause containing this literal was added since the last
subsumption round". Cheap to allocate, cheap to clear, cache-dense.

### 4.2 What sets the bits — and what does not

**[C]** `references/kissat/src/inline.h:39-67`:

```c
static inline void kissat_mark_removed_literal (kissat *solver, unsigned lit) {
  flags *flags = FLAGS (IDX (lit));
  if (flags->fixed) return;
  if (!flags->eliminate) { flags->eliminate = true; INC (variables_eliminate); }
}

static inline void kissat_mark_added_literal (kissat *solver, unsigned lit) {
  flags *flags = FLAGS (IDX (lit));
  if (!flags->subsume) { flags->subsume = true; INC (variables_subsume); }
  const unsigned bit = 1u << NEGATED (lit);
  if (!(flags->factor & bit)) { flags->factor |= bit; INC (literals_factor); }
}
```

Note the counters incremented on the **rising edge only** — that is what makes
§3.4's watermark test correct.

**[C] The decisive restriction.** In `references/kissat/src/clause.c`:

```c
  if (redundant) {
    if (solver->first_reducible == INVALID_REF) solver->first_reducible = res;
  } else {
    kissat_mark_added_literals (solver, size, lits);      // clause.c:98
    solver->last_irredundant = res;
  }
```

and

```c
static void mark_clause_as_garbage (kissat *solver, clause *c) {
  if (!c->redundant)
    kissat_mark_removed_literals (solver, c->size, c->lits);   // clause.c:153-154
  ...
}
```

**Learned (redundant) clauses never set a flag.** Neither their creation nor
their deletion during `reduce` schedules any variable for BVE or subsumption.

**[I]** This is, I believe, the single largest cost difference between "run it
once on everything" and "run it every round". The irredundant formula is nearly
static between rounds; the redundant one churns constantly and is excluded. Our
`bve.rs` seeds its queue with **every** variable (`bve.rs:465-467`) on every
call, which is the "run it once on everything" cost — every time.

### 4.3 Consuming the marks: three different disciplines

**[C] BVE (`src/eliminate.c:131-158`).** `schedule_variables` walks all
variables and pushes into a **max-heap** only those with `active && eliminate`.
The priority is `variable_score` (`src/eliminate.c:41-72`):

```
pos = min(|occ(x)|,  occlim)         neg = min(|occ(¬x)|, occlim)
score     = pos·neg − (pos + neg)
relevancy = stable ? VSIDS_heap_score(x) : VMTF_queue_stamp(x)
result    = relevancy + score − occlim²
```

**[I]** `pos·neg − (pos+neg)` is a direct estimate of *resolvents produced minus
clauses removed* — i.e. the heap pops the variables most likely to shrink the
formula first, so a budget cut-off keeps the best work. The `− occlim²` term
forces the whole occurrence component negative so that `relevancy` (search
activity) breaks ties among structurally similar variables. Our `bve.rs` uses a
plain FIFO `VecDeque` (`bve.rs:196`, `bve.rs:472`), which under a budget keeps an
arbitrary prefix instead of the best one.

`eliminate_variable` clears the bit *before* attempting
(`src/eliminate.c:396-397`), so a failed attempt is not retried until something
touches the variable again.

**[C] Forward subsumption (`src/forward.c:125-165`).** Two-sided use of the same
bit, and the thresholds differ:

- **candidate** (a clause that might *be* subsumed): kept only if
  **at least two** of its literals are marked `subsume`
  (`src/forward.c:145-161`: `if (subsume < 2) continue;`), it is irredundant,
  and `c->size <= subsumeclslim`;
- **index entry** (a clause that might *do* the subsuming): connected only if
  **every** literal is marked (`src/forward.c:485-502`:
  `if (!flags->subsume) { subsume = false; break; }`), and only on its
  **single minimum-occurrence literal**, and only if that literal's occurrence
  count is `<= subsumeocclim` (`src/forward.c:504-508`).

**[I]** "At least two marked" is a sound-by-construction filter for the
*strengthening* case (self-subsuming resolution needs one clashing plus one
matching literal); "all marked" for the index side keeps the index tiny. Both
are pure cost reductions with a bounded completeness loss, which is exactly the
trade an inprocessor should make and a preprocessor should not.

All `subsume` bits are cleared at the end of the round
(`src/forward.c:591-592`).

**[C] Vivification (`src/vivify.c`).** A **per-clause** bit, `c->vivify`,
initialised `false` on creation (`src/clause.c:44`). Its lifecycle:

1. `schedule_vivification_candidates` (`src/vivify.c:231-305`) runs the clause
   sweep **twice**, `for (prioritize = 0; prioritize < 2; prioritize++)`, keeping
   clauses with `c->vivify == prioritize`. Pass 1 also accumulates literal
   occurrence counts.
2. If **no** clause was prioritized — i.e. everything has already been tried —
   *all* scheduled clauses get `c->vivify = true` (`src/vivify.c:297-301`),
   restarting the sweep.
3. A clause that is actually tried gets `candidate->vivify = false`
   (`src/vivify.c:1311`).
4. Clauses left in the schedule when the budget runs out **keep** their bit, so
   they are prioritized next round (`src/vivify.c:1322-1343`).

**[I]** That is a **resumable round-robin**: budget exhaustion is not lost work,
it is a bookmark. Combined with the tier split (§5.1) it means each vivification
round examines a *new* slice of the clause database rather than re-doing the
front of it. Our `vivify.rs` re-sweeps all clauses in index order from the start
of every call (`vivify.rs:483-501`), so under a budget it repeatedly vivifies the
same low-index prefix.

Candidate ordering, **[C]** `src/vivify.c:307-350` (`worse_candidate`): already-
prioritized clauses first; then lexicographically by the per-literal occurrence
counts of the clause's sorted literals (**lower count first** — rarer literals
propagate more); then shorter clause first; then by reference for a total,
deterministic order. Sorting is skipped for irredundant clauses when
`IRREDUNDANT_CLAUSES / 10 > REDUNDANT_CLAUSES` (`src/vivify.c:1269`).

There is also a cheap pre-filter, `simplify_vivification_candidate`
(`src/vivify.c` ~line 80-126), applied during scheduling, so clauses already
satisfied or shrinkable by trivial means never enter the queue. Did not read it
line by line.

### 4.4 The occurrence index: reuse the watch arrays

**[C]** `references/kissat/src/dense.c:99-110`:

```c
void kissat_enter_dense_mode (kissat *solver, litpairs *irredundant) {
  if (irredundant) flush_large_watches (solver, irredundant);
  else             kissat_flush_large_watches (solver);
  solver->watching = false;
}
```

Kissat does **not allocate a separate occurrence index.** It flushes the
*large-clause* watches out of `solver->watches` and repopulates the same arrays
with full occurrence lists; binary clauses are already stored as complete
two-sided watch lists so they need no conversion. `kissat_resume_sparse_mode`
reverses it. The `solver->watching` flag tells the shared propagation code which
regime it is in.

**[I]** Two transferable points, one not:
- **Transferable:** the occurrence index is *built and torn down per BVE round*,
  and its cost is charged against a budget that already accounts for it — it is
  not a persistent structure kept in sync on every clause change. Trying to
  maintain full occurrence lists incrementally through search would be much worse.
- **Transferable:** binaries are stored separately from large clauses throughout,
  so the expensive rebuild only touches large clauses.
- **Do not copy:** the specific trick of overloading one array for both roles
  depends on Kissat's watch layout (a 4-byte tagged `watch` word, blocking
  literal inline). Our CNF representation would need its own decision.

### 4.5 The strength ratchet

**[C]** `references/kissat/src/eliminate.c:339-372`:

```c
static void set_next_elimination_bound (kissat *solver, bool complete) {
  const unsigned max_bound = GET_OPTION (eliminatebound);          // 16
  const unsigned current_bound = solver->bounds.eliminate.additional_clauses;
  if (complete) {
    if (current_bound == max_bound) {
      limits->eliminate.variables.eliminate = statistics->variables_eliminate;
      limits->eliminate.variables.subsume  = statistics->variables_subsume;
    } else {
      const unsigned next_bound = !current_bound ? 1 : MIN (2 * current_bound, max_bound);
      solver->bounds.eliminate.additional_clauses = next_bound;
      try_to_eliminate_all_variables_again (solver);
    }
  }
}
```

with `try_to_eliminate_all_variables_again` (`src/eliminate.c:329-337`) setting
`flags->eliminate = true` for **every** variable and resetting the watermark.

So the bound ladder is **0 → 1 → 2 → 4 → 8 → 16** (`eliminatebound` default 16,
range 0..8192, `src/options.h:43`), and each step is taken **only when the
previous bound has been driven to completion** (nothing left in the heap and
nothing eliminated in the last round, `src/eliminate.c:544`). A full re-sweep of
all variables is the *price of raising the bound*, paid at most 5 times.

**[C]** The bound enters the resolvent test at `src/resolve.c:282-297`:

```c
const unsigned occlim = GET_OPTION (eliminateocclim);         // 2000
limit = pos_count + (uint64_t) neg_count;
if (pos_count && limit > occlim) return false;                // too many occurrences
if (pos_count) {
  const uint64_t bound = solver->bounds.eliminate.additional_clauses;
  limit += bound;
}
```

and the check `if (++resolved > limit) { failed = true; break; }`
(`src/resolve.c:194-198`).

**[I]** Our `BveOptions::DEFAULT` sets `growth: 0` permanently (`bve.rs:82`).
That is Kissat's *first* rung and it is the right first rung — but we never climb,
so we permanently forgo the eliminations that need growth 1..16, and we also never
get the *cheapness* benefit, because we pay the full-formula sweep on every call
regardless.

---

## 5. Priority order and per-pass bounds

### 5.1 Order within a probing round

**[C]** `references/kissat/src/probe.c:26-43`:

```c
static void probe (kissat *solver) {
  kissat_backtrack_propagate_and_flush_trail (solver);
  STOP_SEARCH_AND_START_SIMPLIFIER (probe);
  kissat_congruence (solver);              // gate extraction + congruence closure
  kissat_substitute (solver, false);       // equivalent-literal substitution
  kissat_binary_clauses_backbone (solver);
  kissat_vivify (solver);
  kissat_sweep (solver);                   // SAT sweeping via embedded kitten
  kissat_substitute (solver, false);       // again, to consume sweep's equivalences
  kissat_transitive_reduction (solver);
  kissat_binary_clauses_backbone (solver);
  kissat_factor (solver);                  // bounded variable addition
  STOP_SIMPLIFIER_AND_RESUME_SEARCH (probe);
}
```

**[I]** The visible principle: **passes that discover equalities and units run
before passes that consume them**, and `substitute` appears twice because two
different producers (congruence, sweep) feed it. Backbone runs twice for the same
reason. This is a *pipeline with re-entry at the consumer*, not a fixpoint loop
over everything.

Within vivification the order is **tier1 → tier2 → tier3 → irredundant**
(`src/vivify.c:1436-1458`), i.e. **lowest-glue (most reused) learned clauses
first**, irredundant last and skippable by the delay counter. Tier boundaries:
tier1 = `glue <= tier1` (default 2), tier2 = `tier1 < glue <= tier2`
(default 6), tier3 = everything above (`src/vivify.c:239-257`,
`src/options.h:92,94`).

### 5.2 Order within an elimination round

**[C]** `references/kissat/src/eliminate.c:435-453`, inside the round loop, with
`forward` default 1 (`src/options.h:71`):

```c
for (;;) {
  round++;
  if (forward) {
    complete = kissat_forward_subsume_during_elimination (solver);
    kissat_flush_large_connected (solver);
    kissat_connect_irredundant_large_clauses (solver);
    kissat_flush_units_while_connected (solver);
  } else {
    kissat_connect_irredundant_large_clauses (solver);
    complete = true;
  }
  schedule_variables (solver);
  while (!kissat_empty_heap (&solver->schedule)) { ... eliminate_variable ... }
  ...
  if (round == GET_OPTION (eliminaterounds)) break;      // eliminaterounds = 2
  if (statistics->eliminate_resolutions > resolution_limit) break;
}
```

**[C] Subsumption runs before BVE, inside the same round, sharing the same
occurrence lists**, and both are cut off by the same `resolution_limit`.
`eliminaterounds` defaults to **2** (`src/options.h:48`).

**[I]** Subsumption-first is the classic ordering (SatELite): removing subsumed
clauses shrinks the occurrence lists that BVE's `pos·neg` cost is quadratic in,
so it pays for itself. Sharing the occurrence index means the expensive
dense-mode build is amortised over both passes — a second reason not to run them
as separate top-level passes the way our `inprocess_into` currently does.

### 5.3 The bounds table

**[C]** All from `references/kissat/src/options.h` unless noted.

| bound | default | range | meaning | enforced at |
|---|---|---|---|---|
| `eliminateocclim` | **2000** | 0..INT_MAX | reject variable if `\|occ(x)\| + \|occ(¬x)\| > this` | `resolve.c:282-290` |
| `eliminateclslim` | **100** | 1..INT_MAX | reject if any resolvent exceeds this many literals | `resolve.c:106`, `resolve.c:239-243` |
| `eliminatebound` | **16** | 0..8192 | max additive resolvent growth (ladder 0,1,2,4,8,16) | `eliminate.c:340-365` |
| `eliminaterounds` | **2** | 1..10000 | subsume+BVE rounds per elimination call | `eliminate.c:521` |
| `eliminateint` | **500** | 10..INT_MAX | base conflict interval | `eliminate.c:600` |
| `eliminateinit` | **500** | 0..INT_MAX | initial conflict interval | `kimits.c:124` |
| `eliminateeffort` | **100**‰ | 0..2000 | share of search ticks | `eliminate.c:428` |
| `subsumeocclim` | **1000** | 0..INT_MAX | do not index a clause on a literal with more occurrences | `forward.c:504` |
| `subsumeclslim` | **1000** | 1..INT_MAX | do not consider clauses longer than this | `forward.c:127,142` |
| `forwardeffort` | **100**‰ | 0..10^6 | share of search ticks | `forward.c:539` |
| `vivifyeffort` | **100**‰ | 0..1000 | share of search ticks | `vivify.c:1422` |
| `vivifytier1/2/3` | **3 / 3 / 1** | 0..100 | relative sub-budgets | `vivify.c:1406-1408` |
| `vivifyirr` | **3** | 0..100 | relative sub-budget for irredundant clauses | `vivify.c:1405` |
| `vivifysort` | **1** | 0..1 | sort candidates by occurrence rarity | `vivify.c:1268` |
| `tier1` / `tier2` | **2 / 6** | glue thresholds | vivification tiering | `vivify.c:128-134` |
| `mineffort` | **10** (millions) | 0..INT_MAX | absolute floor on the effort reference | `kimits.h:143` |
| `probeint` / `probeinit` | **100 / 100** | | probing conflict interval | `probe.c:85`, `kimits.c:131` |
| `proberounds` | **2** | 1..INT_MAX | | `options.h:99` |
| `substituterounds` | **2** | 1..100 | | `options.h:137` |

**[C]** There is also a deliberately cheap BVE variant, `fastel.c`, for *initial*
preprocessing, with much tighter bounds — `fastelim = 8` resolvents,
`fasteloccs = 100` occurrences, `fastelclslim = 100`, `fastelrounds = 4` — and it
is **off by default** (`fastel, 0`, `src/options.h:62`).

### 5.4 Kissat does no heavy BVE before search

**[C]** `references/kissat/src/preprocess.c:59-74`. The initial preprocessing loop
runs `kissat_probe_initially` and, only if `fastel` is enabled (default 0),
`kissat_fast_variable_elimination`. `preprocessrounds` defaults to **1**
(`src/options.h:94`). **Full BVE is reachable only from the search loop.**

**[I]** This directly contradicts the shape of our `InprocessOptions::preprocess()`
(`inprocess.rs:126-136`), which is a one-shot subsume+BVE before search. Kissat's
first BVE happens after ~12,500 conflicts of search on a 10^5-clause formula
(§3.3) — by which point units have been derived, the trail has been simplified,
and the marked-variable set already tells it where to look. **[I]** That
sequencing is plausibly a real part of why their round is cheap and ours is not,
though I did not measure it.

---

## 5A. The literature — what it justifies, and one hazard it names for us

Fetched and read by a parallel literature lane; I have **not** independently
re-fetched every PDF, so treat these as **[P]** with the source URL given so a
reader can check the quote. Where a paper claim and the source disagree, the
source wins.

### 5A.1 Biere states the tick rationale in his own words

**[P]** Biere, Fazekas, Fleury, Heisinger, *"CaDiCaL, Kissat, Paracooba,
Plingeling and Treengeling entering the SAT Competition 2020"*, Proc. SAT
Competition 2020, Univ. Helsinki Report B-2020-1
([PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFazekasFleuryHeisinger-SAT-Competition-2020-solvers.pdf)):

> *"Our first attempt to limit the time spend in stable mode was to use the
> number of propagations as metric. But this was not precise enough, since
> propagations per second still vary substantially with and without many
> restarts. Instead we now count 'ticks', which approximate the number of cache
> lines accessed during propagations. This refines what Donald Knuth calls 'mems'
> but lifted to cache lines and restricted to only count watcher stack access and
> large clause dereferences, ignoring for instance accessing the value of a
> literal."*

> *"Computing these 'ticks' was useful limit the time spent in other procedures,
> e.g., vivification, in terms of time spent during search (more precisely the
> time spend in propagation)."*

This matches the source reading in §1.2 exactly — including the *omission* of
value-array accesses, which is why `values[other]` reads in `proplit.h` are not
charged.

**[P]** Biere & Fleury, *"Chasing Target Phases"*, PoS'20
([PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFleury-POS20.pdf)),
§5, on why not wall clock:

> *"Kissat determines the time spent in focused and stable mode by estimating the
> number of memory accesses (instead of measuring the time directly in order to
> be deterministic across runs)."*

**[P]** Pollitt, Fleury, Biere, Heule, Sakallah, Chen, Fisseha, *"Revisiting
Clause Vivification"*, PoS'25
([PDF](https://www.cs.cmu.edu/~mheule/publications/PoS25-viv.pdf)), §5, on the
cost of the approach:

> *"Counting ticks is only an approximation and the result of profiling runs and
> inspecting the code, i.e., the programmer adds instructions which increase the
> ticks counter whenever the program reaches a point, where a non-local memory
> access is expected. … Even though less automatic to implement, ticks are more
> precise than mems, i.e., correlate better with actual running time."*

**[I]** Budget honestly for this: the tick counter is *hand-instrumented*, and
its quality depends on someone having profiled the propagator. It is not
derivable mechanically, and a badly placed charge silently mis-prices a pass.
Pair the implementation with a test that asserts tick counts are stable across
runs and a one-off correlation check against measured time.

### 5A.2 The growth laws, stated as policy

**[P]** SC2020 description, same PDF:

> *"For variable elimination ('elim') the scaling function of the base conflict
> interval is n · log²n. For 'probe' it is n · log n. Similarly we scale the base
> conflict interval for 'reduce' by n / log n, while for 'rephase' it remains
> linear. More precisely as logarithm we use log₁₀(n+10). Thus 'reduce' occurs
> most often, followed by 'rephase', then 'probe' and least often 'elim', all in
> the long run, independently of the base conflict interval, and the initial
> conflict interval."*

This confirms §3.2 from the source side and supplies the *intent*: the ordering
of frequencies is the designed invariant, and it is asymptotic — deliberately
independent of the base constants. **[I]** So when we pick our own base
intervals, we should preserve the *ordering* and the *asymptotics*, and treat
the constants as freely tunable.

**[P]** SC2024 description
([PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf))
gives the fullest statement of the vivification budget policy, matching §2.3
verbatim in behaviour:

> *"We vivify redundant tier 1 and tier 2 clauses separately, in this order, as
> before within a per-tier propagation (ticks) budget limited relative to
> propagation (ticks) used in the CDCL search loop. … However, we now add any
> left over budget from vivifying a tier to the budget of vivifying the next tier
> or even the irredundant clauses. Clauses not vivified due to hitting the limit
> are marked and tried in the next probing-inprocessing round for vivification."*

### 5A.3 A scheduling-feedback bug worth internalising before we build

**[P]** SC2023 description
([PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFleuryPollitt-SAT-Competition-2023-solvers.pdf)):

> *"We fixed two heuristic bugs, by avoiding to increase the number of conflicts
> during vivification, as it is used for scheduling various procedures, as well
> as initializing used flags of learned clauses correctly."*

**[I]** The inprocessor was incrementing the very counter that decides when
inprocessing runs. **Design rule: the counter a pass is scheduled by must not be
incremented by that pass.** In our terms: if we schedule on conflicts, our
vivification's internal propagations must not produce counted conflicts; if we
schedule on `search_ticks`, an inprocessing pass must charge `probing_ticks`, not
`search_ticks` (which is what Kissat's separate accumulators in §1.3 achieve).
This is cheap to get right up front and expensive to find later — it presents as
a schedule that mysteriously accelerates on hard instances.

### 5A.4 The policy oscillated — do not treat any one year as settled

**[P]** SC2022 description
([PDF](https://cca.informatik.uni-freiburg.de/papers/BiereFleury-SAT-Competition-2022-solvers.pdf))
lists features *removed* because they "did not substantially improve performance
on the last three competitions benchmarks":

> *"• delaying of inprocessing functions based on formula size
>  • vivification of irredundant clauses
>  • keeping untried elimination, backbone and vivification candidates for next
>    inprocessing round (removed options)
>  • initial focused mode phase limited only by conflicts now (not as before also
>    by ticks)"*

and, in the Bulky configuration, *"fixed clause length and variable occurrences
limits during variable elimination instead of dynamically increasing"*.

**[I]** Every one of those is a mechanism this note recommends. SC2023 brought
irredundant vivification back; SC2024 brought the untried-candidate carry-over
back; the formula-size delay is CaDiCaL's headline mechanism (§2A.2) in the tree
I read. **The mechanisms are individually removable and were each removed and
restored.** Consequence for us: build every one of them behind a flag with a
default we can flip, and measure each independently. Do not ship them as an
inseparable bundle, and do not read the current Kissat defaults as a verdict.

### 5A.5 Candidate selection dominates trigger timing

**[P]** Li, Xiao, Luo, Manyà, Lü, Li, *"Clause vivification by unit propagation
in CDCL SAT solvers"*, Artificial Intelligence 279 (2020) 103197
([PDF](https://home.mis.u-picardie.fr/~cli/clauseVivificationPublishedVersion.pdf);
[arXiv:1807.11061](https://arxiv.org/abs/1807.11061)), §5.3: varying the
activation trigger across five strategies (every restart / after reduceDB / every
500, 1000, 1500 conflicts) moved the solved count only between **930 and 938** of
1450, and the paper concludes:

> *"the most crucial aspect is to determine which clauses should be vivified or
> re-vivified rather than when they should be vivified."*

**[P]** Their cost/impact table (§5, 300 SAT-2014 application instances, 5000 s),
where *Cost* is vivification propagations as a ratio of search propagations:

| variant | solved | literal reduction | cost | fraction of learnt vivified |
|---|---|---|---|---|
| Glucose (base) | 213 | — | — | — |
| Glucose + low-LBD half | **224** | 23.9 % | **29.9 %** | 6.8 % |
| Glucose + high-LBD half | **206** (worse than base) | **33.2 %** | **132 %** | 24.1 % |
| MapleLRB (base) | 234 | — | — | — |
| MapleLRB + | **248** | 27.6 % | 58.1 % | 21.7 % |

with the paper's own conclusion: *"Vivifying clauses with high LBD is very costly
and useless."*

**[I] Two calibration facts we should carry.** First, the **high-LBD variant had
the best literal reduction and was the only one that hurt** — literal reduction
is not the objective, so any success metric we build must be solve-time, not
clauses shortened. Second, a vivification cost of **30-60 % of search
propagations is a winning configuration** in that study, and 132 % is not. That
is a far larger tax than one might guess, and it argues our problem is
*selection*, not that the budget must be tiny.

**[P]** Their own budget: *"we empirically limit the number of propagated
literals in preprocessing vivification to 10⁸"*, and the schedule
`nbNewLearnts ≥ α + β·σ` with **α = 1000, β = 2000** (σ = vivifications so far)
— an *arithmetic* interval, matching CaDiCaL's `elim` law (§2A.4) rather than
Kissat's `n log² n`.

**[P]** The Biere camp explicitly rejects LBD gating in favour of tiered ticks
budgets — PoS'25 *"Revisiting Clause Vivification"*, §4:

> *"Li et al. advocate to vivify only clauses with low LBD… Both CaDiCaL
> (2.2-rc2) and Kissat work differently: they determine a fixed budget of ticks
> spent on each kind of clauses; the budget is split between irredundant, tier-1,
> tier-2, and tier-3 clauses… Therefore, fewer tier-3 (high LBD) clauses are
> vivified achieving a similar limiting effect, but without completely
> disregarding them."*

and on carry-over vs. re-vivification limits:

> *"we … prioritize clauses that could not be vivified in the previous
> inprocessing round (as the corresponding ticks budget was exhausted). As our
> solvers rarely manage to vivify all clauses, this achieves a similar effect."*

**[I]** So the tiered-budget design (§2.3, §4.3) is *the alternative to* LBD
gating, not a complement to it, and the two camps agree on the outcome by
different means. Implement the budget split; do not also hard-gate by LBD.

The same paper reports a structural optimisation worth noting: building an
implicit **prefix tree (trie)** over sorted candidate clauses to share
propagation prefixes *"saves roughly 30% of decisions (median … 33%)… This also
saves propagations and makes it possible to vivify many more clauses within the
same ticks budget."* **[I]** A pure win that costs no soundness; a good later
increment once the budget machinery exists.

### 5A.6 SatELite's bounds were far tighter than today's

**[P]** Eén & Biere, *"Effective Preprocessing in SAT through Variable and Clause
Elimination"*, SAT 2005, LNCS 3569, 61-75
([PDF](http://fmv.jku.at/papers/EenBiere-SAT05.pdf)):

- the occurrence cut-off is **10**, not 2000:
  `if (#occurs of x and x̄ are both > 10) return  – heuristic cut-off`,
  motivated by *"the majority of time was spent on failed attempts to eliminate
  variables occurring frequently in both polarities"*;
- the elimination test is a strict improvement in **clause count**, and the
  choice of metric is argued: *"previous work [NiVER] is focused on minimizing
  the number of literal occurrences. In our implementation we minimize the number
  of clauses. The rationale behind this is that propagation in a SAT solver is
  roughly proportional to the number of clauses, independent of their size."*
- the touched machinery is **three** sets, not one: `Touched` (variables),
  `Added` (clauses), `Strengthened` (clauses), all initially full except
  `Strengthened`;
- **self-subsumption runs before subsumption**: *"Self-subsumption is applied
  first as it may render more (standard) subsumptions possible."*
- cost as reported: *"For problems requiring between 30 seconds and 30 minutes to
  solve, preprocessing took less than 1/10th of the total time."*

**[I]** Two things this changes. Our `occurrence_limit: 100` (`bve.rs:83`) sits
between SatELite's 10 and Kissat's 2000, but the three are not the same
quantity — SatELite's is per-side, Kissat's is `pos + neg` (§4.5), CaDiCaL's is
the *larger* side (§2A.6). **Check which convention our code implements before
comparing the number to anything.** And the clause-count-not-literal-count
rationale is a direct argument for the shape of the BVE priority score in §6.5.

### 5A.7 The soundness framework, and the DRAT hazard it predicts

**[P]** Järvisalo, Heule, Biere, *"Inprocessing Rules"*, IJCAR 2012, LNCS 7364,
355-370 ([PDF](http://fmv.jku.at/papers/JarvisaloHeuleBiere-IJCAR12.pdf)). The
state is a triple `φ [ρ] σ`: irredundant clauses φ, redundant clauses ρ, and a
reconstruction stack σ of literal-clause pairs. Four rules — **Learn**
(add to ρ; precondition must consider `φ ∧ ρ`), **Forget** (drop from ρ, no
precondition), **Strengthen** (promote ρ→φ, no precondition), **Weaken**
(demote φ→ρ *and push `l:C` onto σ*; precondition considers φ only).

The reconstruction algorithm (§6.1, Fig. 4) is four lines and linear:

> *"while σ is not empty do: remove the last literal-clause pair l:C from σ; if C
> is not satisfied by τ then τ := (τ \ {l = 0}) ∪ {l = 1}; return τ"*

and it covers BCE, VE, equivalence reasoning and combinations with one
implementation.

**The hazard.** The φ/ρ asymmetry that makes a step *sound* is what DRAT cannot
see. **[P]** SC2024 solver descriptions, §III (IsaSAT), quoted:

> *"we deactivated our version of pure literal elimination as it is not compatible
> with DRAT (as discovered last year during the competition when proof checking
> broke). Our implementation simply learns the unit clause of that literal and is
> (provably) correct. … The issue is that pure literals redundancy is a criteria
> that needs only be checked on irredundant clauses [Inprocessing Rules], i.e.,
> redundant clauses can be ignored. However, **DRAT does not distinguish these
> sets of clauses, leading to incorrect proofs (even if the answer is correct).**"*

**[I] This is directly load-bearing for us and it answers an open question I had
listed.** We are a proof-carrying stack; `inprocess.rs:44-56` already commits that
every emitted step is plain RUP against the *original* formula. Moving to an
*interleaved* schedule means the passes run against `φ ∧ ρ` — the original
formula plus everything the search has learned — and the failure mode is not a
wrong verdict but **a right verdict with a proof that a checker rejects, or worse
accepts while not covering the original formula.** Concretely:

- A step justified against φ alone (pure literals is the canonical case; blocked
  clauses another) is **not** emissible as DRAT even though it is sound under the
  Inprocessing Rules calculus.
- Conversely, the paper's §7 warns it is *"not correct to use the clauses in ρ to
  eliminate an irredundant clause … unless the clauses, based on which the
  eliminated clause is redundant, are added to ϕ"* — and records that this exact
  bug *"was kept in the [Lingeling] code for some months without triggering any
  inconsistencies."*
- The paper also notes Learn *"may add clauses to ρ that are not entailed by the
  clauses in the original formula"* — so `φ ∧ ρ ∧ CNF(σ)` may be unsatisfiable
  while everything is correct, because reconstruction saves you. Any test we
  write that asserts the reduced formula is equisatisfiable *without* applying σ
  will be wrong for the wrong reason.

**[I] Design consequence.** Before implementing interleaving (recommendation 3),
decide per pass whether its justification uses ρ. Passes that are RUP against
`φ ∧ ρ` (subsumption, self-subsuming resolution, vivification, resolution-based
BVE) are DRAT-emissible as they stand. Passes justified against φ alone are not,
and must either be dropped, restricted to a φ-only regime, or emitted under a
richer format. Our current three passes look safe on this axis — **but I did not
verify that, and it must be checked pass by pass, not assumed.**

### 5A.8 Two more recent results relevant to our reconstruction

**[P]** Fazekas, Biere, Scholl, *"Incremental Inprocessing in SAT Solving"*, SAT
2019, LNCS 11628, 136-154
([PDF](https://cca.informatik.uni-freiburg.de/papers/FazekasBiereScholl-SAT19.pdf)):
replaces literal-clause pairs with **witness-labelled clauses** `(ω : C)` where ω
is a set of literals read as a partial assignment; splits Weaken into **Weaken⁺**
(push to σ) and **Drop** (implied clause — just delete, remember nothing); adds
**Restore** and a *clean clause* condition. Frozen variables *"are not allowed to
be eliminated or occur in witnesses"*.

**[P]** Fazekas, Pollitt, Fleury, Biere, *"Incremental Inprocessing Rules beyond
Resolution"*, PoS'25
([PDF](https://cca.informatik.uni-freiburg.de/papers/FazekasPollittFleuryBiere-POS25.pdf)),
which reports a strengthening of the redundancy definition found necessary by an
Isabelle formalisation, and states a practical consequence outright:

> *"solution reconstruction needs to work with total assignments and has to assign
> all variables initially and not on-the-fly during the reconstruction
> procedure."*

**[I] This is a concrete bug class to check in our `Reconstruction`
(`bve.rs`).** If our model lift assigns variables lazily as it walks the stack
rather than starting from a total assignment, it is in the failure mode this
sentence names. Worth a targeted test with a witness whose clauses overlap on an
unassigned variable — I did not check our implementation against it.

**[P]** Nadel, *"Backtrackable Inprocessing"*,
[arXiv:2605.03654](https://arxiv.org/pdf/2605.03654) (May 2026), SAT 2026: the
first framework enabling inprocessing *under the current trail at any decision
level*, with per-level tracking so effects can be soundly undone on backtrack.
Covers subsumption, self-subsuming resolution and BVE; reports ~1.5x as many
difficult BMC bounds solved versus a global-level incremental preprocessor.
**[I]** Interesting but a later increment; and the literature lane did not find
proof-logging discussion in it, so its interaction with our DRAT obligation is
unknown.

### 5A.9 The convergence point that suggests our target constant

**[P]** Wotzlaw, van der Grinten, Speckenmeyer, *"Effectiveness of pre- and
inprocessing for CDCL-based SAT solving"*,
[arXiv:1310.4756](https://arxiv.org/pdf/1310.4756) (2013):

> *"The solver was allowed to use 10% of the timeout on preprocessing and 10% of
> the timeout on inprocessing. These values have been determined empirically
> through testing. Inprocessing was run each time the ratio of the inprocessing
> time-limit consumed so far and the current solver runtime was less than 0.1."*

**[I]** Independently derived, in wall-clock terms, the same 10 % that Kissat
encodes as `vivifyeffort = eliminateeffort = forwardeffort = 100` per mille of
ticks (§2.1). Three sources converge on ~10 % of search effort per major pass.
That is a defensible starting constant for us, and Biere's contribution is
replacing the clock with a deterministic counter — which is exactly the change we
need for our API promise.

**[I]** The literature lane searched arXiv 2023-2026 for a dedicated paper on
inprocessing *scheduling / effort allocation* and **did not find one**. The
knowledge lives in solver descriptions and PoS workshop notes. Plan to read
future SAT Competition descriptions as the primary channel, not conference
proceedings.

---

## 6. What to build, as separable Rust pieces

Framed as reusable components with their own knobs, so this serves SAT and SMT
divisions rather than being a narrow port. Everything below is **[I]** — a design
proposal derived from the **[C]** findings above.

### 6.1 `Ticks` — the deterministic work counter

A newtype over `u64` plus the charging rules, living next to our propagator.
Charge: `1 + ceil(n / W)` on entering a watch list of `n` entries, `+1` per
arena dereference, `+1` per watch move, `+1` per assignment with a large reason.
`W` (elements per assumed cache line) is a `const` we choose once from our watch
size — **not** read from the host.

Separate accumulators, drained per propagation call: `search_ticks`,
`probing_ticks`, plus whatever named counters passes need. Expose them in the
public stats so a determinism test can assert two runs produce identical tick
counts.

*Essential.* Without a deterministic budget unit the rest cannot be both adaptive
and reproducible.

### 6.2 `EffortBudget` — the budget abstraction

```rust
struct EffortPolicy { per_mille: u32, min_reference: u64 }
struct EffortBudget { limit: u64 }   // absolute, in the pass's own counter

impl EffortPolicy {
    fn budget(&self, counter_now: u64, search_ticks_now: u64, search_ticks_at_last_round: u64)
        -> EffortBudget
    {
        let reference = (search_ticks_now - search_ticks_at_last_round).max(self.min_reference);
        EffortBudget { limit: counter_now + (reference * self.per_mille as u64) / 1000 }
    }
}
```

Generic over *which* counter — ticks for vivification, resolution attempts for
BVE, occurrence steps for subsumption. Plus `EffortBudget::split(weights) ->
Vec<EffortBudget>` implementing §2.3's **cumulative** carry-over.

*Essential.* Knobs: `per_mille` per pass, `min_reference` global.

### 6.3 `DelayCounter` — the failure backoff

```rust
struct DelayCounter { count: u32, current: u32 }
// delaying(): if count > 0 { count -= 1; true } else { false }
// bump():     current = current.saturating_add(1); count = current;
// reduce():   current /= 2; count = current;
```

Driven by a success-rate predicate the caller supplies (Kissat's is
`vivified / tried < 0.01`).

*Essential for us specifically*, because our measured problem is "the pass loses
on this workload". Knobs: the success-rate threshold, per pass.

### 6.3b `DelayThreshold` — the accumulate-and-delay gate

Distinct from §6.3 and, on the evidence of §2A.2, more important:

```rust
struct DelayThreshold { multiple: u64 }   // ticks per clause

// inside the budget computation, before committing:
let thresh = self.multiple * formula.clause_count() as u64;
if delta < thresh {
    return Decision::Delay;   // do NOT advance `search_ticks_at_last_round`
}
```

The whole mechanism is the *omission* of the watermark update on the delay path,
so the accrued window keeps growing until the budget can pay for the round's
fixed setup cost. `multiple` encodes that setup cost — CaDiCaL uses 20 for
vivify, 7 for factor, 5 for sweep, 6 for ternary (§2A.2).

*Essential, and the highest-leverage single item in this note.* Knobs:
`multiple` per pass; a pass whose setup is genuinely cheap passes `None`.

### 6.4 `TouchSet` — the change tracker

A `Vec<VarFlags>` bitfield (one byte per variable: `active`, `eliminate`,
`subsume`, `fixed`, `eliminated`, …) plus **monotone rising-edge counters** and
per-pass **watermarks**.

Two hard rules, both load-bearing:

- **Only irredundant clause changes set bits.** Learned-clause creation and
  reduction must not touch it (§4.2).
- **A pass clears the bit before it attempts**, so a failed attempt is not
  retried until something changes (§4.3).

*Essential — this is the crux.* Knobs: which clause classes count as "changing"
(we may want a `TrackRedundant` mode for a division where the redundant DB is the
subject).

### 6.5 `CandidateQueue` — priority, budget-aware and resumable

Two shapes, both needed:

- **Variable queue (BVE):** a max-heap keyed by
  `activity + (pos·neg − pos − neg) − occlim²` with `pos`/`neg` clamped to
  `occlim`. Replaces our `VecDeque` (`bve.rs:196`) so a budget cut-off keeps the
  most profitable work.
- **Clause queue (vivification):** a per-clause `vivify` bit giving the resumable
  round-robin of §4.3, plus a sort by rarest-literal-first, and a full reset when
  the sweep completes.

*Essential.* The heap ordering is what makes an early cut-off *not* a loss.
The scoring formula itself is a tuning choice — the shape (`removed − added`,
with an activity tiebreak) is the transferable part.

### 6.6 `SchedulePolicy` — the trigger

Per pass: `{ base_interval, growth: Growth, size_scaled: bool }` with
`Growth ∈ {Linear, Sqrt, Log, NLogN, NLog2N, NLog3N}`, evaluated as
`next = conflicts_now + base * growth(times_run) * size_scale(formula_size)`.
Plus, for the change-driven half, a `requires_change: bool` consulting §6.4's
watermarks.

*Growth law and constants are tuning.* **The change-driven gate is essential.**

### 6.7 `OccurrenceIndex` — built per round, torn down after

Full literal→clause lists, built once per elimination call and shared by
subsumption and BVE in the same call (§5.2), with binaries kept separate from
large clauses. Not maintained through search.

*Essential that it is per-round and shared.* Kissat's specific trick of
overloading the watch arrays is **architecture-specific — do not copy**; decide
our own layout.

### 6.8 The pipeline

`InprocessRound { passes: Vec<Pass>, order: fixed }`, with producers before
consumers and consumers re-entered after each producer (§5.1), and with the
subsume→BVE pair fused inside one occurrence-index lifetime (§5.2).

*Essential.* The exact pass list is ours to choose.

### 6.9 Explicitly do NOT copy

- Kissat's watch-array-as-occurrence-list overloading (§4.4) — depends on their
  4-byte tagged watch word.
- The `kitten` embedded sub-solver behind `sweep` — a whole second SAT engine.
- `ASSUMED_LD_CACHE_LINE_BYTES = 7` as a *number*: pick our own from our watch
  size. Copy the *idea* that it is a compile-time assumption, not a host query.
- `factor` / bounded variable addition — it *adds* variables, which interacts
  with our reconstruction and DRAT obligations in ways this note did not examine.
- The specific per-mille values as gospel; they are tuned for a 5000 s
  competition limit, and our 24 s budget is a different regime. **[I]** The
  *formula* is what transfers; the constants need our own measurement.

---

## 7. Ranked recommendations

Ordered by my expected impact on making inprocessing affordable inside our
budget. All rankings are **[I]**; the evidence each rests on is cited.

1. **Add the accumulate-and-delay gate: do not run a pass until its accrued
   budget exceeds `thresh x |clauses|` (§2A.2).** This is the mechanism CaDiCaL
   built *specifically* for our symptom — a pass whose `O(|F|)` setup cost makes
   a small round uneconomic — and the rationale is written into
   `references/cadical/src/probe.cpp:902-907`. It is roughly thirty lines: an
   accrued-tick counter that is *not* reset on the delay path, and one
   comparison. Expected to convert "the passes lose inside 24 s" into "the passes
   run twice instead of ten times, and win both times."
2. **Exclude learned clauses from the change tracker (§4.2, §6.4).** Kissat's
   BVE and subsumption schedules are driven only by irredundant clause changes,
   so round *n+1* re-examines almost nothing. Our `bve.rs` seeds its queue with
   every variable on every call (`bve.rs:465-467`). Largest single lever on the
   *per-round* cost, as opposed to the *number of rounds*.
3. **Replace absolute budgets with per-mille-of-search-ticks (§1, §2, §6.1-6.2).**
   Our vivify budget is a fixed `1 << 22` (`vivify.rs:109`); our simplify budget
   is `64*(lits+vars) + 2^16` (`simplify.rs:297`); neither knows what search has
   spent. Three independent sources converge on ~10 % of search effort per major
   pass (§5A.9). This is also what removes the wall-clock `deadline` from our
   determinism caveat (`inprocess.rs:64-67`).
4. **Fix candidate selection before touching the trigger (§5A.5).** Li et al.
   measured 930-938 solved across five different activation schedules and
   concluded selection dominates timing. Concretely for us: the BVE max-heap
   (item 7) and the vivification tier split with carry-over (§2.3) matter more
   than when the round fires.
5. **Interleave instead of preprocessing (§3, §5.4) — but read §5A.7 first.**
   Kissat runs no heavy BVE before search at all; its first BVE is ~12,500
   conflicts in. Our one-shot `preprocess()` pays the whole cost with the least
   information. **Blocked on a per-pass DRAT audit** (§8).
6. **Add the change-driven gate (§3.4, §2A.4).** Two monotone counters and two
   watermarks; skips whole rounds for free when nothing has changed. Both solvers
   have it and both advance the watermark only on a *completed* round.
7. **Add the delay/backoff counter (§2.4, §6.3).** AIMD on skips, driven by a
   1 % success threshold. Directly addresses "does not pay off on this workload"
   with a per-instance answer instead of our global `OFF`.
8. **Make BVE's queue a max-heap by an occurrence-product score (§4.3, §2A.5,
   §6.5).** Replaces our FIFO `VecDeque` so a budget cut-off keeps the most
   profitable work rather than an arbitrary prefix. Score the *clause-count*
   delta, not literals (§5A.6).
9. **Make vivification resumable via a per-clause bit (§4.3).** Both solvers do
   it; without it, a budget cut-off means we re-vivify the same low-index prefix
   on every call.
10. **Fuse subsumption and BVE into one occurrence-index lifetime, subsumption
    first (§5.2).** Halves the index build and shrinks BVE's quadratic input.
    Self-subsumption before subsumption (§5A.6).
11. **Adopt the bound ladder 0 -> 1 -> 2 -> 4 -> 8 -> 16 (§4.5, §2A.6).** A
    *quality* lever whose affordability depends on 1-10 landing first.

Two rules to build in from the start, both cheap now and expensive later:

- **The counter a pass is scheduled by must never be incremented by that pass**
  (§5A.3). Kissat achieves this with separate `search_ticks` / `probing_ticks`
  accumulators (§1.3).
- **Every mechanism above goes behind its own flag with its own default.** All of
  them were individually removed from Kissat in SC2022 and several restored in
  SC2023/SC2024 (§5A.4). Do not ship them as an inseparable bundle, and do not
  read today's Kissat defaults as a verdict.

---

## 8. Open questions and things not verified

- **Did not measure anything.** This note is a source reading plus a literature
  review. The arithmetic in §3.3 is mine, computed from **[C]** formulas; every
  other number is quoted.
- **The DRAT question is now a known hazard, not an open one (§5A.7), and it
  gates recommendation 5.** Before interleaving, audit each of our three passes
  for whether its justification uses only irredundant clauses. A step sound under
  the Inprocessing Rules calculus but justified against `φ` alone produces an
  *incorrect DRAT proof with a correct verdict* — the IsaSAT pure-literal
  incident. Our passes look safe (subsumption, self-subsuming resolution,
  vivification and resolution-based BVE are all RUP against `φ ∧ ρ`), **but I did
  not verify this pass by pass and it must not be assumed.**
- **A second, distinct DRAT obligation:** `inprocess.rs` currently guarantees the
  emitted steps prove the *original* formula. Under interleaving the passes run
  against original-plus-learned, and the ordering constraint ("adds precede the
  deletions that would remove their justification") has to hold against a
  clause database the search is concurrently mutating. Not analysed here.
- **A likely bug class in our `Reconstruction` (§5A.8).** PoS'25 states that
  solution reconstruction "has to assign all variables initially and not
  on-the-fly during the reconstruction procedure". I did not check `bve.rs`
  against this. Worth a targeted test regardless of the rest of this note.
- **Our `occurrence_limit: 100` is not comparable to a quoted constant until we
  check the convention** (§5A.6): SatELite's 10 is per side, Kissat's 2000 is
  `pos + neg`, CaDiCaL's 100 is the larger side. Read `bve.rs` before comparing.
- **Did not read** `simplify_vivification_candidate` (`kissat/src/vivify.c` ~80-126)
  line by line, nor `vivify_clause`'s internal tick charging, nor CaDiCaL's
  `elimfast.cpp`.
- **A determinism risk we must design around (§2A.7).** Both solvers' growth laws
  call libm (`log10`, `log`, `sqrt`). libm results are not bit-identical across
  implementations, so a schedule boundary could differ by a conflict across
  libcs. Recommend an **integer-only** `Growth` enum from the start rather than
  discovering this in a cross-platform determinism test.
- **A suspected defect in CaDiCaL's `ternary.cpp` (§2A.8)** was derived
  algebraically and **not verified by execution**; neither lane built CaDiCaL. If
  it holds, hyper ternary resolution is inert in that tree. Do not copy the line;
  do not use that tree's ternary results as a baseline without checking.
- **Did not resolve** whether Kissat's exclusion of redundant clauses from the
  BVE/subsumption touch set is a stated policy or a consequence of BVE being
  sound only over the irredundant formula. **[I]** It reads as the latter with the
  cost saving as a bonus — and CaDiCaL *does* mark subsume on redundant clauses
  (§2A.5), compensating elsewhere, which suggests the two are separable choices.
