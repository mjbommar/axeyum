# Which routes spend a ladder's clock without deciding, and which of them cost a file

Lane `budget-discipline`, 2026-09-08. Three separate measurements that day found
the same shape by accident — a route consumes its whole slice, decides nothing,
and the file is then decided in milliseconds by something underneath it. This
note enumerates the rest deliberately, says which are wasteful and which are
earning their keep, and records the one reusable fix.

## 1. The enumeration

**Source: the committed span-log sweep**
([span-log-sweep-2026-09-08.md](span-log-sweep-2026-09-08.md)), 300 files — the
first 50 of each committed parity list in `bench-results/parity-lists/` for
`QF_ABV`, `QF_BV`, `QF_IDL`, `QF_LIA`, `QF_LRA`, `QF_NIA` — at solver commit
`049afd423`, 24 s and 8 GiB per file, one process at a time on s6 and s7. Shards:
`~/projects/personal/axeyum.com/public/data/spans/<division>.json`.

Every `route_attempt` span carries the route, its wall time, and its outcome, so
"what fraction of its slice did it take, how often did it decide, and what ran
after it" is answerable from the artifact rather than from a new sweep.

**Two caveats that change how the table reads.** A route attempt's wall clock is
a *prefix sum* — time is attributed to the next route that records — so a route
that never returns leaves its budget on whichever attempt is recorded next, or on
no attempt at all. And the sweep predates two changes landed later the same day
(the `QF_UFLIA` ladder reserve and the `QF_ABV` congruence-scan fix), so
`QF_UFLIA` is absent and two `QF_ABV` rows are now decided.

Routes that spent more than 100 ms across the sweep without deciding, ordered by
that wasted time. `recov` is the count of non-deciding attempts on files where a
LATER route did decide — the only column that says whether a reservation could
buy anything at all.

| division | route | n | decided | wasted (s) | median % of the 24 s budget | > 10% of budget | recov | after it, median |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| QF_NIA | `nia-linearize` | 50 | 2 | 487.8 | 44.6% | 47 | **1** | 1.7 s |
| QF_IDL | `dl-online` | 50 | 25 | 421.9 | 87.5% | 25 | **0** | — |
| QF_LRA | `nra` | 29 | 4 | 270.1 | 12.2% | 13 | **0** | — |
| QF_NIA | `int-blast-ladder` | 48 | 1 | 154.6 | 4.4% | 21 | **0** | — |
| **QF_ABV** | **`abv-online-cdclt`** | 47 | 24 | 121.2 | 0.0% | 5 | **18** | **168 ms** |
| QF_LIA | `lia-simplex` | 42 | 19 | 97.2 | 0.0% | 4 | 17 | 1.6 ms |
| QF_BV | `qf-bv` | 48 | 44 | 95.9 | 100.3% | 4 | 0 | — |
| QF_ABV | `array-fast-path` | 22 | 18 | 72.2 | 96.0% | 3 | 0 | — |
| QF_LRA | `dl-online` | 47 | 17 | 40.9 | 1.0% | 3 | 4 | 3.1 s |
| QF_LIA | `lia-dpll` | 18 | 17 | 24.0 | 100.0% | 1 | 0 | — |
| QF_IDL | `lia-dpll` | 14 | 0 | 12.9 | 1.9% | 1 | 0 | — |
| QF_BV | `dl-online` | 50 | 0 | 12.2 | 0.1% | 1 | 44 | 17 ms |

Plus one route with no row at all in this sweep, measured separately the same day
([nia-refinement-round-2026-09-08.md](nia-refinement-round-2026-09-08.md)):
`int-real-relax` holds **188.5 s of the `QF_NIA` population's 762.6 s (24.7%)**
and refutes **zero of 50** files, at a fixed `budget / 6` per file.

### What the `recov` column decides

**A route that never decides is not automatically wrong, and four of these are
not.** The reservation this lane builds is worth nothing unless something below
the route would have decided the file:

- **`QF_LRA/nra`** (270 s, 4 decisions of 29): nothing runs after it. Every
  route recorded below it in the trail is a string-front-door gate that declines
  in microseconds. A reserve here would be pure loss — it would shorten the only
  route with a chance.
- **`QF_IDL/dl-online`** (421.9 s, 25 decisions of 50): it **already reserves**
  `min(t/4, 6 s)` for the ladder, and on this population the ladder decides
  **zero** of the files it declines. The reserve's entire justification is one
  file outside this sample (`QF_IDL/sal/lpsat/lpsat-goal-18`, undated). Recorded
  as a finding against `DL_LADDER_RESERVE_SHARE`; **not changed**, because
  removing a reserve on the strength of a 50-file sample that does not contain
  the file it was built for is the same error in the other direction.
- **`QF_NIA/nia-linearize`** (487.8 s, 2 decisions of 50): the routes after it
  decide **one** file in the whole sweep. A reserve would cost the route that is
  doing the work to feed routes that are not. The `QF_NIA` lever is the one
  `nia-refinement-round-2026-09-08.md` names — the linearizer builds a relaxation
  its own consumer refuses on size — not a budget split.
- **`QF_NIA/int-blast-ladder`**, **`QF_BV/qf-bv`**, **`QF_LIA/lia-dpll`**,
  **`QF_ABV/array-fast-path`**: last rungs. Nothing runs after them by
  construction.
- **`QF_LIA/lia-simplex`** has 17 recoverable attempts but they carry **0.1 s**
  of the 97.2 s between them: it declines instantly on the shapes `lia-dpll`
  decides, and burns its time on files nothing else decides either. Not a
  reservation case.

**`QF_ABV/abv-online-cdclt` is the one route in six divisions where the pattern
is real and costly**, and it is the instance that was found by accident.

### The `QF_ABV` case, per file

`abv-online-cdclt` runs first on every array query and took `config.timeout` in
**full**. From the shard:

| | |
|---|---:|
| files it decided | 24 of 47 |
| its **slowest** decision | **5.723 s** |
| decisions over 1 s | 8 of 24 |
| files it spent the whole 24 s on | 5 |
| ...of those, decided by `array-fast-path` immediately after | **4** |
| that ladder's decision time on those four | **0.007 – 0.174 s** |
| slowest `array-fast-path` decision anywhere in the sweep | 2.898 s |

Those four files are `sat` today only because the harness watchdog's grace period
outlasts the budget: 24 s spent above plus a **fresh** 24 s budget below is 48 s
of a 24 s promise. Under a hard external limit they are losses.

## 2. The fix: one policy, not a fourth divisor

The tree had grown four hand-rolled copies of this arithmetic before it had a
name for it (`dl_probe_budget`, `extended_dl_probe_timeout`, `cegar_probe_budget`,
`int_real_relax_budget`), plus three more inside dispatch bodies
(`probe_budget`, `mbqi_first_refusal_budget`, `pre_lia_uf_probe_budget`, and a
bare `timeout / 2` in the quantifier retry). Each had to be found by measuring a
division.

`LadderSlice` (`crates/axeyum-solver/src/auto.rs`) is now the single policy. Two
shapes, and the distinction is the one the `QF_UFLIA` measurement paid four files
to learn ([uf-arith-overbound-2026-09-08.md](uf-arith-overbound-2026-09-08.md)):

- **`AllButReserve`** — the route keeps everything except `1/N` (optionally
  capped at a flat ceiling). For a route that decides most of what it is given.
- **`Fraction`** — the route takes `1/N` (optionally capped). For speculative
  insurance ahead of the routes that do the work.

Halving a budget is the worst of both: it starves the deciding route without
buying the ladder anything it needed.

Every share is now a named `const` with a `config_registry` entry, so "why does
this route get 18 s of a 24 s budget" is answerable by name. Nine constants were
named in the process; seven of them were literals inside an expression that no
name-keyed registry could see.

### Two policy inversions closed

`int_real_relax_budget` returned the caller's config **unchanged** — the full,
unshrunk timeout — whenever `timeout / 6` rounded to zero. So a route asked for a
sixth of the clock got all of it, at exactly the small-budget end where
starvation matters most. This was recorded as a FINDING against
`INT_REAL_RELAX_BUDGET_SHARE` in the config registry and not acted on.

Looking for a second instance of it found one: `pre_lia_uf_probe_budget` had the
identical inversion at `timeout / 10`. Both now clamp to `MIN_LADDER_SLICE`
(1 ms), which differs from the old behaviour only under 6 ms and 10 ms
respectively. That is the argument for writing a finding down rather than fixing
one site quietly.

### The ratchet

`every_route_budget_in_this_file_goes_through_the_slice_policy` derives its
population from `auto.rs`'s own source: every site that sets a route's `timeout`
must be one of the three helpers that narrow a config to the **remaining** clock,
or `LadderSlice::apply`. A fifth hand-rolled divisor fails the test at the moment
it is written, which is the only moment it is cheap to notice. The test asserts a
non-zero site count first, so a scan that stopped matching the source fails
rather than passes.

### `ABV_ONLINE_LADDER_RESERVE_SHARE = 4`

Chosen against **both** bounds the sweep gives, which is why it is neither the
largest nor the smallest defensible value:

- it leaves the online route **18 s of a 24 s budget, above every decision it
  made** in the sweep (slowest 5.723 s of 24 decisions);
- it gives the ladder **6 s, twice the slowest ladder decision** observed
  (2.898 s) and 35x its median (168 ms).

A route needing 99% of the clock is not recoverable by any reserve. `QF_UFLIA`
had one such file (`hash_uns_05_20`, 23.7 s of 24 s) and paid it as the named
cost of the same change; nothing in this `QF_ABV` population does, and
`AXEYUM_ABV_ONLINE_RESERVE=off` is the arm that measures whether one exists
outside it.

The array ladder also now runs on the **same clock**: `dispatch_array_fast_paths`
receives what is left of the dispatcher's entry deadline instead of a fresh copy
of the caller's full timeout. That is the half of the change that removes the
reliance on watchdog grace.

## 3. The A/B

<!-- RESULTS-AB -->

## 4. Reproducing

```sh
# the enumeration, from the committed span shards
python3 scripts/analyze-ladder-slices.py

# the A/B, one arm per host
AXEYUM_ABV_ONLINE_RESERVE=off scripts/span-log-sweep.sh QF_ABV /tmp/off.jsonl 200 24000
AXEYUM_ABV_ONLINE_RESERVE=on  scripts/span-log-sweep.sh QF_ABV /tmp/on.jsonl  200 24000
```
