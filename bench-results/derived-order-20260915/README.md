# Derived ladder order — Phase 4 (ADR-2106)

**2026-09-15, lane DERIVED-ORDER.** Phase 4 of the
[dispatch-and-instrumentation plan](../../docs/plan/dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional),
conditioned on [ADR-2102]'s ledger and sized by
[`bench-results/ledger-structure-20260915/`](../ledger-structure-20260915/README.md),
which named two classes and ranked them:

1. `QF_NIA` / `Int` — `int-blast-ladder` decides 65 of 84, 631,307 ms prefix cost
2. `UFNIA` / `Int|Function` — `q:skolem-qf` decides 24 of 24, 126,764 ms prefix cost

**Both numbers are in TIME on files that already decide.** This directory
answers the question the brief put first: how many FILES could a reorder
convert, and how much of the "prefix cost" is actually a prefix.

## The sizing, up front, with denominators

| class | undecided rows (the denominator) | raw ceiling | **refined ceiling** | reorderable prefix |
|---|---:|---:|---:|---:|
| `QF_NIA` / `Int` | 115 of 199 | 47 | **3** | 628,792 ms / 65 files (9,674 ms/file) |
| `UFNIA` / `Int\|Function` | 6 of 30 | 0 | **0** | **0 ms** |

**Both classes are under five. Both are therefore a TIME SAVING, not a gain**,
which is what the brief says the ADR must record rather than imply otherwise.

Two corrections got to those numbers, and each one moved a headline figure.

### Correction 1 — 42 of the 47 `QF_NIA` candidates are a SIZE ceiling wearing the word `budget`

`size.py`'s ceiling counts an undecided row when the decider was never reached
or got less clock than its median winning time (339 ms for `int-blast-ladder`).
That is necessary and it is not sufficient: a route can fail for the clock, and
a reorder fixes that — or for anything else, and a reorder fixes nothing.

`size-why.py` splits the 47 by the decider's own recorded decline
(`decline_reasons` / `decline_details` / ADR-2104's `decline_names`):

| bucket | rows | can a reorder help? |
|---|---:|---|
| CAPACITY — `estimated 130191180 CNF clauses before lowering exceeds budget 64000000` | 42 | no |
| FRAGMENT — `integer constant 4294967295 does not fit the bounded width 32` | 2 | no |
| no recorded decline at all, decider NEVER reached | 3 | **yes** |
| **refined ceiling** | **3** | |

The 42 are ADR-2060's defect in miniature: `DeclineReason` renders a CNF-size
refusal and a clock expiry with the same word, `budget`. Only the detail text
separates them, which is why `size-why.py` matches on the detail and not on the
reason.

### Correction 2 — `UFNIA`'s 126,764 ms is not a prefix at all

`q:skolem-qf` records a **probe**, hands off to `check_auto` — the entire
quantifier-free ladder — and records its decision when that returns
(`auto.rs::solve_inner`). The ledger-structure README's `prefix_cost_ms` sums
every attempt before the `decided` occurrence, so the whole hand-off lands in
the "prefix".

`prefix-decompose.py` splits it, and the split is total:

| | before its FIRST trail entry (reorderable) | between that entry and its decision (its OWN work) |
|---|---:|---:|
| `UFNIA` / `Int\|Function` | **0 ms**, all 24 files | 126,764 ms |
| `QF_NIA` / `Int` | 631,307 ms | 0 ms |

`q:skolem-qf` appears twice on all 24 trails; `int-blast-ladder` appears twice
on none of its 65. So `QF_NIA`'s figure survives unchanged and `UFNIA`'s goes to
zero. The 126,764 ms is real work and 89.8 % of it is `uf-arith-online`
(113,777 ms) — but that is a **quantifier-free** route inside the hand-off, so
it is a finding about the QF ladder on `Int|Function` queries and not about the
quantified ladder's head, which is the thing a `UFNIA` reorder would move.

**So `UFNIA` / `Int|Function` ships nothing: its ceiling in files is 0 and its
reorderable clock is 0 ms.** That is a refutation of the second of the two
classes Phase 4 was conditioned on, and it is recorded here rather than
softened.

## The derived order

`derive.py` reads `scripts/outcome_ledger.py`'s `load()` only, orders each
window's routes by (decision rate desc, median elapsed asc, name asc — a total
order, so it is deterministic), and prints the numbers beside each route.

### `QF_NIA` / `Int` — `auto.rs::dispatch_nonlinear_int_tail`

| # | hand order (source today) | derived order | decides | rate | median |
|---|---|---|---:|---:|---:|
| 0 | `nia-square` | **`int-blast-ladder`** | 65/177 | 0.367 | 339 ms |
| 1 | `int-real-relax` | **`nia-linearize`** | 19/198 | 0.096 | 788 ms |
| 2 | `nia-linearize` | **`cas-ideal-refuter`** | 0/115 | 0.000 | 0 ms |
| 3 | `nia-bounded-blast` | `nia-bounded-blast` | 0/179 | 0.000 | 0 ms |
| 4 | `cas-ideal-refuter` | **`nia-square`** | 0/199 | 0.000 | 0 ms |
| 5 | `int-blast-ladder` | **`int-real-relax`** | 0/198 | 0.000 | 4,020 ms |

The shape in one line: the two routes that decide anything are last and third,
and the route that decides nothing on this class in 198 attempts
(`int-real-relax`) is second and costs a median of 4.0 s.

### `UFNIA` / `Int|Function` — `auto.rs::solve_inner` head

| # | hand order | derived order | decides | rate | median |
|---|---|---|---:|---:|---:|
| 0 | `q:ground-subset` | **`q:skolem-qf`** | 24/30 | 0.800 | 0 ms |
| 1 | `q:bool-skeleton` | `q:bool-skeleton` | 0/30 | 0.000 | 0 ms |
| 2 | `q:skolem-qf` | **`q:ground-subset`** | 0/30 | 0.000 | 0 ms |

The order differs, and it is **not shipped**. Every route above `q:skolem-qf`
costs 0 ms on every one of the 30 rows, so promoting it recovers nothing; and
the promotion is not a permutation of independent rungs but a hoist of the
skolemization step that **mutates the assertion list** the rungs above read, so
it is a restructure of `solve_inner`'s head rather than a reorder. Phase 4's own
non-goals say it is "not a rewrite of `auto.rs`".

## The key is under-specified, and the existing suite says so

Phase 4's ordering key is **"(decision rate, then median elapsed)"**. It does
not say *whose* elapsed, and on this class the two readings are not close.
`cost-when-declining.py` measures both over the same 199 rows:

| rung | wins | losses | median WIN | median LOSS | p90 LOSS | max LOSS | total LOSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| `nia-square` | 0 | 199 | — | 0 ms | 0 ms | 0 ms | 0 ms |
| `int-real-relax` | 0 | 198 | — | 4,020 ms | 4,195 ms | 9,573 ms | 753,694 ms |
| `nia-linearize` | 19 | 179 | 788 ms | 6,680 ms | 6,959 ms | 8,004 ms | 1,078,885 ms |
| `nia-bounded-blast` | 0 | 179 | — | 0 ms | 8 ms | 984 ms | 1,866 ms |
| `cas-ideal-refuter` | 0 | 115 | — | 0 ms | 1 ms | 13 ms | 68 ms |
| `int-blast-ladder` | 65 | 112 | **339 ms** | **12,566 ms** | 14,297 ms | 23,189 ms | 863,439 ms |

The derived order promotes `int-blast-ladder` from the ladder's **tail** to its
**head** on a 339 ms median winning clock. On the 112 attempts of 177 where it
does not decide it costs **12,566 ms median and 23,189 ms at worst, against a
24,000 ms budget** — and at the head that is paid out of every rung below it, on
exactly the population that still needs one. Its position at the tail is not an
oversight; it is what makes it the rung that soaks up the remainder.

**This is not a prediction. Five committed capability fixtures refute it.**
Under `AXEYUM_LADDER_ORDER=derived`, at their own 2 s budget, these go red:

```
hypothesis_min::tests::closes_the_route_b_l3_lemma_from_the_full_hypothesis_set
hypothesis_min::tests::finds_the_minimal_sufficient_subset
hypothesis_min::tests::minimisation_is_deterministic
hypothesis_min::tests::reported_indices_are_ascending_unique_and_in_range
hypothesis_min::tests::reported_subset_independently_refutes_the_goal
```

The minimiser's small nonlinear-integer subsets stop being refuted, because
`nia-linearize` and `int-real-relax` no longer get the clock. All ten
`hypothesis_min` tests pass under `hand`. A fixture is not weakened to let a
lever ship, so **`int_tail_order::SHIPPED` points at `HAND`** and `DERIVED` is
retained exactly as derived, as the A/B's treatment arm and as the record of
what the key yields.

## Files

| file | what it is |
|---|---|
| `size.py` | the ceiling in FILES, per class, with the per-row candidate list |
| `size-why.py` | splits the candidates by the decider's own decline reason |
| `prefix-decompose.py` | splits "prefix cost" into reorderable vs the decider's own work |
| `derive.py` | the derived order, from `outcome_ledger.load()` only |
| `cost-when-declining.py` | what each rung costs on the rows it does NOT decide |
| `sizing.txt`, `sizing.tsv` | `size.py`'s output |
| `sizing-why.txt` | `size-why.py`'s output |
| `prefix-decompose.txt` | `prefix-decompose.py`'s output |
| `docs/plan/fixtures/derived-ladder-order-20260915.tsv` | `derive.py`'s table — **not in this directory**, because `scripts/tests/mutation_controls.py` excludes `bench-results` from the tree it copies, and a Rust fixture included from here turns every mutation into `BASELINE DID NOT BUILD` |
| `cost-when-declining.txt` | `cost-when-declining.py`'s output |

Every script's exit status depends on its finding: `size.py` exits 3 when no
class clears five files, `size-why.py` exits 3 when no refined ceiling does, `prefix-decompose.py` exits 3 when no class has reorderable clock at all, and
`cost-when-declining.py` exits 3 when a derived head is expensive on its losses.

## Reproduction

```sh
python3 bench-results/derived-order-20260915/size.py \
  --tsv-out bench-results/derived-order-20260915/sizing.tsv
python3 bench-results/derived-order-20260915/size-why.py
python3 bench-results/derived-order-20260915/prefix-decompose.py
python3 bench-results/derived-order-20260915/derive.py \
  --tsv-out docs/plan/fixtures/derived-ladder-order-20260915.tsv
```

[ADR-2102]: ../../docs/research/09-decisions/adr-2102-the-outcome-ledger.md
