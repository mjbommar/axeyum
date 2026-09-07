# QF_LRA, the theory side: cutting the `final_check` call count

Lane `lra-theory-side`, 2026-09-07. Diary — written as the work happens,
including the hypotheses that turn out to be wrong. The numbers live in
[the measurement log](lra-theory-side-2026-09-07-log.md).

## Why this lane exists

[ADR-1732](../09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
re-measured the QF_LRA frontier and the gap is **84 files**, not the 52 the
board carried: Yices 2.7.0 decides 181 of the committed 200-file list where
cvc5 decides 145 and we decide 97. That makes this the largest single
arithmetic target.

The [family page](../../plan/families/smt-quantifier-free/qf-lra.md) census
splits the loss cleanly in two, with no third class:

- **31 search timeouts.** Profiled: `final_check` → `feasibility` → simplex was
  84% of wall, called **1,150–15,000 times per file**. A prior slice fixed one
  redundant `O(rows × columns)` pass inside the pivot — the *per-call* half.
  The **call count** is untouched.
- **23 admission declines** at `MAX_ONLINE_LRA_ATOMS = 1_024`.

Two things this lane will not do. It will not unify the engine — measured on
2026-09-06, `CdclT` is already 3.4% *faster* than the native core. And it will
not raise the atom constant; if that moves it becomes a measured budget
([ADR-1752](../09-decisions/adr-1752-the-lra-admission-cap-becomes-a-memory-budget.md)).

## The method, and why it is not negotiable here

The last person on this division found the plan's stated cause was **false**.
The belief was that the tableau needed a warm start; S4 wired six counters in
*before changing anything* and measured `simplex_cold_restarts = 0` across
6,571 checks. So the rule is **wire the counter, then look**.

That rule paid immediately, and then it paid again in the opposite direction:
the first change I made from a correct diagnosis was still **1.77x slower**, and
only a counter-identical A/B could tell me so.

## Pre-registered hypotheses, and what the baseline did to them

Recorded before any measurement, ranked H1 > H3 > H4 > H2 > H5.

| | hypothesis | verdict |
|---|---|---|
| **H1** | Most `final_check` calls conflict, and the cores are wide, so the search enumerates assignments | **Confirmed, at the limit.** `final_check_conflicts / final_checks` is 20732/20732, 21138/21138, 30443/30443, 5736/5737 … **every** total assignment the Boolean search reaches is refuted. Core width 8.5–138.2 literals against 176–859 live rows. |
| **H2** | The `rows_to_core` widening fallback fires | **Refuted.** `final_check_core_widenings = 0` on all eleven traced files. Every core is a genuine self-verified Farkas core. |
| **H3** | The cheap `assert` bound check almost never fires | **Confirmed.** `assert_partial_conflicts` is 7–339 against thousands to tens of thousands of complete refutations — between 0.03% and 1.1%. Nothing but Boolean propagation prunes between two total assignments. |
| **H4** | Propagation is still thin after S4 | **Split, and family-dependent.** 78,251 and 43,209 literals on the two Heizmann files (S4's form generalization works there), but **79** on `blending/1` — the identical figure quoted from before S4 — and **0** on `miplib/pp08a-1000` and `TM/p-driverlogNumeric_s7`. |
| **H5** | Repeated checks re-decide settled work | Not measured. Overtaken. |

## The finding I did not predict, which is where the work went

The plan says `final_check` is 84% of wall. On the population that is true for
**two files of eleven** and badly wrong for the rest:

| file | ms | `theory_final_check` | `theory_propagate` |
|---|---:|---:|---:|
| `blending/1` | 6903 | 6396 (93%) | 325 (5%) |
| `Heizmann/_standard_two_index_06…` | 24024 | 16984 (71%) | 6332 (26%) |
| **`miplib/pp08a-1000`** | 24033 | 3288 (**14%**) | **18051 (75%)** |
| `clock_synchro/…_4clocks` | 24266 | 3 | 46 |

`miplib/pp08a-1000` spends **18.05 s of a 24.03 s budget in theory propagation**
and offers **zero** literals. Eighteen seconds scanning, nothing derived. The
scan visits every registered atom at both polarities on every propagation call,
and that file takes 1.9 M decisions.

And the `clock_synchro` family spends **0.2–2% of its budget inside the whole
CDCL(T) driver** — 51 ms of traced stages against 24,266 ms of wall on
`_4clocks`. Whatever consumes those files' budget is not the search the census
attributed it to. That is a **third census class**, and this lane did not have
the runway to find it; it is the most valuable thing on the board for whoever
takes this next.

## What was changed, and what each change cost

### 1. `propagatable` — an exact scan filter

An atom whose two polarity forms are touched by no *other* atom can never emit:
a bound on a form is only ever installed by an atom touching it, so the only
bound such an atom can see is its own, which the existing `held.atom == atom`
guard already refuses. So restricting the scan to atoms sharing a form is
**output equivalence**, not an approximation, and the control
(`the_scan_filter_offers_exactly_what_a_full_scan_would`) re-derives the full
scan body and compares literal for literal and reason for reason.

Mutation-checked in both directions, and the second direction is the
interesting one: dropping a *shared* atom kills the control (and one existing
test), while making the filter keep everything does **not**. That is correct —
an over-inclusive filter is a performance regression, not a wrong answer — and
it is worth writing down, because a mutation table that recorded only the first
result would overstate what the control guards.

### 2. The GCD — a correct diagnosis and a wrong fix, then the right one

`gcd` is the whole cost of exact rational arithmetic here: one `small_mul` calls
it three times, one `small_add` twice. That diagnosis was right.

The fix I reached for was **Stein's binary GCD**, on the reasoning that x86-64
has no 128-bit divide so every `u128 %` is a `__udivti3` call. It measured
**1.77x slower**: `final_check` on `blending/1` went 6,396 → 11,335 ms with
every other counter byte-identical — 20,732 checks, 46,618 pivots, 216,280 bound
retractions, 20,791 learned clauses — so the difference was arithmetic alone.

The reason is operand *shape*, which the algorithm-level argument never looked
at. The cross-cancellations are `gcd(large numerator, small denominator)`:
Euclid settles that in one or two divisions, Stein pays one shift-subtract
iteration per bit. The win was not a different algorithm but a **narrower** one
— keep Euclid, step down to `u64` as soon as both operands fit, where `%` is a
single instruction. That measures **0.86x** against the pre-lane baseline on the
same file.

The integer (`den == 1`) fast paths in `small_new` / `small_add` / `small_mul`
keep the magnitude arithmetic verbatim rather than switching to a signed
`checked_mul`, because the two disagree at exactly one product (`−2^127`) and a
fast path that *succeeds* where the general body declines changes the search
trajectory, not only its speed. The random draw did not catch that mutant; the
named boundary case does, and finding that gap is what the named cases exist for.

### 3. The atom cap became a memory budget (ADR-1752)

Mid-lane the coordinator established that this half is the larger one: the
QF_NRA lane's A/B showed `MAX_ONLINE_LRA_ATOMS` is the real gate behind **62
QF_NRA losses** as well as this division's 23.

Reading the code before measuring found something better than a tuning
opportunity. The cap's own doc records the measurement it rests on — the 8 GiB
abort at 1,492 atoms — and names `AtomBuilder` normalization as the cost. That
measurement is dated **2026-08-03** (`e62086742`). `MAX_LRA_CACHED_COEFFICIENTS`,
which bounds exactly that cost, landed **2026-08-06** (`96ff85930`), three days
later, and the cap was never re-measured. The number the cap rests on describes
a tree in which the thing it protects against was unbounded.

That is the CLAUDE.md gotcha in its pure form: *a file that records obstacles
accumulates stale ones by construction, and its authority is what makes them
expensive.* The doc was specific, numerate and authoritative, which is exactly
why it survived a month unchecked.

The replacement is in ADR-1752. The short form for a sibling division: a **count**
is the wrong currency, because the footprint is `atoms × coefficients-per-atom`
and 23,385 atoms over a handful of variables cost less than 1,492 over 700. The
budget is charged in coefficients, deterministically, from the builder's own
counters rather than a resident-set probe, and a refusal now says *projected N
MiB > budget M MiB at K atoms over V variables* instead of `1493 > 1024`.

## Log

### 2026-09-07 — lane opened

Read the family page, `lra_theory.rs`, the `LraTheory` half of `lra_online.rs`,
and `CdclT::run_final_check`. Nothing measured. Five hypotheses registered.

### 2026-09-07 — counters landed, baseline taken

`a56c43639`. Five new engine counters, no behaviour change. Baseline on the
33-file population: **7 of 33 decided**, and the table above.

### 2026-09-07 — first change, and its regression

`aa6847be0`. Scan filter + Stein + integer fast paths: **8 of 33**, with
`spider_benchmarks/no_op_accs.base.smt2` moving unknown → unsat at 19.2 s. But
`blending/1` and `blending/5` were 1.70x and 1.66x *slower*, all from Stein.

### 2026-09-07 — the fix, and the budget

`4acb9332f`. Narrowed Euclid replaces Stein; the atom cap becomes ADR-1752's
byte budget; `smtcomp_cli` gains `--memory-limit-mb` and a
`; give-up kind=… detail=…` line under `--trace`, because the binary was
discarding `UnknownReason` entirely — so in every recorded run a resource
refusal was indistinguishable from a search timeout.
