# The NRA cross-product admission bound: what it protects

Lane `nra-admission-bound`, started 2026-09-07. Diary; appended as work lands.

## The subject

`crates/axeyum-solver/src/nra.rs`:

```rust
const MAX_CROSS_PRODUCTS: usize = 2;
```

`check_nonlinear_abstraction` counts the **distinct-operand cross-product
monomials** of the normalized assertions
(`nra_real_root::normalized_cross_product_count`, falling back to the raw
distinct-operand product count) and, when the count exceeds 2, refuses the
generic linear-abstraction / McCormick / branch-and-bound route with
`Unknown(ResourceLimit)` — after two cheap sound pre-checks (sign/zero, then
threshold-1 monotonicity), each under a 500 ms `SIGN_REFUTE_BUDGET`.

The 2026-09-06 QF_NRA loss census attributes **62 of 77 reference-only losses
(80.5%)** to this decline, with counts up to 7,874
(`bench-results/parity-losses-20260906/QF_NRA.census.tsv`).

## Step 0 — archaeology, before any measurement of my own

The bound was introduced by `9a8b09220` (2026-06-19,
"fix(nra): deterministic cross-product admission bound — graceful unknown,
never OOM"). Its commit message is the only first-hand record of what it was
built to stop, and it is specific:

> The NRA solver OOM-killed the host on multi-variable nonlinear queries
> (e.g. a²+b²+c² ⋈ ab+bc+ca). Root cause: ≥3 distinct-operand cross-products
> generate a dense disjunctive monotonicity + sum-of-squares lemma set whose
> DPLL(T)/exact-rational LRA relaxation blows up *inside a single solve call* —
> so the per-round / per-node wall-clock checks never get a turn — and bounds do
> NOT tame it (the bounded variant SIGABRT'd at the 64 GiB cap; McCormick just
> adds more lemmas).

So the **claimed** protected resource is **memory**, not soundness and not
(directly) time. That is consistent with the code: the route is sound in both
directions independently of the bound — the abstraction is a *relaxation*
(only `unsat` transfers) and every `sat` is replayed against the original
assertions by the ground evaluator in `check_with_nra`'s outer guard. Nothing
about admission changes which verdicts are *correct*; it changes only which
are *reachable*. **Raising the bound therefore cannot introduce a wrong
verdict by construction; it can only cost memory or time.** That is the
direction question the brief asks to settle before touching the constant, and
it settles in the safe direction — but the OOM claim still has to be
re-measured, because an OOM is a host-level failure, not a graceful loss.

### Three reasons the 2026-06 claim may no longer describe the code

The measurement behind the bound is 2.5 months and several relevant commits
old. Each of these post-dates it and touches exactly the mechanism the claim
names:

1. `4c2dc2524` / `3d9be6e99` — `config.timeout` threaded into the NRA/NIA
   relaxation loops and the lazy-SMT loop. The claim's core is "the per-round
   / per-node wall-clock checks never get a turn"; deadline threading is
   precisely the repair for that.
2. `487fecea9` — pure arithmetic defaults to the generic `CdclT` spine.
   `check_with_lra_dpll_within` now tries `check_qf_lra_online_cdclt` *first*,
   with a deadline derived from the caller's. The engine the 2026-06 blowup
   was measured on is no longer the first engine the relaxation reaches.
3. `68a3c8551` — "Bound oversized exact polynomial fallback".

None of that proves the bound is stale. It means the *premise* ("the wall
clock never gets a turn") is a claim about an engine that has since been
replaced on this path, and must be re-measured rather than inherited. Per
CLAUDE.md's standing rule: verify a blocker still exists before treating it
as one, including a blocker this repository's own comments name.

### What is NOT in question

- **Soundness.** Admission gates *reachability*, never correctness. Both
  transfer arguments (relaxation-`unsat`, replayed-`sat`) are independent of
  the count.
- **That the 62 files trip it.** Measured through the front door, with a
  divergence check (0 of 72 rows divergent).
- **That squares are excluded.** Only distinct-operand cross-products count;
  `x²+y²+z²+1=0` is not gated
  (`tests/nra.rs::square_only_multivariable_is_not_gated_by_cross_product_bound`).

## The measurement plan (fixed before the data is visible)

Three questions, in order. Q1 decides whether the rest is even needed.

- **Q1 — does the blowup still happen at all?** Re-run the exact shape the
  bound was built for (`a²+b²+c² ⋈ ab+bc+ca`, three cross-products, bounded
  and unbounded) with the cap lifted, under `ulimit -v`. Outcome recorded as
  one of: aborts on the memory cap (the claim holds), exceeds the wall clock
  gracefully (the claim's *mechanism* is stale but a cost remains), or
  decides.
- **Q2 — what does it cost on the real population?** The 62 census files,
  cap-2 vs cap-lifted, at the protocol's 24 s / 8 GiB, arms interleaved,
  peak RSS recorded per file. This distinguishes "OOM guard" from "time
  guard": a file that ends at the wall clock with 200 MB resident was never
  protected by a *memory* bound.
- **Q3 — is the count the right predictor?** If the cost is real, is it
  monotone in the cross-product count, or driven by something else (variable
  count, degree, lemma count, Boolean structure)? A count cap is only the
  right instrument if the count predicts the cost.

Recorded before the run so the answer cannot be chosen after seeing it:
**the honest outcome may be that the bound is right and the 62 files need a
different route.** That is a reportable finding, not a failure of the slice.

## Log

- 2026-09-07 — archaeology above; no code touched yet. Next: Q1.

## Q1 — the answer is not the one the plan expected

### The lever, and its positive control

`AXEYUM_NRA_MAX_CROSS_PRODUCTS` (`41e5ff267`) overrides the bound for one
process. Everything below is **one binary**, sha256
`e115759a741e55f0ef1a345c8937be7fd7bea96c557435fb8bacef2baa17f2d1`, built on s6
at lane HEAD; the arms differ only in that variable, so no code difference can
be mistaken for a bound difference.

A lever that silently did nothing would make arm B identical to arm A on every
file and the whole A/B would read "lifting the bound changes nothing" — the
exact false negative to rule out first. **The first control failed to
discriminate and the second succeeded**, and both are worth recording:

- A four-query synthetic battery (bounded McCormick sat, bounded McCormick
  unsat, refinement sat, a 2-cross-product unsat) run at the default bound and
  at bound `0` — which must decline *every* genuine cross-product — produced
  **identical verdicts on all four**. That is not evidence the lever works, and
  it is not evidence it does not: these shapes never reach
  `check_nonlinear_abstraction` at all. The exact real-root / CAD / SOS routes
  in `nra_real_root` sit *upstream* of it and decide them first.
- The discriminating control is `explain_corpus --json --timed-trace` on a real
  census file, which prints the declining route's own message.

### The control, and the finding it produced

`20161105-Sturm-MBO/mbo_E1.smt2`, 771 cross-products, both arms:

| arm | `nra` route outcome | detail | elapsed |
|---|---|---|---|
| A (bound 2) | declined, `budget` | `nonlinear abstraction: 771 cross-products exceed the deterministic admission bound of 2 …` | 0.834 s |
| B (unbounded) | declined, `budget` | **`online CDCL(T) LRA atom cap exceeded (23385 > 1024)`** | 0.822 s |

The lever works — the message changed. And the message it changed *to* is the
finding:

> **Lifting the cross-product bound does not admit this query. It hands it to
> the next gate, one file down, which refuses it immediately and for free.**

`crates/axeyum-solver/src/lra_theory.rs`'s `MAX_ONLINE_LRA_ATOMS = 1_024` is a
*measured* ceiling (its own doc comment records the measurement: raising it to
16384 on the QF_LRA parity list changed **no** verdict, cost one file 24 s it
used to decline in 0.12 s, and made a 1,492-atom file abort at the 8 GiB cap).
`check_with_lra_dpll_within` treats a `ResourceLimit` decline from the online
route as **terminal** — it does not fall through to the legacy mixed route — so
an over-cap abstraction returns `unknown` at once.

So on this file the cross-product bound is not protecting anything: the thing
it was built to prevent is prevented one layer down, by a bound that was
measured, at no cost. Same elapsed (0.834 vs 0.822 s), same peak RSS
(101,240 vs 101,280 KiB at the front door).

### Why this reframes the slice

The two gates are 15× apart and unrelated in their units. At the observed
~30 atoms per cross-product (23,385 / 771), the 1,024-atom ceiling corresponds
to roughly **34 cross-products** — not 2. Everything between 3 and ~34 is
refused by a constant that has no relationship to the capacity of the engine
that would consume the query.

That range is where the population lives. Of the 62 files, 53 carry a count in
their decline message; **30 of them are at 30 cross-products or fewer**
(5 files at 3, 5 at 4, 2 at 5, 6 at 6, 3 at 7, 2 at 8, and singletons through
30), and 23 are far above (44 … 9,706). So the question the measurement has to
answer is no longer "does lifting the bound OOM" — on the big files it
demonstrably does not, because they never get in — but **"what happens to the
30 files that would now actually enter the relaxation?"**

### The 2026-06 OOM mechanism has an independent guard now

The introducing commit's blowup was the *refinement* loop chasing a
quadratically-escalating witness through the exact-rational simplex — the same
mechanism `threshold_1_lemmas`' own doc names for squares. Two commits since
address it directly: `7a323853e` (overflow-safe `Rational` across all engines)
and `nra.rs`'s `too_large_to_refine` (`REFINE_BOUND = 2^31`, checked at
`nra.rs:647` before a candidate is refined). Neither existed when the count
bound was written. That does not retire the bound by argument — it is why the
62-file A/B has to be run under `ulimit -v` and read for aborts, not just for
verdicts.


## Q2 — what the bound costs, on the 62 files it is charged with

Front door (`smtcomp_cli` = `solve_smtlib`), 24 s / 8 GiB via `scripts/mem-run.sh`,
`taskset -c 0-7`, arms interleaved per file, one binary
(`e115759a741e55f0`), s6. Load 1.03 before, 2.06 after (the only other load on
the host was one long-running 13% bash, checked in `ps`, not another lane's
cargo). 62 files × 2 arms = 124 runs.

| | arm A (bound 2) | arm B (unbounded) |
|---|---|---|
| sat | 0 | **2** |
| unsat | 0 | 0 |
| unsolved | 62 | 60 |
| disagreements with cvc5 | 0 | **0** |
| nonzero exit (memory abort / crash) | 0 | **0** |
| total wall | 583.2 s | 1,085.2 s (**+502.1**) |
| max peak RSS over the population | 3,315 MiB | 3,316 MiB |
| largest single-file RSS increase | — | +967 MiB |

**The bound protects wall time. It does not protect memory.** Not one of the 124
runs hit the 8 GiB address-space cap, and the population's peak RSS moved by
1 MiB. The 2026-06 rationale — "OOM-killed the host", "SIGABRT'd at the 64 GiB
cap" — no longer describes this code; `too_large_to_refine` and overflow-safe
`Rational` landed in between, and the online CDCL(T) route now refuses an
oversized abstraction before it can allocate.

Both new decides are `sat` and both agree with cvc5:
`20200911-Pine/1599121863243316000.smt2` (1.22 s → 5.60 s) and
`.../1599122159626470000.smt2` (1.24 s → 2.24 s). A third file from the same
family and the same cross-product count (`1599122164633784000.smt2`) was
admitted and burned the full budget — so the count does not even predict which
members of one family are reachable.

### Where the population actually sits

Splitting the 62 by what lifting the bound did to them (`|Δt| ≤ 0.2 s` means no
additional search happened at all):

| | files | what it means |
|---|---:|---|
| never gated by the bound | **25** | the abstraction is refused one layer down by `MAX_ONLINE_LRA_ATOMS`, same time, same memory |
| admitted, still undecided | **35** | the relaxation runs and does not close them — a capability gap, not an admission one |
| admitted and decided | **2** | the whole measured gain |

So the census's "62 files, one cause" is an over-attribution by construction:
on 25 of them the cross-product bound was the *message*, not the constraint.
That is not a defect in the census's method — it read the declining route's own
text, which is the best available signal — it is a defect in the message, and
the fix belongs in the engine (see the decline text in ADR-1751 §5).

### Q3 — the count is not the right instrument

Cost against threshold, computed from the same run (a threshold of *n* admits
every file whose census count is ≤ *n*):

| threshold | files admitted (of the 53 with a count) | added wall | new decides |
|---:|---:|---:|---:|
| 2 (today) | 0 | +0.0 s | 0 |
| 6 | 18 | +183.5 s | **2** |
| 10 | 25 | +283.4 s | 2 |
| 20 | 30 | +387.2 s | 2 |
| 34 | 34 | +468.9 s | 2 |
| 100 | 37 | +503.0 s | 2 |

Every threshold from 6 upward buys the *same* two decides while cost grows
monotonically. Picking a number off that curve would be fitting a constant to
two data points, and it would still leave the producer metering in a unit its
consumer does not use.

The conversion between the units is not a constant either. Measured by running
arm B on the large-count files and reading the atom count out of the LRA cap's
own message:

| cross-products | atoms | atoms per cross-product |
|---:|---:|---:|
| 96 | 2,562 | 26.7 |
| 396 | 10,620 | 26.8 |
| 638 | 8,356 | 13.1 |
| 771 | 23,385 | 30.3 |

A 2.3× spread. Any single conversion factor is wrong by that much on real
input, which is why the decision (ADR-1751) **counts** the atoms of the system
about to be handed over rather than scaling the cross-product count.

Only 4 of the 19 large-count files reported an atom count; the other 15 declined
through a different route under `explain_corpus`'s flat view or ran out its
external bound before printing one. Four points is a thin population and the
2.3× spread is what it establishes — that no single factor is safe — not a
precise ratio.

### A correction to this document's own earlier draft

The first pass at this section said "28 of the 62" were never gated, read off a
sorted delta table by eye. Computed with the stated rule (`|Δt| ≤ 0.2 s`) it is
**25**. The figure appears as 28 in the message of commit `07b8da6ca`, which is
history and stays as written; 25 is the number, and it is what the source
comments, the ADR and this table now carry.
