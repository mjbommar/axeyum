# Keeping a late verdict, and making the deadline reachable: what each is worth

Roadmap item **3.9**, the build follow-on to
[`why-43-satisfiable-qfbv-miss-2026-09-10.md`](why-43-satisfiable-qfbv-miss-2026-09-10.md)
(lane B1). Lane D1, 2026-09-10, on `c35941f9b`. The safety argument that gates
the change is [`late-result-keep-safety-2026-09-10.md`](late-result-keep-safety-2026-09-10.md);
the decision is [ADR-1906](../09-decisions/adr-1906-a-decided-verdict-is-kept-regardless-of-the-wall-clock.md).

B1 recommended two fixes and wrote that "they compose; neither subsumes the
other." **On decided counts at a fixed budget that is not what they do.** They
are a trade, and the shape of the trade is the main finding here.

## The headline table

32 instances (the committed width-graduated corpus, 15 `addcmp` + 14 `mul`, plus
`pspace/ndist.b.20000`, `pspace/ndist.b.24491` and `Sage2/bench_15255` from the
NAS). Cold `SatBvBackend` arm, release build, prebuilt binary, one file per
process under `timeout -s KILL 400` and `ulimit -v`. `uptime` read around every
run; load average 1.9-6.7 throughout, and the load is called out below wherever
a number depends on it.

| build | budget | decided | gained | lost | worst wall clock | worst overrun |
|---|---:|---:|---:|---:|---:|---:|
| baseline (`c35941f9b`) | 10 s | **22 / 32** | — | — | 83.5 s | **8.35x** |
| + keep | 10 s | **30 / 32** | +8 | **0** | 77.3 s | 7.73x |
| + keep + cadence | 10 s | **22 / 32** | 0 | **0** | 10.6 s | **1.06x** |
| + keep + cadence | 90 s | **30 / 32** | +8 | **0** | 77.5 s | **within budget** |

Read the last two rows together. The cadence fix does not lose anything the
baseline had — the comparison against baseline is 0 gained, **0 lost**. What it
gives back is the budget: the worst overrun falls from **8.35x to 1.06x**. And
the eight instances the keep gained are still there at any budget the caller
actually intends to pay; at 90 s all eight decide `sat` and all eight finish
*inside* the budget.

The two instances that never decide in any row are `bvwide-mul-w02048` and
`bvwide-mul-w04096`. Those are B1's finding 4 — the `ABSOLUTE_CLAUSE_CEILING`
estimator refusing an instance it is 2.83x pessimistic about — and nothing in
this lane touches them.

## The trade, stated plainly

- **The keep alone** turns 8 `unknown`s into `sat`, and leaves the budget
  meaningless: those answers still arrive at 11-77 s against a 10 s budget.
- **The cadence alone** would make the budget mean something and return the same
  8 as honest `unknown`s.
- **Together**, at a fixed nominal budget the counts look like the baseline —
  because the searches now stop when they were told to. The gain is not in the
  count column; it is that the wall clock finally matches the promise, and that
  the count comes back the moment the budget is raised to something the search
  can finish in.

So B1's "they compose" is right about the defects and wrong about the arithmetic.
Anyone quoting "+8 decided" for this item must say which build and which budget,
because the same change set gives +8 at 90 s and +0 at 10 s.

## What the keep is still worth after the cadence lands

Not nothing, and the reason is structural: **any cadence has a last check before
the end.** A search that finishes within one cadence window of the deadline
completes and keeps its answer.

That window is *narrow* on the family B1 measured — those searches run many
loop iterations, so the checks are dense. Measured, `+ keep + cadence` at a
10 s budget:

| instance | baseline returns at | with cadence returns at | residual overrun |
|---|---:|---:|---:|
| `addcmp-w12288` | 11,100 ms | 10,075 ms | 75 ms |
| `addcmp-w16384` | 18,966 ms | 10,085 ms | 85 ms |
| `addcmp-w20000` | 37,427 ms | 10,049 ms | 49 ms |
| `addcmp-w24576` | 43,761 ms | 10,051 ms | 51 ms |
| `addcmp-w32768` | 83,521 ms | 10,037 ms | 37 ms |
| `ndist.b.20000` | 30,645 ms | 10,084 ms | 84 ms |
| `ndist.b.24491` | 43,833 ms | 10,069 ms | 69 ms |
| `Sage2/bench_15255` | 24,771 ms | 10,579 ms | 579 ms |

**But the window is wide on the opposite shape, and that shape is in the same
corpus.** A search that runs FEWER than the 1,024 iterations the cadence needs is
never checked at all, so it cannot be interrupted no matter how long it takes.
The `bvwide-mul` family is exactly that: encoding-bound with a short search
(B1 measured 47.4% of its wall clock in bit-blast + CNF at width 1,024).
Measured directly, on the shipped `+ keep + cadence` build:

| instance | budget | verdict | returns at | encode | search |
|---|---:|---|---:|---:|---:|
| `bvwide-mul-w00512` | 700 ms | **sat** | **1,034 ms** | 551 ms | 441 ms |
| `bvwide-mul-w00768` | 1,000 ms | unknown | 1,459 ms | 1,402 ms | 0 ms |
| `bvwide-mul-w01024` | 2,000 ms | unknown | 2,748 ms | 2,644 ms | 0 ms |

The first row is the keep doing its job with the cadence in place: the search ran
441 ms past a budget that had 149 ms left, was never interrupted because it takes
under 1,024 iterations, and returned a replay-checked `sat` instead of throwing
it away. The other two rows are a different gate — the *pre*-solve one — firing
because the encoding alone exhausted the budget, which is correct behaviour and
is untouched.

This is also why the regression test for the keep uses a wide `bvmul` and not the
`ndist.b` shape that motivated it: after the cadence fix, `ndist.b` can no longer
be made to produce a late result on demand, and a test that cannot reach its
subject is not a test.

## Where the answer was being thrown away — it was not one place

B1 named `sat_bv_backend.rs:327`. **Fixing only that would have been inert on the
shipping front door.** `check_with_all_theories` (`combined.rs`) is the funnel
every QF_BV arm in `auto.rs` goes through, and it carried the same defect in a
worse form — it did not inspect the result before discarding it:

```rust
let result = backend.check(arena, int_blast.assertions(), &backend_config)?;
if past_deadline(deadline) {
    return Ok(timeout("combined-theory timeout after scalar backend"));
}
```

Four more gates sat below that one, on the path a kept `Sat` has to walk: three
model projections and one **per-assertion** check inside the replay loop. Any one
of them left in place would have neutered the fix — a kept `sat` reaches the
replay loop and fails its very first clock read. Those four are deleted rather
than made unreachable; a guard that cannot fire is not a safety mechanism.

Counting them, the answer was discarded at **six** points on one route, and the
measurement that found the class named one of them. The general shape worth
carrying forward: *a gate you can name is rarely the only instance of itself —
search for the SHAPE (a clock read immediately after a call that produced a
result), not the line.* Doing that across `crates/axeyum-solver/src` found all
six, and confirmed that the five `auto.rs` gates with similar-looking
`"timeout after X"` reasons are **not** the same shape — each fires after a route
has already *declined*, with no verdict in hand, which is the correct use of a
deadline.

## The decision was already taken once, and not propagated

`dispatch_reduced` (`auto.rs:2382`) — the preprocessed-dispatch route, and
`preprocess` defaults **on** — already carried this exact fix, in this exact
shape, with its own measurement:

> *"A DEFINITE verdict (Sat/Unsat) from the reduced solve is valid regardless of
> the wall clock — the deadline is a resource budget, not a correctness gate. …
> measured, `nia-bounded-blast` decides bounded nonlinear SATs like
> `nia-pythagorean` a hair past the budget, and the old unconditional
> `past_deadline` gate below turned that decided `sat` into `unknown`."*

So this lane did not discover a principle. It found that an accepted principle
had been applied at one layer and left unapplied at the two below it, for long
enough that a separate measurement had to rediscover the consequence from
outside. That is the argument for ADR-1906 existing at all: the reasoning was
already written down, in a comment, on one of the three sites that needed it.

## The cadence fix had a precedent in its own file, too

`proof_sat.rs` already ran an iteration-cadence deadline check — but only under
`T::HAS_THEORY`, with this rationale:

> *"The Boolean core reads the clock on a conflict cadence, which a theory that
> propagates without ever conflicting never reaches. Read it on an iteration
> cadence too, at the same interval, so a CDCL(T) search is deadline-bounded on
> every path and not only on the conflicting one."*

The reasoning is correct and its scope was wrong. A **Boolean** search that
propagates without conflicting never reaches the conflict cadence either, and
that is not a corner case — B1 measured it as the whole `pspace/ndist.b` family
plus a `Sage2` file. The fix is to hoist the check out of the `HAS_THEORY` block;
the theory path keeps its separate `THEORY_STEP_BUDGET` guard and loses its now
duplicate clock read.

Determinism is unchanged in kind. The cadence remains a **count of search
events**, never a clock poll rate, so the trajectory up to the stopping point is
still identical to the unbounded run and only *whether* the search stops is
time-dependent — the exact property `DEADLINE_CHECK_INTERVAL` was chosen to
protect. On the keep's side determinism strictly improves: it removes one of the
two points at which the wall clock could change a verdict (see the safety note,
§5).

## Gates, and the mutation control

- `corpus_regression` 2/2, `qfbv_width_frontier` 3/3, `axeyum-solver --lib
  --features full` **1,693/1,693**, `axeyum-cnf --lib` 618/618, `axeyum-bv
  --lib` 34/34. Nonzero counts confirmed on each.
- `progress_frontier` **12/12**, `taskset -c 0-7`, `--test-threads=1`, and all
  five families report `comparable: true, ratchetable: true, enforced: true`
  at load 2.26-3.82 — an **enforced** pass, not an advisory one, so it does rule
  out a frontier regression. Frontiers: `bv_reduction` 36, `lia_cuts` 35,
  `nia_unsat` 40, `nra_degree` 40, `string_bound` 40. Artifacts restored, not
  committed.
- clippy `-D warnings` on both changed crates, exit code read directly: **0**.
  `cargo fmt --all --check`: **0**.

The regression suite is `crates/axeyum-solver/tests/late_result_keep.rs`, 4
tests. **The two gates are covered by different mechanisms on purpose** — a
calibrated real solve for the backend gate, and a stub `SolverBackend` that
decides correctly and then sleeps past the caller's budget for the combined gate.
A shared mechanism is how one test ends up standing in for two guards, which is
precisely the failure this item's own history warns about.

Mutation control, run in this lane's own worktree with the source restored and
re-verified green afterwards:

| mutant (restores the pre-fix behaviour) | tests killed |
|---|---|
| backend gate made unconditional again | exactly `…_survives_the_backend_gate` |
| combined post-backend gate made unconditional again | exactly `…_survives_the_combined_theory_gate` |
| one DELETED replay-loop gate put back | exactly `…_survives_the_combined_theory_gate` |

Three guards, three single kills, and the two *gates* die to **different** tests
— which is the property that says the second route is not riding on the first's
coverage. The control asserts the suite ran 4 tests before believing any of
this, so a suite that compiled to nothing cannot report a pass.

Two controls in the suite guard the other direction: an undecided search is still
`unknown` (`resource_limit = 0`), and an already-expired budget still refuses to
decide (`timeout = 0` → `UnknownKind::Timeout`). Without them "keep the result"
and "never time out" would be indistinguishable.

## What I did not measure

- **The front-door (`auto`) arm.** Everything above is the cold backend arm. B1
  measured the front door separately and found it flips on the same instances;
  the `combined.rs` fix is what makes the front door follow, and its regression
  test is the stub-backend one rather than a corpus run. **A front-door corpus
  sweep did not run here.**
- **The other 33 of B1's 42 named misses.** They are 3-90 MB; this lane inherited
  B1's 9-instance subset and did not extend it.
- **`bench-results/parity-losses-20260908/QF_BV.txt`.** Its six entries are NAS
  paths in `2017-BuchwaldFried`, `Sage2`, `asp`, `bruttomesso` (x2) and `stp`.
  They were **not** run: the population this item is about is the satisfiable
  miss class, and the parity-loss list is a different (and differently
  constructed) set. Whether the keep or the cadence moves any of those six is
  **unmeasured**, and "did not run" is the honest label, not an inference from
  the width-graduated result.
- **Any head-to-head.** No z3, cvc5 or Bitwuzla was run.
- **Whether `DEADLINE_CHECK_INTERVAL = 1_024` is the right iteration cadence.**
  It is inherited from the conflict cadence because that is the value the theory
  path already used, and it is measured to be *sufficient* (residual overrun
  37-579 ms on a 10 s budget). It is not measured to be optimal, and the residual
  579 ms on `Sage2/bench_15255` is 15x the best of the others — a per-iteration
  cost spread that nobody has looked at.
- **The incremental façade under this change.** It does not reach either gate
  (established by reading, in the safety note §3), and no warm-session test was
  added because there is no behaviour to test there.

## Reproducing

```sh
cargo build --release -p axeyum-bench --example qfbv_sat_attribution
B=target/release/examples/qfbv_sat_attribution
G=corpus/public-curated/synthetic/QF_BV/width-graduated

# the headline table: the whole width-graduated corpus at one budget
for f in "$G"/bvwide-*.smt2; do "$B" "$f" 10000 backend; done

# the eight the keep gained, at a budget they can finish in
for w in 12288 16384 20000 24576 32768; do "$B" "$G/bvwide-addcmp-w0$w.smt2" 90000 backend; done

# the keep still firing WITH the cadence in place (search under 1,024 iterations)
"$B" "$G/bvwide-mul-w00512.smt2" 700 backend
```

Run each under `timeout -s KILL` and `ulimit -v`, and read `uptime` around the
set: the verdicts are stable but every millisecond in the tables above is
load-sensitive, and the instances that sit within a factor of two of the budget
can move across it under load.
