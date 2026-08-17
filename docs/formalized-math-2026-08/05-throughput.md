# 05 — The construction plan

**What we are building:** a mathematical library that the system extends itself,
axiom-free, in parallel, at a rate we have measured.

This supersedes the README's original framing. That framing asked how we stack
against an existing library. Wrong question. The right one is: **given a solver,
a CAS, a kernel and an evidence ledger in one process, what can we construct
that a library written by hand cannot be?**

## The rate, measured

One lane, one ordinary working day, on `nat_prelude.rs`:

```
2026-08-13 21:22     33 proved theorems
2026-08-14 09:05    106 proved theorems
                    +73 in 11 h 43 min
```

**6.2 theorems/hour/lane — ~149/day/lane, sustained**, while also writing one
ADR per theorem and updating tests.

| lanes | theorems/day |
|---:|---:|
| 1 | 149 |
| 10 | 1,490 |
| 30 | 4,470 |
| 100 | 14,900 |

### Re-measured 2026-08-17: the burst is real, "sustained" is not

The table above extrapolates from one 11 h 43 min window. Checking the same
metric — `nat_theorem_inventory`'s count, the one that produced 33 and 106 —
three days later:

```
2026-08-14 09:05    106 proved theorems   (this document's second datapoint)
2026-08-17 14:00    139 proved theorems
                    +33 in 76.9 h = 3.20 days
```

**10.3 theorems/day/lane realized, against 149/day/lane projected — 14× lower.**

Read that carefully, because the obvious reading is the wrong one. It is *not*
that the 6.2/hour measurement was wrong: a lane that spends a day on
`nat_prelude.rs` plausibly still does that. What fails is the word **sustained**,
and the reason is visible in what the three intervening days actually contain —
solver routes, evidence gates, CI repairs, a false certification claim found and
reverted, two aggregate gates that had stopped checking things. Theorem
production is not what a lane spends its time on, and the table silently assumes
it is.

So the honest form of the projection is not `N lanes × 149/day`. It is
`N lanes × 149/day × f`, where `f` is the fraction of lane-time spent proving,
and `f ≈ 0.07` over the only multi-day window anyone has measured. A roadmap
item justified by "at 149/day/lane, ℚ is no longer a close call" is being
justified by `f = 1`.

Two consequences, neither of which is "give up on the rate":

- **The leverage is in `f`, not in the burst rate.** Doubling 6.2/hour is hard;
  doubling the share of lane-time that reaches a theorem is a scheduling and
  tooling question, and the parallel-prelude change this document already
  proposes is the right kind of answer — it raises `f` by removing the serial
  assembler, not by proving faster.
- **Anything downstream of the table should be re-derived.** The `N × 149/day`
  figures are an upper bound reachable only if lanes do nothing else, and should
  be labelled that way wherever they are used to decide priority.

Measured with the metric this document already uses; the 33 and 106 datapoints
are taken from it rather than re-derived, so the comparison inherits whatever
they were.

And every one reports **no axioms**. That is the artifact: not volume, but volume
on a trusted base of zero.

## The loop only this architecture can run

A hand-written library is a one-way pipeline: humans write proofs, a kernel
checks them. **We have a cycle**, and it is the thing to build:

```
        library (proved ℕ, ℤ, …)
             │  gives the solver facts to reason with
             ▼
        solver (30 logics, CAS, quantifiers)
             │  decides goals the library needs
             ▼
        reconstruction  →  kernel term  →  admitted, axiom-free
             │  becomes a library theorem
             └──────────────────────────────┐
                                            │
        DAG (1,567 concepts, 2,254 edges) ──┘  says what to prove next
             │  and the claim ledger records what was proved, re-derivably
```

Every arrow already exists in some form. On 2026-08-14: the solver produced
refutations, reconstruction turned them into kernel terms at **4.57 M LRAT
hints**, Lean's own kernel accepted the result from an empty environment, and
the claim ledger re-derived 103 claims with zero errors. **The cycle has been
closed once, end to end.** What it has never been is *automatic*.

That is the construction: **close the loop and turn the crank.**

## What to build, in order

### C1 — Shard the library so lanes compose instead of collide

`nat_prelude.rs` is one file of 9,969 lines with one writer. That is the entire
throughput ceiling: every parallel lane on 2026-08-14 had to route *around* it.

One module per topic — order, division, gcd, congruence, finite sums — each with
its own tests, composed by a prelude assembler. **This converts a serial 149/day
into `N × 149/day`** and is the highest-leverage change in the whole roadmap.

### C2 — Let the solver write library theorems

The reconstruction path already turns a solver refutation into a kernel-checked
term. Point it at the library: for a goal in the DAG, dispatch to the solver,
reconstruct, admit, record. Where it succeeds the library grows without a human
in the loop; where it declines, that decline is a **ranked feature request** for
the solver.

This is the arrow no hand-written library has, and it is why the integration
matters rather than being a slogan.

### C3 — Drive from the DAG

1,567 concepts, 2,254 prerequisite edges, depth 19. That is a build order, and a
scheduler that reads it gets near-linear speedup because lanes stop colliding on
prerequisites. It also makes progress *measurable against mathematics* rather
than against a commit count.

### C4 — Budget the kernel for the resulting scale, now

At `N × 149/day` these stop being roadmap items and become load-bearing within
weeks: the monotone arena, the per-query rebuild (**26 ms vs 6.6 µs cached,
~4,000×**), and the O(n³) permutation prover. The evidence that they yield: in
single sessions on one day, proof-checking memory improved **5.4×**,
reconstruction arena **5.6×** with a **55×** speedup, and the reconstruction
frontier moved **86×**.

### C5 — Keep `#print axioms` as the gate

Per module, published per release. Throughput without it is just volume; with it,
every theorem added is a theorem on a zero-axiom base — which is the property
that makes this library *ours* rather than a re-derivation of somebody else's.

## Where import fits

As **cross-validation and superstructure**, not as the strategy. Admitting a
foreign library into an independent kernel is a measurement we can nearly
uniquely produce — and it tells us where our own construction diverges from the
world's. Useful, and secondary.

Two corrections from the first real import run, 2026-08-15
([`01-collect.md`](01-collect.md)):

- **We are not the only independent kernel that reads `lean4export`.**
  `ammkrn/nanoda_lib` is a Rust checker that consumes the same output and was
  pushed 2026-08-12. `digama0/lean4lean` is independently active. The claim to
  keep is narrower and still worth having: a second kernel, in a different
  language, with a fact ledger that records the disagreement.
- **Import currently supplies less than this section assumes.** 13 of 40
  well-known `Init`/`Std` theorems import; the rest are declined by our own
  kernel's definitional equality. Superstructure via import is gated on
  `brecOn`/`below` reduction, so the boundary below moves in favour of building
  by default rather than by argument.

The boundary in [`04-implement.md`](04-implement.md) still holds and moves in
favour of building: at 149/day/lane, ℚ is no longer a close call.

## The measure of success

Not theorem count. **Theorems the system proved without a human writing the
proof**, on a zero-axiom base, in the order the DAG asked for.

That number is currently zero. C2 makes it positive, and everything else here
makes it grow.
