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

As **cross-validation and superstructure**, not as the strategy. We hold the only
independent kernel that reads `lean4export`, so admitting a foreign library is a
measurement we can uniquely produce — and it tells us where our own construction
diverges from the world's. Useful, and secondary.

The boundary in [`04-implement.md`](04-implement.md) still holds and moves in
favour of building: at 149/day/lane, ℚ is no longer a close call.

## The measure of success

Not theorem count. **Theorems the system proved without a human writing the
proof**, on a zero-axiom base, in the order the DAG asked for.

That number is currently zero. C2 makes it positive, and everything else here
makes it grow.
