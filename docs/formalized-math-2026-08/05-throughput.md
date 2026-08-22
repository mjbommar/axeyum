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

### Re-measured 2026-08-19: the counter is flat, and the counter is now the wrong instrument

Same metric, run again — `cargo run --release -p axeyum-lean-kernel --example
nat_theorem_inventory`, 2026-08-19 12:49 EDT:

```
2026-08-14 09:05    106 proved theorems
2026-08-17 14:00    139 proved theorems
2026-08-19 12:49    139 proved theorems   <== unchanged, +0 in ~2.1 days
                    +33 over 5.16 days = 6.4 theorems/day/lane
```

So `f` did not recover: over the longer window the realized rate is **6.4/day/lane
against 149 projected — 23x lower**, and `f ≈ 0.043` rather than 0.07. The 2026-08-17
reading was, if anything, generous.

**But do not read the flat 139 as "nothing was proved," and this is the more
important correction.** `nat_theorem_inventory` counts one prelude, and production
moved off it. Measured the same day, on the same host:

```
Int                57 derived theorems, 57 with an EMPTY axiom footprint, 0 still asserted
                     (`--example int_theorem_inventory`)
trusted surface    complex 0 · creal 0 · integer 0 · logic 0 · nat 0 · rat 0 · string 0 · real 30
                     (`--example nat_axiom_inventory -- --include-constructed`, exit 0)
```

ℚ, the constructed ℝ (`creal`) and ℂ did not exist when this document's rate was
first measured; they do now, and none of them moves the Nat counter. A rate claim
that leans on a single-prelude counter is therefore **not falsifiable in either
direction** at this point: the counter cannot rise when the work is elsewhere, and
a fall would not mean a regression.

The honest statement is not a rate. It is: **nobody can currently measure this
project's theorem-production rate, because no tool counts theorems across preludes,
and the one that counts them in `nat_prelude` has been superseded by where the work
went.** The `N × 149/day` table above stands as what it always was — an upper bound
at `f = 1` — and until a cross-prelude counter exists, no number in this section
should be used to size a roadmap item.

### Resolved 2026-08-22: the instrument now exists, and the answer is 418

The paragraph above named a missing instrument, and it stayed missing for three
more days. It exists now:

```sh
python3 scripts/gen-theorem-production-ledger.py --check
cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory \
  -- --include-constructed
```

Measured 2026-08-22 over all eight preludes:

```text
prelude   cumulative  originated  axiom-free
logic              2           2           2
nat              139         137         139
axreal             2           0           2
integer          201          62         201
rat              320         119         320
string             6           4           6
creal            390          70         390
complex          414          24         414
distinct         418         418         418      axiom-bearing 0
```

**418 distinct theorems, every one with an empty axiom footprint.** The flat 139
was exactly what this document said it was — one prelude's counter, blind to
where the work went. ℚ contributed 119, the constructed ℝ 70, ℤ 62, ℂ 24.

Two cautions the ledger enforces rather than states. The cumulative column
**does not sum** — preludes nest, so `rat`'s 320 already contains Nat and Int,
and adding the column gives 1,474 for a 418-theorem library. And the generator
fails if the `originated` column does not sum to the distinct total, because if
that attribution is wrong then every per-prelude production number under it is
wrong with it.

Cross-checked against the two instruments that already existed, on the preludes
they share: `nat_theorem_inventory` reports 139, matching exactly.
`int_theorem_inventory` reports 60 against this ledger's 62 — the difference is
`Rat.den_pos` and `Rat.reduced`, two ℚ invariants that `build_int_prelude`
declares and that a count filtered to `Int.*` cannot see. Both are right for
their own question.

**What this still does not measure is the rate, and deliberately so.** A count
is not a rate, and this ledger has one datapoint. More importantly it counts
theorems, not *autonomous* theorems — the `N × 149/day` table above remains an
upper bound at `f = 1`, and the metric this programme actually claims is
"results the system established with nobody writing the proof." Splitting 418 by
provenance is the next increment of P1 in
[`docs/autogenesis/226-production-measurement-and-general-producer-plan.md`](../autogenesis/226-production-measurement-and-general-producer-plan.md).
Until that lands, **418 is a library size, not a production rate**, and should
not be used to size a roadmap item either.

Nothing measured on 2026-08-18/19 moves the figures in **C4** below (the 26 ms /
6.6 µs rebuild, the 5.4x / 5.6x / 55x / 86x single-session results); those were not
re-derived here and are cited as they stood.

And every one still reports **no axioms** — and that claim is now measured over the
whole trusted surface rather than asserted. Read from the kernel on 2026-08-19, the
eight preludes carry `axiom=0 opaque=0 quotient=0` apart from `real`, which is the
**axiomatized** ℝ package at 30 and is exactly what the constructed `creal` carrier
exists to replace. That is the artifact: not volume, but volume on a trusted base of
zero.

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

> **Correction, 2026-08-18.** "Lean's own kernel accepted the result" was true
> and narrower than it read. Emission is **reachability driven**: what Lean saw
> was the closure of one refutation, not the carrier. When ADR-0511's lane
> measured it, a refutation reached **343 of the 465** declarations in the
> constructed-real context, so **122 had never been handed to any Lean at all**
> — and the first time anything pointed Lean at the whole set, four were
> refused. The three explanations were distinguishable and the answer is the
> third: see [`03-integrate.md`](03-integrate.md#lean-has-two-checkers-and-they-disagree)
> and [ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md).
> Our kernel is **not** more permissive than Lean's; Lean's *kernel* takes all
> 470 declarations the carrier holds today. Its *elaborator* does not.

That is the construction: **close the loop and turn the crank.**

## What to build, in order

### C1 — Shard the library so lanes compose instead of collide

`nat_prelude.rs` is one file of 9,969 lines with one writer. That is the entire
throughput ceiling: every parallel lane on 2026-08-14 had to route *around* it.

One module per topic — order, division, gcd, congruence, finite sums — each with
its own tests, composed by a prelude assembler. **This converts a serial 149/day
into `N × 149/day`** and is the highest-leverage change in the whole roadmap.

> **C1 is DONE, and its promise did not arrive. Recorded 2026-08-19, because a
> roadmap item that landed and did not deliver is worth more than one that is
> still pending.** `nat_prelude.rs` is **845** lines today and the content lives
> in eleven topic modules under `src/nat_prelude/` — `order`, `division`, `gcd`,
> `divisibility`, `modular`, `primes`, `algebra`, `bezout`, `defs`, `ops`,
> `helpers` — almost exactly the split proposed above. The first two splits
> landed on **2026-08-14** (`bc094a3dd`, `55a366a1b`), the same day as the burst
> this section extrapolates from.
>
> Five days of sharded, collision-free library then produced **+33 theorems**,
> and none in the last ~2.1 days. So the single-file lock was **not** the
> binding constraint on `f`, or removing it was not sufficient. The `N × 149/day`
> claim above should now be read as **falsified by its own remedy**, not as
> pending. What the shard did buy is real and different: lanes stopped colliding
> on one file, which is a multi-agent-hygiene win. It was not a throughput win,
> and the two were conflated here.
>
> The open question this leaves is the useful one: **if not the file lock, what
> is `f` actually spent on?** Nobody has measured that, and until somebody does,
> C1's successor cannot be chosen on evidence.

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

The boundary in [`04-implement.md`](04-implement.md) still holds, but **not for
the reason given here.** "At 149/day/lane, ℚ is no longer a close call" is
exactly the `f = 1` argument this document's own re-measurement retired, and it
has been overtaken by events besides: ℚ was **built**, not imported, and reads
`rat: axiom=0 opaque=0 quotient=0` from the kernel on 2026-08-19 — as do the
constructed ℝ and ℂ that followed it. The boundary now moves in favour of
building on the *evidence* argument (an imported theorem carries its source's
trust) rather than on a rate.

## The measure of success

Not theorem count. **Theorems the system proved without a human writing the
proof**, on a zero-axiom base, in the order the DAG asked for.

### It is no longer zero — corrected 2026-08-19

This section read "that number is currently zero" until 2026-08-19. It was true
when written (2026-08-17, commit `56f4c2b23`) and was falsified the next day, by
a mechanism this document did not anticipate. Three facts now carry
`kind: kernel-term`, `check_status: checked` and an empty axiom footprint where
no Lean proof term or tactic script was written by hand:

| fact | statement | admitted | how |
|---|---|---|---|
| `F:ml430-nat-ascfactorial-zero-fd183202` | `Nat.ascFactorial_zero` | 2026-08-18 | bounded reflexivity producer |
| `F:ml430-nat-descfactorial-zero-966b01df` | `Nat.descFactorial_zero` | 2026-08-19 | bounded reflexivity producer |
| `F:ml430-nat-fib-add-two-b86e0c82` | `Nat.fib_add_two` | 2026-08-19 | target-specific term program |

Re-derived here rather than read off the ledger: all three
`scripts/check-autogenesis-fact-operation.py --fact …` runs exit 0 on 2026-08-19
(`AUTOGENESIS_FACT_OPERATION_OK|…|label=…-axiom-free`).

**Three qualifications, none of them optional**, because the difference between
"3" and what this section actually asks for is most of the distance:

1. **The first two are `Eq.refl`.** The producer
   (`crates/axeyum-lean-import/examples/statement_reflexivity_support/`) is
   target-independent and was run blind over 138 candidate rows; it emitted 4
   nodes for **2** of them. That is a real machine result and a very small one.
2. **`Nat.fib_add_two` does not meet this programme's own autonomy bar.** Its
   term was built by a program written for that goal
   (`examples/nat_fib_iterate_recurrence.rs`, `MAX_PLAN_TEMPLATES = 2`) and
   repaired by hand across two failed runs (ADR-0496 → ADR-0500 → ADR-0502).
   `docs/autogenesis/04-metrics-and-evaluation.md` defines *autonomous* as "no
   human wrote, repaired, or selected the credited proof after launch"; this
   fails "wrote" and "repaired". What **is** machine-driven for all three is
   selection, checking and crash-safe admission.
3. **C2 has still produced zero.** Nothing above came from "dispatch a DAG goal
   to the solver, reconstruct the refutation, admit". The only autogenesis fact
   on a solver route (`F:no-integer-square-is-minus-one`) is a certificate with a
   non-empty trust footprint and says so in its own evidence notes.

So: C2 makes the *solver* arrow positive and is still ahead of us. The number
this section names became positive by a different and smaller route, and the
distinction is worth more than the count.
