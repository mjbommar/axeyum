# Refactor and cleanup plan — August 2026

> **This is the engineering strand.** Its companion is
> [`docs/mathematics-2026-08/`](../mathematics-2026-08/README.md), which asks what
> mathematics the system can do rather than where the code is untidy. Read that
> one if you want the ceiling; this one is the floor.
>
> A third strand,
> [`docs/formalized-math-2026-08/`](../formalized-math-2026-08/README.md),
> covers collecting and integrating the ~10 M lines of formalized mathematics
> that already exist outside this project.
>
> **Before taking any item, read [`00-parallel-work.md`](00-parallel-work.md).**
> A second lane owns `crates/axeyum-lean-kernel/` and two shared append points,
> and it re-orders both strands.

A plan grounded in measurement, written after a twelve-hour multi-agent campaign
that pointed the whole stack at open mathematics and recorded where it bent.
Nothing here is an impression: every number was measured on 2026-08-14 and the
command that produced it is given.

This folder does **not** restate the architecture. Those documents exist and are
the input to this one:

- [`docs/internals/architecture.md`](../internals/architecture.md) — the layer diagram
- [`docs/research/03-architecture/system-architecture.md`](../research/03-architecture/system-architecture.md)
- [`docs/research/08-planning/foundational-dag.md`](../research/08-planning/foundational-dag.md) — the dependency *contract*, which says what must exist before a layer may depend on another

## The measured baseline

| fact | measurement |
|---|---|
| workspace size | **476,449** lines of Rust across 23 crates |
| `axeyum-solver` | **236,275 lines — 51% of the workspace**, 164 top-level modules, depends on 13 of 22 other crates |
| solver public API | **267 `pub use` re-exports** over 7 direct `pub` items — a façade, not a tangle |
| solver subsystems | quantifiers 38 modules · arithmetic 20 · arrays/BV 18 · UF 8 · strings 7 · dispatch 5 |
| tests | 278 integration files + 83 in-source `#[cfg(test)]` modules |
| library | `nat_prelude` **119 proved / 0 trusted**; `int_prelude` **52 proved / 1 axiom**; `arith_prelude` **0 proved / 30 axioms — but see below: it is not an axiomatisation of ℝ** |
| library provenance | counts from `nat_axiom_inventory` over the FULL trusted surface (`Axiom`/`Opaque`/`Quotient`), not from counting `Declaration::Axiom` literals in source — the literal count said `3` where the real figure was `34` |
| library growth | `nat_prelude.rs` 3,856 → **9,969 lines in 60 commits**, one session |
| architecture doc | 82 lines, documents **11 of 23 crates**; omits `axeyum-cas` (47,472 lines, the second-largest crate) |
| decision records | **455 ADRs** |

## The findings this plan is built on

The first four are what the plan was written from; 5–8 were measured while
executing it, and each one corrected something this folder already asserted.

**1. ℤ and ℝ are one hole running through every layer at once.** Five agents in
five crates hit it independently and each reported it as a local gap. It is not
five gaps. → [`01-int-real-keystone.md`](01-int-real-keystone.md)

**2. The components are adjacent, not composed.** Two real-algebra
implementations, two colouring encoders (one citing a parity test that does not
exist), and a Lean kernel rebuilt from scratch on every query at six call sites.
If the product is "an SMT solver, a CAS, and a proof-assistant kernel in one
process", then the *composition* is the product. →
[`02-composition.md`](02-composition.md)

**3. The god-crate is decomposable, and its seams are already visible.** 51% of
the workspace in one crate — but behind a 267-entry re-export façade, with six
clean subsystem groupings and a feature flag that already separates the minimal
deployment from the full one. →
[`03-solver-decomposition.md`](03-solver-decomposition.md)

**4. Gates report success over work they do not do, and documents assert what
the code does not.** Three gate-scope holes and one whole class of
prose-only guards were found in a single day — none by running the gates. →
[`04-gates-and-truth.md`](04-gates-and-truth.md)

**5. Proof consumption is nearly closed, and this folder was quoting the
pre-fix number.** ADR-0426 took backward checking from 8.00× the proof's size to
**1.49×** — verdicts identical, and faster — which moved the 18.9 GB certificate
from uncheckable anywhere in the fleet to checkable on s0/s4. The remaining wall
is not I/O at all: the Lean *proof-term* route peaks at 96.6 GB on a 628 MB
certificate, so large combinatorial results have to reach Lean by reflection. →
[`05-proof-consumption.md`](05-proof-consumption.md)


**6. The `Real` prelude is not ℝ, and `Quot.sound` does not exist here.** Two
measurements taken before writing any code refuted the premise of item `01`'s
second half. The 30 `arith_prelude` declarations are 8 carrier/operation
constants plus 22 laws, with **no `inv`, no `div`, no completeness, no
Archimedean axiom, and not even totality** — an ordered commutative ring with 1,
every one of whose laws is true of ℤ. Separately, this kernel's quotient package
is `PACKAGE_LEN = 4` (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) with **no
`Quot.sound` variant at all**, so a Cauchy-sequence ℝ is not expensive here, it
is *inexpressible*. Three places in the codebase said the quotient route "merely
costs `Quot.sound`"; they were describing Lean's package, not ours, and the
measurement is now a test. →
[`01-int-real-keystone.md`](01-int-real-keystone.md), ADR-0456


**7. Where work goes was never written down, and every element of it was learned
by losing something.** A 2¼-hour solve, a 90-minute test sweep and two watchers
died to `systemd-oomd` killing a cgroup under *pressure*; the recommended scratch
disk was root-owned and unwritable; the NFS mount was probed one directory too
high, so `df` answered a different question confidently. →
[`06-scratch-and-snapshots.md`](06-scratch-and-snapshots.md)


**8. Finding 4 reaches the fact ledger: a quarter of its checkers cannot fail.**
The ledger's whole promise is that a status is worth what its checker returns.
Audited 2026-08-15: **40 of 162 checker runs, across 36 settled facts, exit 0 on
completion alone** — nothing in the command makes the exit status depend on what
the run found.

> **RE-MEASURED 2026-08-16 (lane `ledger-integrity`): remediated, and this
> paragraph was steering lanes at a number that no longer holds.** The ledger now
> carries **177 checker runs over settled facts, and every one has an exit status
> that depends on its finding.** Verified per command family by *running* the
> checker with input that should make it fail, not by reading the command:
> `check-imported-fact-lean-axioms.sh` exits 1 on an unknown identifier and 0 on
> a real one; `axeyum-fp`'s `kernel_equivalence` exits 2 on an unknown claim and
> 1 on `MISMATCH`; `check-dbdesign-negative-controls.sh` exits 1 and additionally
> refuses a *shrinking* control set; `check-lean-gate.sh` was observed exiting 1
> on this very fleet when a misconfigured Lean shim shadowed the toolchain; and
> `validate-claims.py` was observed exiting 1 the same day on a real
> schema-violating claim. Not exercised: `check-claim-certificates.py` (one row),
> which needs the gitignored `drat-trim` clone and takes minutes.
>
> Two cautions kept, because "can fail" is necessary and not sufficient. First,
> an intermediate regex-based audit of the same ledger flagged **19** runs as
> inert and **every one was wrong** — a heuristic over command text is not a
> measurement of behaviour, which is the same mistake one level up. Second, a
> checker that can fail may still be bound loosely to its subject:
> `F:ordered-ring-farkas-refutation` cites a whole-gate run, so it fails when
> *any* Lean suite fails rather than when its own theorem stops checking. That
> binding, not the exit status, is the remaining work here. Not all 40 are defects (a kernel-lean binary that builds a term
and lets `Kernel::infer` reject it *is* a real check), but the largest family is,
and it is the most load-bearing one:

```
$ cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory -- this_theorem_does_not_exist
0 theorems
$ echo $?
0
```

That is the shape of `F:nat-add-comm`'s checker. Delete `add_comm` from the
kernel and the fact stays green. `nat_axiom_inventory` is worse: it prints
`nat: axiom=0` and exits 0 **whatever the number is**, so `axiom_footprint: []`
on 31 kernel-lean facts — the axiom-freedom claim that is this project's headline
metric — is asserted by nothing. All three inventory examples are plain
`fn main()` with no `ExitCode`, no `exit`, no `assert`, no panic.

It has already cost a real one. `F:schedule-critical-chain-infeasible` recorded
30 axioms while the code produced 26 and nobody noticed, because the checker ran
the route and exited 0 without comparing. That drift was benign — `False` and
`Eq` had become `inductive` declarations with `Eq.rec` the recursor, a genuine
shrink of the trusted surface — but the same silence would have hidden growth,
which is the direction that matters. Fixed in `b94b56425`: `--dump-axioms` prints
sorted names so a diff against the ledger is a diff, `--expect-axioms N` fails on
drift in **either** direction, and it errors when the kernel route never produced
a module rather than treating an unreached check as a pass.

This is the CLAUDE.md Gotcha — *"an empty result from a tool that was never
pointed at your subject is indistinguishable from a strong negative result"* —
promoted from an agent-brief hazard to a ledger-integrity one. →
[`04-gates-and-truth.md`](04-gates-and-truth.md)

## What this plan is not

It is not a rewrite. The measured evidence says the architecture is sound and
the *seams* are unfinished: a façade that is already a façade, subsystems that
already group cleanly, a dependency contract that already exists in
`foundational-dag.md`. Every item below is a matter of finishing a boundary that
is half-drawn, and each is independently landable.

Nor is it a performance plan. Where performance appears — the 4,000× kernel
rebuild, the proof-checking blow-up measured at 8.00× and since reduced to
1.49× (ADR-0426) — it appears because it *bounds what can be proved at all*,
not because it is slow. The earlier "6.6× since reduced to 1.5×" phrasing here
mixed a pre-fix measurement with a figure that was only ever a rule of thumb.

## Order

The items are not equally urgent and they are not independent. **This is the
single-owner ordering; it is superseded while a second lane is live —
see [`00-parallel-work.md`](00-parallel-work.md), which is the operative
sequencing today.**

1. **`01` — ℤ/ℝ.** The keystone. Everything above it is currently assumed, and
   the layers cannot compose across a sort the evidence system cannot express.
   *Its first item, constructing ℤ from proved ℕ, is currently owned by another
   lane; the rest of `01` is free.*
2. **`02` — composition.** Directly blocks `01`: the CAS certificate is over ℝ
   while the mathematics is over ℤ, and the kernel rebuild tax rises with every
   theorem `01` adds. *W1 (kernel reuse) is contested; W2/W3 are free.*
3. **`04` — gates and truth.** Cheap, and it protects everything else. A
   refactor guarded by gates that do not see the files is not guarded. *Free.*
4. **`03` — decomposition.** The largest and the least urgent. Do it after the
   boundaries above are real, or it will freeze today's seams into crate
   boundaries. *Do not start while another lane is in `axeyum-solver`.*
