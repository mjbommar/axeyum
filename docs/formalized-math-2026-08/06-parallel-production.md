# 06 — Parallel production: how to run a fleet against the frontier

Written 2026-08-23, from one day of doing it. Every number here is measured on
this host, not estimated. The companion is
[05-throughput.md](05-throughput.md), which argues *why* production rate is the
metric; this is *how* to get it out of a fleet of Sonnet and Haiku workers.

## What this pushes, on the flywheel

CLAUDE.md's cycle has four arrows. This document is about the first one —
**library → solver** — and specifically about the case where the library is
built directly in the kernel rather than reconstructed from a solver's
refutation:

```
        library (proved ℕ, ℤ, ℚ, ℝ, ℂ, …)
             │  gives the solver facts to reason with
             ▼
        solver → reconstruction → kernel term → admitted, axiom-free
             └──────────────────────────────┐
        the concept DAG and the fact ledger ┘  say what to prove next
```

The reconstruction arrow has a hard ceiling: a solver can only reconstruct what
it can decide, and a proof route only exists for propositions the library can
already state. **The library arrow has no such ceiling**, and it is the one that
parallelizes cleanly — a lane proving Euclid's lemma over ℤ does not contend
with a lane proving continuity over ℝ, because they touch different files and
different carriers.

That is the whole opportunity. It is also why the constraints below are almost
entirely *mechanical* rather than mathematical.

## What one day produced

| | |
|---|---:|
| Distinct kernel theorems | **463 → 544**, every one axiom-free |
| Trusted surface | 30, unchanged, all in the unreached `axreal` package |
| Lane commits | 78 |
| Agents dispatched | ~30 on mathematics (187 output files across the session) |

Named classical results that landed, all over our own constructed carriers and
all with an empty `Kernel::axiom_footprint`:

* **Elements I.47** (Pythagoras) and **III.31** (Thales), over `CPoint`/`CReal`
* **The concurrence of the altitudes**, as an *unconditional* bilinear identity
* **Elements VII.2** (Bézout) and **VII.30** (Euclid's lemma) over ℤ
* **The Chinese Remainder Theorem**, existence and uniqueness
* **Pascal's rule** and the binomial coefficients over ℕ
* **Euclidean division on ℤ as a total function**, with uniqueness, divisibility
  and modular congruence built on it
* **The first theorem of analysis** — limits are unique — plus the algebra of
  limits and sequential continuity
* **The Brahmagupta–Fibonacci two-square identity**, and **ℂ as a field**

## The four binding constraints, in order

Parallelism here is not limited by model capacity. It is limited by these, and
knowing the order matters because relieving the wrong one buys nothing.

### 1. Cargo slots: exactly 5 on this host

`scripts/cargo-serialized.sh` is a counting semaphore sized from RAM:
`123 G / 24 G per job = 5`, clamped to 6. Agents past five that need cargo
**queue**. This is not advisory — a lane's kernel verification was killed twice
by contention today and correctly reported **"did not run"**, and the
coordinator had to run it.

So five is the natural fleet size for lanes that compile. A sixth lane doing
pure analysis (reading, censusing, writing a diagnostic) costs nothing and is
free to add.

### 2. Disjoint file areas: about six exist

The real cap. Today's areas, which do not contend:

```
nat_prelude/   int_prelude/   creal/   creal_point.rs   complex.rs
axeyum-lean-import/src/       axeyum-lean-import/examples/
axeyum-cnf + axeyum-solver
```

Two lanes in one area is not a merge problem, it is a *silent revert* problem —
see §5. Assign areas explicitly in the brief and name the forbidden ones.

### 3. The coordinator's merge/verify throughput

This is the ceiling nobody plans for. Every returned lane costs the coordinator
5–15 minutes of **serial** work: check its base for clobbering, copy, run the
suite, run both ledger generators, lint, format, commit. With five lanes
finishing together, the coordinator *is* the queue.

Two consequences. First, **stagger dispatch** rather than launching five at
once. Second, the highest-leverage automation available is not more agents but a
merge script that refuses on a stale base and runs the standard battery.

### 4. Stalls

Several lanes per day stop with some variant of *"I'll wait for the background
task notification before continuing."* The task notification then arrives with
**no results in it**, and the lane looks completed. Each costs a `SendMessage`
round-trip.

## The brief that works

Ten dispatches converged on a shape. The elements that measurably mattered:

**State what already exists, by name.** Seven times today a lane discovered the
thing it was asked to build already existed internally and was merely unexposed
— `Nat.zero_le`, `Nat.le_trans`, `Nat.lt_irrefl`, `Nat.not_succ_le_zero`,
`Nat.le_of_succ_le_succ`, `Nat.sumRange`, and ℂ's `conj`/`normSq`/`mul_conj`.
**Grepping first is the most reliable prior in this repository.** Put it in the
brief as an instruction, not a hope.

**Stage the slice and say "X alone is a result."** Every brief that named a
minimum viable deliverable got one. The binomial lane returned a toolkit and a
precise stall point instead of a half-proved theorem, which was the right trade.

**Name the checks, bounded and foreground.** Give the exact command with a
`timeout`, require a **nonzero test count**, and state that a check which did not
finish is reported as *"did not run"*, never as a pass. This is the only thing
that reduced the stall rate.

**Give the diagnostic that costs an hour.** In this kernel, a *mismatched-type*
proof term makes the checker spend enormous time before rejecting rather than
failing fast. One lane lost an hour to what looked like a 60-second hang and was
two ordinary argument-order bugs. Every later brief carried: *if a declaration
appears to hang, suspect a type error first and bisect with standalone
micro-declarations.*

**Forbid editing the ledger.** Lanes prove theorems and state them exactly;
recording is the coordinator's job. This is not bureaucracy — a fact whose
`formal.statement` can be edited to match whatever was proved makes the ledger
unfalsifiable, and that happened once today before the gate existed.

**Ask to be corrected.** Briefs that said *"verify this signature yourself, I
have relayed a wrong one before"* got verification. Three briefed blockers today
turned out wrong once a lane pushed on them, and **each corrected version was
sharper than the original**:

| I briefed | The lane found |
|---|---|
| `converges_mul` needs a boundedness hypothesis | Boundedness is free; the obstruction is a cross-index sampling estimate |
| The footprint gap runs through *constructor* types | It runs through **recursor** types — `ctor=[]` in 40 of 41 rows |
| `Nat.div_rec_fuel_lemma` is well-founded-recursion machinery | Its declared type has no recursion in it at all |

The last one generalises: **a name is not evidence.** Reading the stream's own
declared type took minutes and would have avoided the wrong caution entirely.

## Model selection

| | Use for | Evidence |
|---|---|---|
| **Sonnet** | Anything producing a claim or a proof term | Handled kernel proof construction across ℕ, ℤ, ℝ, ℂ and geometry. Its errors were *specific and kernel-caught* — a backwards `ediv_add_emod`, a missing `Exists` layer, a wrong-direction bridge lemma, opposite summand orders across two call sites. All self-corrected. |
| **Haiku** | Mechanical work verifiable by construction — census sweeps, extracting numbers from committed artifacts, running a fixed command over a file list | A Haiku lane earlier in this session produced a **fabricated P0 finding** from a file containing zero references to `argv`. Not usable where the output is a claim. |

The distinction is not difficulty, it is **falsifiability of the output**. A
proof term is checked by the kernel, so a Sonnet lane cannot fool it. A prose
finding is checked by nobody, so a fabricating lane succeeds.

## The merge protocol

**Check the lane's base before copying anything.** This caught a real near-miss:
a lane branched at a commit before `Int.modEq_iff_dvd` landed and modified both
files that commit had touched. Copying its versions would have **silently
reverted five theorems and a definition**, with nothing in `git status` to show
it.

```sh
W=.claude/worktrees/agent-<id>
git log --oneline $(git -C "$W" rev-parse HEAD)..HEAD -- <the files it touched>
# empty  => safe to copy
# nonempty => send it back to merge; do NOT hand-resolve
```

Sending it back is better than hand-resolving: the lane has the context to
check *build order*, which is where these conflicts actually bite. Additive
conflicts in a `NameId` list auto-merge; a wrong declaration order surfaces as a
missing-declaration error at build time, not as a conflict.

**After merging, confirm both sides survive by name**, not by reading the diff:

```sh
for n in <my names> <their names>; do grep -c "p\.$n\b" <the test file>; done
```

**Then verify, in this order**: the crate suite (nonzero count), the axiom
ledger `--check` (it *rebuilds* the isolated preludes, so admission is measured
rather than asserted), the theorem ledger `--check` (which will report the rise
and ask you to say so), clippy, rustfmt.

## What to measure, and what not to quote

The trusted-surface number (`creal=0`, `integer=0`, …) is a **regression
ratchet**. It has been 0 all day for every constructed prelude, so quoting it as
evidence for new work is quoting a number that cannot move in the direction
implied. It is worth running and worth reporting as *held*.

The checks that can actually fail, and therefore the ones to lead with:

* **Theorem-count delta**, derived and gated. It moved 463 → 544 today.
* **Per-name footprint assertions** — because `axiom_footprint` of a name that
  was interned but never *declared* is **vacuously empty**. Presence matters as
  much as the footprint, and two lanes today added declarations without adding
  list entries.
* **Verbatim rendered-statement tests** for headline theorems. An axiom-free
  proof of something *weaker than its name* still reads zero axioms.
* **The scoping hypothesis, stated honestly.** `0 < n` rather than `n ≠ 0`;
  convergence *at a linear rate* rather than convergence; *sequential*
  continuity rather than ε-δ continuity.

And check that the instrument covers the subject at all. The theorem ledger
silently excluded the entire `cpoint` prelude — **19 theorems invisible**,
including one that had landed that morning — because the inventory example never
built it. An empty result from a tool never pointed at your subject is
indistinguishable from a real zero.

## Toward Mathlib

Two routes exist and they behave differently under parallelism.

**From scratch, in our own kernel.** Parallelizes well, bounded only by disjoint
file areas. Everything in §"What one day produced" came this way. The carriers
are ours, so nothing is imported and the axiom-free claim is direct.

**Imported statements, reconstructed proofs.** This is the autogenesis pipeline,
and its bottleneck is different: a statement adapter that refuses any Mathlib
*proof*, so each blocked declaration must be reconstructed from primitives
before the statement can even be attempted. Today that wall fell for the
`Int.ModEq` family after four bridges in sequence, each measured against the
real archive before the next was attempted, and the family's producer then
generalized **4/4 blind** on a held-out development set.

The two routes meet at a useful place. Our `Int.emod` is a *structural*
definition, so nothing over it needs well-founded recursion; Mathlib's `Nat.mod`
is well-founded, which is precisely why the imported route was blocked for hours
on `Nat.div_rec_lemma`. **The from-scratch library is not just an alternative to
the import pipeline — it is sometimes the shorter path to the same theorem.**

The practical sequencing that follows:

1. Run four to five compiling lanes on **disjoint carriers**, each with a named
   classical target rather than a topic.
2. Keep one non-compiling lane on **audit or census** work — it costs no cargo
   slot and it is where the metric errors get caught.
3. Prefer **widening an existing producer** to writing a new capsule. 24 of 25
   registered operations cover exactly one fact, and the legitimate training
   surface is only 56 open facts; a bespoke capsule spends an irreplaceable row
   and teaches nothing transferable.
4. When a lane returns a **blocker**, treat it as the more valuable half of the
   report and re-brief from it. Three of today's sharpest results came from
   blockers, not from successes.
