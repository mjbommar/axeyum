# Mathematics strand — August 2026

## STATUS 2026-08-15 — what this strand actually produced

The numbered documents below were written before any of it and **do not mention
these domains**. Read this section first; treat `01`–`05` as the reasoning that
led here, not as a description of the present.

The ledger now holds **69 settled facts** across six domains and five
proof routes, every one re-derived by `scripts/check-fact-evidence-replay.sh`
rather than asserted:

| domain | settled facts |
|---|---|
| kernel library | 22 |
| logic / SMT | 16 |
| summation identities | 9 |
| numerics / FP | 6 |
| algebraic geometry | 6 |
| operations research | 4 |
| algorithms | 4 |
| combinatorics | 2 |

Routes: `cas-certificate` 15, `kernel-lean` 23, `search-certificate` 8, `smt-clausal` 8, `smt-term-level` 15.

Results worth naming, each with its own diary in this folder:

- **Apéry's recurrence**, order 2, coefficient for coefficient — reachable only
  after `MvPoly`'s intermediate coefficients went unbounded (4187 bits → 76).
  Not ζ(3)'s irrationality; the recurrence.
- **Chu–Vandermonde and Gauss as identities**, not merely recurrences, with the
  base case *decided* at symbolic parameters rather than sampled.
- **Six Euclidean geometry theorems** in fully generic coordinates, and the
  measured finding that **four need no non-degeneracy condition at all**: a side
  condition is required exactly when a theorem *locates* a point the hypotheses
  are supposed to pin down. Incidence is free; location is not.
- **S(3)…S(6) optimal sorting-network sizes**, with the symmetry-breaking
  soundness control at every size — an unsound break manufactures a wrong UNSAT.
- **fp8/fp16/fp32 kernel equivalence**, exhaustive where the width permits, and
  a capability edge: neither z3 nor bitwuzla can decide *any* fp8 E5M2 query.
- **ℤ constructed over proved ℕ** — 34 axioms to 6, 20 theorems with an empty
  axiom footprint.
- **R₄(5(x−y)=3z) = 625**, one cell of one family, and deliberately not the
  centre of this strand.

What the numbered documents still get right is the *shape* of the question —
decide vs certify, the library, reachability. What they get wrong is the
inventory. When they next get rewritten, derive the table above from the ledger
instead of restating it.

The companion to [`docs/refactor-2026-08/`](../refactor-2026-08/README.md).

> **Before taking any item, read
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).**
> A second lane owns `crates/axeyum-lean-kernel/` — which is rung 5, the
> library — and two shared append points. It re-orders this strand.
>
> A third strand,
> [`docs/formalized-math-2026-08/`](../formalized-math-2026-08/README.md),
> covers collecting and integrating the ~10 M lines of formalized mathematics
> that already exist outside this project.

That strand asks *where is the code untidy*. This one asks **what mathematics
can this system do, what can it only assert, and what can it not yet state.**

They are deliberately separate. A refactor plan answers the easier question, and
during the 2026-08-14 campaign it quietly substituted itself for this one.

## The ladder, and where the frontier sits on each rung

The north star is a ladder: finite domain → arithmetic → theory combination →
quantifiers → proof production. Measured on 2026-08-14:

| rung | what it means | measured frontier |
|---|---|---|
| **1. Decide** | return a correct verdict | **101 capability entries over 26 areas**; 49 `Checked`, 40 `Validated`, 13 `SoundIncomplete`, 3 `Experimental`. 30 logics. |
| **2. Certify to ourselves** | evidence our own checker re-derives | broad on the SAT/BV path: DRAT + an independent backward checker; instances re-checked clause by clause |
| **3. Certify to a stranger** | a certificate an independent kernel accepts | **4 of 26 areas** name a kernel/Lean-checked proof in their evidence: `QF_LIA`, `QF_LRA`, `QF_NRA`, `quantifiers` |
| **4. Prove with symbolic parameters** | a theorem about an infinite family | the `∀`-route proved `k=2` for symbolic `a` **and** `b` over unbounded ℤ; `k=3` is 1 of 3 cases |
| **5. State it at all** | a library to say it in | `nat_prelude` **106 proved / 0 assumed**; `int` **0 / 3**; `arith` **0 / 3** |

Read the table downward and the shape of the problem is plain: **the system
decides far more than it can certify, and certifies far more than it can
state.** Rungs 1–2 are strong, rung 3 is narrow, rungs 4–5 are barely begun.

## The finding that reframed this strand

I nearly wrote "we have no CAD" into this document, on the strength of a comment
at `nra.rs:107` saying multi-variable SOS is "gated on a future principled
engine (nlsat/CAD)". That inference was wrong, and checking it produced the
strand's central result.

`capabilities.rs:705-719` describes `QF_NRA` as

> a **complete cylindrical-decomposition decision side** (single-variable
> real-algebraic + degree-2 SOS/PSD + coupled-equality resultant grid + strict
> and non-strict CAD, **ANY dimension**, rational OR algebraic coordinates)

differentially validated against Z3 with **DISAGREE=0** over an NRA fuzz that
found and fixed real wrong-unsats. CAD exists, in `nra_real_root.rs` (7,684
lines), and it decides.

And then, in the same entry:

> degree-2 SOS UNSAT carries a kernel-checked Lean proof, **general CAD UNSAT no
> proof yet**

**That is the shape of the whole strand.** The deciding path outran the
certifying path. `MAX_CROSS_PRODUCTS = 2` is not "no engine" — it is the width
of the *certifying* path (SOS, which produces Lean proofs) beside a *deciding*
path (CAD) that produces none. The cap looks like a performance knob and is
actually the boundary between what we can prove to someone and what we can only
tell them.

## The four documents

1. [`01-decide-vs-certify.md`](01-decide-vs-certify.md) — the central gap, area
   by area. Where a verdict exists with no certificate, and what a certificate
   would have to be.
2. [`02-the-library.md`](02-the-library.md) — ℕ → ℤ → ℚ → ℝ. What 106 proved Nat
   theorems unlock, the construction order, and why the library is the rung
   everything else waits on.
3. [`03-symbolic-and-infinite.md`](03-symbolic-and-infinite.md) — values versus
   theorems. The campaign produced 20 new exact values and zero theorems; this
   is why, and what closes it.
4. [`04-reachability.md`](04-reachability.md) — what this stack cannot yet
   *state*, using the curriculum's own decidability classes as the map.
5. [`05-the-mathematics-dag.md`](05-the-mathematics-dag.md) — the 1,567-concept
   prerequisite DAG that already exists next door, the prior art on formal
   dependency graphs, and six lines of research that are fully parallelisable
   against the lane holding the library.

## The honest summary

The 2026-08-14 campaign produced **18 new off-diagonal Schur values and 2 new
Rado numbers** — every one finite, bounded, and over a `BitVec`-shaped domain —
and **zero theorems**. That was not a choice of targets. It is the shape of what
the stack can currently carry evidence about, and every item in this strand is
aimed at changing it.
