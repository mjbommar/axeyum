# Two deficiencies found by lanes on 2026-08-27

Both were found by lanes doing something else, and both were reported rather
than worked around. Neither is fixed here.

## 1. `Rat.sumRange` has no diagonal/rectangle reindexing, and it blocks two things

The kernel-Taylor lane landed the degree-≤1 expansion
(`Rat.taylor_deg1`) and stopped at general degree with the obstacle named
exactly: a **general-degree closed form needs a diagonal/rectangle double-sum
reindexing lemma over `Rat.sumRange`**, because `q(x)`'s coefficients are

    Σ_{i=k+1}^{n-1} c(i)·a^(i−1−k)

which cannot be built or evaluated without it.

**That machinery exists for `ℕ`** — `nat_prelude::diagonal` / `rectangle` — and
**not for `ℚ`**.

What makes this worth its own entry rather than a line in a status file: it is
the **same gap `rat_prelude/polynomial.rs`'s own module doc already names** as
blocking `Rat.polyEval_mul`, the Cauchy product. So it has now been reached
independently from two directions, by lanes that did not know about each other.
A blocker hit twice from different sides is infrastructure, not a local
difficulty.

Note also what this is *not*: it is **not a failed proof attempt**. The lane did
not try and fail to prove general-degree Taylor; it identified the missing
prerequisite before spending effort on it. That is the sizing behaviour that has
worked all session.

**The `ℕ` version existing is the strongest evidence the `ℚ` version is
reachable** — and also the reason to check carefully whether it can be
transported rather than re-derived. Re-deriving beside the original is how this
repository ends up with two proofs of one fact that must stay in sync while the
kernel happily verifies both.

## 2. Two tools disagree on how many `Nat` theorems exist, and the ledger's
   denominator is the loser

The fact-generation lane found:

| tool | `Nat.*` theorems |
| --- | --- |
| `kernel_declaration_projection` (the generator's source) | **338** |
| `prelude_theorem_inventory --include-constructed` (coverage's denominator) | **329** |

The 9-theorem gap traces exactly to the **`Nat.Peano.*` family**, which the first
tool enumerates and the second does not.

The consequence is quiet and specific: all 9 facts were generated and pass
`--audit`, but they **cannot move the `registered` counter**, because the
denominator never reaches them. So the ledger under-reports its own coverage, and
nothing fails — the numbers simply do not add up, in a direction nobody would
notice.

This is a variant of a trap CLAUDE.md already documents: *an empty result from a
tool that was never pointed at your subject is indistinguishable from a strong
negative result.* Here it is not empty, just short by nine, which is worse —
a partial answer is far more convincing than a blank one.

**Do not assume the inventory is the one that is wrong.** It excludes
`Axiom`, `Definition`, `Opaque`, `Inductive`, `Constructor`, `Recursor` and
`Quotient` by construction, and those exclusions are deliberate. The question to
answer first is *what kind of declaration `Nat.Peano.*` actually is* — read it
from `kernel.environment()`, not from either tool's output, and not from the
name.
