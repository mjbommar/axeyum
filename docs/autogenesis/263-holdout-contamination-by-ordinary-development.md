# The held-out partition can be spent by ordinary library work, and the gate cannot see it

**2026-08-25.** Found while auditing the fact ledger for open facts the kernel
already proves — not while looking for this.

## The finding

`artifacts/autogenesis/nursery-v1.json` preregisters 216 Mathlib propositions
into `train` (78), `development` (79), `held-out` (57) and `longitudinal` (2).
The held-out partition exists to blind-evaluate the autogenesis pipeline, and
`scripts/check-autogenesis-holdout-isolation.py` enforces it: a held-out fact
whose `epistemic_status` becomes `proved`/`computed` fails the build, because
establishing one **by any route** spends it.

**At least 4 of those 57 are already proved in this kernel**, by ordinary hand
development that had nothing to do with autogenesis:

| Held-out fact | Kernel theorem |
|---|---|
| `F:ml430-nat-choose-zero-right-1ed2802a` | `Nat.choose_zero_right` |
| `F:ml430-nat-choose-self-25bb9fb8` | `Nat.choose_self` |
| `F:ml430-nat-choose-succ-succ-671856b6` | `Nat.choose_succ_succ` |
| `F:ml430-nat-choose-zero-succ-62c6520b` | `Nat.zero_choose_succ` |

Each verified by comparing the fact's `formal.statement` against the kernel's
rendered type, not by name. Note the fourth: the fact says `choose-zero-succ`
and the kernel says `zero_choose_succ`. **An exact-name scan finds only 3 of the
4**, so 4 is a lower bound and the true number needs statement comparison across
all 57.

## Why the gate misses it

`check-autogenesis-holdout-isolation.py` reads `epistemic_status` — one field,
one line — and separately scans files for textual *references* to held-out ids.
It never asks whether the kernel **contains a theorem proving the proposition**.
It currently reports `held_out=57|settled=0|references=0|verdict=PASS`, and that
PASS is accurate about what it measures and silent about what matters.

So the guard covers the *ledger's bookkeeping* and not the *information*. A
capsule registered against a held-out row is caught; a lane proving the same
proposition in `nat_prelude/choose.rs` because it needed it for something else
is not. The second is far more likely — it is just people doing the work.

This is the repository's own recurring failure mode, one level up: a checker
whose exit status does not depend on the thing you actually care about. It is
worth being explicit that this instance is **not** the usual `grep -q`/vacuous
shape — the gate genuinely discriminates on its own predicate. The predicate is
the wrong one.

## What this does and does not mean

It does **not** mean the pipeline cheated, and it does not mean the theorems
should be removed. Proving `Nat.choose_self` is ordinary, correct library work,
and the kernel is the product.

It does mean that for those rows, a later autogenesis "discovery" is not
evidence of discovery: the answer is already in the environment the producer
reads from. Any headline computed over the held-out partition is, to that
extent, measuring something weaker than it claims.

## What to do about it

Per ADR-0542 the repair for a spent row is an **amendment ledger, never a
deletion** — the record of what was spent is the point. So:

1. **Measure the real number**: compare all 57 held-out `formal.statement`s
   against the kernel inventory by statement, not by name. Expect false
   positives to dominate a name-based pass — in the audit that produced this
   note, **14 of 16** name-level candidates were refuted on statement
   comparison.
2. **Extend the gate** so contamination is detected at the moment it happens,
   and reported as an amendment rather than a build failure. Failing the build
   would only pressure a lane into *not* proving a theorem it needs, which is
   the wrong incentive entirely.
3. **Recompute any held-out headline** over the uncontaminated remainder, and
   say what was excluded.

The general rule, which is worth stating beyond this instance: **a blind
evaluation population that overlaps a growing library is not blind, and no
amount of bookkeeping discipline about the population fixes it.** The
partition's guarantee has to be checked against the library, not against the
ledger's own record of itself.
