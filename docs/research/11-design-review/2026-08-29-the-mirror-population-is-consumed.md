# The `ml430` mirror population is consumed (2026-08-29)

**Measured, not estimated.** The autogenesis flywheel's input queue is
effectively empty, and the remaining rows are blocked for reasons that more
lane-hours cannot fix.

## The numbers

| | count |
| --- | --- |
| `ml430` population | 214 |
| proved | 155 (72%) |
| open | 59 |

The 59 open decompose as:

- **12 mutation negative controls** — deliberately perturbed, often false.
  Proving one is a soundness alarm. Never closable by design.
- **37 held-out** — preregistered blind evaluation population
  (`artifacts/autogenesis/nursery-v1.json`; 216 entries split train 78 /
  development 99 / held-out 37 / longitudinal 2). Dispatching at these spends
  the evaluation, and doing so once already cost 19 of 76 rows for one theorem.
- **~12 dispatchable**, of which **11 are structurally blocked**:

| blocker | rows | why it cannot be fixed by effort |
| --- | --- | --- |
| codomain mismatch | 6 | Mathlib's `Nat.testBit` returns `Bool`; ours returns `Nat` in `{0,1}`. Closing a `Bool`-typed pinned statement with a `Nat`-valued proof manufactures a flip. Ten mirrors blocked this way today, each checked against the pinned source. |
| definitional divergence | 3 | `multichoose` — Mathlib's is a three-case double recursion and its closed form is a *theorem* about it; ours *defines* that formula. Different propositions. |
| algorithmic divergence | 1 | `minFac` — ours is a fuel-structural linear search, Mathlib's is well-founded on `sqrt n` skipping evens. Same values, different construction. |
| recursion-principle divergence | 1 | `fastFib` — Mathlib's `binaryRec` is `WellFounded.fix` with a **dependent** motive. A fuel encoding's non-dependence is *forced* (the exhaustion row must return a value for arbitrary `n` with only `motive 0` in hand), so no amount of infrastructure reaches it. The keystone was built anyway; the mirror still cannot flip. |

The twelfth, `lt_xor_cases`, is in flight with all four of its blocking pieces
landed today.

## Why this is a strategic gap, not a milestone

The flywheel's premise is that the concept DAG and the fact ledger *say what to
prove next*. That mechanism now selects from a set that is 72% closed and whose
remainder is either off-limits (held-out), adversarial by design (mutations), or
blocked by a definitional mismatch no proof effort resolves.

Meanwhile the non-mirror open set is **five** facts, all deep metamathematics:
Gödel first incompleteness, CH independence, FOL validity undecidability,
Fermat, and "excluded middle is not intuitionistically derivable". These are not
a queue; they are four keystones and one tractable slice.

So the selection mechanism has run out of things to select, and nothing in the
pipeline notices. That is the defect: **a queue that empties silently reads
exactly like a queue that is being worked down.**

## What a fix has to respect

Adding population is not simply "generate more mirrors":

1. **The held-out partition is a shared resource with no owner.** The split key
   is `<family>:<statement-shape>` precisely because a route for one member is
   evidence about its siblings. New population must be preregistered without
   disturbing the existing split, and `check-autogenesis-holdout-isolation.py`
   must stay green.
2. **The codomain and definitional blockers are systematic, not incidental.**
   A generator that emits more `Bool`-codomain mirrors adds unclosable rows and
   inflates the open count without adding work. Whatever selects new targets
   should screen for the four divergence classes above *before* preregistration.
3. **Ten of the eleven blocked rows produced a local fact instead**
   (`F:nat-testbit-xor`, `F:nat-lt-of-testbit`, `F:nat-exists-most-significant-bit`,
   …). That is the honest outcome and it is real mathematics — but it is
   invisible to any metric that counts mirror closures, which is what the
   nursery measures. The measurement and the work have drifted apart.

## Related

- ADR-0542 (held-out isolation), ADR-0603 (graded statement families).
- `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`
  — row 3's 28 `cas-internal` certificates are the *other* place the ledger
  says there is work, and that one is a genuine backlog rather than a boundary.
