# ADR-0950: `natural-bit-decode` amended out of held-out, and the closed-evaluation screen moves to draw time

Status: accepted
Date: 2026-08-30
Index-summary: draw 11 preregistered `natural-bit-decode` held-out on
2026-08-30 even though `Nat.bit false 0 = 0` and `Nat.size 1 = 1` were already
decided by reduction over `Nat.bit` (landed 2026-08-28) and `Nat.size`
(landed 2026-08-24) days earlier -- the same defect ADR-0695 recorded for
`fermat-numbers`, this time repeated rather than prevented -- so the family is
amended to `development` per ADR-0542, and `gen-autogenesis-nursery-refill.py`
gains an R12 guard that runs the standing closed-evaluation classifier against
every NEW held-out row before the manifest is written, so a third occurrence
is refused at draw time rather than found in a later audit

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0695
(the construction spends the closed rows, not the evaluation test; the
precedent this amendment mirrors), ADR-0762 (a spent family does not return
to the drawable pool)

## Context

`scripts/check-holdout-closed-evaluation.py` is registered in both aggregate
gates specifically because ADR-0695 measured that a held-out row decided by
reduction is not blind, whatever anyone has or has not proved about it. It
ran red:

```
HOLDOUT_CLOSED_EVALUATION|held_out=156|closed_shaped=2|violations=2|verdict=FAIL
  closed-evaluation|F:ml430-nat-bit-false-zero-d996adbf|natural-bit-decode|
    Nat.bit false 0 = 0|decided by reduction over ['Nat.bit', 'false']
  closed-evaluation|F:ml430-nat-size-one-e23e5f71|natural-bit-decode|
    Nat.size 1 = 1|decided by reduction over ['Nat.size']
```

Both rows are held-out in `nursery-v2-extension.json`, family
`natural-bit-decode` (10 rows, `Mathlib.Data.Nat.{Bits,Size}`), preregistered
by draw 11 (`882ae1a52`, 2026-08-30 23:07:25). `Nat.bit` was admitted by
`2facd789` on 2026-08-28 06:23:04, and `Nat.size` by `a7ac623d7` on
2026-08-24 15:30:55 -- both confirmed ancestors of the draw commit by
`git merge-base --is-ancestor`. `Nat.bit false 0 = 0` and `Nat.size 1 = 1`
are ground equations between a constant applied to numerals and a numeral, so
each closes by `Eq.refl` the instant those definitions exist. Nothing had to
be proved for either row to stop being blind.

**Measured, not assumed, whether more rows are affected**: running the
gate's own classifier over every held-out row in both manifests (156 rows,
snapshot at 2,507 declarations, dated after this incident) finds exactly
these two closed-shaped rows and no others. The remaining eight
`natural-bit-decode` rows are genuinely quantified (`Nat.bit_add`,
`Nat.bit_le`, `Nat.bit_lt_bit`, `Nat.bit_ne_zero`, `Nat.size_bit`,
`Nat.size_eq_zero`, `Nat.size_le_size`) and stay usable evaluation targets --
this amendment does not claim they are spent, only that the family as a whole
cannot stay held-out once two of its ten rows are not blind
(`whole-family-with-source-review-groups-indivisible`).

Draw 11 (recorded in `docs/plan/status/nursery-refill-draw-11.md` and this
tree's commit history) knew about the fermat-numbers precedent and did not
apply it before drawing `natural-bit-decode`. The standing checker caught it
after the fact, exactly as designed -- but this is the SECOND time this
defect has reached a committed manifest, and the first repair (ADR-0695)
recorded the risk in prose ("the next unblocking constant should be screened
for this before it is declared, not after") rather than in a guard. Prose
did not hold.

## Decision

**1. `natural-bit-decode` is amended out of held-out as a whole**, moving all
ten rows to `development`, per ADR-0542's `whole-family-with-source-review-
groups-indivisible` partition unit -- the same unit ADR-0695 applied to
`fermat-numbers` even though only three of its ten rows were spent. No fact
is deleted or reopened; every row keeps whatever `epistemic_status` it holds.
The ledger entry in `mathlib-nursery-split-policy-v1.json` records the two
spent statements, the two admitting commits, and the draw commit, mirroring
ADR-0695's row shape field for field.

**2. The cost is stated, not hidden.** Held-out shrinks from 156 rows across
16 families to 146 rows across 15 families (both manifests combined; the v2
extension's held-out set alone goes from 100 rows across 10 families to 90
across 9). ADR-0762 measured directly that this move does **not** return
`natural-bit-decode`'s module to the drawable pool for a future held-out
family -- the repair narrows the blind population and stays narrowed. That is
the honest price of two rows in a ten-row family not having been blind.

**3. `gen-autogenesis-nursery-refill.py` gains R12: a draw-time
closed-evaluation screen.** For every row a draw ADDS with partition
`held-out`, R12 loads `scripts/check-holdout-closed-evaluation.py` by path
(mirroring R11's import of `check-holdout-adjacency.py`) and applies its
`is_closed_evaluation` classifier and declared-constant check against the
row's `statement`. A row that is a closed evaluation over constants the
kernel environment snapshot already declares is refused before the manifest
is written, naming the fact id, family and statement.

This is not a hypothetical improvement: replayed against the real snapshot
and the real `natural-bit-decode` statements
(`scripts/tests/test_gen_autogenesis_nursery_refill.py::
ClosedEvaluationScreenTests::test_the_real_spent_statements_are_refused_as_a_new_draw`),
R12 refuses exactly the two rows this ADR amends, using the actual committed
kernel-environment snapshot rather than a synthetic fixture. Had R12 existed
on 2026-08-30, draw 11 would have failed before `natural-bit-decode` reached
the manifest, at the cost of choosing a different family.

**4. The obstruction ADR-0695 already named is unchanged and still real: R12
cannot see a construction declared AFTER the draw.** The kernel-environment
snapshot is a point-in-time file (`artifacts/autogenesis/
kernel-environment-snapshot-v1.json`), refreshed by a separate step
(`--snapshot-from`), not by the generator itself reading `Kernel::environment()`
live -- doing so would require this Python script to invoke the Rust kernel,
which it deliberately does not (ADR-0652: this script reads, it does not
build). So R12 closes the "already spent at draw time, snapshot is current"
gap -- which is what both incidents to date actually were, confirmed above by
commit ancestry -- but a construction landing between the last snapshot
refresh and a draw remains a live route to the same spend. The standing
`check-holdout-closed-evaluation.py` gate is what catches that residual case,
same division of labour as R9/R11 versus their own standing counterparts.

## Alternatives rejected

**Weaken or special-case the classifier to admit these two rows.** Rejected
outright per this repository's standing rule: a checker that cannot fail is
worse than no checker, and adjusting a detector's threshold to make a gate
green is exactly that failure arriving through a door marked "cleanup".

**Move only the two spent rows, leaving the other eight held-out.** Rejected
for the same reason ADR-0542 rejected it for `natural-gcd`: the partition
unit is the whole family, and `check-autogenesis-nursery.py`'s
`no-family-may-cross-evaluation-partitions` rule enforces it structurally.

**Have R12 re-derive the kernel environment live instead of reading the
snapshot.** Rejected: this generator is a pure-Python artifact consumer by
design (ADR-0652), and shelling out to a Rust kernel build on every draw
would make an already-heavy generation step depend on a full cargo build.
The snapshot's staleness is fail-open for this exact screen (a declaration
that landed minutes ago reads as absent), which is disclosed rather than
hidden -- see decision 4 -- and is the same trade-off `check-holdout-
closed-evaluation.py` and R9 already accept.

## Consequences

- `scripts/check-holdout-closed-evaluation.py` returns to
  `verdict=PASS` with `closed_shaped=0` (measured after the amendment,
  reported in `docs/plan/status/holdout-closed-evaluation-amendment.md`).
- `scripts/check-autogenesis-nursery.py`,
  `scripts/check-autogenesis-holdout-isolation.py`, and
  `scripts/check-dispatchable-frontier.py` are re-run and their results
  recorded in the same status file; none of this ADR's paths touch their
  code.
- A third occurrence of this defect, if the construction were declared
  *before* the draw and the snapshot were current, is now refused at draw
  time by R12 rather than surfacing in the next audit. A fourth occurrence
  from a construction declared in the gap between snapshot refresh and draw
  remains possible and is caught by the standing gate, one cycle later, same
  as today.
