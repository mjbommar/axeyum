# Lane: nursery-refill-two -- the second refill draw, and why it did not happen

<!-- plan-section: lane-status -->

**Lane block (`IN PROGRESS`, nursery-refill-two, 2026-08-29).**

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 99
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 11
      F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0
      F:ml430-nat-base-induction-83561d4c
      F:ml430-nat-dvd-two-of-totient-le-one-3642bf31
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-b6a6596f
      F:ml430-nat-odd-totient-iff-eq-one-d0491d84
      F:ml430-nat-totient-coprime-totient-iff-3932cf83
      F:ml430-nat-totient-dvd-of-dvd-9622e44a
      F:ml430-nat-totient-eq-one-iff-68d883a0
      F:ml430-nat-totient-even-28e0415f
      F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
exit 0
```

9 of the 11 are `natural-totient`, matching the brief's "a lane is actively
working" note.

```
python3 scripts/check-autogenesis-holdout-isolation.py
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Matches the brief's quoted baseline exactly.

## The ceiling is the binding constraint -- worked out from the generator's own rules

```
artifacts/autogenesis/nursery-v1.json entries:            216  (214 evaluation + 2 amendments)
artifacts/autogenesis/nursery-v2-extension.json entries:   80
V1_EVALUATION_ENTRIES (frozen constant in the generator):  214
EVALUATION_CEILING:                                        300
current total (R3's own formula, 214 + 80):                294
headroom:                                                    6
```

`gen-autogenesis-nursery-refill.py` regenerates the WHOLE `nursery-v2-extension.json`
from `FAMILY_MODULES` in one pass (it is not designed for incremental append);
its own guards (R3-R6) fix the minimum size of any rule-compliant refill:

- `PER_FAMILY = 10` -- every family contributes exactly 10 rows or the
  generator refuses (`family {family!r} yields {n} screened candidates, fewer
  than the 10 the refill takes`).
- `assign_partitions()` cycles `(held-out, development, train)` over the
  families sorted by Mathlib module path, restarting the cycle at `held-out`
  for the NEW family set on every invocation of the generator.
- **R5** refuses a refill that adds fewer than 2 new held-out families.

Working the cycle: with `N` new families, indices `0..N-1 mod 3` land on
`held-out` at positions `0, 3, 6, ...`. Two held-out families need indices `0`
and `3` both to exist, i.e. **`N >= 4` families minimum** -- and `4 * 10 = 40`
rows is the smallest input that can pass R3+R5+R4 together (4 families:
held-out, development, train, held-out -- 20 held-out, 10 development, 10
train, so R4's "something dispatchable" and R5's "2 new held-out families" are
both satisfied at the same time for the first time).

**40 rows is the floor for a rule-compliant refill through the existing
generator. The ceiling headroom is 6.** A "refill" that adds fewer rows than
the generator's own leakage/breadth rules require is not a refill in the
sense those rules define -- it would either violate R5 (no held-out breadth
restored) or, if it tried to add a single non-held-out family alone, would not
even reach `PER_FAMILY = 10` without ALSO adding whatever partition the cycle
assigns next, which for a lone new family is `held-out` (index 0) again.

**Conclusion: no meaningful draw is possible within the current 300-entry
ceiling using the existing family-based methodology.** This lane did not
preregister anything. Preregistering 6 rows to make a counter move would
either violate R5 (if all 6 are non-held-out, added by hand-editing the
generator's own refusal, which is exactly the kind of unilateral rule-bending
CLAUDE.md and this brief forbid) or spend the ceiling on partial held-out
families that test nothing new.

### What should change (a decision for the humans/coordinators, not this lane)

- **Raise `EVALUATION_CEILING`.** The generator's own minimum viable refill
  is 40 rows, so a ceiling raise needs to clear at least `214 + 80 + 40 = 334`
  to make a third refill possible later too; something like 400-450 gives
  two more refills of this shape before the question recurs. This is a
  recorded-decision change (the ceiling exists on purpose, per the brief), not
  a lane's unilateral edit -- flagging it here for whoever owns that call.
- **Alternatively, loosen `PER_FAMILY`** for a family whose candidate pool is
  naturally small, or allow a refill to extend an EXISTING dispatchable-eligible
  family (`natural-totient`, `natural-division`, ...) rather than only adding
  brand-new families -- this sidesteps R5's "2 NEW held-out families" rule
  (extending an existing train/development family adds no held-out obligation)
  and could fit inside 6 rows. That is also a rule change, not something this
  lane did unilaterally.
- **Shrink `PER_FAMILY` from 10** for future refills once each family's
  candidate pool and the review cost of extra work per proof shape are
  weighed -- a call for whoever set 10 in the first place, not a hyperparameter
  to flip mid-lane to hit a target count.

## Already-proved screening (in progress)

Continuing to build a reusable "does this candidate already exist under this
exact name in the kernel environment" check, since the sibling lcm/gcd lane
found 5 of 10 rows in its family already proved before doing any new work.
Numbers to follow in this file once the tool is built and run against the
current dispatchable queue.
