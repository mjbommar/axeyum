# Lane: nursery-refill-two -- the second refill draw, and why it did not happen

<!-- plan-section: lane-status -->

**Lane block (`DONE -- well-founded refusal, plus a reusable already-proved screen`, nursery-refill-two, 2026-08-29).**

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

Detail moved to [`../notes/292-nursery-refill-two.md`](../notes/292-nursery-refill-two.md).

