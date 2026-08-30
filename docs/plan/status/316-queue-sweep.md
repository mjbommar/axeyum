# Lane: queue-sweep — the 3 non-sign dispatchable facts declined, with a correction to `301`'s multiplicative-formula plan

<!-- plan-section: lane-status -->

**DONE for this dispatch (`queue-sweep`, 2026-08-30). No fact closed. No
Rust changed.** This lane's value is a correction that stops a future lane
from trying to prove a false lemma, plus a documented reason for declining
all three assigned targets.

## The task

`scripts/check-dispatchable-frontier.py` listed 8 dispatchable facts. Five
are the `Int.mul_*_iff` sign family, explicitly assigned to the sibling lane
`int-sign-product` and skipped here. The remaining three, all `Nat.totient`
statements over general (not-necessarily-coprime) arguments:

```
F:ml430-nat-totient-dvd-of-dvd-9622e44a            a ∣ b → totient a ∣ totient b
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7   totient(gcd a b) * totient(a*b)
                                                    = totient a * totient b * gcd a b
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7  a∣b → totient a = totient b
                                                    → a=b ∨ 2*a=b
```

`scripts/brief-step0.py` on each: ABSENT (provisional, stale snapshot; a
fresh `shape_search --concl Or --hyp Nat.dvd --hyp Eq` confirms ABSENT
directly against 1,112 declarations). `scripts/check-autogenesis-already-proved.py`
was also run; it does not name-match any of the three (expected — none is a
verbatim rename of an existing declaration).

## Why these are open, per two prior dedicated lanes

Detail moved to [`../notes/316-queue-sweep.md`](../notes/316-queue-sweep.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | queue-sweep | No fact closed. All three assigned non-sign dispatchable facts (`totient_dvd_of_dvd`, `totient_gcd_mul_totient_mul`, `eq_or_eq_of_totient_eq_totient`) declined for this session: correctly-stated Mathlib mirrors this kernel does not yet have the general multiplicative-function theory to prove, distinct from the divergence-registry category. Corrected a false numerical claim in `301-totient-multiplicative.md`'s Step 4 (`count_range_row_major` is NOT coprimality-independent — fails at every tested non-coprime pair, e.g. `totient(4)=2 ≠ totient(2)*totient(2)=1`), which would have sent the next totient lane at a statement a sound kernel cannot admit. |
