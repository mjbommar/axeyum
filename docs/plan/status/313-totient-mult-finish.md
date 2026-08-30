# Lane: totient-mult-finish — `totient_coprime_totient_iff` closed, `coprime_mul_of_coprime` landed, three mirrors still open

<!-- plan-section: lane-status -->

**DONE for this dispatch (`totient-mult-finish`, 2026-08-30).**

## The task

Close `F:ml430-nat-totient-coprime-totient-iff-3932cf83` (the cheap one, per
`306-totient-even-finish.md`'s traced route) and then land one of the two
weakest steps toward `totient(m*n) = totient(m)*totient(n)` per
`301-totient-multiplicative.md`, needed by the remaining three:

```
F:ml430-nat-totient-dvd-of-dvd-9622e44a
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
```

## Result: `totient_coprime_totient_iff` proved, `coprime_mul_of_coprime` landed, the other three still open

Detail moved to [`../notes/313-totient-mult-finish.md`](../notes/313-totient-mult-finish.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | totient-mult-finish | `Nat.totient_coprime_totient_iff` (closed, `F:ml430-nat-totient-coprime-totient-iff-3932cf83` flips to proved) and `Nat.coprime_mul_of_coprime` (new, axiom-free, the first of the multiplicative formula's two weakest steps — route (b), the prime-divisor contrapositive via `coprime_of_forall_prime_dvd`+`euclid_lemma`, worked first try and needed no Bézout algebra) landed and verified. `Nat.count_range_row_major` (the second weak piece, the genuinely novel row-major double-counting induction) and the three facts needing the full multiplicative formula remain open, per this task's own "don't force the formula" guidance. |
