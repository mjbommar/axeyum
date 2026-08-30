# Lane 302 — mirror statement repair

**Status:** in progress (this file is committed early, per the ten-call rule; it
records the re-measured set before any repair).

## Step 0 — re-measurement (reproduced, then widened)

Over the whole ledger at merge-with-`main`:

```
total facts 2114 | ml430 374 | non-ml430 1740
  starts-theorem   19
  AxNat            19
  x0-binder        18
  ascii-arrow      18
  Eq.{             13
union flagged by ANY pattern: 19
baseline signature (starts-`theorem ` | AxNat | AxInt): 19
EXTRA beyond baseline: 0
```

The reported count of **19 is exact and reproduces**. I widened the detector to
twelve independent kernel-rendering signatures — `AxRat`, `AxReal`, `CReal`,
`Eq.{`, an `(xN :` binder, a leading `def `/`axiom `, `Sort.{`/`Type.{`, and an
ASCII ` -> ` arrow — and **the union is the same 19 files**. No wider signature
finds a twentieth fact.

**Positive control (the detector does not flag the healthy majority).** The 355
unflagged `ml430` facts carry Mathlib surface syntax, e.g.

```
F-ml430-int-add-assoc-749cb0ff.json      ∀ (a b c : ℤ), a + b + c = a + (b + c)
F-ml430-int-add-ediv-of-dvd-left-…json   ∀ {a b c : ℤ}, c ∣ a → (a + b) / c = a / c + b / c
F-ml430-int-add-emod-b5735756.json       ∀ (a b n : ℤ), (a + b) % n = (a % n + b % n) % n
```

Note the sub-signature counts: `x0-binder` and `ascii-arrow` each hit 18, not
19 — `Nat.not_coprime_zero_zero` is closed, so it has no binder and no arrow.
A detector built on binders alone would have missed it. `Eq.{` hits only 13.
Only `starts-theorem ` and `AxNat` are individually complete over this set.

## The 19

```
F-ml430-int-fib-of-odd-66560495                 Int.fib_of_odd
F-ml430-nat-coprime-add-self-left-5e93448c      Nat.coprime_add_self_left
F-ml430-nat-coprime-add-self-right-c3ed0f45     Nat.coprime_add_self_right
F-ml430-nat-coprime-iff-isrelprime-0c08eb25     Nat.coprime_iff_isRelPrime
F-ml430-nat-coprime-of-dvd-left-b0e2aa94        Nat.coprime_of_dvd_left
F-ml430-nat-coprime-of-dvd-right-a640bd56       Nat.coprime_of_dvd_right
F-ml430-nat-coprime-one-left-iff-45945e80       Nat.coprime_one_left_iff
F-ml430-nat-coprime-one-right-iff-42fed4ce      Nat.coprime_one_right_iff
F-ml430-nat-coprime-self-add-left-51351fa1      Nat.coprime_self_add_left
F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb        Nat.dvd_lcm_of_dvd_left
F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3       Nat.dvd_lcm_of_dvd_right
F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b Nat.dvd_of_forall_prime_mul_dvd
F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c        Nat.dvd_of_lcm_left_dvd
F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60       Nat.dvd_of_lcm_right_dvd
F-ml430-nat-dvd-two-of-totient-le-one-3642bf31  Nat.dvd_two_of_totient_le_one
F-ml430-nat-mod-lcm-ee6bdd41                    Nat.mod_lcm
F-ml430-nat-not-coprime-zero-zero-6c4e8dd8      Nat.not_coprime_zero_zero
F-ml430-nat-prime-dvd-iff-not-coprime-77854741  Nat.prime_dvd_iff_not_coprime
F-ml430-nat-totient-eq-one-iff-68d883a0         Nat.totient_eq_one_iff
```

## Note on the `ml430-mutation-*` family

13 `ml430` facts are `ml430-mutation-*` rows whose top-level `statement` is
`"A \`<kind>\` mutation of the pinned source proposition \`X\`"` rather than the
prose reference. None are flagged. They are a distinct family (deliberate
falsifiable mutations of a pinned proposition), but their `formal.statement`
is still Mathlib surface syntax, so the gate applies to them unchanged.

(Sections on the restore source, the schema change and the gate follow.)
