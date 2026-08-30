# Notes: 356-prime-dvd-mirrors

Detail moved out of [`../status/356-prime-dvd-mirrors.md`](../status/356-prime-dvd-mirrors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

New test `prime_dvd_mirrors_state_exactly_what_they_claim`
(`nat_prelude_tests.rs`) rebuilds each new theorem's DECLARED type
independently — never via `prime_condition`, the helper the theorem was built
with — and asserts `def_eq`, catching a swapped `Iff` side or transposed
hypothesis the kernel's own type-check cannot distinguish from the intended
statement. It also instantiates `prime_coprime_pow_of_not_dvd` at a concrete
`p=3, m=2, a=5` (`gcd(5,9)=1`) with a genuine COMPOSITE control at `a=6`
(`gcd(6,9)=3 != 1`, and `3|6` genuinely holds — confirmed by reduction, not
asserted), which is what makes `not(p|a)` load-bearing rather than a control
that happens to pass at zero composites.

Every `checker_command` verified in both directions before landing: the real
kernel name returns `grep -c` count 1 against `nat_theorem_inventory`'s
tab-separated output, a fabricated name (`<name>_zzzfabricated`) returns 0.
Checked with `/usr/bin/grep -cE` explicitly, anchored on
`^Nat\.<name>[[:space:]]` so no name is a substring of a longer one (e.g.
`prime_dvd_mul` inside `prime_dvd_mul_iff`).

`scripts/check-fact-depends-derived.py --fix` added the proof-term-level
dependency edges these 14 facts needed, plus one edge each to three
PRE-EXISTING facts that already used `euclid_lemma`
(`F:ml430-nat-prime-dvd-of-dvd-pow-e76f834a`,
`F:ml430-nat-prime-not-dvd-mul-cb3a915e`, `F:nat-prime-dvd-choose`) — nothing
else in those three files changed.

**Blocked, still `open`, all still genuinely dispatchable (re-checked against
`scripts/check-dispatchable-frontier.py --json` after this lane's work):**

- `F:ml430-nat-prime-eq-one-of-pow-846d2949` (`Prime (x^n) -> n=1`)
- `F:ml430-nat-prime-not-prime-pow-5f14afc6` (`n != 1 -> ~Prime(x^n)`)
- `F:ml430-nat-prime-not-prime-pow-d6480abf` (`2 <= n -> ~Prime(x^n)`)
- `F:ml430-nat-prime-mul-eq-prime-sq-iff-d3fd2e31` (`x!=1 -> y!=1 -> (x*y=p^2 <-> x=p /\ y=p)`)

  These four cluster: `Prime(x^n)` forces case analysis on `x in {0,1,>=2}`
  crossed with `n in {0,1,>=2}` (x=0: `x^n` is 0 for `n>=1`, not prime via
  `prime_ne_zero`; x=1: `x^n=1`, not prime via `prime_ne_one`; x>=2, n>=2:
  `x^n = x * x^(n-1)` has `x` as a divisor with `1 < x < x^n`, contradicting
  the divisor clause's `d=1 \/ d=x^n`, which needs `x < x^n` established
  first — not yet built here). No new proof code was attempted for these; the
  blocker is genuinely the casework volume, not a missing lemma noticed and
  skipped. `mul_eq_prime_sq_iff` likely reduces to `eq_one_of_pow`'s content
  once that lands (`x*y=p^2` with `x,y != 1` forces `x,y` to each be a
  divisor of `p^2` other than 1, and primality of `p` plus `x*y=p*p` pins
  `x=y=p`) but this was not worked out in detail.

- `F:ml430-nat-prime-not-coprime-iff-dvd-c83110ca`
  (`~Coprime(m,n) <-> exists p, Prime p /\ p|m /\ p|n`)

  The EXISTENCE direction can adapt `declare_coprime_of_forall_prime_dvd`'s
  proof shape (`primes.rs`) almost directly: that function already does the
  `g := gcd(m,n)` trichotomy (`g=0`, `g=1`, `g>=2`) and, in the `g>=2` branch,
  extracts a prime `pw | g` via `exists_prime_dvd` and shows `pw|m`, `pw|n` —
  it just uses that fact to derive a contradiction (`pw|1`) rather than
  supplying it as the existential witness this fact needs. The `g=0` branch
  needs a concrete prime witness (e.g. `2`, already known prime in this file)
  since `p|0` holds for every `p`. This was SIZED, not attempted: the
  `eliminate_prime_dvd` and `prime_divisor_predicate` helpers it would reuse
  are still private (`fn`, not `pub(super)`) in `primes.rs` and would need the
  same visibility change made to `prime_condition`/`prime_parts` this lane
  already did.

Next lane: either finish the four prime-power facts (casework-heavy but no
missing infrastructure identified) or `not_coprime_iff_dvd` (infrastructure
mostly exists, needs the visibility bump plus the new-witness case split).
