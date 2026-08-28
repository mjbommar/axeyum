# Lane: nat-modeq-gcd — close the remaining natural-modular-equivalence / natural-gcd facts

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, nat-modeq-gcd, 2026-08-28).** Six open facts across
two small families (all `development`, none HELD-OUT/MUTATION, verified against
a fresh `scripts/fact-frontier.py` run before touching anything):
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`,
`F:ml430-nat-coprime-of-dvd-6f652673`,
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-div-dvd-div-left-b56f6f7c`,
`F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`,
`F:ml430-nat-modeq-gcd-eq-5167ff4f`.

Landed `Nat.ModEq.gcd_eq` (`F:ml430-nat-modeq-gcd-eq-5167ff4f`) in
`nat_prelude/gcd.rs` as `declare_modeq_gcd_eq`, dispatched after
`declare_dvd_antisymm` (needs `dvd_antisymm`, `gcd_dvd_left/right`, `dvd_gcd`,
`dvd_add`, `dvd_add_iff_right`, `dvd_mul_right_of_dvd`, `add_comm`). Route:
eliminate the balanced-witness `modEq m a b := ∃ u v, a+m*u=b+m*v` twice, show
`gcd a m ∣ gcd b m` and the mirror image, close with `dvd_antisymm`. Kernel
accepted first attempt; `every_nat_declaration_is_checked_and_axiom_free`
caught the missing `theorem_names` entry (recounted, not incremented: 400).
`nat_prelude::` sweep: 110 passed, 0 failed (was 109 before).

Two of the six are judged genuinely out of scope for this lane, both because
they need a NEW predicate/definition the whole kernel lacks, confirmed absent
by grep across `nat_prelude.rs` and every `nat_prelude/*.rs`:
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` needs `IsRelPrime` (per the
  brief; agreed after independent check).
- `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` needs `Nat.minFac` (least prime
  factor) — **not previously flagged, newly confirmed absent this session**.
  `exists_prime_dvd`/`least_divisor_search` give existence of *a* prime
  factor, not a computable minFac with defining equations; building one is a
  separate, larger task.

Landed `Nat.div_dvd_div_left` (`F:ml430-nat-div-dvd-div-left-b56f6f7c`) in
`nat_prelude/divisibility.rs` as `declare_div_dvd_div_left`, dispatched right
after `declare_divisibility` (needs `div_mul_cancel_of_dvd`,
`one_le_of_dvd_pos`, `mul_left_cancel_of_pos`, both declared inside
`declare_divisibility` itself; `mul_assoc`/`mul_comm`/`zero_mul`/`zero_div`
from earlier). Route: case-split on `m` via `d.induct` (a case split, not a
recursion -- the induction hypothesis is ignored) to isolate `m`'s positivity.
`m=0`: `dvd 0 k` forces `k=0`, so `k/0` and `k/n` both reduce to `0` and
`dvd_refl` closes it (`dvd n 0` unused). `m=succ pred`: extract witnesses from
both hypotheses, substitute to show `n ∣ k` directly (picking up `n`'s
positivity along the way via `one_le_of_dvd_pos`), then cancel `n` from two
expressions for `k` via `mul_left_cancel_of_pos` to land on the exact witness
`k/n = (k/m)*q`. No positivity hypothesis on `n`/`m`/`k` needed -- both zero
cases fall out of the case split. First kernel attempt hit six borrow-checker
rejections (`cannot borrow *d as mutable more than once`) from nested
`d.foo(..., d.bar())` calls -- flattened into sequential `let`s per the
standing house rule, then the KERNEL accepted first try (no `TypeMismatch`
etc. at all). `theorem_names` recounted: 401. `nat_prelude::` sweep: 110
passed, 0 failed.

Wrote local `dvd_elim`/`dvd_intro` helpers into `divisibility.rs` (private,
`fn` not `pub(super)`) mirroring the existing per-file copies in `lcm.rs`
(read-only for this lane), `irrational.rs` and `perfect.rs` -- this repo
already duplicates this pair per-file rather than sharing one; followed the
existing convention rather than introducing a new cross-file dependency.

Remaining two (`coprime_of_dvd'`, `exists_mul_mod_eq_gcd`) are unstarted;
`coprime_of_dvd'` needs `exists_prime_dvd` plus a 3-way case split on
`gcd m n` (0 / 1 / >=2, the last via `lt_or_ge`) to extract a prime factor
when the gcd isn't already 1, or handle `m=n=0` directly. `exists_mul_mod_eq_gcd`
is the one the brief already flagged as needing genuine `Int`/`Nat`
mod-arithmetic bridging (reducing a Bézout coefficient mod `k`) -- not
attempted yet.

Two of the six are judged genuinely out of scope for this lane (unchanged
from above), both because they need a NEW predicate/definition the whole
kernel lacks, confirmed absent by grep across `nat_prelude.rs` and every
`nat_prelude/*.rs`:
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` needs `IsRelPrime` (per the
  brief; agreed after independent check).
- `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` needs `Nat.minFac` (least prime
  factor) — **not previously flagged, newly confirmed absent this session**.
  `exists_prime_dvd`/`least_divisor_search` give existence of *a* prime
  factor, not a computable minFac with defining equations; building one is a
  separate, larger task.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-modeq-gcd | land `Nat.ModEq.gcd_eq` (gcd.rs); confirm minFac absent, isRelPrime absent |
| 2026-08-28 | nat-modeq-gcd | land `Nat.div_dvd_div_left` (divisibility.rs) |
