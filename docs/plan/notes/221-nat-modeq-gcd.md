# Notes: 221-nat-modeq-gcd

Detail moved out of [`../status/221-nat-modeq-gcd.md`](../status/221-nat-modeq-gcd.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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

Landed `Nat.coprime_of_dvd'` (`F:ml430-nat-coprime-of-dvd-6f652673`) in
`nat_prelude/primes.rs` as `declare_coprime_of_forall_prime_dvd` (named that,
not `coprime_of_dvd`, since that name is already taken by the unrelated
`Nat.Coprime.of_dvd`). Route: trichotomy on `g := gcd m n` via `lt_or_ge`
twice. `g<1` (so `g=0`) forces `m=n=0` (`zero_mul` on the `dvd 0 _` witness),
and applying the hypothesis at `k=2` (`prime_two`, already existed in this
file) self-contradicts via `refute_dvd_one_against_prime` -- **an existing
PRIVATE helper this file already had for exactly the `dvd p one -> False`
shape**, reused rather than rebuilt (found by reading the file, not by
grepping a name I didn't know). `1<=g` and `g<2` gives `g=1` directly. `1<=g`
and `2<=g`: `exists_prime_dvd` gives a prime factor of `g`, hence of `m` and
`n` (`dvd_trans`), so the hypothesis gives a contradiction the same way.

Also reused `prime_parts`/`prime_condition`/`absurd`/`or_cases`/`prime_two`
(all private `fn`s already in `primes.rs`) rather than rebuilding any of
them, and added two NEW private helpers this proof needed and the file
didn't have: `eliminate_prime_dvd` (destructuring `exists_prime_dvd`'s
result, mirroring the inline elimination `declare_euclid` already builds
for the same shape) and `dvd_elim` (a per-file copy matching the ones in
`lcm.rs`/`irrational.rs`/`perfect.rs`/`divisibility.rs`).

**BUILD ORDER hit on the first attempt**: `UnknownConst { name: NameId(122) }`
= `Nat.succ_pred_of_pos`, needed transitively by `prime_two` via
`two_divisor_dichotomy`. My first dispatch placement (right after
`declare_coprime_of_dvd_both`, alongside the other `coprime_of_*` calls) ran
BEFORE `declare_succ_pred_of_pos` (which itself runs much later, right before
`declare_prime_pred_pos`, per an existing comment: "Must run before
`declare_fermat`/`declare_totient_all`"). Diagnosed by temporarily adding a
throwaway `#[test]` that caught the `KernelError`, scanned `NameId(115..130)`
via `k.display_name`, and printed the name directly -- faster than guessing.
Fixed by moving the dispatch call to right after `declare_succ_pred_of_pos`.
Kernel accepted the proof term on the FIRST attempt after that move (zero
`TypeMismatch`/`UnboundFVar` from the proof term itself, only the build-order
issue). `theorem_names` recounted: 402. `nat_prelude::` sweep: 110 passed,
0 failed. clippy -D warnings clean.

All six facts named in the brief are now accounted for: three landed above,
two out of scope (below), and `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`
remains unstarted -- it is the one the brief already flagged as needing
genuine `Int`/`Nat` mod-arithmetic bridging (reducing a Bézout coefficient
mod `k` and showing the residue lands in range), confirmed still real work
by this lane's own read of the statement; not attempted this session.

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
