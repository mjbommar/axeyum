# Notes: 191-parity-coprime

Detail moved out of [`../status/191-parity-coprime.md`](../status/191-parity-coprime.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**One kernel rejection, and it was a Rust-level ordering bug, not a proof
error.** The first attempt wired the four new `declare_coprime_two_*`/
`declare_coprime_odd_of_*` calls in next to the other `coprime_*`
declarations near `declare_primes`, which runs *before* `declare_parity_all`
(the call that declares `Nat.Even`/`Nat.Odd`). Every one of the 97
`nat_prelude::` tests failed with `UnknownConst { name: NameId(510) }` —
build-wide poisoning from one bad declaration, per the standing gotcha.
Moved the four calls to run right after `declare_parity_all`; the kernel
then accepted all four proof terms on the first attempt with no further
changes.

**Duplicated two private helpers rather than promoting them.** The
divisor-of-2 dichotomy (`dvd c 2 → c=1 ∨ c=2`) already has two file-private
copies (`irrational.rs`'s `two_divisor_dichotomy`, `perfect.rs`'s
`divisors_of_two`); this lane added a third, in `primes.rs`. The `2*k = k+k`
identity (`powsq.rs`'s private `two_mul_eq_add_self`) got a second, rebuilt
locally in `primes.rs`. `ops.rs` — the only place either could be shared
from — is out of scope for this lane (shared, concurrently edited by other
lanes per its own module doc in `parity.rs`), and the repository's own
history already tolerates this shape of duplicate (`bool_true_or_false` has
two copies for the same reason). Said so in the commit rather than silently
re-deriving.
