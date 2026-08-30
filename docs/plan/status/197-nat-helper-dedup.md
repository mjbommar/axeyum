# Lane: nat-helper-dedup — promote nat_prelude private helpers duplicated 2-3 ways

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-helper-dedup, 2026-08-28).** Promoted the
three genuine duplicate groups the brief named, all confirmed byte-for-byte
identical before consolidation:

- `two_divisor_dichotomy` (`d ∣ 2 → d = 1 ∨ d = 2`) — three copies:
  `irrational.rs`'s `two_divisor_dichotomy`, `perfect.rs`'s `divisors_of_two`,
  and a third inlined directly inside `primes.rs`'s `Nat.prime_two`
  construction (not its own `fn`, but the identical term-building sequence).
  Promoted to `nat_prelude/ops.rs` as `pub(super) fn two_divisor_dichotomy`,
  self-contained (uses an inline `or_rec` application rather than depending
  on `or_elim`/`or_cases`, since those remain private per-file combinators
  used extensively elsewhere in `irrational.rs` and `primes.rs`). 4 call
  sites re-pointed (1 in `irrational.rs`, 2 in `perfect.rs`, 1 inlined
  construction in `primes.rs`'s `prime_two` replaced with a direct call).
- `two_mul_eq_add_self` (`Eq (mul two k) (add k k)`) — two copies:
  `powsq.rs`'s `two_mul_eq_add_self` and `primes.rs`'s
  `two_mul_eq_add_local`. Promoted to `ops.rs` under the more descriptive
  original name. 4 call sites re-pointed (2 in `powsq.rs`, 2 in `primes.rs`).
- `bool_true_or_false` (`Or (beq b true) (beq b false)`, `Bool.rec`) — the
  brief named two copies (`totient.rs`, `primes.rs`); a third turned up while
  re-pointing call sites: `perfect.rs` had its own copy too, used at **5**
  internal call sites, byte-identical and even self-documented as "local
  copy of `totient.rs`'s `bool_true_or_false`" — so the duplication was
  already known and recorded, just never acted on. All three promoted to
  `ops.rs`. 7 call sites re-pointed total (1 `totient.rs`, 1 `primes.rs`, 5
  `perfect.rs`).

Placed in `nat_prelude/ops.rs` rather than `helpers.rs`: the brief named
`ops.rs` as the shared-machinery location, `ops.rs` is in this lane's scope
and `helpers.rs` is not, and every one of the five touched files already
`use super::ops::{NatDev, NatOps}`, so promoting into that same module means
callers just widen an existing import rather than adding a new one.

Detail moved to [`../notes/197-nat-helper-dedup.md`](../notes/197-nat-helper-dedup.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-helper-dedup | promoted `two_divisor_dichotomy` (3→1), `two_mul_eq_add_self` (2→1), `bool_true_or_false` (3→1, found a 3rd copy in `perfect.rs` beyond the brief's two) to `nat_prelude/ops.rs`; re-pointed 15 call sites across `irrational.rs`/`perfect.rs`/`primes.rs`/`powsq.rs`/`totient.rs`; census unchanged at 10/10 (tool is blind to private-fn duplication by construction) |
