# Notes: 241-nat-minfac-relprime

Detail moved out of [`../status/241-nat-minfac-relprime.md`](../status/241-nat-minfac-relprime.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` mirror stays `open`,
deliberately.** Mathlib's own `Nat.minFac` is NOT this — theirs is
well-founded recursion on `sqrt n`-bounded measure, skips even candidates,
and exits early once `k*k > n`. The two agree pointwise (both are "the least
divisor ≥ 2 of `n`" with identical boundary values) but are structurally
different `def`s, so per the established mirror-flip criterion this is the
`Nat.multichoose` case, not the `Nat.descFactorial_of_lt` case. A theorem
about coprimality relative to THIS `minFac` needs its own new `F:nat-*` fact
and a minimality property (`∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d`) not attempted
here — sized as further, separate work.

**Kernel REJECTED nothing in this lane** — both declarations and every test
were accepted on first `add_declaration`/`declare_theorem`. The one real
correctness risk (a `Definition` that type-checks but computes the wrong
value; `Kernel::add_declaration` cannot catch this) was caught by evaluation
tests, not the kernel: `min_fac_computes_the_least_prime_factor_with_negative_controls`
checks `minFac 12 = 2` against `minFac 15 = 3` (the brief's discriminating
pair — "first divisor" and "smallest prime divisor" coincide for an
upward-from-2 scan, argued in `min_fac.rs`'s module doc) plus `minFac 0 = 2`,
`minFac 1 = 1`, `minFac 2 = 2`, `minFac 9 = 3`, each with a negative `def_eq`
control (including `minFac 12` vs `minFac 15` not collapsing to each other).

`nat_prelude` count: **85 + 443 -> 88 + 444** (1 new theorem
`coprime_iff_isRelPrime`, 3 new definitions `IsRelPrime`, `minFacAux`,
`minFac`; confirmed by `the_build_is_deterministic`'s own panic message, not
hand-counted).

## Verification run

- `cargo test -p axeyum-lean-kernel --lib nat_prelude` (targeted `nat_prelude::`
  filter): **127 passed, 0 failed** (was 126 before this lane's declarations
  + tests, 120 before `nat-singles`).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`:
  clean, no allow-lists needed.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py`: 0 errors (1922 facts, 1834 proved).
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25`'s new `checker_command`s run
  and confirmed to actually discriminate: `nat_theorem_inventory` prints the
  exact rendered type for `Nat.coprime_iff_isRelPrime`,
  `nat_axiom_inventory --require-axiom-free nat` exits 0, and both
  concrete-instance tests (mp/mpr round trip at (3,5); a real
  `Not (IsRelPrime 4 6)` proof from `gcd 4 6 = 2`) pass individually by name.
- Did NOT run the full aggregate `just check`/`./scripts/check.sh` (out of
  scope for a single-lane targeted change; the coordinator re-runs the full
  gate before merge per standing project convention).

## What's still needed for `F:ml430-nat-coprime-of-lt-minfac-0f79bdba`

A NEW fact (not the `ml430` mirror — see above) stating coprimality relative
to THIS `Nat.minFac`, which needs:

- **Minimality**: `∀ n, 2 ≤ n → ∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d` — that
  `minFac n` really is the LEAST divisor `≥ 2`, not merely A divisor. Not yet
  proved; the natural route is an induction over the fuel search itself
  (every candidate `2, …, minFac n - 1` was tried and failed), mirroring
  `primes.rs`'s existing `least_divisor_search` minimality argument but
  adapted to the concrete recursive function rather than an existential
  witness.
- **The coprimality argument itself**, once minimality is in hand: for
  `m ≠ 0`, `m < minFac n`, suppose `g := gcd n m > 1`; `g ∣ n` and `g ≥ 2`
  gives `g ≥ minFac n` by minimality, but `g ∣ m` and `m ≠ 0` gives `g ≤ m`,
  contradicting `m < minFac n ≤ g ≤ m`. So `gcd n m = 1`.
