# Notes: 240-nat-singles

Detail moved out of [`../status/240-nat-singles.md`](../status/240-nat-singles.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`** (`m != 0 -> m < n.minFac ->
  n.Coprime m`) needs `Nat.minFac` as a COMPUTABLE definition with defining
  equations, which does not exist. `Nat.exists_prime_dvd`/
  `Nat.least_divisor_search` only give an EXISTENCE proof of a prime
  divisor, not a value-returning function. Building `Nat.minFac` as a
  fuel-recursive `Nat -> Nat` (mirroring `nat_prelude/log.rs`'s pattern,
  deciding `dvd d n` via `beq (mod n d) 0` the way
  `least_divisor_search` already does) is a legitimate definition task per
  this lane's brief, but Mathlib's own `Nat.minFac` uses well-founded
  recursion bounded by `sqrt n`, not a simple fuel bound, and getting the
  defining equations AND an evaluation test (with a negative control
  discriminating "first divisor" from "smallest prime divisor", e.g.
  `minFac 12 = 2` vs `minFac 15 = 3`, plus the `minFac 1 = 1` boundary) right
  is a sized task on its own -- not attempted this lane, to avoid
  half-landing it.
- **`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`** (`m.Coprime n <->
  IsRelPrime m n`) needs an `IsRelPrime` predicate, confirmed absent from
  the whole kernel (this lane's own grep, zero hits). Mathlib's
  `IsRelPrime m n := forall d, d ∣ m -> d ∣ n -> IsUnit d`, specialized to
  `Nat` where the only unit is `1`, so `IsRelPrime m n := forall d, dvd d m
  -> dvd d n -> Eq d 1`. This is a NEW predicate declaration (not merely a
  theorem), and the iff with `gcd m n = 1` needs both directions: forward
  (`gcd m n = 1 -> IsRelPrime m n`) via `dvd_gcd` + `eq_one_of_dvd_one` (a
  direct consequence, cheap); backward (`IsRelPrime m n -> gcd m n = 1`) via
  `gcd_dvd_left`/`gcd_dvd_right` fed into the hypothesis at `d := gcd m n`
  (also cheap, symmetric to `coprime_of_forall_prime_dvd`'s existing shape).
  Neither direction looked hard once the predicate exists; the predicate
  itself is the only missing piece.

## Verification run

- `cargo test -p axeyum-lean-kernel --lib nat_prelude` (targeted `nat_prelude::`
  filter): **120 passed, 0 failed** (was 118 before this lane's two new
  theorems + two new tests).
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`:
  clean (needed one `#[allow(clippy::too_many_arguments)]` on the new
  `mod_lcm_le`, matching `crt.rs`'s `crt_le`).
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py`: 0 errors.
- Both new `checker_command`s (from each fact's evidence) run and confirmed
  to actually discriminate: `nat_theorem_inventory` prints the exact
  `formal.statement` for each name, `nat_axiom_inventory --require-axiom-free
  nat` exits 0, and both concrete-instance tests (with negative controls)
  pass individually by name.
- Did NOT run the full aggregate `just check`/`./scripts/check.sh` (out of
  scope for a single-lane targeted change; the coordinator re-runs the full
  gate before merge per standing project convention).
