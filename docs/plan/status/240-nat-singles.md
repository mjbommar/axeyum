# Lane: nat-singles — close the two unassessed `ml430` singleton facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-singles, 2026-08-29).** Landed both
unassessed facts: `Nat.mod_lcm` and `Nat.dvd_of_forall_prime_mul_dvd`.
Neither needed the stated blockers to be investigated first -- nobody had
looked, and both turned out to have short proofs from infrastructure already
in the prelude (`Nat.lcm_dvd`, `crt.rs`'s `gap_dvd`/`modeq_of_dvd_gap`,
`Nat.exists_prime_dvd`).

`Nat.mod_lcm : modEq n x y -> modEq m x y -> modEq (lcm n m) x y`,
**unconditional** in `n`/`m` (unlike `Nat.crt_unique`, which needs
`gcd n m = 1`). The combination step is `Nat.lcm_dvd : dvd n c -> dvd m c ->
dvd (lcm n m) c`, already unconditional, so the whole proof is `crt_unique`'s
own `crt_le`/`gap_dvd`/`modeq_of_dvd_gap` shape with `lcm_dvd` swapped in for
`coprime_mul_dvd`. `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`, private) were
widened to `pub(super)` and reused from `lcm.rs` rather than duplicated.

`Nat.dvd_of_forall_prime_mul_dvd : (forall p, Prime p -> p|a -> p*a|b) ->
a|b`. Turned out to need only ONE prime dividing `a` (any one), not
induction over `a`'s factorization: `a=0` uses the hypothesis at `k=2`;
`a=1` needs `dvd_mul`+`one_mul` and never touches the hypothesis; `a>=2`
uses `exists_prime_dvd` for a witness `pw`, the hypothesis at `k=pw` gives
`pw*a | b`, and `a | (a*pw)` (`dvd_mul` + `mul_comm`) chains via `dvd_trans`.
Same nested `lt_or_ge`-on-`a` trichotomy as the neighbouring
`coprime_of_forall_prime_dvd`.

The other two facts (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`) are left `open`, confirmed
still blocked (re-grepped the whole `crates/axeyum-lean-kernel/src/` for
`minFac`/`min_fac` and `IsRelPrime`/`is_rel_prime`/`isRelPrime`: zero hits
outside this status doc and the fact files themselves) -- see "What's still
needed" below for the precise construction each one is missing.

`nat_prelude` count: **85 + 441 -> 85 + 443** (2 new theorems, 0 new
definitions; confirmed by `the_build_is_deterministic`'s own panic message,
not hand-counted).

## What's still needed for the other two facts

- **`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`** (`m != 0 -> m < n.minFac ->
<!-- was-absent: Nat.minFac -->
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

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-singles | `Nat.mod_lcm`: unconditional lcm-combination of two congruences, closes `F:ml430-nat-mod-lcm-ee6bdd41` |
| 2026-08-29 | nat-singles | `Nat.dvd_of_forall_prime_mul_dvd`: needs only one prime witness, closes `F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b` |
| 2026-08-29 | nat-singles | `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`) widened `fn` -> `pub(super) fn` so `lcm.rs` can reuse them |
