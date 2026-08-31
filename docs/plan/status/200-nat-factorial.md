# Lane: nat-factorial — the `Nat.factorial` Mathlib v4.30 import backlog

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-factorial, 2026-08-28).** Landed four of the
six assigned facts: `Nat.factorial_dvd_factorial`, `Nat.factorial_le`,
`Nat.factorial_lt_of_lt`, `Nat.factorial_ne_zero`, all `kernel-lean`,
axiom-free (`nat` trusted surface still 0). `factorial_le`/`factorial_lt_of_lt`/
`factorial_ne_zero` had to move OUT of `declare_divisibility` into a new
`declare_factorial_order` (`divisibility.rs`) called after `declare_euclid` in
`build_nat_prelude`'s dispatcher — all three need `one_le_factorial`, which
`declare_euclid` (`primes.rs`) declares, and `declare_euclid` runs after
`declare_divisibility`. Same shape as the documented `declare_dvd_antisymm`
precedent in `lcm.rs`; `UnknownConst { name: NameId(306) }` was the tell, not
`TypeMismatch`.

The remaining two — `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` and
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` — are left **open**.
`Nat.ascFactorial`/`Nat.descFactorial` do not exist in this kernel: no field on
`NatPrelude`, and `asc_factorial`/`desc_factorial`/`ascFactorial`/
`descFactorial` all grep to zero hits anywhere in
`crates/axeyum-lean-kernel/src/`. The prelude struct field list is the
authoritative registry here (every field is declared exactly once, at
construction), so this is a confirmed absence, not an unfound search — matches
the brief's expectation. Building the two ascending/descending factorial
definitions plus their base-case facts (`F-ml430-nat-ascfactorial-zero-…`,
`F-ml430-nat-descfactorial-zero-…`, etc. — eight open facts already sit in the
ledger for this family) is out of scope for an import-backlog lane and is the
next lane's task if picked up.
*(Corrected 2026-08-31, kernel-measured: `Nat.ascFactorial` and
`Nat.descFactorial` now both exist as `nat`-prelude `Definition`s, landed by a
later lane. This paragraph's "do not exist in this kernel" is a historical
record of the 2026-08-28 snapshot, not a live claim.)*
<!-- was-absent: Nat.ascFactorial, Nat.descFactorial -- both landed after this lane's 2026-08-28 snapshot -->

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 98 passed, 0 failed
(347 → 351 theorems; `the_build_is_deterministic`'s pin recounted by reading
its own panic message, not incremented by hand).
`cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.

<!-- plan-section: landed-changes -->

| 2026-08-28 | `b67d472dc` | `Nat.factorial_dvd_factorial`/`factorial_le`/`factorial_lt_of_lt`/`factorial_ne_zero` admitted, axiom-free. |
| 2026-08-28 | `822c77a97` | fact: close `F:ml430-nat-factorial-ne-zero-5fc0b0a1`. |
| 2026-08-28 | `e0ca4c407` | fact: close `F:ml430-nat-factorial-dvd-factorial-e9d14845`. |
| 2026-08-28 | `aa391cd39` | fact: close `F:ml430-nat-factorial-le-d0f4a912`. |
| 2026-08-28 | `ddd2e0855` | fact: close `F:ml430-nat-factorial-lt-of-lt-d6c2125d`. |
