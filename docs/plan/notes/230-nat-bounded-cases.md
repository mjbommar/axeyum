# Notes: 230-nat-bounded-cases

Detail moved out of [`../status/230-nat-bounded-cases.md`](../status/230-nat-bounded-cases.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`F:ml430-nat-le-fib-add-one-5284f0bf`** (`Nat.le_fib_add_one : n <= fib n
  + 1`, unconditional). Split at `Nat.lt_or_ge n 5`: `Le 5 n` chains
  `le_fib_self` + `le_add_right` + `le_trans`; `Lt n 5` is
  `cases_lt_bound`'s 5-way split to `n ∈ {0,1,2,3,4}`, each branch closed by
  `le_add_right` (or `zero_le` at `n=0`, no reduction needed) at a
  hand-picked slack defeq to `fib(n)+1` for that literal `n` — the exact
  device `le_fib_self`'s own base case (`fib_ge_shifted_gen`) already used.
  The bound is TIGHT (equality) at `n=2,3,4`, which is the algebraic fact
  the fib-2 lane's own analysis (`docs/plan/status/228-fib-2.md`) proved
  rules out a bare pair-induction — confirmed correct; this is why the
  eliminator was necessary, not a shortcut around it.
- **`F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786`**
  (`Nat.Prime.five_le_of_ne_two_of_ne_three`, twice-deferred before this
  lane). Split at `Nat.lt_or_ge p 5`: `Le 5 p` is the hypothesis itself;
  `Lt p 5` is `cases_lt_bound_absurd`'s 5-way split — `p=0,1` contradict the
  primality lower bound `2 <= p` (`p=1` reused the ALREADY-EXISTING private
  `refute_eq_one_against_prime_lower_bound`; `p=0` is a one-line variant of
  it, `refute_eq_zero_against_prime_lower_bound`, new); `p=2,3` contradict
  the two `Not` hypotheses directly; `p=4` is refuted as composite
  (`refute_eq_four_against_prime`, new) via the ALREADY-DECLARED
  `not_prime_of_dvd_of_ne` at `(2,4)` — `dvd_mul 2 2` defeq `dvd 2 4`, and
  `2≠1`/`2≠4` both come from the ALREADY-EXISTING `finite::ne_of_lt` off a
  cheap `Le`/`Lt` fact (`Le 2 2` defeq `Lt 1 2`; `le_add_right 3 1` defeq
  `Lt 2 4`). No new numeral-disequality infrastructure was needed — it
  already existed and this lane found it before rebuilding it (per the
  standing "search for the STEP" rule).

**What the kernel REJECTED and why: nothing.** Both theorems were accepted
on the first `cargo test` run against the kernel — no rejected drafts, no
`TypeMismatch`/`UnboundFVar` bisecting needed. The one real failure mode hit
repeatedly was the OWN INVENTORY test (`every_nat_declaration_is_checked_
and_axiom_free`), which correctly named each new declaration as unchecked
until it was added to `theorem_names` — exactly the "any test named 'every
X' must derive its X from the authority" discipline this repo's own
CLAUDE.md documents; it worked as designed.

**Whether the fib-2 lane's "pair-induction cannot close" analysis held up:**
yes, on my own re-derivation. `n <= fib(n)+1` is an equality at `n=2,3,4`,
so any single margin `M` a bare induction carries forward needs slack that
does not exist below `n=5` — confirmed both algebraically (mirroring their
check) and constructively: `le_fib_self`'s OWN pair-induction only starts
being provable from `n=5` onward for exactly this reason (its base case is
`Le 5 (fib 5)`, an EQUALITY, with zero room to spare beneath it).

Prelude counts: `nat_prelude_tests.rs` `D + T` moved **83 + 422 -> 83 +
424** (two new theorems; recounted from the test's own panic message at
each step, not incremented by hand).

Verified: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 116
passed, 0 failed (was 114 before this lane's two theorems). `cargo fmt
--edition 2024` on touched files, plus `cargo fmt --all --check` clean.
`cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D
warnings` — clean. `python3 scripts/validate-facts.py` — 1909 facts, 0
errors, `proved` 1809 -> 1811. Both facts' `checker_command`s executed
directly (not just structurally mirrored) and confirmed exit 0.
