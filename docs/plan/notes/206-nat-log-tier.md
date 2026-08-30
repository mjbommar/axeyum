# Notes: 206-nat-log-tier

Detail moved out of [`../status/206-nat-log-tier.md`](../status/206-nat-log-tier.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What the kernel rejected: nothing.** Both declarations were accepted on the
first `Kernel::add_declaration` call. `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` went from 99 passed / 1 failed (only the pinned
`the_build_is_deterministic` count, recomputed from its own panic message
430 -> 432, i.e. 69 defs + 363 theorems, never hand-incremented) to **101
passed, 0 failed** after adding the two theorem names to `theorem_names` and
one concrete-instantiation test.

**`log_lt_self`/`log_mono_right` were NOT attempted, and this is a finding, not
a shortfall.** The brief's framing ("if it goes well, these follow") does not
survive a quick semantic check: `logAux b f n < f` is FALSE in general even
restricted to the diagonal-adjacent case — e.g. `logAux 2 1 2 = 1`, and
`1 < f = 1` is false. `log_lt_self` needs the strict bound specifically at the
DIAGONAL fuel (`f = n`), which `logAux_le_fuel`'s fuel-generalized induction
does not give for free; it needs its own argument (plausibly strong induction
on `n` itself, or a route through `b ^ log b n <= n`), which is genuinely more
than a corollary. Scoped out rather than forced.

**Not touched, per scope:** `clog_pos`/`log_le_clog` (sibling lane owns
`Nat.clog`, which does not exist on this branch); the `F:ml430-nat-log-*`
mirror facts (still `open` — this lane's own `F:nat-logaux-le-fuel` /
`F:nat-log-le-self` are new, separate kernel-lean facts, not a hand flip of
the mirrors, per the standing rule against claiming a Mathlib statement
without a reconciliation route).

**Gates run:** `rustfmt --edition 2024 --check` on all three touched files
(clean); `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
(clean — needed one `#[allow(clippy::too_many_arguments)]` on the new
8-argument `le_of_bool_select` helper, matching the existing convention on
`or_cases`); `cargo test -p axeyum-lean-kernel --lib nat_prelude::` (101
passed, 0 failed); `python3 scripts/validate-facts.py` (1875 facts, 0
errors, both new facts counted as `proved`/`kernel-lean`).
