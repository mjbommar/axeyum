# Notes: 203-nat-sqrt

Detail moved out of [`../status/203-nat-sqrt.md`](../status/203-nat-sqrt.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What the kernel rejected: nothing.** All four declarations (`sqrtAux`,
`sqrt`, `sqrt_zero`, `sqrt_one`) were accepted on the first attempt. Both
boundary theorems are fully concrete instantiations (no free variable
survives past the literal arguments), so both close by a single `Eq.refl` —
no induction needed, unlike three of `Nat.log`'s four boundary theorems.

**`sqrt_zero` and `sqrt_one` are simultaneously the `n ∈ {0, 1}` instances of
the still-open Mathlib family `Nat.sqrt_eq (n) : sqrt (n * n) = n`**
(`F:ml430-nat-sqrt-eq-79ae8eae`) — `0 * 0` and `1 * 1` reduce to `0` and `1`
definitionally, so they land in the `sqrt_zero`/`sqrt_one` shape rather than
being restated as `sqrt (n*n) = n` at a literal `n`. The GENERAL theorem is
not claimed: it needs an inductive argument that the linear search never
overshoots, which was out of scope for this pass.

**Not attempted, deliberately:** the 14 `F:ml430-nat-sqrt-*` mirror facts
(`sqrt_le`, `sqrt_lt`, `sqrt_pos`, `sqrt_eq_zero`, `sqrt_le_self`,
`sqrt_lt_self`, `sqrt_le_sqrt`, `sqrt_eq`/`sqrt_eq'`, …) stay `open`. Our
`Nat.sqrt` is a *different construction* from Mathlib's (linear search vs.
Newton's method, though the same VALUE), so claiming their statements by hand
would be the checker-that-cannot-fail defect this repository's CLAUDE.md
names explicitly. The next tier needs real induction — generalizing
`sqrtAux n f <= f` or similar over a free fuel argument, the same technique
`Nat.log`'s harder lemmas need — and is sized as a follow-on, not attempted
here.

**Gate state at the time of this commit:** `cargo check -p axeyum-lean-kernel
--lib` clean; `cargo test -p axeyum-lean-kernel --lib nat_prelude` 105
passed, 0 failed (includes `sqrt_computes_and_its_boundary_equations_apply`,
`the_build_is_deterministic` at `71 + 363`, and
`every_nat_declaration_is_checked_and_axiom_free`); `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` clean;
`python3 scripts/validate-facts.py` 0 errors over 1875 facts.
`nat_prelude` definition+theorem count: 69 (`D`) + 361 (`T`) before this lane
→ 71 + 363 after (2 definitions, 2 theorems).
