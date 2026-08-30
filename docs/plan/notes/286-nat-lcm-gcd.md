# Notes: 286-nat-lcm-gcd

Detail moved out of [`../status/286-nat-lcm-gcd.md`](../status/286-nat-lcm-gcd.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `Nat.gcd_dvd_mul : gcd m n ∣ m * n` — one-liner, `gcd_dvd_left` composed
  with `dvd_mul_right_of_dvd`. No induction.
- `Nat.gcd_le_mul : 0 < m → 0 < n → gcd m n ≤ m * n` — `gcd_dvd_mul` plus
  `one_le_mul` on the two positivity hypotheses, combined via `le_of_dvd`.
- `Nat.eq_zero_of_lcm_eq_zero : lcm m n = 0 → m = 0 ∨ n = 0` — transport
  `gcd_mul_lcm` along the hypothesis to collapse `m*n` to `0`, then
  `mul_eq_zero` splits it. No induction.
- `Nat.lcm_assoc : (lcm m n).lcm k = lcm m (lcm n k)` — the "usually
  hardest" one, and it turned out to need NO induction at all: both sides
  divide each other purely from the universal property
  (`dvd_lcm_left`/`dvd_lcm_right` give the "it's a multiple" half,
  `lcm_dvd` gives the "it's the least" half, `dvd_trans` chains them), and
  the pre-existing `dvd_antisymm` closes the two directions into one
  equality.
- `Nat.lcm_div : dvd k m → dvd k n → lcm (m/k) (n/k) = lcm m n / k` — the
  actual hardest one. Induction on `k`: at `k=0`, `div _ 0 = 0` collapses
  every term on both sides regardless of the hypotheses (no case-split on
  the hypotheses needed at all). At `k=succ k'`, write `m=k*m1`, `n=k*n1`
  (`dvd_elim` on the two hypotheses) and let `q := (lcm m n)/k`; the same
  mutual-divisibility technique `lcm_assoc` uses shows `lcm m1 n1 = q`,
  scaled by `k` through two new small reusable local helpers
  (`scale_dvd : dvd a b -> dvd (k*a) (k*b)` and its converse
  `dvd_cancel_left_of_pos : Le 1 k -> dvd (k*a) (k*b) -> dvd a b`), then a
  third helper (`div_eq_of_mul_eq`) rewrites the conclusion from the
  witnesses `m1`/`n1` back to `div m k`/`div n k`.

**A single reusable helper beats N independent proofs, per the brief** —
here it's three small local helpers (`div_eq_of_mul_eq`, `scale_dvd`,
`dvd_cancel_left_of_pos`) shared between `lcm_div`'s body and (implicitly)
the same mutual-divisibility pattern `lcm_assoc` already established.

**One real bug caught before landing:** the first `lcm_assoc` negative
control compared the proof against a DIFFERENT correct grouping of the
same three numbers (`(lcm 2 4).lcm 3` vs `lcm 2 (lcm 3 4)`) and it
type-checked — lcm is associative AND commutative, so every parenthesization
of `(2,3,4)` reduces to the same `12`, making that control vacuous exactly
in the shape CLAUDE.md warns about. Replaced with a genuinely false
right-hand side (`6` instead of `12`).

**`gcd_le_mul`'s two `0 < x` hypotheses** are stated as `d.lt(zero, x)`
(this codebase's standing convention for such hypotheses, confirmed via
`mod_lt`'s declaration and its test-file callers) and fed directly into
`one_le_mul`, which wants `Le 1 x` — the kernel's own delta-unfolding
`def_eq` on `Nat.lt`'s `Regular(1)` definition accepts this with no
explicit conversion, exactly the technique `mod_lt`'s own callers
(`f.zero_lt_succ(three)` fed where `Lt zero four` is expected) already
rely on. Confirmed working, not merely assumed — this was the one place in
the whole lane genuinely uncertain before `cargo test` ran.

**Verification.** `scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib nat_prelude::` — **160 passed, 0 failed** (159 baseline + the new
`lcm_gcd_lemmas_apply_at_concrete_discriminating_instances` test). That
test instantiates all five new theorems at concrete numerals chosen to
discriminate a swapped argument or a wrong disjunct order (e.g.
`eq_zero_of_lcm_eq_zero` is checked once with the LEFT factor zero and
once with the RIGHT factor zero — a proof built as `Or (Eq n 0) (Eq m 0)`
instead of `Or (Eq m 0) (Eq n 0)` would fail `def_eq` on at least one of
the two), plus two genuinely-false negative controls
(`gcd_dvd_mul`'s dividend/divisor swapped, `lcm_assoc`'s wrong right-hand
side) confirmed rejected with `KernelError::DeclarationValueMismatch`.
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
`python3 scripts/check-test-attribute-integrity.py`: 0 findings.
`python3 scripts/validate-facts.py`: 2034 facts checked, 0 errors.
`nat_axiom_inventory --require-axiom-free nat`: `axiom=0 opaque=0
quotient=0`, exit 0.

Every `checker_command` verified BOTH directions against the prebuilt
`target/release/examples/nat_theorem_inventory` binary (no cargo lock): the
real name's `grep -Ec '^Nat\.<name>[[:space:]]'` count is 1 for all 10, and
a nonexistent name's count is 0 (grep exit 1).

The `the_build_is_deterministic` pin moved `93 + 524` → `93 + 529` (the
five new theorem names added to `theorem_names`), recomputed from the
panic message's own mismatch, not hand-incremented blind.

All ten facts flipped to `epistemic_status: proved`, each with a
kernel-term evidence row (`nat_theorem_inventory -- <name>`, rendered type
compared verbatim against `formal.statement`) and an
exhaustive-enumeration axiom-freedom row
(`nat_axiom_inventory --require-axiom-free nat`). `proof_route:
kernel-lean`, `axiom_footprint: []` on all ten.

**Commits** (not pushed): `067d3c60f` (WIP: five new declarations,
untested), `03a2c21ef` (formatted + concrete-instance test, confirmed
green), `0bf53f907` (all ten fact-ledger JSON updates). This status file is
uncommitted as of writing — commit it together with `PLAN.md`
regeneration.

**For the next lane on this family:** nothing left open here — 10 of 10
closed. If more `Nat.lcm`/`Nat.gcd` mirrors get preregistered, the three
new local helpers in `lcm_gcd_lemmas.rs`
(`scale_dvd`/`dvd_cancel_left_of_pos`/`div_eq_of_mul_eq`) plus the
mutual-divisibility-via-`dvd_antisymm` pattern `lcm_assoc`/`lcm_div` both
use are the reusable pieces to reach for first.
