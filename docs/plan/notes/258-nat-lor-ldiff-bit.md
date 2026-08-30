# Notes: 258-nat-lor-ldiff-bit

Detail moved out of [`../status/258-nat-lor-ldiff-bit.md`](../status/258-nat-lor-ldiff-bit.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`lor`'s guard-tree leaves** follow `lor.rs`'s own absorbing-zero analysis:
  the fuel-exhaustion rows PASS THROUGH the full bit-encoded operand
  (`on_n_zero = bit a m`, `on_m_zero = bit b n`), not `land`'s constant `0`.
  The `n=0` leaf needs a case split on `a` (`or_fn(a, false)`'s scrutinee is
  `a`, needing it literal to ι-reduce — unlike `and_fn(a, false)`, which
  collapses to a constant regardless of `a`'s shape). The `m=0` leaf needs
  **no** split at all: `or_fn(false, b)` ι-reduces straight to `b` (literal
  scrutinee, `b` itself unexamined) and `lor(0, n)` is defeq `n`
  unconditionally (`lor_zero_left` is `refl`), so both sides land on the
  identical raw `bit b n` expression by pure defeq — `d.refl(bit_bn)` closes
  it directly.
- **`lor`'s per-bit combine** (`max` via `ble`, `or_cond_max_eq_cond`) needs a
  split on `a`, then — only in the `a = true` branch — a further split on
  `b`, because `ble 1 (cond b 1 0)` needs `cond b 1 0`'s VALUE, not just its
  shape. The `a = false` branch needs **no** further split: `Nat.ble 0 y`
  reduces to the literal `true` regardless of `y`'s shape (`ble`'s own
  zero-row), so `bool_select_nat true cond_b cond_a` reduces straight to
  `cond_b`, matching `cond (or false b)` (`or_fn(false, b)` reduces to `b`
  too) without ever inspecting `b`.
- **`ldiff` is the documented hybrid.** Its `n = 0` guard leaf is
  `lor`-flavoured (pass-through `bit a m`, needing the identical `a`-split +
  `Nat.ldiff_zero_right` as `lor_bit`'s `n=0` leaf). Its `m = 0` leaf is
  `land`-flavoured (constant `0`) and **reuses `land_guard_on_m_zero_leaf`
  verbatim** — no split needed, exactly as for `land`.
- **`ldiff`'s per-bit combine** (`beq`-gated: `if n%2=0 then m%2 else 0`,
  `ldiff_cond_eq_cond`) needs a FULL `a`-then-`b` split (4 leaves), unlike
  `land`'s single-split shortcut: `ldiff_fn(a, true) = bool_select_bool(a,
  not_true, false) = bool_select_bool(a, false, false)`, and both branches
  being the literal `false` does **not** let `Bool.rec` fire without `a`
  itself being literal — there is no general `Bool`-valued "both branches
  equal regardless of scrutinee" reduction, only the `Nat`-valued
  `bool_select_nat_same`. Simulated the full truth table in Python before
  writing any Rust, per the standing rule (the `land`-style shortcut would
  have been vacuous here).
- A local, generic-over-`NatOps` `bool_select_bool_local` + `ldiff_fn`
  (`a && !b`) back `ldiff_bit`'s target, since `bitwise.rs`'s private
  `bool_select_bool` and `ldiff.rs` were both off-limits; `or_fn` is imported
  from `bitwise.rs` (already `pub(super)`, no edit needed there).

**Mirror-flip honesty.** Both flips are honest by the same criterion
`land_bit`'s did: Mathlib v4.30 defines `Nat.lor`/`Nat.ldiff` via the same
`bitwise` recursion `Nat.land` uses, and `Nat.bitwise_or_eq_lor` (already
landed by an earlier lane) proves our `Nat.lor` equal to that specialization
— so this closes the SAME function Mathlib states, not a lookalike.
`scripts/gen-autogenesis-bitwise-family-projection.py`'s `MAPPINGS` names
three unrelated `testBit` facts (`F:ml430-nat-testbit-{land,lor,ldiff}`), not
these two — confirmed no pin conflict before flipping.

**Counts.** `nat_prelude`: 139 tests before this lane → **141** (two new
concrete-discriminating-instance tests, sharing one instance across all
three siblings: `a=true, m=2, b=false, n=3` gives `land=4`, `lor=7`,
`ldiff=1` — mutually discriminating). 2 new declarations, both theorems
(`lor_bit`, `ldiff_bit`) — `the_build_is_deterministic`'s pin moved
`93 + 489` → `93 + 491`, taken from the panic's own mismatch. `nat` trusted
surface still `axiom=0 opaque=0 quotient=0`
(`nat_axiom_inventory --require-axiom-free nat`). Two new facts
(`F:nat-lor-bit`, `F:nat-ldiff-bit`); both `F:ml430-nat-lor-bit-a2f98c7c` and
`F:ml430-nat-ldiff-bit-6be49bb8` flipped open → proved.
`python3 scripts/validate-facts.py`: 1936 facts, 0 errors.
`cargo fmt --edition 2024 --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean.
NOT run: the aggregate `just check` / `./scripts/check.sh`.

**Fixed in passing, same file, unrelated to this lane's subject:** a
misplaced `#[test]` attribute from lane `nat-bit-decode` had left
`clog_computes_and_its_boundary_equations_apply` as dead code and produced a
duplicate-attribute warning on `land_bit`'s own test — both flagged by
`cargo clippy --all-targets`, which is this lane's own required gate.
Restored the correct `#[test]` placement and doc-comment ownership.

**What is left in the `natural-bitwise` family.** The 7 facts CLAUDE.md's
Gotchas name as needing fuel-irrelevance (`land_comm`, `land_assoc`,
`lor_comm`, `lor_assoc`, `land_bit`, `lor_bit`, `ldiff_bit`) are now ALL
closed except `land_assoc`/`lor_assoc` — those two are the remaining
frontier for a follow-up lane, and per the same Gotchas entry they need
"something further" beyond fuel-irrelevance (unspecified here; not
attempted this lane).
