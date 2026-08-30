# Notes: 254-nat-parity-lowbit

Detail moved out of [`../status/254-nat-parity-lowbit.md`](../status/254-nat-parity-lowbit.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`mod_two_mul_add_of_lt`** (`Eq (mod (add (mul two x) r) two) r`, given
`Lt r two`) is the one genuinely new arithmetic fact, and it is SIMPLER
than `binary.rs`'s `declare_mod_two_mul_split` (which it otherwise
mirrors exactly — hand-built `divMod` witness compared against
`div_mod_exec` via `div_mod_unique`): the dividend IS `add (mul two x) r`
verbatim, so the equation half of the hand-built witness is `refl`, no
reconstruction algebra needed. Made `pub(super)` (was going to stay
`fn`-private, promoted once `xor_parity.rs` needed it too).

Verified: `even_iff_mod_two_eq_zero_and_odd_iff_mod_two_eq_one_apply_and_agree`
round-trips both bridges at concrete witnesses (`Even 4 <-> Eq (mod 4 2)
0`, `Odd 5 <-> Eq (mod 5 2) 1`) with transposed-remainder negative
controls, the same swap-detecting shape
`parity_predicates_apply_at_concrete_witnesses_and_are_axiom_free` uses
for `even_iff_odd_succ`.

### 2. `Nat.even_xor`, closing `F:ml430-nat-even-xor-78a39432`

New `nat_prelude/xor_parity.rs`:

```
Nat.even_xor : ∀ m n, Iff (Even (xor m n)) (Iff (Even m) (Even n))
```

Admitted by the trusted kernel gate, axiom-free (confirmed both by
`every_nat_declaration_is_checked_and_axiom_free`'s environment-derived
sweep and `nat_axiom_inventory --require-axiom-free nat`).

**The codomain question that killed four `testBit` mirrors did not apply
here** — the statement is about `Even`, not `testBit`, so there is no
`Bool`-vs-`Nat` mismatch to route around.

Structure, via `cases_zero_succ` on `m` then `n`:

- **`m = 0`**: `xor 0 n` reduces to `n` by PURE `refl` (fuel = literal
  `0`, hits `bitwiseAux`'s fuel-exhaustion row directly — no lemma
  needed, unlike `bitwise_zero_left`'s general-`f` version, because here
  `f = xor_fn` is concrete and the boundary `Bool`s reduce too). The goal
  becomes `Iff (Even n) (Iff (Even 0) (Even n))`, closed by a generic
  "one side of an `Iff` is unconditionally true" construction needing
  only a hand-built `Even 0` (`even_zero`, witness `0`, `refl`).
- **`n = 0`, `m` already `succ`-shaped**: `xor m 0` reduces to `m` the
  same way (the `n = 0` guard fires immediately, regardless of whether
  `m`'s predecessor is symbolic). Same construction, mirrored.
- **both nonzero (`even_xor_hard_case`)**: with `m = succ pm`,
  `n = succ pn` both literal, `beq (succ _) zero` reduces to `false`
  regardless of the predecessor, so BOTH zero-guards in `bitwiseAux`'s
  `succ_minor` row collapse by `refl`, landing on
  `xor m n ≡ add (mul two (bitwiseAux xor_fn pm (m/2) (n/2))) combined_nat`
  where `combined_nat` is the per-bit XOR value. The higher-order
  recursive term is NEVER INSPECTED — `mod_two_mul_add_of_lt` erases it
  under `mod _ 2` in one application (`x := bitwiseAux xor_fn pm (m/2)
  (n/2)`, `r := combined_nat`). Composing that with the bridge at `xor m
  n`, `m`, `n` reduces the WHOLE goal to a purely numeric fact about
  `combined_nat`, `mod m 2`, `mod n 2` — closed by `cases_mod_two` twice
  (four leaves, mirroring `rec_agreement.rs`'s `bit_agreement` nesting
  exactly, but proving an `Iff` at each leaf instead of an `Eq`).

Five small local `Iff` combinators (`iff_of_true_true`,
`iff_of_false_false`, `iff_trans`, `iff_symm`, `iff_congr_iff`) do the
composition; none existed in `LogicPrelude` as ready-made constants
(`iff_mp`/`iff_mpr`/`iff_intro` did).

**This was NOT sized as achievable going in.** The prior lane
(`docs/plan/status/253-nat-xor-parity.md`) and `xor.rs`'s own module doc
both estimated the bitwise case needed "new machinery... well beyond
defining xor" and left it open. What made it tractable: the per-bit
combine only needs to survive being DOUBLED-then-mod-2'd, so the
recursive term underneath it never has to be related to anything —
`mod_two_mul_add_of_lt` is a one-step arithmetic fact, not an induction
over the recursion. No `agree_by_fuel_induction`/
`agree_by_double_fuel_induction` needed.

Verified concretely, not just symbolically:
`even_xor_applies_at_concrete_even_even_and_odd_odd_instances` exercises
the genuinely-bitwise branch at `(4, 6)` [both even, `xor 4 6 = 2`] and
`(3, 5)` [both odd, `xor 3 5 = 6`], round-tripping `mp`/`mpr` against
independently hand-built `Even`/`Odd` witnesses. Both would fail to
type-check or land on the wrong side under a swapped `mp`/`mpr`, a wrong
bridge remainder, or a sign error in the per-bit combine.

### 3. Fact ledger

`F:ml430-nat-even-xor-78a39432` flipped `open` -> `proved` by
reconciliation with a new native `F:nat-even-xor` (three
`checker_command`s, each verified by hand before writing: kernel
inventory presence via anchored `grep -c`, the concrete evaluation test,
`nat_axiom_inventory --require-axiom-free nat`). `scripts/validate-facts.py`:
1929 facts, 0 errors.

`scripts/gen-autogenesis-bitwise-family-projection.py` does NOT mention
either `even-xor` or `lt-xor-cases` (checked directly — it names three
unrelated `testBit` facts per `docs/plan/status/244-nat-testbit-bitwise.md`),
so nothing pins either fact open independent of provability.

## What `F:ml430-nat-lt-xor-cases-c43a1e85` still needs

Stays `open`. Statement: `∀ a b c : ℕ, a < b ^^^ c -> a ^^^ c < b ∨ a ^^^ b
< c` (Mathlib's own proof inducts on `Nat.testBit` disagreement — the
HIGHEST bit at which the two sides differ). This lane's technique gives
it **no foothold**:

- `even_xor`'s whole method works because the goal only needs the LOW bit
  (mod 2) of the xor'd value, which survives exactly one step of
  unfolding. `lt_xor_cases` is a statement about the FULL value (an
  order comparison), which needs every bit, not just the low one — one
  step of `bitwiseAux`'s recursor is not enough, and there is no
  analogous "erase everything except what I need" move for `Lt`.
- A highest-differing-bit argument needs either: (a) a `testBit`-indexed
  induction with a "first bit where two numbers differ" construction
  (nothing like this exists in `binary.rs` — `sum_test_bit_lt` builds
  numbers FROM bits, not the reverse), or (b) a direct arithmetic
  argument via `size`/`log` bounding the differing high bits, which this
  prelude also does not have connected to `xor` specifically.
- Sizing: this is closer in shape to the `agree_by_fuel_induction`-class
  proofs (`bitwise_and_eq_land`, `land_comm`) than to anything in this
  lane's scope — a new induction relating TWO independently-tracked
  quantities (which bit differs, and the resulting order relation), not
  a one-step erasure.

Recommend treating it as its own lane, scoped explicitly around building
a "highest bit where two naturals disagree" construction over `testBit`,
rather than attempting it as a follow-on to this one.

## Commits (this lane)

1. `feat(nat): parity <-> low-bit bridge (compiles, builds prelude cleanly)`
   — the two bridge theorems, compiling but not yet test-verified (landed
   early per the ten-tool-call rule).
2. `test(nat): round-trip evaluation test for the parity <-> low-bit bridge`
   — the bridge's evaluation test, plus the `the_build_is_deterministic`
   pin fix (89+460 -> 89+462).
3. `feat(nat): Nat.even_xor, closing F:ml430-nat-even-xor-78a39432` — the
   new file, the fact-ledger flip, the evaluation test, and the pin fix
   (89+462 -> 89+463).

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 133 passed, 0
failed (130 before this lane). `cargo fmt --all --check` clean. `cargo
clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean.
`python3 scripts/validate-facts.py` — 1929 facts, 0 errors. Workspace gate
NOT run (coordinator re-verifies before merging, per the lane brief).
