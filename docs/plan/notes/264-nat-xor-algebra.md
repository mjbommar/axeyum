# Notes: 264-nat-xor-algebra

Detail moved out of [`../status/264-nat-xor-algebra.md`](../status/264-nat-xor-algebra.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`Nat.eq_of_testBit_eq` is the single highest-value thing built this lane**,
per the brief's own framing: it turns "same bits" into "same number" and is
what makes the whole `testBit_xor`-based route to `xor_assoc`/`xor_xor_cancel`/
`xor_ne_zero_iff` work at all, replacing any need for `land_assoc`'s
zero-propagation-lemma route or fuel-level case analysis on `bitwiseAux`.

## Does `testBit_xor` + extensionality shortcut the fuel induction? Yes, confirmed

The brief asked this explicitly. The answer, now measured rather than
speculated: **yes, completely**, for at least `xor_assoc`. Neither
`Nat.testBit_xor` (piece 1, already landed) nor `Nat.eq_of_testBit_eq` (this
lane) touches `bitwiseAux`'s fuel recursion directly — the entire route stays
at the `testBit`/`Bool` level until the very last step (`eq_of_testBit_eq`),
which itself uses only a lightweight fuel induction bounding `m` (not
`bitwiseAux`'s fuel at all). `docs/plan/status/260-…`'s land_assoc-transport
warning ("the `lor` analogue of `land_assoc`'s propagation lemma is false —
check before transporting") turned out moot: this route never needed a
propagation lemma of that shape for any of the three targets.

## `Nat.eq_of_testBit_eq` — the general extensionality lemma

```
∀ m n, (∀ i, Eq (testBit m i) (testBit n i)) → Eq m n
```

Generalizes `binary.rs`'s `Nat.zero_of_testBit_eq_zero` (the one-sided case)
to the two-value form. Proved by induction on a FUEL `k` bounding `m` (the
same device `rec_agreement.rs`'s fuel-irrelevance lemmas and
`testbit_bitwise.rs`'s own index/value bridge use), motive
`P(k) := ∀ n, ∀ m, Le m k → (∀ i, testBit m i = testBit n i) → Eq m n`:

- **Base** (`k = 0`): `Le m 0` forces `m = 0` (`le_antisymm`/`zero_le`); the
  bit hypothesis at `m := 0` forces every bit of `n` to `0` too (via
  `test_bit_of_zero` + `zero_of_testBit_eq_zero`), so `n = 0 = m`.
- **Step** (`k = succ pk`): case-splits on `m` (`cases_zero_succ`, folding the
  `Le`/bit hypotheses into the per-case motive rather than pre-introducing
  them — that helper's own documented device). At `m = succ pm`: the bit-0
  hypothesis gives the low-bit equation (`testBit _ 0` is `refl`-defeq to
  `mod _ 2`); the bit-`(succ j)` hypotheses give the IH's own hypothesis at
  the halved operands (`testBit _ (succ j)` is `refl`-defeq to
  `testBit (_ / 2) j`), bounded via `half_le_predecessor_of_succ`. Combined
  with the Euclidean reconstruction identity `x = 2*(x/2) + x%2`
  (`div_mod_exec`/`and_left`) on both sides, this gives `succ pm = n`.

Instantiating the fuel bound at `k := m` itself (`le_refl`) gives the public
two-argument statement directly.

## `Nat.xor_assoc` — via `testBit_xor` twice + `eq_of_testBit_eq`

`testBit (xor (xor a b) c) i` unfolds (via `testBit_xor` at `(xor a b, c)`
then at `(a, b)`) to `xor_bit (xor_bit (testBit a i) (testBit b i))
(testBit c i)`, and symmetrically for the right side. `eq_of_testBit_eq`
turns per-bit agreement back into the value-level equation, given a proof
that `xor_bit` itself associates.

**`xor_bit`'s algebra holds for ALL `x, y, z : Nat`, not merely bits in
`{0, 1}`** — this is the key structural fact that makes the route cheap.
`xor_bit(x, y) := bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` depends
on `x`, `y` ONLY through whether each equals `1`, so no `test_bit_le_one`
restriction is needed to prove `xor_bit_assoc`. Built as:

- `digitize` — `bool_select_nat cond 1 0`, factored out.
- `cases_bool` — a generic `Bool.rec` case split (the pattern
  `combined_lt_two`/`bool_select_nat_same` in `testbit_bitwise.rs`/`ops.rs`
  use inline, promoted here since this file needs it repeatedly).
- `beq_digitize_one` — the round-trip `Eq (beq (digitize cond) 1) cond`.
- `bool_xor_assoc` — the `Bool`-level fact, **confirmed by a Python
  truth-table simulation over all 8 triples before any Rust was written**
  (CLAUDE.md's standing rule). Proved by a SHALLOW `Bool.rec` split:
  splitting on the outer argument alone collapses `a = false` to `refl` for
  ANY `b, c` (since `xor_fn false w` reduces to `w` regardless of `w`'s
  shape — the outer scrutinee is the LITERAL `false`), so only 4 of the 8
  leaves need a further split (one more level on `b`, then on `c`, only
  inside the `a = true` branch).
- `congr_bool_to_nat` — a cross-carrier congruence `NatOps::congr` cannot
  supply: that helper's `eq_motive`/`transport` hardcode the `Nat` carrier
  for the HYPOTHESIS slot too, so a `Bool`-typed hypothesis `h : Eq Bool a b`
  with `f : Bool -> Nat` needs `bool_eq_motive`/`bool_transport` instead,
  with the conclusion built at `Nat`. **This is new, reusable
  infrastructure** — nothing in the prelude bridged a `Bool` equality into a
  `Nat` congruence before this file.
- `xor_bit_assoc` — lifts `bool_xor_assoc` through the round-trip to the
  `Nat` level.

## A genuine bug, found and fixed via a bisecting probe (not by reading a poisoned failure)

`Eq.refl.{1} Bool sel` was built for `sel := digitize(cond)` — a `Nat`-typed
value (`bool_select_nat`'s own output) — which is ill-typed: the round-trip
lemma's reflexivity witness needs to be of `beq (digitize cond) 1` (the
`Bool`-typed re-encoding), not of `digitize cond` itself. A blanket
`d.eq(` → `d.bool_eq(`, `d.refl(` → `d.bool_refl(` substitution across the
whole Boolean-algebra region (needed everywhere ELSE in that region) went
one step too far in exactly these two leaves.

**Wiring `declare_xor_assoc` into the live prelude and running the full
`nat_prelude::` suite poisoned all 147 tests with one opaque `TypeMismatch`**
(`expected: Bool, got: (fun x0:Bool => AxNat) Bool.false`) — the standard
"one bad declaration poisons the shared prelude build" failure mode this
project's CLAUDE.md documents. Rather than reading that message harder, the
fix was a throwaway `#[cfg(test)] mod debug_probe` at the bottom of
`xor_algebra.rs`, calling each helper directly against a hand-built
`Kernel`/`NatDev` (bypassing `declare_xor_assoc` and the full prelude
dispatch entirely) and checking `Kernel::infer` on each one in isolation:
`beq_digitize_one` alone, `bool_xor_assoc` alone, `congr_bool_to_nat` alone,
`xor_bit_assoc` alone. `beq_digitize_one` failed identically to the full
build; the other three passed. That isolated the defect to one function in
about two probe-and-rebuild cycles, versus reading a 147-line identical
failure list. The probe module was removed before the final commit — only
the corrected helpers remain in the file.

## Codomain / mirror check

No `ml430` fact for `xor_assoc`/`xor_xor_cancel_left`/`xor_xor_cancel_right`/
`xor_ne_zero_iff` exists in the ledger. Reading Mathlib's source directly at
the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
`Mathlib/Data/Nat/Bitwise.lean:266-275` **cites** all four names in
`xor_trichotomy`'s proof but does not **define** them there — grepping the
whole Mathlib tree for `theorem xor_assoc`/`xor_xor_cancel` under `Nat`
turns up nothing outside `Bitwise.lean`'s own call sites, meaning these are
Lean4 **core** lemmas about `Nat.xor`/`^^^`, not Mathlib-authored. So there
is no `ml430` mirror fact to flip for any of the four — every one that lands
here is a new local `F:nat-*` fact. `Nat.eq_of_testBit_eq` likewise has no
`ml430` mirror (no such general extensionality statement appears under this
or a related name in `Bitwise.lean`).

## What still needs building (2 of the original 4 sub-targets)

### `Nat.xor_xor_cancel_left` (`∀ a b, Eq (xor a (xor a b)) b`) — has a real complication, worked out below

The natural route (`testBit_xor` once + `eq_of_testBit_eq` + a per-bit
`xor_bit_cancel_left`) hits a genuine obstacle that `xor_bit_assoc` did NOT:

**`Eq (xor_bit x (xor_bit x y)) y` is FALSE for general `y : Nat`.** Tracing
the same digitize/round-trip/lift route `xor_bit_assoc` uses:

```
xor_bit(x, xor_bit(x, y))
  = digitize(xor_fn(bx, xor_fn(bx, by)))     [round-trip, same as xor_bit_assoc]
  = digitize(by)                              [bool_xor_cancel_left(bx, by)]
  = digitize(beq(y, 1))
  = bool_select_nat(beq(y, 1), 1, 0)
```

This equals `y` only when `y ∈ {0, 1}` — at `y := 5`, `digitize(beq(5,1))
= digitize(false) = 0 ≠ 5`. `xor_bit_assoc` never hit this because BOTH
sides of that identity stayed at the `digitize(...)` level throughout (never
needing to "match back" to a raw operand); `xor_cancel`'s conclusion is a
bare `y`, forcing exactly that match.

**The fix is available and cheap, just not built**: at the actual use site
(`y := testBit b i`), `Nat.testBit`'s codomain IS `{0, 1}`
(`test_bit_le_one` already proves `Le (testBit n i) 1` for every `n`, `i`).
So the real lemma needed is:

```
nat_round_trip_le_one : ∀ y, Le y 1 → Eq (digitize (beq y 1)) y
```

proved by case-splitting `y` via `Nat.lt_two_cases` (`Or (Eq y 0) (Eq y 1)`,
already in the prelude, `rec_agreement.rs`) — reachable from `Le y 1` via
`le_succ_succ` (`Le (succ y) (succ 1)`, and `succ (num 1)` is `refl`-defeq to
`num 2`, so this IS `Lt y 2` already, no separate lemma needed) — then two
leaves (`y = 0`: both sides `0`, `refl`; `y = 1`: both sides `1`, `refl`).
**This needs an `Or`-elimination combinator this file does not yet have**
(`p.logic.or_rec` or equivalent — `zero_or_succ_applies_at_a_compound_term_
and_is_consumed_by_or_elim`, an EXISTING test, names the pattern to copy;
find its construction rather than re-deriving one). Once that one small
lemma exists, `xor_bit_cancel_left` becomes: `xor_bit(x, xor_bit(x,y)) =
digitize(by) = y` given `Le y 1`, and `Nat.xor_xor_cancel_left` follows the
same `testBit_xor` + `eq_of_testBit_eq` shape `xor_assoc` used, instantiating
the round-trip lemma's hypothesis with `test_bit_le_one` at each bit.

`Nat.xor_xor_cancel_right` (`∀ a b, Eq (xor (xor a b) b) a`) is the
symmetric partner and should transport directly once `_left` exists (swap
the roles via `xor_comm`, already landed, or redo the same argument
mirrored).

### `Nat.xor_ne_zero_iff` — not attempted, but the forward direction is now cheap given the above

`xor a b = 0 → a = b`: for each bit `i`, `testBit (xor a b) i = testBit 0 i
= 0` (`test_bit_of_zero`), and via `testBit_xor`, `xor_bit (testBit a i)
(testBit b i) = 0`. Need `xor_bit x y = 0 → x = y` for `x, y ≤ 1` — a small
case split on the SAME `lt_two_cases`-derived `{0,1}` shape the
`xor_xor_cancel_left` fix above needs (4 cases via a doubled split, 3 of
which are immediate, 1 of which needs `bx ≠ by` i.e. `xor_fn bx by = true`
being impossible when the RESULT is `0`... actually simpler: `xor_bit(x,y)=0
` reduces `digitize(xor_fn(bx,by))=0`, i.e. `xor_fn(bx,by)=false` (round trip
again), i.e. `bx = by` as Bools by a `Bool.rec` case split, then `x = y`
follows from BOTH being ≤1 via the SAME `nat_round_trip_le_one`-style
argument this file's other gap needs). Then `eq_of_testBit_eq` closes
`a = b`. The reverse direction (`a = b → xor a b = 0`, via `xor a a = 0`)
and the `Iff` packaging were not sketched at all — smaller, but still real
work. Neither direction was attempted this lane.

## Commits (this lane)

1. `wip(nat): xor_algebra.rs scaffold -- Nat.eq_of_testBit_eq draft, uncompiled`
   — landed early (before compiling), per the ten-tool-call rule.
2. `feat(nat): Nat.eq_of_testBit_eq -- same bits imply the same number` —
   compiled, tested, formatted, fact registered.
3. `feat(nat): Nat.xor_assoc -- via testBit_xor twice per side + eq_of_testBit_eq`
   — the `xor_bit` Boolean-algebra machinery, `declare_xor_assoc`, the bug
   fix, evidence, fact.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **148 passed, 0
failed** (146 before this lane, +2: `eq_of_testBit_eq`'s and `xor_assoc`'s
evaluation tests). `cargo fmt --all --check` clean. `cargo clippy
-p axeyum-lean-kernel --all-targets -- -D warnings` clean. `python3
scripts/check-test-attribute-integrity.py` — 0 findings. `python3
scripts/validate-facts.py` — 1941 facts, 0 errors. Both new facts'
`checker_command` lines re-run directly and confirmed passing (not merely
present in the JSON). Workspace gate NOT run (coordinator re-verifies before
merging, per the lane brief). Not pushed.
