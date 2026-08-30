# Notes: 270-nat-xor-ne-zero

Detail moved out of [`../status/270-nat-xor-ne-zero.md`](../status/270-nat-xor-ne-zero.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Built via `mt` (modus tollens, `Π a b, (a → b) → (b → False) → (a → False)`)
applied twice, **not** via an `Iff (Eq _ 0) (Eq _ _)` intermediate that would
then need an extra `Iff`-not-congruence combinator this prelude does not have.
`mt` was already declared in the logic prelude (`prelude.rs`) and had never
been used anywhere in `nat_prelude` until this fact — partially applying it
with just the two propositions and a direction lemma gives a complete
`Not`-to-`Not` implication directly, with no further wrapping.

Two new directional corollaries feed it:

1. **`Eq (xor a b) 0 → Eq a b`** (the `mpr` side) — does **NOT** need
   `Nat.xor_xor_cancel_left`/`_right` at all, confirming
   `docs/plan/status/268-…`'s own handoff note exactly. Per bit,
   `Nat.testBit_xor` plus the hypothesis gives `Eq (xor_bit (testBit a i)
   (testBit b i)) 0`; a new per-bit lemma (`xor_bit_eq_zero_implies_eq`)
   closes that to `Eq (testBit a i) (testBit b i)` given both are `<= 1`
   (`Nat.testBit_le_one`), reusing `round_trip_le_one` (built for
   `xor_xor_cancel_left`) rather than re-deriving a bound lemma. Two more new
   helpers feed it: `digitize_eq_zero_implies_false` (`Eq (digitize cond) 0 →
   Eq cond false`, needing one genuine ex-falso via `Nat.succ_ne_zero` in its
   `cond = true` branch) and `bool_eq_of_xor_eq_false` (`Eq (xor_fn a b) false
   → Eq a b`, confirmed unconditionally true over all 4 `Bool` pairs by a
   Python simulation before any Rust was written).
2. **`Eq a b → Eq (xor a b) 0`** (the `mp` side) — a new `Nat.xor_self`-shaped
   argument (`xor_self`): `congrArg (xor a ·)` on the hypothesis gives `Eq
   (xor a a) (xor a b)`, and a new per-bit self-cancellation-to-zero fact
   (`xor_bit_self_zero`, built from a new `Bool`-level `xor_fn x x = false`
   fact, `bool_xor_self`, a 2-leaf `Bool.rec` split both closing by `refl`)
   plus `Nat.eq_of_testBit_eq` gives `Eq (xor a a) 0`.

**No `false_true_elim` combinator is needed anywhere in this fact's route.**
The one genuinely impossible hypothesis encountered
(`digitize_eq_zero_implies_false`'s `cond = true` branch, where the
hypothesis reduces to the impossible `Eq (succ zero) zero`) is refuted
directly via `Nat.succ_ne_zero` + `False.rec`, the same device
`gcd.rs`/`log.rs`/`fibonacci.rs` already use elsewhere in this prelude.
`bool_eq_of_xor_eq_false`'s own `a = true, b = false` leaf looked at first
like it would need an ex-falso too (the hypothesis is `Eq true false`) but
does not: at that leaf the hypothesis IS the goal (`Eq true false`), so the
branch is the identity function.

## New test and fact

`xor_ne_zero_iff_applies_at_a_concrete_discriminating_instance_and_symbolically`
(`nat_prelude_tests.rs`): at the discriminating pair `(a, b) = (3, 5)`
(`xor 3 5 = 6`), builds a genuine proof of `Not (Eq (xor 3 5) 0)` via
`Nat.succ_ne_zero` at `5` (`succ 5` is `refl`-defeq to `6`, hence to
`xor 3 5`), pushes it through `Iff.mp` to land on `Not (Eq 3 5)` (checked
NOT defeq to the negative control `Not (Eq 3 3)`), then pushes that back
through `Iff.mpr` to land back on `Not (Eq (xor 3 5) 0)`. Plus a symbolic
instantiation at a genuinely free `(a, b)` pair. Confirmed running by name
(`1 passed`, not `0 filtered out`).

New local fact `F:nat-xor-ne-zero-iff` (no `ml430` mirror, same reasoning as
its three siblings `F:nat-xor-assoc`, `F:nat-xor-xor-cancel-left`,
`F:nat-xor-xor-cancel-right`).

`theorem_names` + `the_build_is_deterministic` pin: `93 + 508` -> `93 + 509`
(one new theorem), taken from the panic's own mismatch after adding the name
to `theorem_names`.

## Commits (this lane)

1. `wip(nat): Nat.xor_ne_zero_iff -- NameId field only, not yet declared` —
   the `p.xor_ne_zero_iff` NameId field, landed within the first ten tool
   calls, before the theorem itself compiled.
2. `feat(nat): Nat.xor_ne_zero_iff -- last of the four xor_trichotomy sub-targets`
   — the full declaration, the new test, the coverage-list + pin update, and
   the new fact.

## A lane-hygiene note: this worktree's `git config axeyum.agent` was stale

`AXEYUM_AGENT=nat-xor-ne-zero` was exported in this lane's first Bash
invocation, but per this harness's own documented behaviour ("the working
directory persists between commands, but shell state does not"), that export
did **not** survive into later, separate tool invocations. `hooks/commit-msg`
falls back to `git config --get axeyum.agent` when the env var is unset, and
this worktree's repo-local config still held `fta-existence` — a PRIOR
lane's identity, left over from whatever last worked in this exact worktree
directory before this session. Both of this lane's commits above were
therefore stamped `Agent: fta-existence`, not `nat-xor-ne-zero`.

Per this repository's own hard rule ("NEVER amend unless explicitly
requested"), the two commits were left as-is rather than amended. The
repo-local config was corrected to `nat-xor-ne-zero` afterward so it does
not mislead whatever runs in this worktree next, but a coordinator relying
on `Agent:` trailers to attribute this lane's work should look for
`fta-existence` on these two SHAs, not `nat-xor-ne-zero`. The general lesson
for future lanes: `export AXEYUM_AGENT=...` alone is not durable across tool
calls in this harness — either bundle it into the SAME invocation as every
git command, or check `git config --get axeyum.agent` before your first
commit and correct it if stale.

## What `Nat.lt_xor_cases` (`F:ml430-nat-lt-xor-cases-c43a1e85`) still needs

All four sub-targets Mathlib's own `xor_trichotomy` proof composes
(`xor_assoc`, `xor_xor_cancel_left`, `xor_xor_cancel_right`,
`xor_ne_zero_iff`) are now landed. That was piece 4 of the 4 pieces
`docs/plan/status/260-nat-lt-xor-cases.md` named as blocking the fact. Three
larger pieces remain, per that file's own numbering:

1. **`exists_most_significant_bit`-equivalent** — `∀ n, n ≠ 0 → ∃ i, testBit
   n i = 1 ∧ ∀ j, i < j → testBit n j = 0`. Per
   `docs/plan/status/269-nat-msb-exists.md` (merged into this branch before
   this lane started): the "cheap half" (`Nat.testBit_eq_zero_of_lt`, above a
   value's own magnitude bound every bit reads zero) is landed as
   `F:nat-testbit-eq-zero-of-lt`; the "hard half" (the highest bit really IS
   set) is NOT yet kernel-checked — a scaffold exists
   (`msb_exists_of_le_fuel`) but that lane's own status is `PARTIAL`. Do not
   duplicate that work; once it lands, `lt_xor_cases` needs the natural
   witness `pred (size n)` shown to be the actual highest set bit.
2. **`lt_of_testBit`-equivalent** — bit-`i` disagreement plus agreement above
   `i` forces the order between two values. Genuinely new, not a corollary of
   anything landed so far; needs relating "agreement above `i`" to a quotient
   equality (`n / 2^(i+1) = m / 2^(i+1)`) plus a `sum_testBit_eq`-style
   decomposition bounding the tail below `2^i`.
3. **`xor_trichotomy` itself** — composes 1 and 2 above with the now-complete
   piece 4 (`Nat.xor_assoc _ _ _ ▸ Nat.xor_ne_zero_iff.2 h.ne`, per the
   Mathlib source at `Mathlib/Data/Nat/Bitwise.lean:266-297`) to get
   `a^^^b^^^c ≠ 0 → b^^^c<a ∨ c^^^a<b ∨ a^^^b<c`, and then `lt_xor_cases`
   itself is the cheapest remaining step once `xor_trichotomy` exists.

So piece 4 being complete removes exactly one of the four originally-named
blockers; pieces 1-3 above (2 and 3 in this file's numbering, since piece 1
`testBit_xor` was already landed before piece 4 started) are unaffected by
this lane's work and are comparable in scope to `binary.rs`'s `size`
addendum on their own.
