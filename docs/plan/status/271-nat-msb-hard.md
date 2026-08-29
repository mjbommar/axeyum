# Lane: nat-msb-hard -- `Nat.exists_most_significant_bit`, the hard half

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (F:nat-exists-most-significant-bit landed, admitted axiom-free on the first attempt)`, nat-msb-hard, 2026-08-29).**

## What landed

**`Nat.msb_exists_of_le_fuel : ∀ fuel n, Le n fuel → Not (Eq n zero) →
∃ i, And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j) zero)`**
(fuel-generalized) and **`Nat.exists_most_significant_bit`** (the `fuel :=
n` specialization via `le_refl`), both in
`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`. Both admitted,
axiom-free, on the FIRST real kernel-check attempt -- the entire
construction (~450 lines) compiled and kernel-checked without a single
`TypeMismatch` iteration. Registered as `F:nat-exists-most-significant-bit`.

This is the "hard half" both `docs/plan/status/265-nat-msb-order.md` and
`docs/plan/status/269-nat-msb-exists.md` diagnosed but did not build: the
highest bit really IS set, not just that no higher bit is needed.

## Does `Nat.size` shortcut this? No -- re-confirmed, not newly discovered

Re-read `binary.rs`'s `size` addendum before writing anything, per the
brief. `Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux
fuel n))` is proved by induction on `fuel` generalized over `n`, and it is
an UPPER bound only. It has no lemma relating `size n` to `size (n/2)` when
`n != 0` -- deliberately, since generalizing over ANY sufficient fuel is
exactly what let that proof avoid needing that relation. The route below
does not touch `size` at all; it is an independent fuel-recursion.

## Route taken: (b), an independent fuel-recursion -- NOT a `size`-recursion lemma

Both prior lanes sized this as needing either (a) a new `size`-recursion
lemma, or (b) an independent ~150-line bottom-up `msbAux`-fuel
construction. This lane took (b), and it landed at roughly 3x the
estimated size (the construction plus its two helper theorems is closer to
450 lines) but with NO surprises in the kernel-checking -- the size came
from carefully working out the term-level plumbing in advance (see below),
not from debugging cycles.

**Same fuel/half-recursion shape as `binary.rs`'s `declare_size_aux_lt_pow`**
(off-limits to edit but read closely for the pattern): induction on `fuel`
generalized over `n`, using the SAME `div_mod_lt_mul_iff` +
[`n_lt_mul_two`] bound to get `half <= f` from `half < n <= succ f` (`half
:= div n 2`). The step splits on **`beq half zero`**, not `beq n zero` --
the recursion bottoms out when `n`'s upper half vanishes, mirroring
Mathlib's own `Nat.binaryRec` case split, read at the pinned v4.30 source
(`Mathlib/Data/Nat/Bitwise.lean:176`, commit `c5ea0035…`):
`by_cases h' : n = 0` inside the `bit b n hn` case, where that inner `n` is
this proof's `half`.

**The move that made this tractable**: `testBit n (succ i) ≡ testBit
(div n 2) i` is `refl` (`Nat.test_bit_succ`'s own proof is `d.refl`, per
`binary.rs`'s `declare_test_bit_defs`). So a proof about bit `i'` of `half`
is ALREADY, with zero rewriting, a proof about bit `succ i'` of `n` -- the
kernel's `def_eq` check sees straight through it, for ANY value of `half`
(whether or not `half = 0`). This made the "bit is 1" witness component
trivial (`proof_one := hi` directly, no wrapping) in BOTH branches. Only
the UNIVERSALLY QUANTIFIED "every higher bit is zero" component needed an
explicit rewrite, because there the bit index `j` is an arbitrary bound
variable, not syntactically `succ`-shaped: `succ_pred_of_pos` turns
`Lt zero j` into `j = succ (pred j)`, and transporting along that equation
(twice -- once to shift the hypothesis down, once to shift the conclusion
back up) is the one genuinely new piece of machinery, inlined in both
branches.

- **Base (`fuel=0`)**: `Le n 0` and `Not (Eq n 0)` are jointly
  contradictory -- `succ_pred_of_pos` turns the positivity into
  `n = succ (pred n)`, transported into the bound gives
  `Le (succ (pred n)) 0`, refuted by `not_succ_le_zero`.
- **Step (`fuel=succ f`)**, split on `beq half zero`:
  - **`half = 0`**: `n < 2` from the `div_mod_exec` reconstruction
    `n = 2*half + (n mod 2)` collapsing (given `half = 0`) to
    `n = n mod 2 < 2`; `n != 0` then forces `n = 1` via `le_antisymm`
    against `n`'s own positivity. Witness `0`; bit `0` is `1` via
    `test_bit_zero`/`mod_eq_self_of_lt`; every `j > 0` bit is `0` via
    `test_bit_of_zero` transported along `half = 0` then along
    `j = succ (pred j)`.
  - **`half != 0`**: `half <= f` (same bound `declare_size_aux_lt_pow`'s
    own step uses); the IH at `half` supplies `i'` via `exists_rec`
    elimination, witness `succ i'`.

No new `size`-recursion lemma exists after this lane. If a future lane
wants route (a) instead (for some other purpose -- this fact does not need
it), the gap `docs/plan/status/265-nat-msb-order.md` identified is
unchanged: `size`'s definition (`sizeAux n n`, self-referential fuel
choice) still has no equation relating `size n` to `size (n/2)`.

## Codomain verdict for the Mathlib mirror

**Stays a local fact, confirmed before any proof work started.** Read the
pinned Mathlib v4.30 source directly at
`/data0/axeyum/lean-import-toolchain/mathlib4/Mathlib/Data/Nat/Bitwise.lean:176`:

```
theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = true ∧ ∀ j, i < j → testBit n j = false
```

`Bool`-valued, matching the pattern of every other `testBit`-family mirror
this session found unflippable for the same reason (`F:nat-lt-of-testbit`,
`F:nat-testbit-xor`, `F:nat-testbit-eq-zero-of-lt`). No `ml430` fact for
this specific Mathlib statement existed in the ledger. Landed as the new
local fact `F:nat-exists-most-significant-bit` instead.

Note also that Mathlib's own proof structure (`Nat.binaryRec`, splitting
on whether the "rest" `n` is zero, IH at that rest, witness `k+1`) is
exactly the shape this lane's fuel-recursion mirrors -- the two
constructions are the same argument, translated from a bit-decomposition
recursor into an explicit fuel/`div` recursion because this kernel's
`Nat.binaryRec` (built in an earlier session, see
`docs/plan/status/255-nat-binaryrec.md`) is deliberately non-dependent (its
motive is constant in `n`; a fuel encoding cannot be a dependent
recursor -- see the CLAUDE.md gotcha on this), so it was simpler to work
directly with the fuel/half machinery this proof already needed for the
`half <= f` bound anyway, rather than route through `binaryRec` itself.

## What `Nat.lt_xor_cases` (`F:ml430-nat-lt-xor-cases-c43a1e85`) still needs

Of the four pieces `docs/plan/status/260-nat-lt-xor-cases.md` named:

1. ~~`testBit_xor`~~ -- **DONE** (`F:nat-testbit-xor`).
2. **`exists_most_significant_bit`** -- **DONE, this lane**
   (`F:nat-exists-most-significant-bit`). Both the cheap half
   (`F:nat-testbit-eq-zero-of-lt`) and the hard half now exist.
3. ~~`lt_of_testBit`~~ -- **DONE** (`F:nat-lt-of-testbit`).
4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`** --
   checked directly in this worktree (post-merge, commit `a2630286d`):
   `xor_algebra.rs` declares `xor_assoc`/`xor_xor_cancel_left`/
   `xor_xor_cancel_right`, but its own module doc says plainly
   `Nat.xor_ne_zero_iff` is **NOT declared in this file** and was not found
   anywhere in the ledger at the time that file was written. So piece 4 is
   three-quarters landed, not fully -- `xor_ne_zero_iff` is still open, and
   a sibling lane was reported mid-`xor_ne_zero_iff` at the start of this
   session, so check `git log`/the file directly (not this handoff) before
   dispatching it as new work.

**So pieces 1-3 are now all DONE, and piece 4 needs exactly one more
lemma.** Once `Nat.xor_ne_zero_iff` lands, assembling `Nat.lt_xor_cases`
itself becomes the next task -- composing `exists_most_significant_bit`
(on `a xor b xor c`, per `xor_trichotomy`'s route) with `lt_of_testBit` and
the `xor_assoc`/`xor_xor_cancel_*`/`xor_ne_zero_iff` family to route the
hypothesis. Per both prior lanes' assessment, the final composition is
comparatively small next to the four pieces themselves -- worth attempting
directly (or bundled with `xor_ne_zero_iff` in one lane) rather than
resizing as another multi-piece lane, now that three of four pieces are
landed and the fourth is a single named lemma.

## Commits (this lane)

1. `wip(nat): msb_exists_of_le_fuel scaffold -- Nat.exists_most_significant_bit hard half, NOT yet kernel-checked`
   (`e9247edd2`) -- the full proof term construction, compiles clean via
   `cargo check -p axeyum-lean-kernel`. Landed within the first ten tool
   calls per the standing rule (NOT yet kernel-checked at that point, as
   the message says).
2. `feat(nat): Nat.exists_most_significant_bit -- the hard half, admitted axiom-free`
   (`13be0b204`) -- confirms both theorems kernel-check on the first real
   attempt, registers them in `theorem_names`, recounts
   `the_build_is_deterministic`'s pin from the panic's own mismatch
   (93+508 -> 93+510), adds the dedicated concrete+symbolic test, and the
   fact `F:nat-exists-most-significant-bit`.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- **155 passed, 0
failed** (153 before this lane, +2: the new
`exists_most_significant_bit_applies_at_a_concrete_instance_and_symbolically`
test, confirmed to run BY NAME (`1 passed`, not `0 filtered out`), plus the
symbolic-instantiation theorem it declares internally counting toward the
build rather than as a separate `#[test]`). `python3
scripts/check-test-attribute-integrity.py` -- 0 findings. `cargo fmt --all
--check` clean (files formatted individually with `rustfmt --edition 2024
<file>` first). `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings` clean. `python3 scripts/validate-facts.py` -- 1947 facts, 0
errors (new fact `F:nat-exists-most-significant-bit` added;
`F:ml430-nat-lt-xor-cases-c43a1e85` correctly remains `open`). All three of
the new fact's `checker_command`s run and confirmed passing before
committing (kernel admission by name via `nat_theorem_inventory`, the
instantiation test by name, axiom-free footprint via
`nat_axiom_inventory --require-axiom-free nat`). Workspace gate NOT run
(coordinator re-verifies before merging, per the lane brief). Not pushed.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-hard | Landed `Nat.msb_exists_of_le_fuel` (fuel-generalized) and `Nat.exists_most_significant_bit` (the hard half of piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`: the highest bit really IS set, not just that no higher bit is needed) as the new local fact `F:nat-exists-most-significant-bit` (Mathlib's `testBit` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via an independent fuel/half-recursion (same `div_mod_lt_mul_iff`+`n_lt_mul_two` bound `declare_size_aux_lt_pow` uses, split on `beq half zero` mirroring Mathlib's `Nat.binaryRec`) rather than a `size`-recursion lemma -- `Nat.size` re-confirmed to not shortcut this, since its own development only ever proves an upper bound; pieces 1-3 of the 4 pieces blocking `lt_xor_cases` are now all DONE, piece 4's status needs a fresh check before dispatching the final composition |
