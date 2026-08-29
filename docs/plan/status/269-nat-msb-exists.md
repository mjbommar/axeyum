# Lane: nat-msb-exists -- `Nat.exists_most_significant_bit` (piece 2 of 4)

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL (cheap half landed as F:nat-testbit-eq-zero-of-lt; hard half NOT built, precise diagnosis below)`, nat-msb-exists, 2026-08-29).**

## What landed

**`Nat.testBit_eq_zero_of_lt : forall n j, Lt n (pow 2 j) -> Eq (testBit n
j) zero`** (`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`) --
admitted, axiom-free, on the FIRST real kernel-check attempt (only a
`clippy::doc_markdown` nested-backticks nit needed fixing afterward).
Registered as `F:nat-testbit-eq-zero-of-lt`. This is exactly the "cheap
half" `docs/plan/status/265-nat-msb-order.md` diagnosed but did not build:
above a value's own magnitude bound, every bit reads zero.

Route: `value_eq_sum_range` (already in `bit_order.rs`, private) at
`bound := j` gives `sumRange f_n j = n` directly from the hypothesis (via
`mod_eq_self_of_lt`); the same helper at `bound := succ j` needs
`n < pow 2 (succ j)`, obtained via `pow_j <= pow_j + pow_j = mul pow_j 2`
(`= pow 2 (succ j)` by `pow_succ`/`refl`), bridged with `le_add_right` +
`double_eq` (the exact same bridge `Nat.self_lt_two_pow_add`'s induction
step already uses) composed with `lt_of_lt_of_le`. `sum_range_succ` then
forces `n = add n (f_n j)` (substituting the first equation), so
`add_left_cancel` against `n = add n 0` collapses `f_n j` to `0`; since
`f_n j` is literally `mul (testBit n j) (pow 2 j)` up to beta,
`mul_eq_zero` splits into `testBit n j = 0` or `pow 2 j = 0`, and
`pow_pos` + `lt_irrefl` + `Or.resolve_right` rule out the second
disjunct. No new general arithmetic lemma was needed beyond what
`self_lt_two_pow_add`'s own proof already established the technique for.

## Codomain verdict for the Mathlib mirror

**Stays a local fact, confirmed before any proof work started.** Mathlib
v4.30's `Nat.testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i =
false` (`Mathlib/Data/Nat/Bitwise.lean`, read at the pinned commit
`c5ea0035…`) is `Bool`-valued; this kernel's `Nat.testBit` returns a value
in `{0, 1}` as a `Nat` (`binary.rs`'s module doc). Same pattern as
`F:nat-lt-of-testbit`/`F:nat-testbit-xor`: a Nat-valued proof cannot
honestly flip a Bool-typed mirror. No `ml430` fact for this specific
Mathlib statement existed in the ledger at the time this was registered.

## Does `Nat.size` shortcut the hard half? (NOT landed, confirmed again)

**No new information beyond what `docs/plan/status/265-nat-msb-order.md`
already established** -- this lane did not attempt the hard half, but
re-confirms the diagnosis by re-reading `binary.rs`'s `size` addendum
before writing anything:

`Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux fuel
n))` is an UPPER bound (`n < 2^(size n)`), proved by induction on `fuel`
generalized over `n`. **The hard half needs a LOWER bound**
(`2^(size n - 1) <= n` for `n != 0`, i.e. "the top bit is really set, not
just that no higher bit is needed") which is NOT the same fact and is not
a corollary of the upper bound. `sizeAux`'s definition (`sizeAux (succ f)
n := if beq n 0 then 0 else succ (sizeAux f (n/2))`, a self-referential
fuel choice matched against `size n := sizeAux n n`) has no existing
lemma relating `size n` to `size (n/2)` when `n != 0` -- `size_aux_lt_pow`
was deliberately built to generalize over ANY sufficient fuel specifically
so it would NOT need that relation, and that is exactly the relation the
hard half is missing.

Building it needs one of:
- **(a)** A new lemma of the shape `n != 0 -> size n = succ (size (n/2))`
  (unfolding `sizeAux` at the CANONICAL fuel `n` on both sides, which is
  more delicate than it looks because `n` is not literally `succ`-shaped
  and the two sides use different fuel values, `n` vs `n/2`), from which
  the top-bit-set property follows by an outer induction; or
- **(b)** An independent bottom-up `msbAux`-fuel construction (sketched in
  `docs/plan/status/260-nat-lt-xor-cases.md` piece 2), mirroring
  `declare_size_aux_lt_pow`'s own proof shape and size -- estimated
  ~150 lines there, unchanged by anything found this lane.

Neither was attempted here; this lane's entire budget went to the cheap
half plus its tests/fact/handoff, per the brief's "landing the cheap half
alone, with a precise account of the hard one, is a good outcome."

## What `Nat.lt_xor_cases` (`F:ml430-nat-lt-xor-cases-c43a1e85`) still needs

Stays `open`. Of the four pieces:

1. ~~`testBit_xor`~~ -- **DONE** (`F:nat-testbit-xor`).
2. **`exists_most_significant_bit`** -- **PARTIAL.** Cheap half (this
   lane, `F:nat-testbit-eq-zero-of-lt`) DONE. Hard half ("the highest bit
   is set", (a) or (b) above) NOT DONE -- still its own lane-sized task.
3. ~~`lt_of_testBit`~~ -- **DONE** (`F:nat-lt-of-testbit`).
4. **`xor_assoc`, `xor_xor_cancel_{left,right}`, `xor_ne_zero_iff`** --
   status not re-verified by this lane; briefed as "largely landed with a
   sibling finishing the remainder" at the start of this session. Check
   `xor_algebra.rs` and `git log` before assuming it landed or is still
   open.

Once the hard half of piece 2 and piece 4 land, assembling the full
`exists_most_significant_bit` existential (from the hard half's
"top bit index exists and is set" plus this lane's "every bit above it is
zero") and then `lt_xor_cases` itself (via `xor_trichotomy`'s route:
`exists_most_significant_bit` composed with `lt_of_testBit`,
`xor_assoc`/`xor_xor_cancel_*`/`xor_ne_zero_iff` to route the hypothesis)
is comparatively small -- the expensive piece remaining is the hard half
of piece 2, not the final composition.

## Commits (this lane)

1. `feat(nat): Nat.testBit_eq_zero_of_lt -- piece 2's cheap half, first attempt`
   (`928f82f45`) -- field + wiring + proof, compiles clean, landed within
   the first ten tool calls per the standing rule (WIP: not yet
   kernel-checked at that point).
2. `feat(nat): Nat.testBit_eq_zero_of_lt -- tests, fact, admitted axiom-free`
   (`5465290dc`) -- `theorem_names`/`the_build_is_deterministic` pin
   (93+505 -> 93+506), the concrete+symbolic instantiation test, the fact
   ledger entry `F:nat-testbit-eq-zero-of-lt`, and a doc-markdown clippy
   fix.

## Verified

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- **153 passed, 0
failed** (152 before this lane, +1 new test:
`test_bit_eq_zero_of_lt_applies_at_a_concrete_instance_and_symbolically`,
confirmed to run BY NAME, `1 passed`, not `0 filtered out`).
`python3 scripts/check-test-attribute-integrity.py` -- 0 findings.
`cargo fmt --all --check` clean (files formatted individually with
`rustfmt --edition 2024 <file>`). `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `python3 scripts/validate-facts.py`
-- 1944 facts, 0 errors (new fact `F:nat-testbit-eq-zero-of-lt` added;
`F:ml430-nat-lt-xor-cases-c43a1e85` correctly remains `open`). All three
of the new fact's `checker_command`s run and confirmed passing before
committing (kernel admission by name, the instantiation test by name,
axiom-free footprint). Workspace gate NOT run (coordinator re-verifies
before merging, per the lane brief). Not pushed.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-msb-exists | Landed `Nat.testBit_eq_zero_of_lt` (the "cheap half" of `exists_most_significant_bit`, piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`) as the new local fact `F:nat-testbit-eq-zero-of-lt` (Mathlib's `Nat.testBit_eq_false_of_lt` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via `value_eq_sum_range` at `bound := j` and `bound := succ j` plus `sum_range_succ`/`add_left_cancel`/`mul_eq_zero`; the "highest bit is set" hard half remains open and is re-confirmed (not newly discovered) to need either a new `size`-recursion lemma relating `size n` to `size (n/2)` or an independent ~150-line bottom-up `msbAux`-fuel construction |
