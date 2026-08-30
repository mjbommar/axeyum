# Notes: 261-nat-land-assoc-finish

Detail moved out of [`../status/261-nat-land-assoc-finish.md`](../status/261-nat-land-assoc-finish.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Leaves 1–3 (at least one of `a,b,c` is `0`): all close by pure
  `d.refl`**, exactly as `257` traced — no lemma except leaf 3's use of
  the already-existing `land_aux_zero_left_any_fuel` for the one branch
  where the outer guard's checked slot is a genuinely stuck compound
  (`landAux sk 0 Y` with `Y` stuck), rather than a literal.
- **Leaf 4 (`a,b,c` all positive) — the hard leaf.** Dichotomizes the
  inner value `Y := landAux sk succ_b succ_c` via `Nat.zero_or_succ`
  first:
  - `Y = 0`: mirrors `Nat.land_aux_eq_zero_of_left_eq_zero` via
    `Nat.land_aux_comm_of_fuel`, permuting the argument order to
    `(sk, succ_c, succ_b, succ_a)` and chaining four `comm`/`congr`
    steps back to the goal's own shape.
  - `Y = succ q`: dichotomizes `X := landAux sk succ_a succ_b` via
    `zero_or_succ` again.
    - `X = 0`: the goal's RHS is *exactly*
      `Nat.land_aux_eq_zero_of_left_eq_zero(sk, succ_a, succ_b, succ_c,
      hx)`'s conclusion, verbatim, no massaging.
    - `X = succ p`: the fully generic case. Reconstructs `div(succ_p,2)`/
      `mod(succ_p,2)` from `X`'s own `2*rec_ab+bit_ab` decomposition
      **and independently** `div(succ_q,2)`/`mod(succ_q,2)` from `Y`'s
      own `2*rec_bc+bit_bc` decomposition, each via
      `Nat.div_mod_unique`+`Nat.div_mod_exec` (the same reconstruction
      pattern the propagation lemma already used once, now done twice).
      The recursive halves close via the **outer induction's own `ih`**
      applied at `(half_a, half_b, half_c)` — `landAux k rec_ab half_c`
      IS `landAux k (landAux k half_a half_b) half_c` syntactically,
      matching `ih`'s LHS exactly. The bit halves close via
      `Nat.mul_assoc(bit_a, bit_b, bit_c)` directly (no `symm` needed
      here, unlike the propagation lemma's analogous step — the
      associativity direction already matches). **No new arithmetic
      lemma anywhere in this leaf.**

**`Nat.land_assoc : ∀ a b c, Eq (land (land a b) c) (land a (land b c))`**
— re-fuels through the shared fuel `F := add(a, b)`, **not** `a+b+c`.
Verified directly (not assumed from `257`'s prose) that `c` never needs
its own `Le` bound: `Nat.land_aux_agree_of_fuel`'s two hypotheses
(`Le m fuel1`, `Le m fuel2`) constrain only the **`m`** position, never
`n`, so the `land_aux_assoc_of_fuel(F,a,b,c)` step and both
`land_aux_agree_of_fuel` calls involving `c` in the `n`-slot need
nothing about `c` at all. `Le a F` is direct (`le_add_right`); `Le b F`
needs one `add_comm` transport (`le_add_right(b,a)` gives `Le b (add b
a)`, not `Le b (add a b)`); `Le (land a b) F` chains `land_le_left` +
`le_trans`. This is `land_comm`'s exact bookkeeping shape, one argument
wider, matching `257`'s prediction.

**Registered in `theorem_names`** (coverage is environment-derived).
`the_build_is_deterministic`'s pin moved `93+490 → 93+492` (from the
panic's own mismatch, `left: 585`).

**Test**: `land_assoc_applies_at_a_nonzero_concrete_instance` — symbolic
restatement at fully free `a`/`b`/`c`, plus a concrete instance
`(a,b,c) = (3,7,5)` chosen so **both** `land(a,b)=3` and `land(b,c)=5`
are nonzero (exercising the hard leaf's fully-generic `X≠0,Y≠0`
sub-case, not one of its easy corners or the `X=0`/`Y=0` mirrors), with
the final answer `1` checked on both sides.

**141/141 `nat_prelude::` tests pass** (was 140 before this lane's edits,
+1 land_assoc test). `cargo fmt --edition 2024 --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: both
clean.

## A pre-existing bug fixed along the way (not this lane's proof work)

`cargo clippy -D warnings` failed on entry with a "duplicated attribute"
error and a "function never used" error in `nat_prelude_tests.rs`,
**already present at the merge commit `6cac60005`, before any of this
lane's edits** (confirmed via `git show`). It was exactly the "TWO LANES
ADDING FUNCTIONS TO ONE RUST FILE" splice shape CLAUDE.md documents: an
earlier concurrent-lane merge had inserted `land_bit`'s doc comment +
`#[test]` between `clog_computes_and_its_boundary_equations_apply`'s own
doc comment and its `#[test]`, leaving `land_bit`'s function with a
duplicated attribute and `clog`'s function with none — so `clog` had
been silently NOT RUNNING as a test (compiling as dead code) since that
merge. Fixed by moving `clog`'s doc+`#[test]` back to its own function;
`land_bit` keeps its own doc + single `#[test]`. No test body changed.
`clog` now runs and passes.

## Closing the fact

`F:ml430-nat-land-assoc-ad4775b8` flipped to `proved` via the standard
bitwise-family reconciliation pattern `F:ml430-nat-land-comm-7e6ad72e`
already uses: Mathlib's `Nat.land` is `Nat.bitwise and`, and our
`Nat.land` is proved equal to that specialization by
`Nat.bitwise_and_eq_land`, so `Nat.land_assoc` closes the SAME
proposition Mathlib states. Registered the native theorem as
`F:nat-land-assoc`. Checked
`scripts/gen-autogenesis-bitwise-family-projection.py` does not mention
either fact id — not pinned open independent of provability.

Both `checker_command`s were run for real, not just written:
`nat_theorem_inventory land_assoc` piped through an anchored
`grep -Ec '^Nat\.land_assoc[[:space:]]'` (count 1, `--release`, since the
debug build SIGABRTs on stack depth) and `nat_axiom_inventory
--require-axiom-free nat` (exit 0, `nat` trusted surface is 0).
`python3 scripts/validate-facts.py`: 1935 facts, 0 errors.

## `Nat.lor_assoc`: still not attempted, and here is precisely why

Not touched this lane, per the brief. Restating `docs/plan/status/252-nat-assoc-dichotomy.md`'s
characterization plainly, since it is still the accurate one and nothing
in this lane's work weakens it:

`lorAux`'s fuel-exhaustion row is **pass-through** (`n`, not `0`) —
`land`'s whole leaf-4 strategy (dichotomize on zero-ness, reconstruct via
`div_mod_unique`) does not transport, because:

- `lor a b = 0` forces `a = 0 ∧ b = 0` (OR's only zero is the all-zero
  pair) — a much STRONGER hypothesis than `land`'s zero case, not a
  parallel one.
- If `lor a b = 0` (so `a = b = 0`), then `lor a (lor b c) = lor 0 (lor 0
  c) = lor 0 c = c`, which is **NOT `0`** in general. So the direct
  analogue of `land_aux_eq_zero_of_left_eq_zero` — the one theorem that
  made `land`'s hard leaf tractable — is straightforwardly **false** for
  `lor`, not merely harder to prove.
- `lor_aux_comm_of_fuel` already needed `Le` hypotheses `land`'s never
  did (an existing, already-landed asymmetry, independently confirming
  this).

So a `lor_assoc` proof needs its own case analysis of `lorAux`'s truth
table from scratch, not a copy of `land`'s. The correct first step,
per this repository's own standing rule, is to **simulate `lorAux`'s
recursion in Python at small arguments before writing any Rust** — find
what actually propagates through OR (something like "if `lor a b`'s bits
are a superset of what's needed" rather than a zero/nonzero dichotomy)
before attempting a kernel proof. This lane did not do that simulation;
it is the concrete next step for whoever picks up `lor_assoc`.

## Counts

`nat_prelude`: 140 passed before this lane (at merge commit `6cac60005`,
already at that count post `nat-land-assoc-impl`'s propagation lemma),
**141 passed after** (1 new declaration set: `land_aux_assoc_of_fuel` +
`land_assoc`, both theorems; 1 new test; `clog`'s test also now runs,
which nets against the pre-existing splice bug rather than being new
lane content). `the_build_is_deterministic`'s pin: `93+490 → 93+492`
(taken from the panic's own mismatch). `nat` trusted surface still
`axiom=0 opaque=0 quotient=0`. `cargo fmt --edition 2024 --check`:
clean. `cargo clippy -p axeyum-lean-kernel --all-targets -- -D
warnings`: clean (after the splice fix above). `python3
scripts/validate-facts.py`: 1935 facts, 0 errors. NOT run: the aggregate
`just check` / `./scripts/check.sh` (coordinator re-verifies before
merging, per this repo's standing rule).

`F:ml430-nat-land-assoc-ad4775b8` is now `proved`. `F:ml430-nat-lor-assoc-82c4d0fd`
remains `open`, characterized above.

## Commits

- `566ff7cce` — wip: nat-land-assoc-finish checkpoint (first-ten-tool-calls
  commit, no source changes)
- `cb4d87593` — wip: `land_aux_assoc_of_fuel` + `land_assoc`, builds but
  not yet kernel-verified
- `ad4bb9b20` — feat: kernel-verified, registered, tested; 141/141
  `nat_prelude::` tests pass
- `5e7096acd` — fix: rustfmt `rec_agreement.rs`; repair the pre-existing
  merge splice blocking `clippy -D warnings`
- `6136bc9e0` — close: `F:ml430-nat-land-assoc-ad4775b8` — proved,
  axiom-free
