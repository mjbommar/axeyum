# Notes: 252-nat-assoc-dichotomy

Detail moved out of [`../status/252-nat-assoc-dichotomy.md`](../status/252-nat-assoc-dichotomy.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`Nat.add_eq_zero : ∀ a b, Eq (add a b) 0 → And (Eq a 0) (Eq b 0)`**
  (`algebra.rs`, next to the existing `Nat.mul_eq_zero`). Single
  `cases_zero_succ` on `b` (`Nat.add` recurses on its RIGHT argument only),
  with NO bridging lemma in either branch: `add a 0` is defeq `a` and
  `add a (succ y)` is defeq `succ (add a y)` in one iota step, so the
  hypothesis is reused directly in both leaves (unlike `mul_eq_zero`,
  which needs `succ_mul`+`add_succ` to expose the bare successor its
  contradiction branch needs).
- **`Nat.zero_or_succ : ∀ n, Or (Eq n 0) (Exists p, Eq n (succ p))`**
  (`algebra.rs`). This is the item the prior lane's diagnosis called for
  ("the dichotomy itself is buildable — it is exactly `cases_zero_succ`
  applied to a FRESH universally-quantified n, proved once and then
  instantiated at any concrete term including X") but did not build.
  Proved by `cases_zero_succ` on a fresh bound `n`: `Or_inl (Eq.refl 0)` at
  zero, `Or_inr (exists_intro pred (Eq.refl (succ pred)))` at the
  successor. Stated as a genuine `Or`-typed FACT (not left as raw
  recursor elimination) specifically so `d.lemma(p.zero_or_succ, &[X])`
  can be applied at an ARBITRARY compound term `X` (e.g.
  `landAux fuel a b`) and consumed with `Or.rec`/`or_elim` without ever
  needing `X`'s own formula folded into a `Nat.rec` motive — see "the wall,
  precisely" below for why that distinction is the whole difficulty.
- Both registered in `theorem_names` (`every_nat_declaration_is_checked_and_
  axiom_free` derives its checklist from `kernel.environment()`, so an
  unregistered live declaration fails it loudly). Both carry zero axiom
  footprint. Both instantiated at a concrete case AND at a genuinely free
  variable, per the standing rule — `add_eq_zero` at `(0, 0)` (the only
  `Nat` pair with a real hypothesis witness, discriminated by confirming
  `add 3 5` computes to `8` and is NOT defeq `0`), `zero_or_succ` at a
  COMPOUND term (`mul 2 k` for bound `k`, wrapped in its own `f.theorem` —
  see the `UnboundFVar` note below) and consumed by a genuine `Or.rec`
  elimination at the concrete numeral `5`.
- `the_build_is_deterministic`'s pin moved `88+459 → 88+461` across two
  commits, each taken from that run's own panic-message mismatch, never
  hand-incremented.

**A tooling trap hit and worked around while testing `zero_or_succ`, worth
recording since it is not this repository's most obvious failure mode**:
building a `fresh_fvar()` and using it directly as an argument to
`f.k.infer(...)` fails with `UnboundFVar`, even though this exact pattern
(fresh fvar, no wrapping) works fine INSIDE a `d.theorem(...)` closure.
The reason: `Kernel::infer`'s local context is populated only by the
kernel's OWN binder processing (`Pi`/`Lam`), never by a caller's
`fresh_fvar()`+`fvar()` call in isolation — `try_theorem` never calls
`infer` on the open intermediate term, only on the fully closed,
`pi_fv`/`lam_fv`-wrapped result. So a "does this apply to a genuinely free
variable" check must wrap the check in `f.theorem(...)` (as
`add_eq_zero_applies_at_free_and_concrete_arguments`'s symbolic block and
this lane's `zero_or_succ_at_compound_restated` do), not build a bare
`fresh_fvar()` and hand it straight to `f.k.infer`.

## Confirming `mul_eq_zero` already covers the rest of item 1

The prior lane's diagnosis listed "`mul_eq_zero_of_left`/`_right`-style
facts (or a full `mul_eq_zero_iff` disjunction)" as needed alongside
`add_eq_zero`. **`Nat.mul_eq_zero : ∀ a b, mul a b = 0 → a = 0 ∨ b = 0`
already exists** (`algebra.rs`, declared well before this lane). Given
`Eq (mul 2 rec) 0`, `mul_eq_zero` gives `Or (Eq 2 0) (Eq rec 0)`; the left
disjunct is eliminated inline via `Nat.succ_ne_zero` (2 is `succ (succ 0)`
— `succ_ne_zero` refutes it directly, no new lemma), leaving `rec = 0`.
So no additional named lemma is needed for that step — I checked this by
hand-tracing the exact term shapes involved (below), not by inference from
the name alone.

## The wall, precisely, and why `zero_or_succ` matters more than "a dichotomy exists"

`land_aux_assoc_of_fuel`'s statement (unconditional, no `Le` hypotheses
needed — `land`'s fuel-exhaustion row is the absorbing constant `0`, same
reason `land_aux_comm_of_fuel` needed none, per the 2026-08-29 CLAUDE.md
entry on `lor_aux_comm_of_fuel` needing hypotheses for the OPPOSITE
reason):

```
land_aux_assoc_of_fuel : ∀ fuel a b c,
  Eq (landAux fuel (landAux fuel a b) c) (landAux fuel a (landAux fuel b c))
```

via `agree_by_double_fuel_induction` (already fits its 4-argument
fuel-first shape exactly, per the prior diagnosis).

**Base case (`fuel = 0`)**: both sides defeq `0` regardless of `a`, `b`,
`c` — `landAux 0 X n` is the constant-`0` row for ANY `X`, `n`, even fully
symbolic ones. `d.refl` closes it. Free.

**Step case (`fuel = succ k`)**: write `X := landAux (succ k) a b` (LHS's
nested value) and `Y := landAux (succ k) b c` (RHS's nested value). This
is where the two prior lanes stopped. Here is the FULL case tree,
traced through by hand:

### The 8 base leaves, case-split on `(a, b, c)` in that order — 6 close by pure computation

`land`'s guard checks its SECOND value argument (`n`) for zero first, then
its first (`m`) — `land.rs`'s module doc: "the guard's nesting order is
load-bearing, and it is `n = 0` OUTERMOST". This makes the case split
`c`-first, then `b`, then `a` line up with what each side's OUTER
application actually inspects:

1. **`c = 0`** (any `a`, `b`): LHS's outer application is
   `landAux (succ k) X 0` — `n := 0` is LITERAL (from the case split), so
   the guard resolves regardless of `X`'s shape: LHS defeq `0`. RHS's `Y`
   is `landAux (succ k) b 0`, also `n := 0` literal, so `Y` defeq `0`
   regardless of `b`; then RHS `= landAux (succ k) a 0` defeq `0` again by
   the same literal-`n` argument. **Both sides defeq `0`, zero lemmas
   needed, `a` and `b` never need to be case-split.**
2. **`c = succ c'`, `b = 0`** (any `a`): `Y = landAux (succ k) 0 (succ c')`
   — now `n := succ c'` is nonzero, but `m := b = 0` is literal, so the
   guard's SECOND check resolves: `Y` defeq `0` regardless of `c'`. Then
   RHS `= landAux (succ k) a 0` defeq `0` (literal `n`). Symmetrically,
   `X = landAux (succ k) a 0` defeq `0` (literal `n = b = 0`), so
   LHS `= landAux (succ k) 0 (succ c')` defeq `0` (literal `m`). **Both
   sides defeq `0` again, purely computationally — `a` never needs
   case-splitting.**
3. **`c = succ c'`, `b = succ b'`, `a = 0`**: `X = landAux (succ k) 0
   (succ b')` defeq `0` (literal `m = a = 0`), so
   LHS `= landAux (succ k) 0 (succ c')` defeq `0` (literal `m`). For RHS,
   `Y = landAux (succ k) (succ b') (succ c')` is now a GENUINE stuck
   compound (both operands positive, recursion into fuel `k` which is
   opaque) — but `m := a = 0` is STILL literal for the OUTER application
   `landAux (succ k) 0 Y`, and `land`'s existing
   `land_aux_zero_left_any_fuel : ∀ fuel n, Eq (landAux fuel 0 n) 0`
   (already in the tree) applies at `n := Y` for ANY `Y`, stuck or not.
   RHS `= 0` via this one lemma call, no case-split on `Y` needed. **Zero
   NEW lemmas — the existing `land_aux_zero_left_any_fuel` alone
   suffices.**
4. **`c = succ c'`, `b = succ b'`, `a = succ a'`** — the one genuinely hard
   leaf, both `X` and `Y` are stuck compounds (`2 * rec + bit` shapes) and
   neither guard resolves by unfolding. This is the ONLY leaf needing new
   work.

So **6 of the 8 base leaves (all of 1–3, which cover every `(a,b,c)` combo
except all-three-positive) close by pure defeq or the one existing lemma
`land_aux_zero_left_any_fuel` — no `add_eq_zero`, no `zero_or_succ`, no new
theorem.** This is a sharper reduction than the prior diagnosis had, which
treated the whole tree as uniformly hard.

### Leaf 4 (all positive): a further dichotomy on `Y` alone (not a 2×2 grid) via ONE new lemma

Within leaf 4, split on `Y`'s shape first, using `zero_or_succ` (this
lane's new lemma) applied at `Y`:

- **`Y = 0`**: RHS `= landAux (succ k) a Y` transports to
  `landAux (succ k) a 0`, defeq `0` (literal `n` after transport,
  regardless of `a`). For LHS, we need `landAux (succ k) X c = 0` GIVEN
  `Y = landAux (succ k) b c = 0` — this is the MIRRORED form of a
  propagation lemma (below), derivable from the direct form plus
  `land_aux_comm_of_fuel` (also below), no separate induction needed.
- **`Y = succ q`**: now split on `X`'s shape (`zero_or_succ` again, at
  `X`):
  - **`X = 0`**: LHS `= landAux (succ k) 0 c` defeq `0` (transport, then
    literal `m`). RHS needs `landAux (succ k) a Y = 0` GIVEN
    `X = landAux (succ k) a b = 0` — **exactly** the direct propagation
    lemma (below), applied regardless of `Y`'s actual shape (it does not
    matter that we are in the `Y = succ q` sub-branch; the propagation
    lemma's conclusion holds for ANY `c`, hence any `Y`).
  - **`X = succ p`**: the one truly generic leaf, both sides reduce via
    the guard to `2 * rec + bit` shapes and the argument mirrors
    `land_aux_comm_of_fuel`'s both-positive leaf, but relating THREE
    values instead of two via the outer induction's own `ih`. Needs the
    div/mod reconstruct step (below) on BOTH `X` and `Y`.

**So the top-level structure is a 3-leaf tree (`Y = 0`; `Y ≠ 0 ∧ X = 0`;
`Y ≠ 0 ∧ X ≠ 0`), not a 2×2 = 4-leaf grid — the `X = 0` sub-case closes
via the direct propagation lemma REGARDLESS of `Y`'s shape, which is what
collapses two of the four naive sub-cases into one.**

### The missing piece: a "zero propagates through the other operand" lemma

```
land_aux_eq_zero_of_left_eq_zero : ∀ fuel a b c,
  Eq (landAux fuel a b) 0 → Eq (landAux fuel a (landAux fuel b c)) 0
```

Proved by the SAME triple fuel induction, with a much easier case tree
because the hypothesis (not a dichotomy we must produce) already gives us
`X = 0` in the interesting case:

- **`a = 0`**: RHS `= landAux (succ k) 0 Y = 0` via
  `land_aux_zero_left_any_fuel(sk, Y)`, for ANY `Y` — hyp unused.
- **`a = succ a'`, `b = 0`**: hyp is trivially true (`landAux (succ k)
  (succ a') 0` — wait, re-derive: hyp is about `landAux fuel a b`, i.e.
  `landAux (succ k) (succ a') 0`, which is defeq `0` unconditionally since
  `n := b = 0` literal — so the hypothesis carries no information here,
  which is fine, we don't need it). `Y = landAux (succ k) 0 c` defeq `0`
  via `land_aux_zero_left_any_fuel(sk, c)` (literal `m := b = 0`), for
  ANY `c`. RHS `= landAux (succ k) (succ a') 0` defeq `0` (literal `n`
  after transporting `Y → 0`). Hyp unused again.
- **`a = succ a'`, `b = succ b'`, `c = 0`**: `Y = landAux (succ k) (succ
  b') 0` defeq `0` (literal `n := c = 0`). RHS `= landAux (succ k) (succ
  a') 0` defeq `0` (literal `n` after transport). Hyp unused.
- **`a = succ a'`, `b = succ b'`, `c = succ c'`**: NOW the hypothesis is
  genuine: `hyp : Eq (2 * rec_ab + bit_ab) 0` where
  `rec_ab = landAux k half_a' half_b'`, `bit_ab = mod(a,2) * mod(b,2)`.
  Apply `Nat.add_eq_zero` (this lane's lemma) to `hyp` to get
  `Eq (mul 2 rec_ab) 0 ∧ Eq bit_ab 0`. Apply `Nat.mul_eq_zero` to the
  first conjunct to get `Or (Eq 2 0) (Eq rec_ab 0)`; eliminate the left
  disjunct via `Nat.succ_ne_zero` (2 is `succ (succ 0)`), leaving
  `rec_ab = 0`. Now dichotomize `Y := landAux (succ k) (succ b') (succ
  c')` via `zero_or_succ`:
  - **`Y = 0`**: RHS `= landAux (succ k) (succ a') 0` defeq `0` (literal
    `n` after transport). Done, `rec_ab = 0`/`bit_ab = 0` unused here.
  - **`Y = succ q`**: RHS `= landAux (succ k) (succ a') (succ q)`
    `= 2 * rec_aY + bit_aY` where `rec_aY = landAux k half_a' (div q 2)`,
    wait — more precisely `rec_aY = landAux k half_a' (div (succ q) 2)`,
    `bit_aY = mod(a,2) * mod(succ q,2)`. Reconstruct `div (succ q) 2` and
    `mod (succ q) 2` from `Y`'s OWN formula: `Y` is defeq
    `2 * rec_bc + bit_bc` (`rec_bc = landAux k half_b' half_c'`,
    `bit_bc = mod(b,2)*mod(c,2)`), and `Eq Y (succ q)` (the dichotomy
    hypothesis) transports this to `Eq (2*rec_bc+bit_bc) (succ q)`. With
    `bit_bc < 2` (from `Nat.mod_lt`), `Nat.div_mod_unique` +
    `Nat.div_mod_exec` (both ALREADY in the tree — this is exactly the
    "recompose" technique `land_aux_le_left` already uses for a single
    div/mod pair) give `div (succ q) 2 = rec_bc` and
    `mod (succ q) 2 = bit_bc`. So `rec_aY = landAux k half_a' rec_bc
    = landAux k half_a' (landAux k half_b' half_c')`, which is EXACTLY
    the OUTER induction's own `ih` applied at `(half_a', half_b',
    half_c')` — and `ih`'s hypothesis (`Eq (landAux k half_a' half_b')
    0`) is `rec_ab = 0`, already established above. So `ih` gives
    `rec_aY = 0` directly. For `bit_aY = mod(a,2) * mod(succ q,2)
    = mod(a,2) * bit_bc = mod(a,2) * (mod(b,2)*mod(c,2))`: rewrite via
    `Nat.mul_assoc` to `(mod(a,2)*mod(b,2)) * mod(c,2) = bit_ab *
    mod(c,2)`, and `bit_ab = 0` (established above) makes this `0` via
    `Nat.zero_mul`. So `stepped_aY = 2*0 + 0 = 0` (via existing
    `mul_zero`/`add_zero`-style facts), hence RHS defeq `0`.

  **No new arithmetic lemma is needed inside this branch beyond
  `add_eq_zero` (this lane), `mul_eq_zero` (existing), `succ_ne_zero`
  (existing), `div_mod_unique`+`div_mod_exec` (existing, the exact
  `land_aux_le_left` recompose pattern generalized from one div/mod pair
  to reconstructing `Y`'s own halves), `mul_assoc`, `zero_mul` (existing)
  — plus the outer induction's own `ih`, which is what makes this
  self-referential rather than needing a SEPARATE recursive helper.**

### The mirrored direction, for free via `land_aux_comm_of_fuel`

The `Y = 0` sub-case (in leaf 4's top split) needs
`landAux fuel a b = 0 [Y]  →  landAux fuel (landAux fuel a b) c = 0` — the
propagation lemma with the OTHER argument order (`c` on the right of the
outer application instead of the left). This does NOT need a second
induction. Since `land_aux_comm_of_fuel` (already in the tree,
UNCONDITIONAL — no `Le` hypotheses) gives `landAux fuel m n =
landAux fuel n m` for ANY `m`, `n`, chain:

```
landAux fuel (landAux fuel a b) c
  = landAux fuel c (landAux fuel a b)         [comm]
  = landAux fuel c (landAux fuel b a)         [comm on the inner pair]
  = 0                                          [propagation lemma at (c, b, a),
                                                 hyp: landAux fuel c b = 0,
                                                 itself landAux fuel b c commuted]
```

i.e. apply the DIRECT propagation lemma with its own arguments permuted
to `(fuel, c, b, a)` — `hyp : Eq (landAux fuel c b) 0`, obtained from the
given `Eq (landAux fuel b c) 0` via one more `land_aux_comm_of_fuel` call
— giving `Eq (landAux fuel c (landAux fuel b a)) 0`, then two more `comm`
calls restore the original argument order. **No second theorem, no
second induction — 4–6 lines of `land_aux_comm_of_fuel` chaining.**

## Numeric confirmation the mixed case is real (not a phantom of the case analysis)

Confirmed in Python before trusting any of the above (this repository's
own standing rule — simulate before writing Rust):

```
a=1, b=2, c=2:  land(a,b) = 0   land(b,c) = 2   (mixed: X=0, Y≠0)
  land(land(a,b),c) = land(0,2) = 0
  land(a,land(b,c)) = land(1,2) = 0    -- agrees, and the ONLY reason it
                                          agrees is that land(a,b)=0 means
                                          a,b share no set bits, and
                                          land(b,c)'s bits are a SUBSET of
                                          b's bits, so a and land(b,c)
                                          share no bits either -- this IS
                                          the propagation lemma's content.
```

Over `a,b,c ∈ [1,7]`, **108 of 343 triples** have `(land(a,b)=0) ≠
(land(b,c)=0)` — the mixed case is common, not a corner. This is also
why a naive attempt to prove the hard leaf by "show `X=0` implies
`Y=0`" (i.e. without the actual propagation argument) would fail
immediately — `X` and `Y` are frequently NOT both zero or both nonzero
together, and the true content is the one-directional propagation, not an
equivalence.

## What this buys, concretely, for the next lane

1. `land_aux_assoc_of_fuel` needs exactly ONE new named theorem beyond
   what exists now: `land_aux_eq_zero_of_left_eq_zero` (traced above,
   fully). Budget it similarly to `land_aux_comm_of_fuel` (~150 lines) —
   it is a triple fuel induction with 4 leaves, 3 of which are pure
   computation and one of which needs `add_eq_zero`/`mul_eq_zero`/
   `div_mod_unique` chaining plus the induction's own `ih`.
2. `land_aux_assoc_of_fuel` itself is then a 3-leaf case tree (not the
   naive 8, not even a naive 4) using `zero_or_succ` for two dichotomies
   (on `Y`, then on `X` within `Y≠0`), the propagation lemma for the
   `X=0` sub-case, its mirror-via-`comm` for the `Y=0` case, and the
   `land_aux_comm_of_fuel`-style reconstruct+`ih` argument for the
   `X≠0∧Y≠0` case. Budget similarly to `land_aux_comm_of_fuel` again,
   maybe somewhat larger for the extra case-split layer.
3. `land_assoc` from `land_aux_assoc_of_fuel` is then routine re-fueling
   exactly as `land_comm` follows from `land_aux_comm_of_fuel` — three
   terms instead of two, so the `Le` bookkeeping needs `land_le_left`
   (already in the tree) plus one `add_assoc`/`add_comm` transport to get
   the fuel ordering right across three pairwise `Le`s into
   `a + b + c`.
4. **`lor_assoc` does NOT transport this argument mechanically.**
   `lorAux`'s fuel-exhaustion row is pass-through (`n`, not `0`), so:
   - `lor_aux_comm_of_fuel` already needed `Le` hypotheses `land`'s never
     did (documented in this file's own CLAUDE.md entry, added
     2026-08-29, independently confirming the prior lane's flag).
   - The propagation lemma's analogue for `lor` is almost certainly
     FALSE unconditionally — `lor a b = 0` forces `a = b = 0` (OR's only
     zero is the all-zero pair), which makes the `lor` propagation lemma
     nearly trivial ONE way (if `lor a b = 0` then `a=0∧b=0`, so
     `lor a (lor b c) = lor 0 (lor 0 c) = lor 0 c = c`, NOT `0` in
     general!) — meaning the whole leaf-4 STRATEGY above (dichotomize on
     zero-ness) does not even apply the same way for `lor`, since `lor`'s
     absorbing/interesting values are different. **This needs its own
     case analysis from scratch, not a copy of the `land` one** — do not
     assume the technique transports without re-deriving the truth table
     first (simulate in Python before writing Rust, as this file's own
     CLAUDE.md now insists after the `lor_aux_comm_of_fuel` incident).

## Counts

`nat_prelude`: 130 passed before this lane (post `nat-bitwise-assoc`),
132 passed after (2 new declarations, both theorems, `add_eq_zero` and
`zero_or_succ`; 2 new tests). `the_build_is_deterministic`'s pin:
`88+459 → 88+461` (both increments taken from that run's panic message).
`nat` trusted surface still `axiom=0 opaque=0 quotient=0` (both new
theorems carry empty `axiom_footprint`, asserted in their tests).
`cargo fmt --edition 2024 --check` on all three touched files: clean.
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
`python3 scripts/validate-facts.py`: 1928 facts, 0 errors (unaffected —
no fact file touched, neither target fact closed, both remain `open`
exactly as found). Confirmed no script pins either target fact open
independent of provability (`grep -rl` for both fact ids across
`scripts/` returns nothing — the closing note's warning was about the
OTHER three bitwise facts, the `testBit`-family projection, not these
two). NOT run: the aggregate `just check` / `./scripts/check.sh`
(coordinator re-verifies before merging, per this repo's standing rule).

Neither `F:ml430-nat-land-assoc-ad4775b8` nor
`F:ml430-nat-lor-assoc-82c4d0fd` was touched (both remain `open`, exactly
as found).

## Commits

- `242362c24` — wip: `Nat.add_eq_zero` (early landing, first-ten-tool-calls
  commit)
- `c0d6a72ae` — test: register `add_eq_zero`, re-pin
  `the_build_is_deterministic`
- `8df2e0453` — feat: `Nat.zero_or_succ` + its tests + pin update
