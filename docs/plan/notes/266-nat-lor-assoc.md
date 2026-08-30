# Notes: 266-nat-lor-assoc

Detail moved out of [`../status/266-nat-lor-assoc.md`](../status/266-nat-lor-assoc.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **Base case (`fuel = 0`):** `d.lam_fv(hn_fv, hn_ty, hn)` — the bound
  hypothesis returned directly, accepted via defeq since the goal type
  IS the hypothesis type at this fuel.
- **Step case, `n = 0`:** hypothesis directly refuted (`hn(refl 0)`),
  `absurd` closes any goal.
- **Step case, `n = succ n', m = 0`:** `lorAux sk 0 succ_n` is defeq
  `succ_n` (literal `m = 0`, outer guard's second check fires), so
  `Nat.succ_ne_zero n'` closes it directly — the hypothesis is unused.
- **Step case, `n = succ n', m = succ m'` (the hard branch,
  `lor_aux_pos_both_positive`):** case-splits `Nat.mod succ_n 2`
  (`cases_mod_two`, folding `Nat.div_mod_exec`'s reconstruction equation
  into an ARROW-typed motive — the only way to carry a usable equation
  out of a `cases_mod_two` branch into another term):
  - **bit = 1:** `bool_select_nat (ble bit_m 1) 1 bit_m` reduces to the
    literal `1` at EITHER concrete `bit_m` (`ble(0,1)`/`ble(1,1)` both
    reduce to `true`), so `add (mul 2 rec) 1` is defeq `succ (mul 2 rec)`
    and `Nat.succ_ne_zero` closes it without ever touching the
    reconstruction equation or `rec`'s value.
  - **bit = 0:** `bool_select_nat (ble bit_m 0) 0 bit_m` reduces to
    `bit_m` itself (`max(x,0) = x`), split again: `bit_m = 1` is the
    same `succ_ne_zero` trick; `bit_m = 0` needs `half_n := div(succ_n,2)`
    itself nonzero (else, via the reconstruction equation,
    `succ_n = 2*0+0 = 0`, contradicting `succ_n`'s own literal `succ`
    shape via `Nat.succ_ne_zero`), then the SAME `mul_eq_zero`/
    `succ_ne_zero` contrapositive land's zero-propagation lemma uses
    (extracted as `double_ne_zero`), applied to `rec` via the caller's
    own `rec_ne_zero_of_half_n_ne_zero` closure (`ih` at the halves in
    the step case; nothing further needed in the base case, since there
    `rec` IS `half_n`).

**Registered in `theorem_names`.** `the_build_is_deterministic`'s pin
moved `93+498 → 93+499` (from the panic's own mismatch).

**Test**: `lor_aux_ne_zero_of_right_ne_zero_applies_symbolically_and_at_a_positive_concrete_instance`
— symbolic re-derivation at fully free `fuel`/`m`/`n` (its own theorem,
forcing the kernel to re-check the fully generic statement) plus a
concrete instance at `(fuel=1, m=3, n=5)`: `lorAux 1 3 5 = 5`, genuinely
nonzero (not the vacuous `n=0` corner), and `fuel=1` is exactly enough to
force the real per-bit recursive step rather than the trivial `fuel=0`
identity.

**147/147 `nat_prelude::` tests pass** (was 146). `cargo fmt --edition
2024 --check` and `cargo clippy -p axeyum-lean-kernel --all-targets --
-D warnings`: both clean. `python3 scripts/validate-facts.py`: 1939
facts, 0 errors (unaffected — no fact file touched,
`F:ml430-nat-lor-assoc-82c4d0fd` remains `open` exactly as found).
`scripts/gen-autogenesis-bitwise-family-projection.py` does not mention
either the fact id or `Nat.lor_assoc` — not pinned open independent of
provability. `Nat.bitwise_or_eq_lor` already exists (landed alongside
`Nat.bitwise_and_eq_land`), so the mirror-flip route stays honest and
ready: Mathlib's `Nat.lor := Nat.bitwise or`, and once `lor_assoc` is
built, it closes the SAME proposition via `bitwise_or_eq_lor`.

## Two real bugs found while building this, worth naming for the next lane

Both were caught via a technique worth reusing: `Kernel::infer` on a
**naked intermediate** with genuinely free `fresh_fvar`s ALWAYS throws
`UnboundFVar`, regardless of whether the construction is correct (the
CLAUDE.md gotcha about `try_theorem` never populating a local context
from a bare `fresh_fvar()`). The fix that actually diagnoses something:
wrap the piece under test in its OWN closed `pi_fv`/`lam_fv` chain first
(exactly what a real declaration does), THEN `infer` it. A "closed"
diagnostic on `lor_aux_pos_both_positive` alone passed immediately,
which is what proved the bug was in the surrounding wiring, not the
positivity argument itself.

1. **A hypothesis about a case-split variable, built BEFORE the split and
   referencing the ORIGINAL (unspecialized) variable, is unusable inside
   either branch.** `Nat.rec`'s branches only substitute the case-split
   variable through the MOTIVE; a separately-built term that mentions the
   original variable (e.g. `hn : Not (Eq n 0)` built before
   `cases_zero_succ(d, n, ...)`) still says "n" inside both branches, not
   "0" or "succ n_pred" — so `d.apply(hn, &[d.refl(zero)])` fails with
   `Eq (_fvar_for_n) 0` expected against `Eq 0 0` given. The fix: fold the
   hypothesis into `cases_zero_succ`'s own ARROW-typed motive (build
   `goal_at(candidate) := Arrow(Not (Eq candidate 0), <conclusion at
   candidate>)`, and inside each branch build a FRESH hypothesis fvar of
   the branch's own specialized type), exactly
   `declare_land_aux_eq_zero_of_left_eq_zero`'s convention. Do **not**
   pre-build a hypothesis about a variable you are about to case-split.
2. **The final `value` assembly must bind EVERY variable `ty` quantifies,
   in the SAME order.** `ty` was built with three `pi_fv` layers
   (`fuel`, `m`, `n`); `value` only had two `lam_fv` layers (`m`, `n`) —
   `fuel_fv` stayed free, giving `UnboundFVar` from `add_declaration`
   itself once bug 1 was fixed. Compare against a working sibling's exact
   assembly (`declare_lor_aux_comm_of_fuel`'s) line by line rather than
   re-deriving the wrapping from scratch.

## `lor_aux_assoc_of_fuel`: the full case tree, verified by hand and cross-checked in Python

**Statement:** `∀ fuel a b c, Eq (lorAux fuel (lorAux fuel a b) c)
(lorAux fuel a (lorAux fuel b c))` — via `agree_by_double_fuel_induction`
(the SAME 4-argument helper `land_aux_assoc_of_fuel` uses; nothing about
it is AND-specific). **Unconditional in `fuel`** — confirmed by
exhaustive simulation over `fuel ∈ [0,5]`, `a,b,c ∈ [0,7]`: zero
counterexamples. Step split `c`, then `b`, then `a` (same order as
`land_aux_assoc_of_fuel`, same reason: `guarded`'s `n`-slot check is
outermost, and splitting `c` first is what makes both outer applications
resolve directly in the easy leaves).

**Base case (`fuel = 0`):** `X := lorAux(0,a,b)` is defeq `b` (zero-fuel
row returns its third argument regardless of the first); LHS `=
lorAux(0,X,c)` is defeq `c` (same rule, again). `Y := lorAux(0,b,c)` is
defeq `c`; RHS `= lorAux(0,a,Y)` is defeq `c` (same rule). **Both sides
defeq `c` directly** — `d.refl` closes it in one line, no case-split on
`a`/`b`/`c` needed at all. (Simpler than `land`'s base case, which needed
a similar two-step reduction to `0` rather than to a shared variable.)

**Leaf 1 (`c = 0`):** `X = lorAux(sk,a,b)` (unsplit). LHS `=
lorAux(sk,X,0)` is defeq `X` (literal `n=0` in the outer application,
regardless of `X`'s shape). `Y = lorAux(sk,b,0)` is defeq `b` (same
rule). RHS `= lorAux(sk,a,Y)` transports to `lorAux(sk,a,b)` — **the
SAME expression as `X`.** Both sides defeq `X`. **Zero lemmas.**

**Leaf 2 (`c = succ_c, b = 0`):** `X = lorAux(sk,a,0)` is defeq `a`
(literal `n=b=0`). `Y = lorAux(sk,0,succ_c)`: outer check `n=succ_c`
(nonzero, literal) fails; inner check `m=0` (literal `b=0`) succeeds,
return `n=succ_c` — so `Y` defeq `succ_c`. LHS transports to
`lorAux(sk,a,succ_c)`; RHS transports to the SAME term. **Zero lemmas,
`a` never case-split.**

**Leaf 3 (`c = succ_c, b = succ_b, a = 0`):** `X = lorAux(sk,0,succ_b)`:
outer check `n=succ_b` fails; inner check `m=a=0` succeeds, return
`n=succ_b` — `X` defeq `succ_b`. LHS transports to
`lorAux(sk,succ_b,succ_c)` — **exactly `Y`'s own defining expression.**
`Y` itself is a genuine stuck compound (both operands positive). RHS `=
lorAux(sk,0,Y)`: outer check `n=Y` is STUCK (not literal), so needs
`Nat.lor_aux_zero_left_any_fuel(sk,Y)` (already in the tree, holds for
ANY `n` including stuck ones) to get RHS `= Y`. Combine: LHS defeq `Y`
(pure computation), RHS `= Y` (one lemma). **One lemma call
(`lor_aux_zero_left_any_fuel`), same as `land`'s analogous leaf.**

**Leaf 4 (`a, b, c` all positive) — the hard leaf, and where `lor`
diverges structurally from `land`, in a way that makes it SIMPLER, not
harder, once `lor_aux_ne_zero_of_right_ne_zero` exists:**

`X := lorAux(sk,succ_a,succ_b)`, `Y := lorAux(sk,succ_b,succ_c)`, both
defeq `2*rec+bit` shapes (`guarded`, both operands literal `succ`). In
`land`'s analogous leaf, `X`/`Y` could genuinely be `0` even with all
three operands positive (AND has no absorbing-avoidance), forcing a
nested `zero_or_succ` dichotomy with real `X=0`/`Y=0` sub-cases closed
via the propagation lemma and its comm-mirror. **For `lor`, `X` and `Y`
are UNCONDITIONALLY positive here** — `lor_aux_ne_zero_of_right_ne_zero`
applied at `(sk, succ_a, succ_b)` with hypothesis `Nat.succ_ne_zero b'`
(`succ_b = succ b'`) gives `Not (Eq X 0)` directly; symmetrically at
`(sk, succ_b, succ_c)` with `Nat.succ_ne_zero c'` gives `Not (Eq Y 0)`.
So:

1. `dichotomy_x := Nat.zero_or_succ(X)`, `or_elim`:
   - **`X = 0` branch:** contradicts `Not (Eq X 0)` directly via
     `Not (Eq X 0) (hx)`, then `absurd` at the goal type. **No mirror
     trick needed** — this whole branch is ~5 lines, versus `land`'s
     multi-step `land_aux_comm_of_fuel` mirroring for its analogous
     `Y = 0` case.
   - **`X = succ p` branch** (witness `p`, `hxp : Eq X (succ p)`):
     `dichotomy_y := Nat.zero_or_succ(Y)`, `or_elim`:
     - **`Y = 0` branch:** same contradiction via `Not (Eq Y 0)`,
       `absurd`. **No propagation-lemma sub-case needed.**
     - **`Y = succ q` branch** (witness `q`, `heq : Eq Y (succ q)`) —
       **the one truly generic leaf**, and it is a LINE-FOR-LINE
       transplant of `land_aux_assoc_of_fuel`'s own `X=succ p, Y=succ q`
       leaf (`declare_land_aux_assoc_hard_leaf`, `rec_agreement.rs`),
       with exactly ONE substitution:
       - `cong_l`/`cong_r` transport `X`/`Y` to `succ_p`/`succ_q` inside
         the outer applications, identical to `land`.
       - Reconstruct `div(succ_p,2)`/`mod(succ_p,2)` from `X`'s own
         `2*rec_ab+bit_ab` decomposition via `Nat.div_mod_exec` +
         `Nat.div_mod_unique` — **identical code to `land`'s**, since
         this reconstruction is purely about the `2*q+r` SHAPE, not
         about what `land`/`lor` compute at each bit. Same for `succ_q`
         from `Y`'s `2*rec_bc+bit_bc`.
       - The recursive halves (`rec_Xc → lorAux(k,rec_ab,half_c) →[ih at
         (half_a,half_b,half_c)]→ lorAux(k,half_a,rec_bc) → rec_aY`) are
         **identical to `land`'s** — this is the outer induction's own
         `ih`, unaffected by which per-bit operator is in play.
       - **The one substitution:** where `land` closes
         `bit_Xc → mul(bit_ab,bit_c) →[Nat.mul_assoc]→ mul(bit_a,bit_bc)
         → bit_aY` via `Nat.mul_assoc`, `lor` needs
         `bit_Xc → max(bit_ab,bit_c) →[lor_bit_assoc]→ max(bit_a,bit_bc)
         → bit_aY`, where `max(x,y) := bool_select_nat(ble x y, y, x)`
         (the SAME term shape `lor.rs`'s own per-bit combine and
         `lor_bit_comm` already use) — **a NEW lemma, `lor_bit_assoc`,
         not yet built** (see below).

**Net: leaf 4 needs exactly one new lemma (`lor_bit_assoc`) beyond what
`land_assoc_of_fuel`'s hard leaf already built and this lane's
`lor_aux_ne_zero_of_right_ne_zero`** — no new induction, no new
reconstruction technique, and the top-level structure is SHORTER than
`land`'s (two trivial absurd-closed branches replace `land`'s two
substantive sub-proofs).

## `lor_bit_assoc`: the one missing lemma, fully specified, not yet built

```
lor_bit_assoc : ∀ a b c,
  Eq (bool_select_nat (ble (bool_select_nat (ble bit_a bit_b) bit_b bit_a) bit_c)
        bit_c (bool_select_nat (ble bit_a bit_b) bit_b bit_a))
     (bool_select_nat (ble bit_a (bool_select_nat (ble bit_b bit_c) bit_c bit_b))
        (bool_select_nat (ble bit_b bit_c) bit_c bit_b) bit_a)
  where bit_a := mod a 2, bit_b := mod b 2, bit_c := mod c 2
```

i.e. `max(max(bit_a,bit_b),bit_c) = max(bit_a,max(bit_b,bit_c))` stated
over the ACTUAL `bool_select_nat`/`ble` term shape (not an abstract
`Nat.max`, which this prelude does not have as a named function). Build
exactly like `lor_bit_comm`/`bit_agreement` (`rec_agreement.rs`) — THREE
nested `cases_mod_two` (on `a`, then `b`, then `c`), 8 leaves at the
bottom, each closing by `d.refl` since with all three bits concrete
(`{0,1}`), both sides fully reduce via `ble`'s own computation to the
SAME literal (associativity of `max` over `{0,1}` is trivially true at
all 8 combinations). Budget: roughly double `lor_bit_comm`'s size (one
more nesting level, 8 leaves instead of 4), all mechanical — no new
proof technique, just more `cases_mod_two` nesting following the exact
pattern already in the file twice.

## `lor_assoc` from `lor_aux_assoc_of_fuel`: the fuel bookkeeping, and the one remaining gap

Mechanical, `land_assoc`'s exact shape (`Nat.lor_aux_agree_of_fuel`
already exists, same signature as `land`'s: `∀ fuel1 m n fuel2, Le m
fuel1 → Le m fuel2 → Eq (lorAux fuel1 m n) (lorAux fuel2 m n)` —
constrains only the `m` position, so `c` never needs its own bound,
exactly as `land_assoc` established). Pick `F := add a b` (or similar).
Needed bounds: `Le a F` (`le_add_right`), `Le b F` (`le_add_right` +
`add_comm` transport, same as `land_assoc`), and **`Le (lor a b) F`** —
**this is the one gap `land_assoc` does not have an analogue for**,
because `Nat.land_le_left : Le (land a b) a` exists and `Nat.lor` has NO
such bound (`lor a b` can EXCEED both operands, e.g. `lor 1 2 = 3`).

**What's needed: `Nat.lor_aux_le_add : ∀ fuel m n, Le (lorAux fuel m n)
(add m n)`, unconditional in `fuel`** (confirmed by exhaustive Python
simulation, `fuel ∈ [0,7]`, `m,n ∈ [0,13]`: zero counterexamples). NOT
built this lane. Proof sketch, by `agree_by_fuel_induction` (same shape
as `lor_aux_ne_zero_of_right_ne_zero`):

- **Base (`fuel=0`):** `lorAux 0 m n` is defeq `n`; need `Le n (add m
  n)` — `Nat.le_add_left` (if it exists) or derive from
  `Nat.le_add_right` + `Nat.add_comm` transport (same pattern
  `land_assoc`'s own `Le b F` derivation already uses).
- **Step, `n=0`:** `lorAux sk m 0` defeq `m`; need `Le m (add m 0)` —
  `add_zero` + `le_refl`.
- **Step, `m=0`:** `lorAux sk 0 n` defeq `n`; need `Le n (add 0 n)` —
  `zero_add` (or the `add_comm` transport again) + `le_refl`.
- **Step, both positive:** `lorAux sk succ_m succ_n` defeq `2*rec+bit`
  where `rec = lorAux(k,half_m,half_n)` (via `ih`, giving `Le rec
  (add half_m half_n)`) and `bit = max(bit_m,bit_n)`. Need `Le
  (add (mul 2 rec) bit) (add succ_m succ_n)`. Since `succ_m = add (mul 2
  half_m) bit_m` and `succ_n = add (mul 2 half_n) bit_n` (via
  `div_mod_exec`), this reduces to `Le (2*rec+bit) (2*(half_m+half_n) +
  (bit_m+bit_n))` given `rec ≤ half_m+half_n` (from `ih`) and `bit ≤
  bit_m+bit_n` — the second needing a small NEW fact,
  `max(x,y) ≤ x+y` over the `bool_select_nat`/`ble` shape (a 4-leaf
  `cases_mod_two`-on-both-operands lemma, same size as `lor_bit_comm`,
  simpler than `lor_bit_assoc` since it's an inequality at only 2
  operands not 3). Combine via `Nat.mul_le_mul_left`/`Nat.add_le_add`
  (both should already exist, used throughout the order-theoretic
  lemmas in this file).

**This bound lemma is the one piece of this lane's trace NOT
numerically re-verified against a from-scratch Python re-derivation of
every sub-step** (only the top-level `Le (lorAux fuel m n) (add m n)`
claim itself was simulated) — budget it similarly to
`lor_aux_ne_zero_of_right_ne_zero` (a fuel induction with a genuine
per-bit case split), plus one small new `max ≤ sum` helper.

Once `lor_aux_le_add` exists, `Le (lor a b) F` follows via
`lor_aux_le_add(a,a,b) : Le (lorAux a a b) (add a b)` = `Le (lor a b)
(add a b) = Le (lor a b) F` directly (`F := add a b`, no further
`le_trans` needed — unlike `land`'s `land_le_left` + `le_trans` chain,
since here the bound already targets `F` exactly). The rest of the
refuel (steps 1–7 in `land_assoc`'s own doc comment) transposes
verbatim, swapping `land`→`lor` throughout.

## What this buys, concretely, for the next lane

1. `Nat.lor_bit_assoc` — 8-leaf, purely mechanical, transcribe from this
   file's spec above using `lor_bit_comm`'s exact nesting pattern one
   level deeper.
2. `Nat.lor_aux_assoc_of_fuel` — transcribe `declare_land_aux_assoc_of_fuel`
   almost verbatim (same split order, same base case shape but simpler,
   same leaf 1–3 structure using `lor_aux_zero_left_any_fuel` in place of
   `land_aux_zero_left_any_fuel`), and for leaf 4, transcribe
   `declare_land_aux_assoc_hard_leaf` with: the `Y=0`/`X=0` sub-cases
   replaced by two short `absurd`-via-`lor_aux_ne_zero_of_right_ne_zero`
   closures (shorter than land's originals), and `Nat.mul_assoc` replaced
   by `Nat.lor_bit_assoc` in the bit-combine step.
3. `Nat.lor_aux_le_add` (new, ~similar size to
   `lor_aux_ne_zero_of_right_ne_zero`, plus a small `max ≤ sum` helper)
   for the refuel bound `land_le_left` does not have an analogue for.
4. `Nat.lor_assoc` — transcribe `declare_land_assoc`'s bookkeeping,
   swapping `land`→`lor` and using `lor_aux_le_add` directly (no
   `le_trans` needed) in place of `land_le_left`+`le_trans`.
5. Close `F:ml430-nat-lor-assoc-82c4d0fd` via the standard bitwise
   reconciliation pattern: `Nat.bitwise_or_eq_lor` already exists, so
   `lor_assoc` closes the SAME proposition Mathlib states once built.
   Register the native theorem as `F:nat-lor-assoc`. Both checker
   commands should mirror `land_assoc`'s closing note exactly
   (`nat_theorem_inventory lor_assoc` through an anchored
   `grep -Ec '^Nat\.lor_assoc[[:space:]]'`, and `nat_axiom_inventory
   --require-axiom-free nat`).

## Counts

`nat_prelude`: 146 passed before this lane, **147 passed after** (1 new
declaration, a theorem; 1 new test). `the_build_is_deterministic`'s pin:
`93+498 → 93+499`. `nat` trusted surface still `axiom=0 opaque=0
quotient=0` (the new theorem's `axiom_footprint` is asserted empty in
its test, though not via a standalone assertion outside the test body —
see the test itself). `cargo fmt --edition 2024 --check`: clean. `cargo
clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
`python3 scripts/validate-facts.py`: 1939 facts, 0 errors (unaffected —
`F:ml430-nat-lor-assoc-82c4d0fd` remains `open`, exactly as found). NOT
run: the aggregate `just check` / `./scripts/check.sh` (coordinator
re-verifies before merging, per this repo's standing rule).

`F:ml430-nat-lor-assoc-82c4d0fd` remains `open`, characterized above with
a complete implementation-ready derivation for everything remaining.

## Commits

- `3da011e86` — wip: nat-lor-assoc checkpoint (first-ten-tool-calls
  commit, no source changes)
- `3f77d8574` — wip: `Nat.lor_aux_ne_zero_of_right_ne_zero` — builds, not
  yet kernel-verified
- `933e1dace` — feat: kernel-verified, registered, tested; 147/147
  `nat_prelude::` tests pass; the two bugs found and fixed along the way
