# Notes: 251-nat-bit-decode

Detail moved out of [`../status/251-nat-bit-decode.md`](../status/251-nat-bit-decode.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What remains after the fuel machinery is a claim with no fuel left in
it**: `guarded (bit a m) (bit b n) 0 0 (land m n) (mul (cond a 1 0)
(cond b 1 0)) = bit (a && b) (land m n)`, with two `beq _ 0` guards not
defeq-resolved for symbolic `a, m, b, n`. Resolving them needs a bounded
case tree, closed by `land_zero_left`/`land_zero_right` (already proved) at
the two degenerate leaves and one new fact, `and_cond_mul_eq_cond` (`mul
(cond a 1 0) (cond b 1 0) = cond (a && b) 1 0`), at the "both guards false"
leaf.

**The bug that cost a full debugging cycle, worth stating for the next
lane on ANY of these three bridges.** The first draft split the case tree
on `n`/`m` (the `Nat`s), assuming `bit test k` is `succ`-shaped once `k` is
`succ`-shaped. That is backwards: `Nat.add` recurses on its SECOND
argument, and `bit test k`'s second-position term is `cond test 1 0` — so
`bit true k` is `succ`-shaped for ANY `k` (even fully symbolic, since
`add x (succ zero)` reduces via the succ-row regardless of `x`'s shape),
while `bit false k = mul 2 k` genuinely needs `k`'s own shape exposed. The
kernel rejected the wrong version with a `TypeMismatch` naming two large
opaque `ExprId`s; a throwaway `#[test]` catching the `Err` and printing
`k.render_lean(expected)`/`k.render_lean(got)` (both sides, side by side)
found the guard `beq (bit a (succ m_pred)) 0` still stuck — `a`, not `m`,
was the thing left symbolic. **The correct split is on the `Bool`s first
(`b`, then `a`), and only within the `false` branch of each does the
corresponding `Nat` (`n`, then `m`) need splitting.** This is documented
in `bit_decode.rs`'s module doc in full, including the exact leaf count (7:
`b=true` splits into 3 leaves via `a`; `b=false,n=0` is 1 leaf; `b=false,
n=succ` splits into 3 more via `a` — matching `b=true`'s shape).

**What is still needed to close `lor_bit`/`ldiff_bit`.** The fuel-swap
machinery (`base`/`k1`/`fuel`, both `Le` bounds, the `div`/`mod` decode via
`bit_div_two`/`bit_mod_two`) is IDENTICAL for all three — it never
inspects `land`'s absorbing zero, so it transports unchanged. What does
NOT transport:

- **The degenerate-guard leaves.** `lor`'s fuel-exhaustion row returns the
  OTHER full operand, not the constant `0` — so `lor_bit`'s two degenerate
  leaves need `lor_zero_left`/`lor_zero_right` (both already proved)
  instead of `land`'s, with the target correspondingly `bit a m`/`bit b n`
  rather than `0`. `ldiff`'s guards are the hybrid `land.rs`/`lor.rs`
  already establish (`ldiff_zero_left`/`ldiff_zero_right`), so `ldiff_bit`
  needs both shapes depending on which guard fires.
- **The per-bit combine agreement, and this is the real new work.** `land`'s
  `and_cond_mul_eq_cond` is a two-leaf `Bool` split on `a` ALONE, because
  `and a b` reduces via ι at `a`'s literal alone (`and true b = b`,
  `and false b = false`, regardless of `b`'s shape). `lor`'s combine is
  `max` via `ble (cond a 1 0) (cond b 1 0)` — `ble`'s recursion does NOT
  let `a = true` alone resolve the value (`ble (cond a 1 0) (cond b 1 0)`
  at `a = true` still needs `cond b 1 0`'s VALUE, not just its shape, to
  decide the `ble`), so the `lor` analogue needs a further split on `b` in
  the `a = true` branch — a 3- or 4-leaf split, not 2. `ldiff`'s combine
  (`if n%2 = 0 then m%2 else 0`, via `beq`) needs its own version of the
  same treatment. Simulate each in Python at small concrete arguments
  before writing Rust, per the standing rule — the `and` case's shortcut
  (split on `a` alone) does NOT generalize to `or`/`ldiff`'s combines, and
  assuming it does is exactly the kind of vacuous-transport mistake this
  repository's Gotchas warn about.
- A quicker path than re-deriving `Nat.bitwise_bit'`
  (`F:ml430-nat-bitwise-bit-4c4b28a8`) through the general `bitwise`
  recursion: that theorem carries side hypotheses (`m = 0 → a = true`,
  `n = 0 → b = true`) our `land_bit`/`lor_bit`/`ldiff_bit` do NOT need
  (their specializations don't have the general `bitwise` recursion's
  leading-zero ambiguity), so it is not a shortcut to the other two and was
  not attempted here.

**Counts.** `nat_prelude`: 130 tests before this lane (post `nat-fuel-transport`
merged) → **131** (one new instantiation test,
`land_bit_applies_at_a_concrete_discriminating_instance` — symbolic
re-declaration over fresh Pi/lambda-bound `a, m, b, n` plus the concrete,
bit-discriminating instance `a=true, m=2, b=false, n=3`: `land(5,6)=4`
against `bit false (land 2 3) = bit false 2 = 4`). 3 new declarations, all
theorems (`bit_div_two`, `bit_mod_two`, `land_bit`) — `the_build_is_
deterministic`'s pin moved `88 + 459` → `88 + 462`, taken from the panic
message's own mismatch, not hand-incremented. `nat` trusted surface still
`axiom=0 opaque=0 quotient=0`
(`nat_axiom_inventory --require-axiom-free nat`). New fact `F:nat-land-bit`;
`F:ml430-nat-land-bit-b9ab7475` flipped open → proved via a reconciliation
evidence row (our `Nat.land` is proved equal to Mathlib's `bitwise and`
specialization by `Nat.bitwise_and_eq_land`, so this closes the SAME
function's `bit`-decode identity — the honest-flip criterion in CLAUDE.md's
Gotchas). `python3 scripts/validate-facts.py`: 1929 facts, 0 errors.
`cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean
on the touched files. NOT run: the aggregate `just check` / `./scripts/check.sh`.
