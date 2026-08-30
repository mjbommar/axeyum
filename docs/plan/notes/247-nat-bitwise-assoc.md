# Notes: 247-nat-bitwise-assoc

Detail moved out of [`../status/247-nat-bitwise-assoc.md`](../status/247-nat-bitwise-assoc.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Registered in `theorem_names` (`every_nat_declaration_is_checked_and_
axiom_free` now covers both — this test derives its checklist from
`kernel.environment()`, so an unregistered live declaration fails it
loudly, which is how the omission was caught on the first run). Both carry
zero axiom footprint. Instantiated at a concrete, STRICTLY discriminating
pair (`land 5 6 = 4`, `101 & 110 = 100`, strictly `< 5` — a pair where
`land a b = a`, e.g. `a` a submask of `b`, would not discriminate a bound
that is actually an equality in disguise) plus a fully symbolic
restatement over free `fuel`/`m`/`n`, per the concrete-and-free-variable
rule. `the_build_is_deterministic`'s pin moved `88+452 → 88+454`, taken
from the panic message's own mismatch, not hand-incremented.

**Why the natural next step does NOT go through, in detail — read this
before attempting `land_aux_assoc_of_fuel`.**

The obvious mirror of `land_aux_comm_of_fuel` is:

```
land_aux_assoc_of_fuel : ∀ fuel a b c,
  Eq (landAux fuel (landAux fuel a b) c) (landAux fuel a (landAux fuel b c))
```

proved by induction on `fuel` with `a`, `b`, `c` generalized (this part is
free: `agree_by_double_fuel_induction` already has exactly this
4-argument-with-fuel-first shape — its "two fuels" reading and a "three
values" reading are the SAME combinator, since it never inspects what its
generalized slots mean. No new induction combinator is needed).

The BASE case (`fuel = 0`) is trivial: `landAux 0 X c` is defeq to `0`
regardless of what `X` is, even a fully symbolic/stuck term (the base row
is the constant function `fun m n => 0`, so the recursor's zero-case
doesn't need to inspect `m` at all). Both sides collapse to `0` by `refl`.

The STEP case (`fuel = succ k`) is where it breaks. Write `X := landAux
(succ k) a b` (the LHS's nested value). The outer application
`landAux (succ k) X c` unfolds ONE step via `guarded` regardless of `X`'s
shape (the recursion is on the FUEL, which is literally `succ k` here —
this much is easy, and NOT the problem some earlier framing of this task
worried about). But `guarded`'s OUTER guard checks `c` (n = 0 outermost;
`c` is known positive from an outer 3-way case split on `a`/`b`/`c`, so
that check resolves), and its INNER guard checks `beq(X, 0)` — and `X` is
a compound arithmetic expression (`2*recAB + bitAB`, not a bare
`Nat.succ`/`Nat.zero` application), so this guard does **not** resolve by
mere unfolding. `X` genuinely CAN be `0` even when `a`, `b` are both
positive (e.g. `land 2 1 = 0`), so this is not a vacuous branch to paper
over — the guard's outcome really is undetermined without further work.

Deciding "is `X` zero or positive" while PRESERVING the connection back to
`recAB`/`bitAB` needs a PROP-LEVEL dichotomy folded into the goal's motive
(`cases_zero_succ`'s raw `Nat.rec` elimination does NOT work here — it
would hand back a fresh, structurally UNRELATED opaque predecessor, since
`X` is not the theorem's own bound variable; the doc on `cases_zero_succ`
says this explicitly: "a caller wanting a hypothesis usable inside a
branch must fold it into `motive`"). The dichotomy itself
(`Or (Eq X 0) (Exists p, Eq X (succ p))`) is buildable — it is exactly
`cases_zero_succ` applied to a FRESH universally-quantified `n`, proved
once and then instantiated at any concrete term including `X`, the same
trick that lets `land_aux_agree_of_fuel` be REUSED at an opaque `X` in
`land_le_left`'s proof without redoing its induction.

The actual wall is what happens INSIDE the `X = 0` branch. There, you know
`Eq X 0`, i.e. `Eq (2*recAB + bitAB) 0`. The goal at this point still needs
`landAux (succ k) A (landAux (succ k) B c) = 0` (the RHS), and there is NO
shortcut to this — you cannot derive "RHS is 0" from "X is 0" as an
external fact (associativity is exactly the thing not yet available), so
you need `recAB = 0 ∧ bitAB = 0` (from `2*recAB + bitAB = 0` via an
`add_eq_zero`-style lemma, then `2*recAB = 0 → recAB = 0` via an
`eq_zero_of_mul_eq_zero`-style lemma given `2 ≠ 0`, and `bitAB = 0` i.e.
`(a%2)*(b%2) = 0` gives `a%2 = 0 ∨ b%2 = 0` via a `mul_eq_zero_iff`-style
disjunction) — NONE of which currently exist in this prelude, and even
once built, using them to show the RHS is ALSO forced to `0` needs its own
sub-argument (does `recAB = 0` propagate to show `landAux(k, a/2,
landAux(k, b/2, c)) = 0`? Only via essentially the SAME induction, one
level down — this is why it is a genuine wall, not a missing one-liner).

**Empirically the unconstrained statement (any fuel, not just sufficient)
appears TRUE** — hand-traced at `(fuel=1, a=b=c=2)`, `(fuel=1, a=b=c=3)`,
and other insufficient-fuel triples, both sides always agreed. So this is
not a case of chasing a false lemma; it is a real, provable fact that
needs more supporting lemmas than commutativity did.

**What it would actually take to close `land_assoc`, concretely, next:**

1. Build `Nat.add_eq_zero_iff : ∀ a b, Eq (add a b) 0 ↔ Eq a 0 ∧ Eq b 0` (or
   the two directions separately; only `→` is needed here) and
   `Nat.mul_eq_zero_of_left`/`_right`-style facts (or a full
   `mul_eq_zero_iff` disjunction) — standard, but not yet in this prelude.
2. Fold `Or (Eq X 0) (Exists p, Eq X (succ p))` into the goal's motive (an
   arrow-typed motive per `cases_zero_succ`'s documented pattern) so both
   branches retain the connection to `recAB`, `bitAB`.
3. In the `X = 0` branch, use (1) to get `recAB = 0 ∧ bitAB = 0`, then
   show the RHS also reduces to `0` — this likely needs its OWN nested
   zero-dichotomy on `Y := landAux (succ k) b c` (is `Y` zero or positive?)
   plus the same style of argument, i.e. the "both nested values are zero"
   case may need to be handled as a genuinely separate leaf from "both
   positive", not derived by symmetry.
4. In the `X = succ p` branch (`p` opaque but now `X`'s successor-shape is
   established via the EQUATION `Eq X (succ p)`, not by generic recursor
   substitution): use `Eq X X_reduced` (`X_reduced := 2*recAB + bitAB`,
   provable by pure `refl`/defeq once `a`, `b` are known positive — this
   part is easy and already validated in the analysis above) together with
   the RECOMPOSE identity — `div(2*rec+bit, 2) = rec` and
   `mod(2*rec+bit, 2) = bit` given `bit < 2`, via `div_mod_unique` against
   `div_mod_exec` and a hand-built `divMod` witness (same pattern as
   `land_aux_le_left`'s div/mod extraction, just with a general `rec`/`bit`
   pair instead of `half_m`/`bit_m`) — to relate `div(X,2)`/`mod(X,2)` back
   to `recAB`/`bitAB`, and finally apply the induction hypothesis at
   `(a/2, b/2, c/2)` to close the recursive sub-goal. Once this reconstruct
   lemma exists, THIS branch's algebra is the easy part (mirrors
   `land_aux_comm_of_fuel`'s per-bit `mul_comm` step, but with `mul_assoc`
   instead — the two `bit` expressions `((a%2)*(b%2))*(c%2)` and
   `(a%2)*((b%2)*(c%2))` are literally `Nat.mul_assoc`, no new bit-level
   lemma needed there).
5. Once `land_aux_assoc_of_fuel` is proved, `land_assoc` itself is routine:
   re-fuel `land (land a b) c` and `land a (land b c)` to the shared fuel
   `a + b + c` using `land_le_left` (for the nested-value bound,
   `Le (land a b) (a+b+c)` via `Le (land a b) a` + `Le a (a+b+c)` +
   `le_trans`) and `land_aux_agree_of_fuel`/`land_aux_eq_land_of_le`
   exactly as `land_comm` does — this part is NOT a wall, it is the same
   re-fueling machinery already built and tested, just needing the `a+b+c`
   ordering worked out for THREE terms instead of two (some `Le` sides need
   an `add_assoc`/`add_comm` transport, analogous to `land_comm`'s
   `Le n (add n m)` → `Le n (add m n)` step).

**`lor` diverges from `land` at exactly the bound lemma, not the dichotomy
difficulty.** `lor` GROWS rather than shrinks: `lor a b` can exceed both
`a` and `b` (e.g. `lor 1 2 = 3`), so `land_aux_le_left`'s statement is
FALSE for `lorAux`. The analogous, TRUE bound is
`lor_aux_le_sum : ∀ fuel m n, Le (lorAux fuel m n) (add m n)` (standard:
`a OR b ≤ a + b`, since OR never exceeds the sum of the operands — the
`m = 0`/`n = 0` leaves are `Le 0 n`/`Le m (add m n)` via `zero_le`/
`le_add_right` directly, no `land`-style absorbing-zero shortcut applies
since `lorAux`'s exhaustion row returns the OTHER operand, not `0`; the
"both positive" leaf needs the same `2*rec+bit ≤ 2*(sum/2ish)+...` shape
but the bound target is `add m n`, not `m` alone, so the arithmetic is
messier — budget it as at least as large as `land_aux_le_left`, likely
larger). The zero-check-on-a-compound-value wall in `lor_aux_assoc_of_fuel`
is THE SAME wall as `land`'s (same dichotomy-folding requirement, same
need for `add_eq_zero`/`mul`-style facts on the `max`-via-`ble` per-bit
combine instead of `mul`), so build `land_assoc` first — `lor_assoc`
transports the TECHNIQUE, not the bound lemma.

**Counts.** `nat_prelude` before this lane: 125 passed (post
`nat-fuel-transport`/`land_comm`). After: 127 passed (2 new declarations,
both theorems, `land_aux_le_left` and `land_le_left`; 1 new instantiation
test). `the_build_is_deterministic`'s pin: `88+452 → 88+454` (counted from
the panic message, not hand-incremented). `nat` trusted surface still
`axiom=0 opaque=0 quotient=0` (both new theorems carry empty
`axiom_footprint`, asserted in the new test).
`cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean. `python3 scripts/validate-facts.py`: 1925 facts, 0 errors
(unaffected — no fact file touched, since neither target fact closed).
NOT run: the aggregate `just check` / `./scripts/check.sh` (coordinator
re-verifies before merging, per this repo's standing rule).

Neither `F:ml430-nat-land-assoc-ad4775b8` nor
`F:ml430-nat-lor-assoc-82c4d0fd` was touched (both remain `open`, exactly
as found).
