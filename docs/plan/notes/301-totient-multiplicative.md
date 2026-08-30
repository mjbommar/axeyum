# Notes: 301-totient-multiplicative

Detail moved out of [`../status/301-totient-multiplicative.md`](../status/301-totient-multiplicative.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`Nat.gcd_comm : ∀ a b, Eq (gcd a b) (gcd b a)`** is now declared, axiom-free
(`nat_prelude/totient_multiplicative.rs`). It has been flagged ABSENT across
all three prior totient triages (`287`, `291`, `295`) and was a concrete
blocker inside `295`'s own `totient_even` plan (its Step 1 needed a
`gcd(n−k,n) = gcd(k,n)`-shaped chain). It turned out to need **zero new
induction**: the identical mutual-divisibility-then-antisymmetry shape
`Nat.lcm_comm` (`lcm.rs::declare_lcm_comm`) already uses, built from three
already-declared pieces (`gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`) plus
`dvd_antisymm`. Filed in a new file rather than beside `lcm_comm` in
`lcm.rs`/`gcd.rs`, per this task's own file-collision avoidance (a sibling
lane holds `totient_lemmas.rs`, and this lane was told to create a new file
for anything totient-multiplicative). It is genuinely needed by the plan
below, not incidental: totient's own predicate is `gcd k n` (index first,
modulus second — `totient.rs`), while the mod-invariance step the plan needs
(`gcd (x mod m) m = gcd x m`) falls out of the existing Euclidean recursion
equation `Nat.gcd_succ : gcd (succ k) n = gcd (mod n (succ k)) (succ k)` **in
the other argument order** — instantiating it gives `gcd m x = gcd (x mod m)
m`, and bridging that to `gcd x m` needs exactly `gcd_comm`. No route through
this plan avoids needing it.

Pinned by a concrete-instantiation test at a discriminating pair (`gcd 6 4`
vs `gcd 4 6` — both reduce to `2`, but the pinned conclusion is the
UNREDUCED `Eq (gcd 6 4) (gcd 4 6)`, not `Eq 2 2`, so a theorem that left the
arguments unswapped would still type-check against a def_eq-equal but
differently-shaped goal) plus a genuinely free `(a, b)` via
`LocalContext`/`infer_in`.

Not attached to any fact — like `Nat.coprime_succ_self` before it, this is an
unregistered nat-prelude helper theorem, not an axiom.

## Part 3 — the multiplicative formula, hand-traced and numerically checked, NOT built

**Target:** `Nat.totient_mul_of_coprime : ∀ m n, Coprime m n → Eq (totient
(mul m n)) (mul (totient m) (totient n))`.

This blocks (per the brief, and confirmed by reading their `formal.statement`
fields):

```
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7   -- the GENERAL (non-coprime)
    identity gcd(a,b).totient * (a*b).totient = a.totient * b.totient * gcd(a,b);
    the coprime formula above is a necessary ingredient, not sufficient by
    itself (the general form needs it applied to a's/b's shared-prime-power
    structure, which is further work again).
F:ml430-nat-totient-dvd-of-dvd-9622e44a            -- also routes through the
    general formula.
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7 (half) -- ditto.
```

### Does the CRT machinery transport? Checked, with statements, not names.

**`int_prelude/crt.rs` (`Int.crt_exists`/`Int.crt_unique`) does NOT
transport.** It is stated over `ℤ` with `Int.ModEq`, and existence there is
built from `Int.gcd_eq_gcd_ab`'s SIGNED Bézout certificate — moving it to a
`Nat.countRange` bijection argument over `[0, mn)` would need a `Nat ↪ Int`
embedding plus re-deriving the bounded-representative argument by hand; the
`crt.rs` module doc itself already says this was judged not worth the cost.

**But `nat_prelude/crt.rs` ALREADY EXISTS, is Nat-native, and DOES transport
directly — this is the load-bearing correction to the prior three triages,
none of which found it.** It declares:

- `Nat.coprime_mul_dvd : ∀ m n k, Eq (gcd m n) one → dvd m k → dvd n k → dvd
  (mul m n) k` — coprime divisors of a common value combine into a divisor of
  their product.
- `Nat.crt_unique : ∀ m n x y, Eq (gcd m n) one → modEq m x y → modEq n x y →
  modEq (mul m n) x y` — CRT's uniqueness half, over `Nat.modEq d a b := ∃ u
  v, a + d*u = b + d*v`, proved from `coprime_mul_dvd` plus the existing
  `mod_eq_zero_iff_dvd` divisibility bridge.

Existence is explicitly declined there (same Bézout-sign-resolution cost as
the `Int` version), **but the plan below never needs it**: this kernel
already has the general finite pigeonhole
(`Nat.injective_on_imp_surjective_on : InjectiveOn f n → MapsInto f n →
SurjectiveOn f n`, `finite.rs`), which turns injectivity of a *self-map* into
surjectivity FOR FREE. CRT existence over ℕ was declined specifically because
the classical witness needs signed coefficients; the pigeonhole route never
constructs a witness at all.

### The plan

**Step 0 — the CRT self-map.** Define (not yet declared)
`g(x) := add (mul (mod x m) n) (mod x n)` for `x : Nat`.

- **`MapsInto g (mul m n)`**: `∀ x, x < mn → g x < mn`. Pure arithmetic,
  independent of `Coprime m n`: `mod x m < m` and `mod x n < n`, so `g x =
  (mod x m)*n + (mod x n) ≤ (m-1)*n + (n-1) = mn - 1`. Verified numerically
  for every `x < mn` at 12 coprime pairs up to `(4,25)`.
- **`InjectiveOn g (mul m n)`** (needs `Coprime m n`): from `g x = g y` with
  `x, y < mn`, uniqueness of the `(quotient, remainder)` decomposition against
  the shared modulus `n` (both `mod x n` and `mod y n` are `< n`) gives `mod x
  m = mod y m` AND `mod x n = mod y n` — this is `Nat.mod_eq_iff_div_mod_remainder_eq`
  (`divMod d a qa ra → divMod d b qb rb → (modEq d a b ↔ ra = rb)`) run
  backwards from the remainder equality (a small side lemma:
  `Eq (mod x n) (mod y n) → modEq n x y`, immediate from that `Iff`'s `mpr`
  once `x`/`y`'s own `divMod` witnesses are in hand). Feed both `modEq m x y`
  and `modEq n x y`, plus `Coprime m n`, to `Nat.crt_unique`:
  `modEq (mul m n) x y`. Since `x, y < mn`, `mod x (mn) = x` and `mod y (mn) =
  y` (`Nat.mod_eq_self_of_lt`), and the same remainder-uniqueness bridge turns
  `modEq (mn) x y` back into `x = y`.
- **`SurjectiveOn g (mul m n)`**: `Nat.injective_on_imp_surjective_on(g, mn,
  <InjectiveOn proof>, <MapsInto proof>)`. No Bézout witness ever built.

**Numerically verified**: `g` is a genuine bijection `[0, mn) → [0, mn)` for
every tested coprime pair (`(2,3) … (2,25)`, 12 pairs, full range each), and
demonstrably NOT injective at `m = n = 2` (negative control: `g(0) = g(2) =
0`), confirming the coprimality hypothesis is load-bearing, not decoration.

**Step 1 — mod-gcd invariance.** `Nat.gcd_mod_left_eq_gcd : ∀ x m, Eq (gcd (mod
x m) m) (gcd x m)` (not yet declared; small, follows the pattern
`gcd_succ`/`gcd_comm` already support): case-split `m` (`cases_zero_succ`).
`m = 0`: `mod x 0 = x` (mod-by-zero convention — check the exact totality
lemma name, e.g. `mod_zero`), trivial. `m = succ k`: `gcd_succ` gives `gcd m x
= gcd (mod x m) m`; `gcd_comm` (Part 2, now landed) bridges both sides
(`gcd m x` to `gcd x m`, and the RHS is already in the wanted `gcd _ m` shape)
to close `gcd x m = gcd (mod x m) m`, then `gcd_comm` again for the stated
direction. Verified numerically: `gcd(x mod m, m) = gcd(x, m)` for every `x <
mn`, at all 12 tested coprime pairs.

**Step 2 — the coprimality-combine lemma (WEAKEST STEP, #1 of 2).**
`Nat.coprime_mul_of_coprime : ∀ x m n, Eq (gcd x m) one → Eq (gcd x n) one →
Eq (gcd x (mul m n)) one` — i.e. Mathlib's `Nat.Coprime.mul_right`. **This
kernel does not have it in either direction combined; only the SHRINK
direction exists** (`coprime_mul_right_right`/`coprime_mul_left_right` give
`Coprime x (mul m n) → Coprime x m` and `→ Coprime x n`, both already
declared and directly reusable — no new work for the shrink half).

Two candidate routes, neither attempted in Rust:

- **(a) Bézout-certificate multiplication.** From `1 = x·u₁ + m·v₁` and `1 =
  x·u₂ + n·v₂` (signed), multiplying gives `1 = x·U + (mn)·V` with `U =
  x·u₁·u₂ + n·u₁·v₂ + m·v₁·u₂`, `V = v₁·v₂`. **Verified numerically**
  (extended-Euclid over signed integers, 200 random coprime triples): the
  identity holds exactly. The risk is translating this into `Nat.bezout`'s
  BALANCED difference-of-two-nats encoding (`bezout m n g := ∃ mp mn np nn, g
  + m*mn + n*nn = m*mp + n*np`) — `crt.rs`'s own module doc already records
  that a naive attempt at a DIFFERENT balanced-Bézout construction (the CRT
  existence witness) "fails structurally" because only the *difference* of
  the balanced coefficients is congruent to anything clean, and the same
  four-sign-combination case analysis would likely recur here. Untried.
  `Nat.coprime_of_bezout_one`/`Nat.gcd_bezout`/`Nat.bezout_of_scaled` are the
  existing pieces this route would compose.
- **(b) Prime-divisor contrapositive.** Show the contrapositive: if `gcd x (mn)
  ≠ 1`, some prime `p` divides both `x` and `mn`; Euclid's lemma gives `p | m`
  or `p | n`; either combined with `p | x` contradicts `gcd x m = 1` or `gcd x
  n = 1` respectively (a common prime divisor forces `gcd ≥ p > 1`). This
  kernel's existing prime-divisibility lemmas (`coprime_or_dvd_of_prime`,
  `prime_dvd_iff_not_coprime`, `exists_prime_dvd`, `prime_dvd_mul_of_dvd_ne`)
  are all stated for a FIXED prime dividing a specific target, not phrased as
  "no prime divides both," so this route also needs new assembly, likely via
  `Nat.coprime_of_forall_prime_dvd` (`∀ k, prime_condition k → dvd k m → dvd k
  n → dvd k one) → gcd m n = one`, already declared) run at `(x, mul m n)`.

Route (b) looks slightly cheaper (no balanced-Bézout multiplication algebra)
but needs `prime_dvd_mul_of_dvd_ne`-shaped reasoning generalized from "two
distinct primes" to "a prime dividing a product." **Recommend the next lane
try (b) first**, sizing it against a throwaway probe before committing.

**Step 3 — the pointwise predicate identity.** For `x < mn`:
`beq (gcd x (mul m n)) one` `=` `Bool.and (beq (gcd (mod x m) m) one) (beq
(gcd (mod x n) n) one)`. Forward: Step 2's shrink half (already declared) plus
Step 1. Backward: Step 1 plus Step 2's combine half (the weakest step above).
Verified numerically for ALL `x < mn` at all 12 tested coprime pairs (this is
exactly the `check_coprime_combine_needed` control in the session's scratch
script, generalized past `x < 12` to the full residue range) — the iff holds
with no exceptions, and is FALSE-shaped as an equality of unreduced predicates
that a caller must actually derive, not something reducible by `Eq.refl` at
symbolic `x`.

**Step 4 — the double-counting identity (WEAKEST STEP, #2 of 2, the genuinely
novel induction).** State it **totient-independently**, per the brief's own
instruction:

```
Nat.count_range_row_major : ∀ P Q m n,
  Eq Nat
    (countRange (fun x => Bool.and (P (mod x m)) (Q (mod x n))) (mul m n))
    (mul (countRange P m) (countRange Q n))
```

**No coprimality hypothesis needed here at all** — this is pure counting
combinatorics over the row-major grid, independent of whether `m`, `n` are
coprime (verified numerically at several NON-coprime pairs too, e.g. `(4,6)`:
holds regardless). Proof sketch, by induction on `m` (not attempted in Rust):

- `m = 0`: both sides are `0` (`countRange _ 0 = 0`, `mul 0 (mul m n)` — wait,
  `mul m n` at `m=0` is `0`, and `countRange _ 0 = 0` on the left; on the
  right `mul (countRange P 0) (countRange Q n) = mul 0 _ = 0`). Trivial.
- `m = succ k`: `mul (succ k) n = add (mul k n) n`. `Nat.countRange_split(f,
  mul k n, n)` splits the LEFT side's `countRange` at that point into
  `countRange f (mul k n) + countRange (shift f (mul k n)) n`, where `f x :=
  Bool.and (P (mod x m)) (Q (mod x n))`. The IH applies to the first summand
  (`m := k`) ONLY after showing `f` restricted to `[0, k*n)` is
  `m`-periodic-compatible with `k`'s own row-major predicate at modulus `k`
  rather than `succ k` — this is the part that needs care: `mod x (succ k)`
  for `x < k*n` is NOT simply `mod x k`, so the induction is not a bare
  substitution; it needs the row-major indexing to be BY ROW (`x = a*n + b`,
  `a < m`, `b < n`) rather than by the modulus argument directly. The
  cleaner induction variable is therefore the ROW COUNT, not `m` used as a
  modulus — i.e., generalize to a statement indexed by an explicit row bound
  `a ≤ m` and induct on `a`, with the modulus `m` held FIXED throughout (the
  same "hold the divisor fixed, induct on a separate counter" shape
  `Nat.countRange_split`'s own proof already uses). Each new row `a`
  contributes `countRange (fun k => Q (mod (add (mul a n) k) n)) n`, which
  collapses to `countRange Q n` (since `mod (add (mul a n) k) n = mod k n =
  k` for `k < n` — an `add_mul_mod_self_left`-shaped fact, likely present or
  a one-line consequence of `mod_eq_self_of_lt` plus an existing
  mod-of-sum-with-a-multiple lemma; not checked by name) when `P a` is `true`,
  and to `0` (via a small, likely-needs-building
  `countRange (const false) n = 0` helper — a two-line induction, NOT a real
  risk) when `P a` is `false`. Summing `m` such row contributions, each `0` or
  `countRange Q n` selected by `P a`, IS `mul (countRange P m) (countRange Q
  n)` by definition of `countRange P m` as counting the `true` rows.
- This is structurally the SAME row-major decomposition
  `nat_prelude/rectangle.rs` already executes for `sumRange` (its own module
  doc: "Row `i`'s full width is `Σ_{j<n} F i j`... reindexing `j := (n−i)+k`
  ..."), specialized to a 0/1-valued `F`. **Recommend building this as a
  literal adaptation of `rectangle.rs`'s row/shift helpers
  (`row_fn`/`row_sum`/`shifted`, already `pub(super)` and reused across files
  per that module's own doc) rather than re-deriving the row-peeling
  machinery from scratch** — the sibling file `totient.rs` already imports
  `rectangle.rs`'s `shifted` for an unrelated shift (see its module doc line
  432), so the precedent for cross-file reuse here is direct.

**Numerically verified**: `count_range_row_major`'s conclusion checked
directly (not merely implied by the bijection argument) for `(P, Q, m, n)` at
every one of the 12 tested pairs plus two NON-coprime pairs `(4,6)`, `(6,9)`,
confirming the identity's independence from `Coprime m n` as claimed.

**Step 5 — assembly.** `totient (mul m n) = countRange coprime_mn_pred (mul m
n)` `[Step 3, countRange_congr]= countRange (fun x => Bool.and (coprime_m_pred
(mod x m)) (coprime_n_pred (mod x n))) (mul m n)` `[Step 4, at P :=
coprime_m_pred, Q := coprime_n_pred] = mul (countRange coprime_m_pred m)
(countRange coprime_n_pred n) = mul (totient m) (totient n)`. No further new
machinery once Steps 2 and 4 exist.

### Summary of what's new vs. reused

| piece | status |
| --- | --- |
| `g`, `MapsInto g`, `InjectiveOn g`, `SurjectiveOn g` | reused wholesale from `nat_prelude/crt.rs` + `finite.rs`'s pigeonhole; **turned out NOT to be needed by the final plan** (Steps 3-5 route through the pointwise predicate + row-major counting identity instead, which is more direct) — kept in this doc because it is the thing that answers "does CRT transport", and because a future `eq_or_eq_of_totient_eq_totient`/uniqueness-flavored mirror may want the bijection itself rather than just the count |
| Step 1 (mod-gcd invariance) | new, small, ingredients (`gcd_succ`, `gcd_comm`) now both exist |
| Step 2 (coprime combine) | **new, WEAKEST STEP — real number theory**, two candidate routes, neither built |
| Step 3 (pointwise iff) | new but cheap once Steps 1-2 exist (pure composition) |
| Step 4 (double-counting) | **new, WEAKEST STEP — the one genuinely novel induction**, but the target statement, its totient-independent generality, and its proof SHAPE (row-major peel, precedented by `rectangle.rs`) are all nailed down; only the mechanical Rust construction remains |
| Step 5 (assembly) | new, pure composition, no risk once 2 and 4 exist |

**Do not force a proof of Steps 2 or 4 under time pressure** — each is sized
at roughly the scope of one prior lane's dispatch in this family (comparable
to `291`'s counting-machinery lane or `295`'s two-mirror-plus-plan lane). The
next lane should pick ONE (recommend Step 4 first, since its target statement
is stated totient-independently already and its proof shape is directly
precedented in this codebase, whereas Step 2 has two untried candidate routes
with a real chance the first one picked needs to be abandoned partway).

**Verification of this session's numerical claims**: all checked in a Python
script in this session's scratchpad (not committed — ephemeral per this
repository's own convention), covering: `g`'s bijectivity (12 coprime pairs,
full range, plus a non-coprime negative control), mod-gcd invariance (same 12
pairs, full range), the pointwise coprimality iff (same), the Bézout
multiplication algebra (200 random coprime triples via extended Euclid), and
`totient(mn) = totient(m)·totient(n)` itself (same 12 pairs, as the
end-to-end sanity check the whole plan is aimed at). Reproducible inline from
this doc's Step numbers.

## Verification (this session)

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **173 passed, 0
failed** (171 baseline for this dispatch + `coprime_div_left`'s test +
`gcd_comm`'s test, each confirmed to run by name with a nonzero count).
`cargo fmt` (per-file `rustfmt --edition 2024`) and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean.
`python3 scripts/check-test-attribute-integrity.py`: 0 findings.
`python3 scripts/validate-facts.py`: 2074 facts, 0 errors.
`the_build_is_deterministic`'s pin moved twice, each taken from the panic
message's own mismatch, never hand-incremented: `93 + 557 → 93 + 558`
(`coprime_div_left`), then `93 + 558 → 93 + 559` (`gcd_comm`).

**Commits** (not pushed): `b137856b7` (wip: `coprime_div_left`, build
unverified — within the first ten tool calls), `729f3baca`
(`coprime_div_left`'s tests + coverage + pin, verified), `e18852776` (the
fact-ledger flip), `4d13bcaf1` (`gcd_comm` + tests + coverage + pin,
verified). This status file's own commit follows.
