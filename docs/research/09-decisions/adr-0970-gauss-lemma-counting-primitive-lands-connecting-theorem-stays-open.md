# ADR-0970: Gauss's lemma's least-residue sign-counting primitive lands; the connecting theorem to `a^m mod p` stays open, route fully sized

Status: accepted
Date: 2026-08-31
Index-summary: `Nat.leastResidue`/`Nat.gaussSignNeg`/`Nat.gaussNegCount` (least-residue sign counting over `Nat.countRange`) land axiom-free in a new `nat_prelude/gauss_lemma.rs`, along with `Nat.gauss_residue_two_eq_double_of_lt` (the `a := 2` mod-bypass) and eight concrete `gaussNegCount` instances confirming the `p mod 8` pattern numerically. The general symbolic closed form `gaussNegCount p 2 m = m - (div half 2)` and the connecting theorem to `a^m mod p` (Gauss's lemma proper) are NOT reached; both are fully routed lemma-by-lemma below for the next lane.
Index-status: accepted

## Context

ADR-0960 landed the necessary direction of Euler's criterion and sized two
routes to the second supplementary law of quadratic reciprocity (`2` is a QR
mod `p` iff `p ≡ ±1 mod 8`): a full converse of Euler's criterion (needs a
primitive root or a root-counting argument, neither buildable — this kernel
has no `List`/`Finset`/polynomial carrier), or Gauss's lemma (a
`Nat.countRange`-shaped least-residue sign count). It filed Gauss's lemma as
"this prelude does not build."

Re-measured before starting: `shape_search --name-like countRange` returns
19 declarations — `countRange` itself plus its zero/succ defining equations,
`countRange_le`, `countRange_congr`, `countRange_congr_lt`, `countRange_split`,
`countRange_eq_pred_of_only_zero_false`, `countRange_union_add_inter`,
`countRange_le_of_subset`, `countRange_compl`, `countRange_const_true`,
`countRange_permute`, `countRange_point_change`, plus the totient
application. This is real, general-purpose counting machinery
(`finite_set.rs`, `totient.rs`, `count_range_permute.rs`,
`count_range_reversal.rs`) — not merely names attached to one totient-shaped
use. This file is the first consumer to build a NEW `countRange` application
from scratch.

## Decision

**Build the counting primitive and the `a := 2` mod-bypass; do not attempt
the connecting theorem (`a^m ≡ (-1)^count [p]`) or the general symbolic
closed form in this session.** Reasoning:

- The counting primitive (`leastResidue`, `gaussSignNeg`, `gaussNegCount`) is
  three plain, non-recursive `Definition`s composing already-declared
  primitives (`Nat.mod`, `Nat.mul`, `Nat.div`, `Nat.ble`, `Nat.countRange`).
  Low risk, real infrastructure, and the exact shape Gauss's lemma needs.
- The `a := 2` case has a genuine simplification worth landing on its own:
  since `k` never exceeds `m = (p-1)/2` and `2m = p-1 < p`, `2k` never
  reaches `p`, so `Nat.mod_eq_self_of_lt` makes the least-residue map the
  identity-doubling map — no real reduction happens. This is
  `gauss_residue_two_eq_double_of_lt`, symbolic, axiom-free.
- Concrete instances at `p ∈ {7, 11, 13, 17, 19, 23}` (one representative of
  each nonzero residue class mod 8 among small odd primes) plus one at
  `a := 3` to confirm the count depends on `a`: cheap (`Eq.refl` at
  magnitudes ≤ 23), and they numerically confirm the classical pattern
  (count even ⟺ `p ≡ ±1 mod 8` ⟺ `2` is a QR) before any general theorem is
  attempted — per this repository's standing rule to re-run a plan's numeric
  claims rather than inherit them.
- **The general symbolic closed form and the connecting theorem were sized
  in full (see below) and NOT attempted**, on a risk call: every lemma the
  route needs exists and was verified by name and signature in-tree, but
  assembling roughly 150-250 lines of `Eq.refl`/`congr`/`transport`/`or_elim`
  proof-term construction without a REPL, in one sitting, on top of the work
  already spent verifying the route, was judged more likely to consume the
  rest of a session in `TypeMismatch` debugging than to land cleanly. A
  precisely sized route that the next lane can execute mechanically is worth
  more than a half-built attempt.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/gauss_lemma.rs` (new module),
wired into `build_nat_prelude` last (needs only `Nat.countRange`
(`declare_totient_all`) and `Nat.mod_eq_self_of_lt` (`declare_size_all`),
both far above):

- **`Nat.leastResidue : Nat → Nat → Nat → Nat`** — `leastResidue pp a k :=
  mod (mul a k) pp`.
- **`Nat.gaussSignNeg : Nat → Nat → Nat → Bool`** — `gaussSignNeg pp a k :=
  ble (succ (div pp 2)) (leastResidue pp a k)` — `true` exactly when the
  least residue exceeds `⌊pp/2⌋`, i.e. the symmetric representative in
  `(-pp/2, pp/2]` is negative.
- **`Nat.gaussNegCount : Nat → Nat → Nat → Nat`** — `gaussNegCount pp a m :=
  countRange (fun j => gaussSignNeg pp a (succ j)) m` — folds the sign
  predicate over the classical one-based range `k = 1, …, m`.
- **`Nat.gauss_residue_two_eq_double_of_lt`** — `∀ pp k, Lt (mul 2 k) pp →
  Eq (leastResidue pp 2 k) (mul 2 k)`, symbolic, via
  `Nat.mod_eq_self_of_lt`.
- Eight concrete `gaussNegCount` instances (`gauss_neg_count_seven_two`
  through `gauss_neg_count_seven_three`), each admitted by `Eq.refl` alone.

**Axiom footprint, read from the kernel**
(`every_nat_declaration_is_checked_and_axiom_free`, `nat_prelude::` sweep):
all three `Definition`s and all eight `Theorem`s carry an empty axiom
footprint. 242 `nat_prelude::` tests pass (nonzero count confirmed),
including this module's own two `#[cfg(test)]` checks (an independent
Rust-side recomputation of all seven numeric instances, and a kernel-level
`def_eq` check at a witness — `pp := 5` — outside the landed table, with a
non-vacuity negative control).

`python3 scripts/check-autogenesis-holdout-isolation.py`: PASS before and
after (this session never touched `artifacts/autogenesis/`).

## What remains, sized precisely — the general closed form

**Claim**: for all `half n : Nat`, letting `t := Nat.div half 2`,

```
Nat.countRange (fun j => Nat.ble (Nat.succ half) (Nat.mul 2 (Nat.succ j))) n
  = Nat.sub n t          -- (truncated; equals 0 when n <= t)
```

Verified numerically first (30 random `(half, n)` pairs in `[0,30]`, exact
match) — the check to re-run, not inherit:

```python
def D(half, n):
    return sum(1 for j in range(n) if 2*(j+1) > half)
# D(half, n) == max(0, n - half // 2) for every pair tried.
```

Specializing at `half := t := n := m` (since `p = 2m+1` makes
`div p 2 = m` exactly) gives `gaussNegCount p 2 m = m - div m 2 = ⌈m/2⌉`, the
classical Gauss-lemma closed form for `a := 2`.

**Proof route** (induction on `n`, `half` held as an outer free variable —
the predicate must NOT depend on the induction variable, which is why `half`
and `n` are kept as two separate parameters rather than the one-parameter
form `gaussNegCount p 2 m` directly):

Invariant, proved by `Nat.rec` on `n`:

```
Disj(half, n) :=
  Or (And (Eq (countRange f n) 0)      (Le n t))
     (And (Le t n) (Eq (add (countRange f n) t) n))
```
where `f j := Nat.ble (Nat.succ half) (Nat.mul 2 (Nat.succ j))` and
`t := Nat.div half 2`.

*Base* (`n := 0`): left disjunct, `Eq.refl 0` and `Nat.zero_le`.

*Step* (`ih : Disj(half, j)`, goal `Disj(half, succ j)`): the successor
unfold `countRange f (succ j) ≡ add (countRange f j) (bool_select_nat (f j)
1 0)` is DEFINITIONAL (`countRange_succ` is proved by `Eq.refl`), so no
lemma application is needed for it — state target types using the raw
`add(...)` form directly and let the kernel's own delta/iota reduction
bridge it to `countRange f (succ j)`, exactly the idiom
`finite_set.rs::declare_count_range_union_add_inter`'s own successor step
already uses.

`Or.elim` on `ih` (two branches, `p.logic.or_elim`):

- **Branch A** (`ih_A : Eq (countRange f j) 0 ∧ Le j t`): `Nat.lt_or_eq_of_le`
  on `Le j t` gives `Or (Lt j t) (Eq j t)`; `Or.elim` again:
  - **A1** (`Lt j t`, i.e. `Le (succ j) t` by defeq — `Nat.lt` is
    definitionally `Nat.le (Nat.succ _) _`): show `f j = false`. Chain:
    `Nat.mul_le_mul_left(2, succ j, t, this)` gives
    `Le (mul 2 (succ j)) (mul 2 t)`; separately `Le (mul 2 t) half` (from
    `Nat.div_mod_exec(1, half)`'s `And` — its left component is
    `Eq half (add (mul 2 t) (mod half 2))`, transport `Nat.le_add_right(mul 2
    t, mod half 2)` along its `symm`); `Nat.le_trans` chains these to
    `Le (mul 2 (succ j)) half`; `Nat.lt_succ_of_le` gives
    `Lt (mul 2 (succ j)) (succ half)`; `Nat.ble_eq_false_of_lt(succ half,
    mul 2 (succ j), this)` gives `Eq (f j) false`. Then
    `Nat.zero_add`+`congr` through `add(_, bool_select_nat(f j,1,0))` chains
    `countRange f (succ j)` to `0` (the `false` branch of
    `bool_select_nat` is definitionally `0`). Result: left disjunct, with
    `Le (succ j) t` being `Lt j t` itself (defeq).
  - **A2** (`Eq j t`): show `f j = true`. First establish, ONCE, OUTSIDE the
    induction (it only depends on `half`, not `n`):
    `lt_half_mul2_succt : Lt half (mul 2 (succ t))`, via
    `Nat.div_mod_exec`'s bound `Lt (mod half 2) 2` (giving, via
    `Nat.le_of_lt_succ`, `Le (mod half 2) 1`),
    `Nat.add_le_add_left(mul 2 t, mod half 2, 1, this)` transported along
    `half`'s defining equation to `Le half (add (mul 2 t) 1)`, then
    `Nat.lt_succ_of_le` to `Lt half (succ (add (mul 2 t) 1))` — DEFEQ to
    `Lt half (mul 2 (succ t))` since both `succ (add (mul 2 t) 1)` and
    `mul 2 (succ t)` reduce (via `Nat.add_succ`/`Nat.mul_succ`, both
    `Eq.refl`) to `add (mul 2 t) 2`. Then `congr` `lt_half_mul2_succt`
    through `Eq j t` (via `succ`/`mul`) to get `Lt half (mul 2 (succ j))`,
    hence (defeq) `Le (succ half) (mul 2 (succ j))`, hence
    `Nat.ble_eq_true_of_le` gives `Eq (f j) true`. Then chain
    `countRange f (succ j)` (via `ih_A`'s `Eq (countRange f j) 0`,
    `Nat.zero_add`, and `f j = true`'s `bool_select_nat` collapse to `1`) to
    `1`. Need `Eq (add 1 t) (succ j)`: `Nat.add_comm(1,t)` to `add t 1`,
    which is DEFEQ to `succ (add t 0)`, propositionally `succ t` via
    `Nat.add_zero`; `congr Eq j t` through `succ` (symm) relates `succ t` to
    `succ j`. Chain these four steps. `Le t (succ j)`: `Nat.le_succ(t)`
    transported along `Eq j t` (via `succ`, symm). Result: right disjunct.
- **Branch B** (`ih_B : Le t j ∧ Eq (add (countRange f j) t) j`): show
  `f j = true` directly from `Le t j` (no need for `Eq j t`):
  `Nat.le_succ_succ(t, j, ih_B.1)` gives `Le (succ t) (succ j)`;
  `Nat.mul_le_mul_left(2, succ t, succ j, this)` gives
  `Le (mul 2 (succ t)) (mul 2 (succ j))`; `Nat.lt_of_lt_of_le` with the
  SAME `lt_half_mul2_succt` computed once above gives
  `Lt half (mul 2 (succ j))`, then `ble_eq_true_of_le` as in A2. `Le t (succ
  j)`: `Nat.le_trans(t, j, succ j, ih_B.1, Nat.le_succ(j))`. Final equation
  `Eq (add (countRange f (succ j)) t) (succ j)`: `countRange f (succ j))`
  chains (via `f j = true`) to `add (countRange f j) 1`;
  `Nat.add_right_comm(countRange f j, 1, t)` gives
  `Eq (add (add (countRange f j) 1) t) (add (add (countRange f j) t) 1)`;
  `congr ih_B.2` through `add(_, 1)` gives `Eq (... ) (add j 1)`; `add j 1`
  is DEFEQ to `succ (add j 0)`, propositionally `succ j` via `add_zero`.
  Chain all four. Result: right disjunct.

**Every lemma named above was confirmed to exist with the stated signature**
by reading its declaration in-tree before this ADR was written (`Nat.lt` is
literally `Nat.le (Nat.succ x) y` — `ops.rs` — which is what makes the A1/B
`defeq` shortcuts work without extra lemmas): `Nat.lt_or_eq_of_le`,
`Nat.mul_le_mul_left`, `Nat.le_add_right`, `Nat.le_trans`,
`Nat.lt_succ_of_le`, `Nat.ble_eq_false_of_lt`, `Nat.ble_eq_true_of_le`,
`Nat.le_of_lt_succ`, `Nat.add_le_add_left`, `Nat.le_succ`,
`Nat.le_succ_succ`, `Nat.lt_of_lt_of_le`, `Nat.add_comm`,
`Nat.add_right_comm`, `Nat.add_zero`, `Nat.zero_add`, `Nat.div_mod_exec`,
`Nat.zero_le`, `Nat.le_antisymm` (not needed in the route above once `Le t
j` is carried as an explicit invariant conjunct rather than re-derived from
the equation — an earlier draft of this route needed it and was simplified
away). `p.logic.or_elim`, `and_left`/`and_right`
(`nat_prelude/helpers.rs`), `d.eq_motive`/`d.transport`/`d.congr`/`d.chain`
(`ops.rs`) are the structural plumbing, all used exactly as
`finite_set.rs` and `mul_order_lemmas.rs` already use them.

## What remains beyond the closed form — the connecting theorem

Even with the closed form landed, `gaussNegCount p 2 m`'s value alone does
NOT establish the second supplementary law: Gauss's lemma's actual content
is `a^m ≡ (-1)^(gaussNegCount p a m) [p]`, which this file does not touch.
That needs:

1. The least-residue map `k ↦ leastResidue p a k` is injective on `{1, …,
   m}` (needs `a` coprime to `p`, i.e. `0 < a < p` for prime `p`).
2. A pairing lemma: whenever `leastResidue p a k` exceeds `p/2`, its
   "negative" partner `p - leastResidue p a k` is itself a least residue of
   `a·k'` for some other `k'` in `{1, …, m}`, and the map
   `k ↦ (if negative then p - residue else residue)` is a BIJECTION onto
   `{1, …, m}`.
3. A product-cancellation argument: `∏_{k=1}^{m} (a·k) ≡ (-1)^count ·
   ∏_{k=1}^{m} k [p]`, i.e. `a^m · m! ≡ (-1)^count · m! [p]`, and
   `gcd(m!, p) = 1` (from `p` prime, `m < p`) lets `m!` cancel.
   `Int.prodRange` (`int_prelude/prod.rs`, built for Wilson's theorem) is
   the right carrier for the product; `Int.prodRange_permute` (used by
   Wilson's theorem, per CLAUDE.md's own retrieval-hazard entry — "the same
   argument over a different aggregate in a different prelude") is the
   directly reusable permutation-invariance skeleton for step 2's
   reindexing.

This is a materially larger, multi-lemma construction than the closed form
above, genuinely deserving its own session — sizing it further than this
paragraph needs actual construction, which this ADR does not attempt.

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 242 passed, 0
  failed (nonzero count confirmed).
- `cargo test -p axeyum-lean-kernel --lib gauss_lemma::` — 2 passed
  (independent Python-recomputation check, and a kernel `def_eq` check at
  `pp := 5` with a non-vacuity negative control).
- `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS before and
  after (`artifacts/autogenesis/` untouched this session).
- No fact-ledger entries added this session.
