# ADR-1552: Eisenstein's lemma was blocked on a missing aggregate and nothing else

Status: accepted
Date: 2026-09-02
Index-summary: **Eisenstein's lemma is now a kernel theorem**
(`Nat.eisenstein_lemma : ∀ m n, gcd (2n+1) (2m+1) = 1 → Even (F + N)`), with
the congruence form `Nat.eisenstein_lemma_modEq` beside it. Twelve declarations
land, every one admitted on the FIRST kernel attempt and every one axiom-free.
**ADR-1544's three remaining residues — 2, 3 and 5 — all close**, so nothing
ADR-1540 or ADR-1544 left open is still open. The finding that
matters is a correction: **residue 2 was never blocked on Gauss's lemma or on
coprimality** — it is hypothesis-free, and the only thing standing in front of
it was `Nat.sumRangeIf`, an aggregate two lanes measured ABSENT and neither
built. Three further measurements a name search does not give you: there is no
`Nat.div_add_mod`, but `Nat.div_mod_exec`'s LEFT CONJUNCT is the division
algorithm; `Nat.modEq` DOES exist even though `--name-like modEq` returns 40
declarations that are all `Int`; and the odd parts of both products in the
parity step come off DEFINITIONALLY because `Nat.mul` recurses on its right
argument. **Quadratic reciprocity is NOT proved** — Eisenstein's lemma is one
of its two halves and `Nat.eisenstein_floor_sum` (ADR-1544) is the other; what
is missing is the `Int`-side assembly through `Int.gaussLemmaSignCount`.
Index-status: accepted

## Context

ADR-1260 routed Eisenstein's lattice count around ADR-1135's missing-aggregate
wall and named three residues. ADR-1290 closed the floor-counting family.
ADR-1540 closed the side condition and built `Nat.sumRange_permute`, then named
four residues of its own. ADR-1544 closed its residues 1 and 4 —
`Nat.gauss_fold_sumRange_eq` and `Nat.eisenstein_floor_sum` — and left three
open:

- **residue 2**, the residue/fold reconciliation, *"wants a conditional sum,
  and `sumRangeIf` exists in no prelude"*;
- **residue 3**, the mod-2 bookkeeping, *"open, untouched"*;
- **residue 5**, the `min`-free corollary.

### Step 0, re-measured on this branch rather than inherited

`examples/shape_search`, rebuilt here (`declarations=2092` before this lane's
own declarations, so not a stale binary reporting a false ABSENT):

| query | verdict |
| --- | --- |
| `--name-like sumRangeIf` | **ABSENT**, against `positive control: any-kind=2092` |
| `--name-like prodRangeIf` (the positive control for that query) | FOUND, 12 declarations across `Nat` and `Int` |
| `--name-like bnot` (is there a `Bool.not`?) | **ABSENT** |
| `--name-like div_add_mod` / `mod_add_div` | **ABSENT** |
| `--name-like modEq` | FOUND 29–40, **every one of them `Int`** — see §5 |

So ADR-1544's refusal to claim residue 2 was easy was correct about the
absence, and wrong about nothing. What it did not know is that the absence was
the *only* obstacle.

## Decision

Twelve declarations, in five groups.

### 1. `Nat.sumRangeIf`, the missing corner of the subset-fold triangle

```text
Nat.sumRangeIf p f n := Nat.sumRange (fun i => bool_select_nat (p i) (f i) 0) n
Nat.sumRangeIf_zero     : ∀ p f,     sumRangeIf p f 0 = 0
Nat.sumRangeIf_succ     : ∀ p f n,   sumRangeIf p f (succ n)
                                     = sumRangeIf p f n + bool_select_nat (p n) (f n) 0
Nat.sumRangeIf_congr_lt : ∀ p q f g n, (agree below n, both halves) → equal sums
Nat.sumRangeIf_compl    : ∀ p f n,   sumRangeIf p f n + sumRangeIf (setCompl p) f n
                                     = sumRange f n
```

`Nat.countRange` counts a predicate subset (`totient.rs`), `Nat.prodRangeIf`
multiplies over one (`subset_product.rs`), and nothing summed over one. This is
`subset_product.rs` with exactly one change — the unselected value is `0`, the
additive identity, where the product side uses `1`.

**The split is stated over `Nat.setCompl`, with no complementarity
hypothesis.** That is a decision and not an accident: this kernel has no
`Bool.not` (measured), and `Nat.setCompl p := fun k => if p k then false else
true` (`finite_set.rs`) IS that missing function, already carrying its own
involutivity and De Morgan laws. So the split is the exact additive twin of
`Nat.countRange_compl` and needs no side condition, unlike
`Nat.countRectangle_partition`, which takes one because a strict half-plane
pair cannot supply `setCompl`.

**The trusted gate cannot tell you a `Definition` is wrong**, and here the type
`(Nat → Bool) → (Nat → Nat) → Nat → Nat` is the type of every wrong variant.
So the evaluation tests come first and the definition's VALUE is pinned
character for character. The three negative controls are the numeral above, the
`prodRangeIf` convention's value (unselected index padded with `1`), and the
complement's value (the predicate read the other way round) — three different
numbers at each instance used, checked in Rust before the kernel is asked
anything.

### 2. Residue 2, and the correction it forces

```text
Nat.leastResidue_sumRange_reconcile : ∀ ap a m,
  Σ_{j<m} leastResidue pp a (j+1)  +  (S + S)
  =  Σ_{j<m} gaussFold pp a (j+1)  +  pp · gaussNegCount pp a m
```

with `pp := succ ap` and `S := sumRangeIf sign fold m`.

**Two deliberate restatements of what both prior lanes wrote.**

1. **Additive, not subtractive.** ADR-1540 and ADR-1544 both wrote the residue
   as `Σ leastResidue = Σ gaussFold + pp·N − 2·Σ_neg gaussFold`. That
   statement cannot be made here as written: `Nat.sub` is TRUNCATED, so an
   identity with a subtraction on the right is a *different proposition* from
   the one intended whenever the subtrahend could exceed the minuend, and
   nothing in the statement bounds it. Moving the negative term across removes
   the question entirely and is the same identity over ℤ.
2. **`x + x`, not `2 * x`.** `Nat.mul` recurses on its RIGHT argument, so
   `mul 2 Σ` is stuck at a symbolic sum and would need a `two_mul` bridge this
   prelude does not have. (One is built here as a two-step *local* chain, not a
   declaration, for the one place `add_mul_mod_self_left` forces a `2 * x`.)

**And it has NO hypothesis. This is the correction.** ADR-1540 sized residue 2
as downstream of Gauss's lemma; ADR-1544 repeated that framing. Coprimality is
what makes the FOLD a bijection (`gauss_fold_sumRange_eq`), not what makes a
residue and its reflection add to `pp`. The only side condition the argument
needs is `leastResidue < pp`, which is `Nat.mod_lt` at a positive modulus, and
the modulus is given constructively as `succ ap` so the positivity is
`Nat.zero_lt_succ` and never becomes a hypothesis. C2 of the check script
verifies the identity at 8,450 instances including 5,070 with a composite
modulus and 3,250 non-coprime.

The proof is one pointwise `Bool.rec` on the sign, lifted by
`sumRange_congr` + three `sumRange_add`s + `mul_sumRange` +
`countRange_eq_sumRange`. **The motive has to abstract the sign TWICE** — once
in the selector and once inside `gaussFold`, which contains it by δ and offers
no variable to abstract. That is why the motive is written over
`bool_select_nat x (bool_select_nat x (sub pp L) L) 0` and not over `gaussFold`.

### 3. Residue 3, and where the division algorithm was hiding

```text
Nat.mul_sumRange_div_add_leastResidue : ∀ ap a m,
  a · T  =  pp · Σ_{j<m} ⌊a(j+1)/pp⌋  +  Σ_{j<m} leastResidue pp a (j+1)

Nat.eisenstein_count_identity : ∀ m a, gcd a (2m+1) = 1 →
  a · T + (S + S)  =  pp · (F + N) + T
```

The pointwise content of the first is `a·k = pp·⌊a·k/pp⌋ + (a·k mod pp)` — the
division algorithm — and **it was already in this prelude under a name nothing
points at.** There is no `Nat.div_add_mod` (measured ABSENT). But
`Nat.div_mod_exec ap n : divMod (succ ap) n (div n (succ ap)) (mod n (succ ap))`
exists, and `Nat.divMod d n q r` unfolds to
`And (Eq n (add (mul d q) r)) (Lt r d)` (`division.rs`), so its **left
conjunct** is exactly the identity, at a constructively positive divisor. No
new arithmetic was needed for step 1.

The counting identity then combines step 1, residue 2 and ADR-1544's residue 1.
**The residue sum cancels by ASSOCIATION alone** — it sits on the right of step
1 and on the left of residue 2 — so no subtraction appears anywhere in the
chain. Coprimality enters here and only here, through the bijection, and is
load-bearing: at `m = 4`, `a = 3` (so `pp = 9`, `gcd 3 9 = 3`) the two sides
are 36 and 37.

### 4. Eisenstein's lemma

```text
Nat.eisenstein_lemma : ∀ m n, gcd (succ (2n)) (succ (2m)) = 1 →
  Nat.Even (F + N)
```

`Nat.Even x := ∃ k, x = k + k` (`parity.rs`), so this is
`N ≡ Σ⌊qk/p⌋ (mod 2)`.

**The odd parts come off definitionally.** At `a := q = succ (2n)` the
identity's two products lose their odd part with no lemma at all: `Nat.mul`
recurses on its RIGHT argument, so after one `mul_comm` the terms
`mul T (succ (2n))` and `mul X (succ (2m))` ι-reduce to `mul T (2n) + T` and
`mul X (2m) + X`. One `Nat.add_right_cancel` removes the `+ T` from each side,
leaving

```text
C + C = (B + B) + X       with  C := T·n + S,  B := X·m,  X := F + N
```

and the parity follows by taking `mod _ 2` of both sides:
`add_mul_mod_self_left` deletes `B + B` on the right and `C + C` on the left,
`zero_mod` finishes, `even_iff_mod_two_eq_zero` converts to the existential.

**Coprimality is load-bearing, and it is refuted INSIDE the kernel** rather
than only numerically: at `pp = 9`, `q = 3` the sum `F + N` reduces to `3`, and
`3` is refuted as `k + k` by exhausting every `k` that could reach it (`k ≤ 3`
directly; `k ≥ 4` gives `k + k ≥ 8 > 3`), with a positive control that the same
`def_eq` query accepts `2 = 1 + 1`. That is the strongest row-2 evidence in
this family; it is still not a kernel theorem.

### 5. The congruence form, and a name search that lies

```text
Nat.eisenstein_lemma_modEq : ∀ m n, gcd (succ (2n)) (succ (2m)) = 1 →
  Nat.modEq 2 F N
```

**`Nat.modEq` exists.** `shape_search --name-like modEq` returns 40
declarations, every one of them `Int`, because the `Nat` side spells its
theorems `mod_eq_*` in lower case while the constant they mention is
`Nat.modEq`. The obvious query therefore answers "`Int` only" and looks
conclusive. It is not: `Nat.modEq d a b := ∃ u v, a + d·u = b + d·v`
(`modular.rs`), the BALANCED form.

Because it is balanced, the congruence is a five-line corollary of `Even`
rather than a second proof: from `F + N = k + k` take `u := N`, `v := k`, and
`F + 2·N = (F + N) + N = (k + k) + N` while `N + 2·k = N + (k + k)` — one
`add_comm` apart.

### 6. Residue 5: the `min` comes off, at this shape and not in general

```text
Nat.div_mul_succ_le_of_le : ∀ m n x, Le (succ x) m →
  Le (div (mul (succ (2n)) (succ x)) (succ (2m))) n

Nat.eisenstein_floor_sum_min_free : ∀ m n, gcd (succ (2m)) (succ (2n)) = 1 →
  Σ_{x<m} ⌊q(x+1)/pp⌋ + Σ_{y<n} ⌊pp(y+1)/q⌋ = n·m
```

ADR-1544's `M4`/`M5` recorded that dropping the `min` from
`Nat.eisenstein_floor_sum` is **REFUTED** at the generality that theorem states
and **SURVIVES** only at Eisenstein's own `m = (p−1)/2`, `n = (q−1)/2`. This
turns the survivor into a theorem: at `pp = 2m+1`, `q = 2n+1` the cap never
binds.

**The arithmetic is trivial on paper and is not one line here.** The bound is
`q(x+1) ≤ q·m < pp(n+1)`, and the strict half is `2nm + m < 2mn + 2m + n + 1`,
i.e. `0 < m + n + 1`. But `mul q m` is STUCK in both directions — `Nat.mul`
recurses on its RIGHT argument, so with `m` symbolic it reduces to nothing, and
`mul pp n` likewise. One `mul_comm` on each turns them into `mul m (succ (2n))`
and `mul n (succ (2m))`, which ι-reduce, and the two leading products are then
the same number `2mn` written two different ways — a nine-step chain through
`mul_assoc`, `right_distrib` and `mul_comm` to identify. Everything after that
is `add_lt_add_left`, `succ_le_succ`, `mul_le_mul_left`, `lt_of_le_of_lt`,
`div_lt_of_lt_mul` and `le_of_lt_succ`, plus four **one-hole transports at
`Le`/`Lt` positions**, where the `Nat`-valued `NatOps::congr` does not apply.

**The restriction is refuted inside the kernel, not only in Rust.** At
`pp = 2`, `q = 5`, `m = 1`, `n = 0` — a general instance
`Nat.eisenstein_floor_sum` also reaches, since `gcd 2 5 = 1` and `1 < 2` — the
cap does bind: the bare row sum reduces to `2`, the capped one to `0`, and
`def_eq` rejects the two.

## What this does NOT prove

**Quadratic reciprocity is not proved.** Its two halves are now both proved —
`Nat.eisenstein_lemma` here and `Nat.eisenstein_floor_sum` in ADR-1544 — and
what is missing between them is the ASSEMBLY, which is `Int`-side and is not
attempted here:

1. Instantiate the two lemmas at a pair of distinct odd primes `p`, `q` with
   `m = (p−1)/2`, `n = (q−1)/2`, and combine the two parity statements with
   `eisenstein_floor_sum`'s `F_p + F_q = n·m` to get
   `N_p + N_q ≡ n·m (mod 2)`. Every input exists; nobody has run it. This is
   the cheapest remaining increment and it is `Nat`-side.
2. Turn that into a statement about Legendre symbols through
   `Int.gaussLemmaSignCount`, which is where `(−1)^N` becomes the symbol. This
   is `Int`-side and needs a `(−1)^(a+b) = (−1)^a·(−1)^b` step over
   `Int.pow_neg_one_of_even`/`_of_odd`, both of which exist.

ADR-1544's residue 5 is **closed here too** — see §6.

## Numeric verification

Re-runnable, and **this is the command, not a claim that it passed**:

```sh
python3 docs/research/09-decisions/adr-1552-eisenstein-checks.py
```

Six claims (C1–C6) and eleven controls (M1–M11). C1 checks the conditional sum
and its complement split at 180 instances; C2 sweeps 8,450 instances of the
reconciliation, of which 5,070 have a composite modulus and 3,250 are
non-coprime; C3 sweeps the same 8,450 for the summed division algorithm; C4
checks 519 coprime instances of the counting identity; C5 checks 399 coprime
odd pairs of Eisenstein's lemma and, separately, all 240 ordered pairs of
distinct odd primes below 60; C6 checks the min-free floor sum at 317 coprime
odd pairs and, separately (C6b), that the cap never binds on either axis at any
of them.

Exit status depends on the finding. That claim is itself measured: **19 of 19
mutations of the script exit 1** — the reconciliation's count shifted, the
doubling dropped, step 1's floor sum shifted, its index range shifted, the fold
threshold loosened, the fold's reflection shifted, the counting identity
shifted, Eisenstein's parity read the other way, each coprimality filter
dropped, the complement split broken, M5's and M6's named witnesses made wrong,
C5b's prime range emptied, C2b made blind to non-coprimality, M8's second
predicate made the true complement, the min-free floor sum shifted, C6b's cap
check made to fire spuriously, and M11's witness made to satisfy the cap. Each mutant is written to its own filename
in a scratch directory, so the stale-`__pycache__` trap cannot report the
previous mutant's result.

**Two mutations were deliberately NOT run and the omissions are recorded**, and
they are the same kind: a VACUITY edit of a guard that is *satisfied* in the
baseline cannot be measured, because the guard has nothing to fail on. Turning
`if FAILURES: … return 1` into `if False:` and replacing C6b's cap condition by
`if False:` are both no-ops against a passing run. The measurable form is to
make a condition WRONG rather than absent, which is what M17 does to C6b; and
the return-1 path is exercised by every one of the nineteen mutations above.

### The two recorded survivors

| control | what it is |
| --- | --- |
| **M9** | `modEq 2 F N` and `modEq 2 N F` are the same claim numerically but different kernel terms; no consumer chaining through one can use the other without a commutation step. **Invisible to every numeric check.** |
| **M10** | Same for `Even (F + N)` versus `Even (N + F)`. |

Both are guarded only by the character-for-character type pins in
`eisenstein_lemma_tests.rs`. This is the same class of blind spot ADR-1544's
M10 recorded for the strict/non-strict half-plane spelling.

## Graded family (ADR-0603)

All eleven ledger rows are **row 1**, the general constructive form — and
`F:nat-eisenstein-lemma` is strictly MORE general than the classical statement,
which is about two distinct odd primes rather than any coprime odd pair (C5b
verifies that every classical instance below 60 satisfies the hypothesis).

**Row 2 is UNASSESSED for nine of the eleven** and PARTLY ASSESSED for
`F:nat-eisenstein-lemma` and `F:nat-eisenstein-floor-sum-min-free`: the
coprimality-dropping refutation for the first, and the shape-dropping
refutation for the second, are carried out inside the kernel by `def_eq`, with
positive controls, rather than only in Rust. It is still not stated as a kernel theorem, and no claim is made that one
is impossible. Rows 3 and 4 are absent throughout.

## Checks run

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **395 passed, 0 failed**
- `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1552-eisenstein-checks.py` — PASS; 19 of 19 self-mutations exit 1
- `python3 scripts/validate-facts.py` — **2617 facts, 0 errors**
- `python3 scripts/check-settled-fact-statements.py --write` — 2384 pins, unpinned 0
- twelve kernel declarations, **all twelve admitted on the FIRST attempt**, all
  twelve with an empty `Kernel::axiom_footprint`
