# ADR-1557: Quadratic reciprocity is proved, and the Legendre symbol is defined by Gauss's count

Status: accepted
Date: 2026-09-02
Index-summary: **The law of quadratic reciprocity is now a kernel theorem**
(`Int.quadraticReciprocity : ∀ m n, gcd (2n+1) (2m+1) = 1 →
legendreSym m (2n+1) · legendreSym n (2m+1) = (−1)^(n·m)`), axiom-free, together
with the `Nat`-side parity step (`Nat.gaussCount_sum_even` /
`_modEq`) and the Legendre symbol it is stated over. Five declarations, every
one admitted on the FIRST kernel attempt. ADR-1552's two named steps were both
correct and both cheap; the whole assembly is one `Nat.gcd_comm`, two
`regroup_four` moves, and five `Int` ring lemmas. **Two decisions worth
knowing.** First, `Int.legendreSym` is DEFINED by Gauss's counting exponent,
not by the residue indicator, because the converse of Euler's criterion has no
statable form in this kernel; the name is justified by
`Int.legendreSym_modEq_pow`, and `legendreSym = 1 ↔ is_quadratic_residue` is NOT
proved in either direction. Second, the proof multiplies by the self-inverse
`(−1)^(n·m)` instead of splitting on parity, which avoids two `Even`-transfer
lemmas this prelude does not have. The statement assumes **only coprimality,
never primality** — strictly stronger than the textbook law. The brief this
lane worked from predicted the wrong SIGN at two of its five pairs.
Index-status: accepted

## Context

ADR-1552 landed Eisenstein's lemma and closed everything ADR-1540 and ADR-1544
had left open, then named exactly two remaining steps toward quadratic
reciprocity and said of the first that "every input exists and nobody has run
it". That framing was right. This ADR records running them.

The prior chain, for orientation: ADR-1260 routed Eisenstein's lattice count
around ADR-1135's missing-aggregate wall; ADR-1290 closed the floor-counting
family; ADR-1540 closed the side condition and built `Nat.sumRange_permute`;
ADR-1544 landed `Nat.eisenstein_floor_sum` and the additive Gauss bijection;
ADR-1552 landed `Nat.sumRangeIf`, `Nat.eisenstein_lemma` and the min-free floor
sum. Gauss's lemma itself (`Int.gaussLemmaSignCount`) has been landed since
ADR-1130/1070.

## Step 0 — prerequisite verification (this lane, in-tree, not inherited)

`examples/shape_search`, rebuilt on this branch (`declarations=2133` before this
lane's own declarations, so not a stale binary reporting a false ABSENT).

| named input | verdict |
| --- | --- |
| `Nat.eisenstein_lemma`, `Nat.eisenstein_lemma_modEq` | FOUND |
| `Nat.eisenstein_floor_sum_min_free` | FOUND |
| `Int.gaussLemmaSignCount` | FOUND |
| `Int.pow_neg_one_of_even` / `_of_odd` | FOUND |
| `Int.is_quadratic_residue` (+ 3 lemmas) | FOUND |
| `Int.firstSupplementaryLawResidue` | FOUND (the shape template) |
| `Int.pow_add`, `Int.mul_assoc`, `Int.mul_one`, `Int.one_mul`, `Nat.gcd_comm` | FOUND |
| **any Legendre symbol** (`--name-like legendre`) | **ABSENT**, against `positive control: any-kind=2133` |
| `--name-like quadraticReciprocity` / `reciprocity` | **ABSENT**, same control |

So ADR-1552's "every input exists" was correct for step 1, and the one thing it
did not mention — that there is no Legendre symbol here at all — is what made
step 2 a design decision rather than an assembly.

## Decision 1 — the two `Nat` inputs mesh, and the pairing is legitimate

`Nat.gaussCount_sum_even : ∀ m n, gcd (2n+1) (2m+1) = 1 →
Even ((N_p + N_q) + n·m)`, with `N_p := gaussNegCount pp q m`,
`N_q := gaussNegCount q pp n`.

The content is not arithmetic; it is that ADR-1552's two halves line up index
function for index function.

- `Nat.eisenstein_lemma` at `(m, n)` gives `Even (F_p + N_p)`.
- `Nat.eisenstein_lemma` at `(n, m)` gives `Even (F_q + N_q)` — **at `(n, m)`
  its own modulus is `succ (2n) = q` and its own multiplier is `succ (2m) = pp`,
  so its floor sum is literally `F_q` and its count is literally `N_q`.** The
  two instances share no term but the hypothesis.
- `Nat.eisenstein_floor_sum_min_free m n` gives `F_p + F_q = n·m`, spelled with
  the same `shifted` index functions, so no congruence is needed to align them.

The arithmetic is then two `regroup_four` moves:

```text
  (N_p + N_q) + n·m
= (N_p + N_q) + (F_p + F_q)      [the floor sum, backwards]
= (F_p + F_q) + (N_p + N_q)      [add_comm]
= (F_p + N_p) + (F_q + N_q)      [regroup_four]
= (k₁ + k₁) + (k₂ + k₂)          [the two Even witnesses]
= (k₁ + k₂) + (k₁ + k₂)          [regroup_four]
```

One `Nat.gcd_comm` bridges the two hypothesis orders (`eisenstein_lemma` takes
`gcd q pp = 1`; the other two take `gcd pp q = 1`) and is the only bridging
step in the file. No subtraction appears anywhere, so `Nat.sub`'s truncation
never enters.

`Nat.gaussCount_sum_modEq` is the same two-line corollary
`Nat.eisenstein_lemma_modEq` is: `Nat.modEq d a b := ∃ u v, a + d·u = b + d·v`
is the BALANCED form, so the witnesses are `u := n·m` and `v := k`.

`two_mul` and `regroup_four` are **exported** from `eisenstein_lemma.rs`
(`pub(super)`) rather than copied a third time.

## Decision 2 — the Legendre symbol is defined by Gauss's count

There is no Legendre symbol in this kernel, and the classical definition — the
residue indicator — cannot be connected to anything computable here.
`qr_criterion.rs`'s module doc records why: the CONVERSE of Euler's criterion
(`a^((p−1)/2) ≡ 1 ⟹ a is a residue`) needs a primitive root or a root-counting
argument, and this kernel has no `List`/`Finset`/polynomial machinery to state
either. A residue-indicator `legendreSym` would be a definition nothing could
evaluate and no theorem could reach.

So:

```text
Int.legendreSym m a := pow (neg one) (Nat.gaussNegCount (succ (mul 2 m)) a m)
```

with `Int.legendreSym_modEq_pow` as the justification: for an odd prime
`pp = 2m+1` and `a` coprime to it, `a^m ≡ legendreSym m a (mod pp)`. That is
Euler's criterion for this symbol, and since a nonzero residue class mod an odd
prime contains at most one of `1` and `−1`, it pins the symbol uniquely. The
theorem is `Int.gaussLemmaSignCount` read through the definition; the two
conclusions differ only by delta, so its proof is the application itself.

**What is deliberately NOT claimed.**
`legendreSym m a = 1 ↔ Int.is_quadratic_residue (ofNat pp) (ofNat a)` is not a
theorem here, in either direction. The `⟸` direction is reachable
(`Int.euler_criterion_residue_imp_one` plus `1 ≢ −1` at `pp > 2`) and is not
built; the `⟹` direction is the missing converse and is not reachable. The two
supplementary laws — which DO speak about `is_quadratic_residue` — are
unaffected and unchanged.

## Decision 3 — multiply by the self-inverse instead of splitting on parity

Writing `A := (−1)^N_p`, `B := (−1)^N_q`, `C := (−1)^(n·m)`, `S := N_p + N_q`,
`T := n·m`:

```text
  (A·B)·C = (−1)^S · (−1)^T = (−1)^(S+T) = 1     [pow_add; pow_neg_one_of_even at Even (S+T)]
  C·C     = (−1)^(T+T)      = 1                  [same, witness k := T]
  A·B     = (A·B)·1 = (A·B)·(C·C) = ((A·B)·C)·C = 1·C = C
```

The obvious route is to case on `Even S` / `Odd S` and transfer the parity to
`T`. That needs `Even (a+b) → Even a → Even b` and its odd twin, **neither of
which exists in this prelude**, so it would have been two extra declarations.
Multiplying by `C`, which is its own inverse for exactly the same reason the
law is about signs at all, needs only `Int.pow_add`, `Int.mul_assoc`,
`Int.mul_one`, `Int.one_mul` and `Int.pow_neg_one_of_even` — all landed. The
generalisable form: **when a statement lives in a two-element group, cancel
rather than case-split.**

## Decision 4 — only coprimality is assumed

Both `Nat` inputs ask only for `gcd q pp = 1`, so the law does too. It is
therefore strictly stronger than the textbook statement about two distinct odd
primes, in the same way ADR-1544 recorded for `Nat.eisenstein_floor_sum`.
Primality appears exactly once in this family, in
`Int.legendreSym_modEq_pow`, because Gauss's lemma needs it to cancel `m!`.

## What this lane measured that a document did not tell it

**The brief's expected signs were wrong at two of its five pairs.** It asked for
`(3,5) → −1` and `(5,7) → −1`; both are `+1`. The Legendre product is `−1`
exactly when BOTH primes are `3 mod 4`, and `5 ≡ 1 (mod 4)`. Only `(3,7)` in
that list is the `−1` case, which is why `(7,11)` was added — so the negative
sign is not carried by one row. Computed in Python before any kernel term was
built, and re-derived independently in Rust inside the test files.

## The mutation table

Eight kernel mutants, each applied to one source line, rebuilt, run against the
13 tests of the two reciprocity test modules, and restored. The runner refuses
to classify a mutant whose anchor is not unique, and its own exit status
depends on the finding.

| # | mutation | verdict |
| --- | --- | --- |
| M1 | `gaussCount_sum_even`: transpose the first count's modulus and multiplier | REJECTED by the trusted gate |
| M2 | `gaussCount_sum_even`: state the product as `m*n` rather than `n*m` | REJECTED |
| M3 | `gaussCount_sum_even`: use the SAME Eisenstein instance twice | REJECTED |
| M4 | `quadraticReciprocity`: second symbol at the wrong modulus | REJECTED |
| M5 | `legendreSym`: base `1` instead of `−1` | REJECTED |
| M6 | `legendreSym`: transpose the modulus and the multiplier | REJECTED |
| M7 | `gaussCount_sum_modEq`: the two `Nat` binders in the opposite order | **ADMITTED**, caught ONLY by the type pin |
| M8 | `quadraticReciprocity`: the two `Nat` binders in the opposite order | **ADMITTED**, caught ONLY by the type pin |

**M5 and M6 are the interesting rejections, and they are not what the standing
rule predicts.** `CLAUDE.md` says the trusted gate cannot tell you a
`Definition` is wrong — and that is still true in general — but here the
definition is **pinned from above**: `Int.quadraticReciprocity`'s proof is built
on the unfolded body, so changing the body makes the LAW fail to type-check.
The failure arrives as `DeclarationValueMismatch`, and this lane read the actual
message rather than trusting the runner's classifier. The evaluation tests are
therefore NOT the thing that catches M5/M6; they would be, if the law above the
definition were removed, and they remain the only guard against a definition
with no theorem over it.

**M7 and M8 are ADR-1260's admitted-and-survived shape — and here they do not
survive.** A binder swap produces a true, admitted theorem that is not the
theorem meant, and no numeric check can see it (the statement is symmetric
under renaming). Both are caught by the character-for-character type pins, and
by nothing else in the suite. That is what makes those pins load-bearing rather
than decorative.

## Numeric checks

`adr-1557-quadratic-reciprocity-checks.py`: 6 claims, 8 controls, **3 recorded
survivors**, all recomputed from the kernel definitions rather than from any
prior document or from the Rust tests. Exit status depends on the finding.
**18 of 18 self-mutations exit 1**, each written to a uniquely named file so
the stale-`__pycache__` trap cannot report the previous mutant's result.

Coverage: 422 coprime `(m, n)` pairs below 24 for the `Nat` statements, 240
ordered pairs of distinct odd primes below 60 for the law, and 1,266
`(odd prime, coprime multiplier)` instances for Euler's criterion.

The three survivors, and why they are recorded rather than fixed:

- **K2** — `pp = q = 5` is equally non-coprime and BOTH statements are still
  true there, so a non-coprime control drawn at that pair passes while checking
  nothing. The refuting witness is `pp = q = 3`. Derive the witness from the
  statement, never from a neighbouring file.
- **K4** — `n·m` against `m·n`: equal as numbers, different as kernel terms
  (`Nat.mul` recurses on its right argument, so they are not definitionally
  equal at symbolic arguments). The kernel rejects the transposed statement
  (M2), and the type pins record which one is declared.
- **K5** — `N_p + N_q` against `N_q + N_p`: the same number at every instance.
  Visible only in the type pins.

## Consequences

- **Quadratic reciprocity is proved, axiom-free, over this kernel's own
  constructed integers.** `Kernel::axiom_footprint` is empty for all five
  declarations, and `nat_axiom_inventory --require-axiom-free nat` and
  `-- integer` both exit 0 (with `axreal` at 30 as the control that the flag
  can fail).
- **The two supplementary laws were already proved** —
  `Int.firstSupplementaryLawResidue` / `...NotResidue` (ADR-1230/1235) and
  `Int.secondSupplementaryLaw` (ADR-1150) — so the classical package is now
  complete except for its `is_quadratic_residue` bridge.

## What is still open, sized

1. **The bridge to `is_quadratic_residue`.** `legendreSym m a = 1 ⟸ a is a
   residue` is reachable from `Int.euler_criterion_residue_imp_one` plus
   `1 ≢ −1` at `pp > 2`; the forward direction is the missing converse of
   Euler's criterion and is NOT reachable without a primitive root or a
   root-counting argument. Whoever takes the reachable half should state it as
   an implication, not a biconditional.
2. **The Jacobi symbol.** No declaration exists (not measured absent by this
   lane beyond `--name-like legendre`, so check before building). Its
   reciprocity law is the natural next statement, and it needs a product over
   a factorization — which `nat_prelude/factorization.rs` supplies
   existentially but not canonically, so the ADR-1552-era caution about
   evaluating versus inducting applies.
3. **Row 4 of the graded family (ADR-0603): the labeled Mathlib import**
   (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`) is A SEPARATE
   LANE and is not attempted here. Nothing in this lane's four ledger rows is
   an import; all four are row 1, the general constructive form.
4. **Row 2 (boundary refutation) is stated numerically and inside the kernel,
   not as a theorem.** The non-coprime refutation at `pp = q = 3` is asserted
   as a `def_eq` control in both test files and swept in the check script; no
   claim is made that a kernel-level refutation is impossible.

## What a next lane inherits

- **`Int.legendreSym` is now the symbol every quadratic-residue statement
  should be written over**, and its meaning is Gauss's count. Anything that
  wants the residue-indicator reading must first build the bridge in item 1.
- **A definition under a theorem is pinned by that theorem.** The M5/M6 rows
  are a counter-example to reading "the trusted gate cannot tell you a
  definition is wrong" as unconditional. The rule survives — it is about a
  definition with nothing proved over it — but a lane citing it should check
  whether anything above the definition consumes its body.
- **`Nat.gcd_comm` has no fact row**, so `depends_on` in this lane's ledger
  rows is an intersection that omits it. That is the documented behaviour of
  `check-fact-depends-derived.py`, not a gap in this lane's curation.
