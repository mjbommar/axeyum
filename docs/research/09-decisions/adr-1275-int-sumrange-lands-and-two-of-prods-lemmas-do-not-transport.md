# ADR-1275: `Int.sumRange` lands, and two of `prodRange`'s properties do not transport

Date: 2026-08-31
Status: Accepted
Lane: `int-sumrange`

Index-summary: The signed finite sum ADR-1260 named as Eisenstein's only obstruction now exists, with eight lemmas, all admitted first attempt and all axiom-free. `Int.modEq_sumRange` is UNCONDITIONAL in the modulus where `Int.modEq_prodRange` needs `0 < n`, and `Int.sumRange_sub` needs no induction at all -- two places where transporting the product's shape would have been wrong rather than merely slower. Nine ledger rows; five mutants, one of them admitted-true-and-not-the-theorem, and one that failed to do what it was designed to do.
Index-status: Accepted

## Context

[ADR-1260](adr-1260-eisenstein-routes-around-the-missing-aggregate-wall.md)
landed the lattice-point partition and named exactly one obstruction between it
and Eisenstein's lemma: **`Int.sumRange` does not exist.** The classical
derivation is `(a−1)·Σk = p·(F + N) − 2·Σ_neg`, which subtracts inside a finite
sum, and the `Int` prelude folded **products only** — Wilson's theorem and
Euler's totient theorem both multiply, so nobody had ever needed a signed sum.

That premise was re-verified here rather than inherited, from
`kernel_declaration_projection` with a working positive control:

| name | rows before this ADR |
| --- | --- |
| `Int.sumRange` | **0** |
| `Nat.sumRange` | 98 |
| `Rat.sumRange` | 88 |
| `Int.prodRange` | 132 |

A missing construction over an existing carrier, not a missing carrier.

## Decision

Build `Int.sumRange` in a new `int_prelude/sum.rs`, modelled on `prod.rs`, with
the same conventions `Nat.sumRange` and `Int.prodRange` already share:
exclusive bound, identity of the operation at the base, fresh term accumulated
on the **right**.

Ten declarations, **all admitted by the trusted gate on the first attempt**, all
`axiom_footprint` 0:

| declaration | what it is for |
| --- | --- |
| `Int.sumRange` | the construction (`Nat.rec`, constant `fun _ => Int` motive) |
| `Int.sumRange_zero` / `Int.sumRange_succ` | defining equations, both `Eq.refl` |
| `Int.sumRange_congr` | pointwise congruence |
| `Int.sumRange_add` | additivity in the summand |
| `Int.sumRange_neg` | negation pulls out |
| `Int.sumRange_sub` | **subtraction inside the sum** — the deciding lemma |
| `Int.sumRange_ofNat` | the ℕ→ℤ bridge a lattice-point count needs |
| `Int.modEq_sumRange` | the mod-2 reader |
| `Int.neg_add` | a basic ring lemma the prelude had proved and never stated |

ADR-1260 sized this as "`Int.sumRange` + ~6 defining lemmas". **The sizing held**
— eight lemmas rather than six, and the two extras (`sumRange_ofNat`,
`Int.neg_add`) are both cheap and both forced by the consumer rather than by the
construction.

## Three things that did NOT transport from `prod.rs`

The brief warned against blind transport, citing the `land`→`lor` case where the
unconditional statement is false. Nothing here is *false*, but three properties
differ, and two of them would have produced a weaker theorem had the product's
shape been copied.

1. **`modEq_sumRange` carries NO `0 < n` hypothesis; `modEq_prodRange` does.**
   Not a shortcut: the product's step goes through `Int.ModEq.mul`, whose
   statement in this prelude is positivity-scoped, while the sum's step goes
   through `Int.ModEq.add_right` and `Int.ModEq.add_left`, both of which this
   prelude proves **unconditionally in the modulus** (their own doc comments say
   so, and Mathlib's statements carry no positivity either). Transporting the
   hypothesis would have forced every consumer of the mod-2 reader Eisenstein
   wants to discharge `0 < 2`.

   The test asserts this in **both** directions — `modEq_prodRange` must contain
   `Int.lt Int.zero`, `modEq_sumRange` must not — so the absence is a measured
   difference between the two aggregates rather than an artefact of how the check
   reads types.

2. **The base cases compute, so `prodRange_mul`'s explicit `Int.mul_one` has no
   analogue.** `Int.mul` reduces on neither operand when both are symbolic. Here
   both operands of the base are the literal `Int.zero ≡ Int.ofNat 0`, so
   `Int.add zero zero` δι-reduces to `zero`.

3. **`sumRange_sub` needs no induction at all.** `Int.sub a b := add a (neg b)`
   is a plain non-recursive `Definition`, so the stated left-hand side is
   definitionally `sumRange_add` instantiated at `g := fun j => neg (g j)`, and
   one congruence through `sumRange_neg` finishes it. `prodRange` has no
   analogue because ℤ has no multiplicative inverse to fold.

`add_swap_inner` — the four-summand regroup `sumRange_add`'s step needs — IS a
direct transcription of `prod.rs`'s `mul_swap_inner`, and that transport is safe
for a checkable reason: **no identity element appears anywhere in the chain**, so
nothing about `one` versus `zero` can enter. `Int.add_assoc`/`Int.add_comm` have
exactly the shapes `Int.mul_assoc`/`Int.mul_comm` do, verified by reading their
registry doc comments before writing the function.

## Something that already existed

`Int.neg_add`'s proof term was **already in the tree**, as a private `fn neg_add`
inside `int_prelude/modeq.rs`, built inline for `declare_modeq_add_right`'s
cancellation step, with one caller. Hiding place 2 in the retrieval taxonomy: no
declaration, so no name index and no `check-shape-duplicates.py` group could ever
have found it. `sumRange_neg`'s successor step is exactly that equation read
backwards.

It was found by grepping for the SHAPE (`neg (add`) rather than the name, which
is the technique the retrieval section prescribes. The helper is now
`pub(super)` and reused; re-deriving it beside the original would have left two
proofs of one fact to keep in sync.

Nothing else in this family was nearly rebuilt.

## The mutation table

Three outcomes: **declaration rejected / statement false / admitted, true, and
not your theorem.** Each mutant was applied in this lane's own worktree and
reverted with `git checkout` immediately after; none was ever on disk in the
shared checkout.

| # | mutation | outcome | what caught it |
| --- | --- | --- | --- |
| M1 | `declare_sum_range`'s step folds the fresh term LEFT (`iadd(fj, ih)`), definition only | **REJECTED** | trusted gate — `sumRange_succ`'s `Eq.refl` no longer matches; prelude fails to build, 66 of 67 tests fail |
| M2 | `sumRange_sub`'s RHS stated **unfolded** as `add Sf (neg Sg)` instead of `sub Sf Sg` | **ADMITTED, TRUE, NOT THE THEOREM** | `the_sum_range_family_states_the_intended_types` ONLY — 66 passed, 1 failed. Defeq, so the kernel accepts it and the evaluation probe passes |
| M3 | `sumRange_sub`'s RHS transposed to `sub Sg Sf` | **REJECTED** (statement also false) | trusted gate, 66 of 67 fail |
| M4 | `modEq_sumRange`'s `mod_eq_add_right` given `(n, Sg, Sf, …)` — the two sums swapped | **REJECTED** | trusted gate, 66 of 67 fail |
| M5 | base case `Int.one` in BOTH the definition and `sumRange_zero`, kept consistent | **REJECTED** — `TypeMismatch { expected: ExprId(1250890), got: ExprId(1056670) }` | trusted gate, via `sumRange_congr`'s `Eq.refl zero` base, **not** by either probe |

**M2 is the case the whole exercise exists for.** The kernel admits it, the
statement is true, the evaluation probe passes — and it is not the theorem,
because the ledger row and every downstream reader would see
`Int.add … (Int.neg …)` where the family's other members read `Int.sub`. Only
reading the declared type catches it. This is ADR-1260's M4 shape arriving in a
different family.

**M5 is the mutant that did not do what it was designed to do, and it is
reported because it did not.** It was designed to be the evaluation probe's
unique kill: a wrong base case changes `sumRange (fun j => j−2) 4` from −2 to −1,
which the numeric assertion would see. It never gets that far — `sumRange_congr`'s
base is `Eq.refl Int.zero`, so a base of `Int.one` breaks a *downstream
declaration* and the prelude does not build.

That generalises to an honest limit on this family's controls:

> **The two `Eq.refl` defining equations plus `sumRange_congr` pin the
> construction so tightly that every definition-only mutation is caught by the
> trusted gate first. The evaluation probe therefore has NO unique kill here.**

It is kept anyway, for two reasons that are not "coverage": it is the only thing
that pins the **exclusive** bound numerically (asserted in both directions —
`sumRange f 4 = −2` and `≠ 0`, with `sumRange f 5 = 0` one term further), and the
standing rule is that a `Definition` admitted by the gate is *well-formed*, never
*correct*. A future lemma added to this file could weaken the equations; the
probe is what would then start earning its place.

## What the controls do NOT catch

- **Operand order in the fold.** `Int.add` is commutative, so a definition
  folding the fresh term onto the LEFT computes the identical value at every
  argument **and satisfies every other lemma in this family** — `congr`, `add`,
  `neg`, `sub`, `ofNat` and `modEq_sumRange` are all true of a left fold. Only
  `sumRange_succ`'s stated type distinguishes them. A fully consistent left-fold
  mutant (definition + succ equation + all six proof chains repaired) would be
  admitted and true, and is exactly the shape M2 demonstrates more cheaply.
- **Hiding place 2, structurally.** `Int.neg_add`'s proof was invisible to every
  gate in this repository for as long as it was inline, and nothing added here
  changes that for the next such helper.

## Consequences

- **Eisenstein's lemma is unblocked on the aggregate axis.** The remaining work
  is the three residues ADR-1260 already named, unchanged by this ADR:
  1. **The floor-counting family** — `countRange (fun y => ble (succ y) c) n =
     min n c` plus `Le (succ y) (div B p) ↔ Le (mul p (succ y)) B`. This is the
     one that fights `Nat.div`/`Nat.mod` being stuck at symbolic arguments, and
     it is the largest of the three.
  2. **The side condition** — `p·y ≠ q·x` for `1 ≤ x ≤ m`, `1 ≤ y ≤ n`, `p ≠ q`
     prime, i.e. Euclid's lemma, which this kernel has.
  3. **Step 1's mod-2 bookkeeping** — which is what `Int.modEq_sumRange`,
     `Int.sumRange_sub` and `Int.sumRange_ofNat` were built for. `sumRange_ofNat`
     is the specific piece that lets `Nat.countRectangle_partition`'s counts
     enter the signed identity at all.
- `Int.sumRange_add`, `sumRange_congr`, `sumRange_neg` and `Int.neg_add` are
  general and have no connection to reciprocity; anything folding a signed
  family over `Int` can use them.
- **A consumer still needs, and this family does NOT provide:** `sumRange_split`
  (cut at an offset), `sumRange_shiftFront`, `sumRange_const`, `sumRange_swap`
  (Fubini over ℤ), and any scaling lemma `Σ(c·f k) = c·Σf`. All five have
  `prodRange` analogues that would transport by the same route; none was needed
  to unblock the aggregate, so none was built. `sumRange_swap` over ℤ is the one
  most likely to be wanted next, and `Nat.sumRange_swap` (ADR-1260) plus
  `sumRange_ofNat` covers the non-negative case already.
- **A correction to the brief's premise list:** none of the kernel facts it
  named turned out to be wrong. `Int.mul (ofNat a) (ofNat b) ≡ ofNat (mul a b)`
  and the `Int.add` analogue are both free at symbolic arguments, which is what
  makes `sumRange_ofNat` a one-congruence induction, and `Int.zero` is indeed
  defined as `ofNat 0`. `Int.neg Int.zero` reduces the same way
  (`negOfNat 0 ≡ ofNat 0`), which is why `sumRange_neg`'s base is `Eq.refl` and
  no `Int.neg_zero` lemma exists or is needed.

## Verification

```sh
cargo test -p axeyum-lean-kernel --lib int_prelude::
# -> 67 passed; 0 failed  (65 before this lane)
python3 scripts/validate-facts.py                    # 2511 facts, 0 errors
python3 scripts/check-settled-fact-statements.py     # PASS, 0 unpinned
```

Nine ledger rows registered (`F:int-sumrange-{zero,succ,congr,add,neg,sub,ofnat}`,
`F:int-modeq-sumrange`, `F:int-neg-add`), all `axiom_footprint` 0, all with a
`checker_command` verified to discriminate in both directions:
`Int.sumRange_sub` prints 1 and exits 0, `Int.sumRange_zub` prints 0 and exits 1.
