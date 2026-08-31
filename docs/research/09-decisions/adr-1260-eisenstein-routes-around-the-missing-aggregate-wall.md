# ADR-1260: Eisenstein routes AROUND the missing-aggregate wall, and the rectangle partition lands

Status: accepted
Date: 2026-08-31
Index-summary: **Quadratic reciprocity is NOT proved here.** What is settled is
the question the lane was opened on, and it is settled in the direction that
keeps the target reachable: Eisenstein's lattice-point count does **not** hit
the wall ADR-1135 named for the determinant's multiplicativity. The rectangle
never has to exist as a set — a finite family here is a function plus a bound,
and the argument is a double `sumRange` with a `countRange` inside. Five
declarations land, all admitted on the FIRST kernel attempt, all axiom-free:
`Nat.sumRange_const`, `Nat.countRange_eq_sumRange`, **`Nat.sumRange_swap`**
(Fubini over ℕ — `Rat.sumRange_swap` has existed since the Laplace work, ℕ did
not have it), **`Nat.countRectangle_partition`** (the headline), and
`Nat.countRectangle_partition_compl` (which exists to prove the headline's
hypothesis is satisfiable). The remaining obstruction is named precisely and it
is NOT an aggregate problem: **`Int.sumRange` does not exist**, and Eisenstein's
lemma — `gaussNegCount p a m ≡ Σ_{k=1}^{m} ⌊ak/p⌋ (mod 2)` — is a signed-sum
argument. `Int` has `prodRange` and no `sumRange` at all.
Index-status: accepted

## Context

Five lanes have now built toward quadratic reciprocity. ADR-1130 landed
`Int.gaussLemmaSignCount`, the engine. ADR-1150 landed the second supplementary
law; ADR-1230 and ADR-1235 landed both halves of the first. This lane was asked
to size — and if reachable close — the law itself, and was told explicitly that
the honest deliverable might be a precise obstruction rather than a theorem.

The classical route from Gauss's lemma is Eisenstein's lattice-point count, in
two steps:

1. **Eisenstein's lemma.** For odd `a` coprime to the odd prime `p`, with
   `m = (p−1)/2`:  `gaussNegCount p a m ≡ Σ_{k=1}^{m} ⌊ak/p⌋ (mod 2)`.
2. **The lattice identity.** For distinct odd primes `p, q` with
   `m = (p−1)/2`, `n = (q−1)/2`:
   `Σ_{x=1}^{m} ⌊qx/p⌋ + Σ_{y=1}^{n} ⌊py/q⌋ = m·n`.

Step 2 is the one that classically partitions a SET of lattice points, and the
brief asked whether it hits ADR-1135's wall (no `Finset`, no `List`, no `Prod`;
Leibniz over permutations and Cauchy–Binet over functions `[0,n) → [0,n)` all
blocked on the same absence).

## Decision

**It does not hit that wall, and the step that decides it is now a theorem.**

Restate step 2 with no floors, no division and no primality:

```text
Nat.countRectangle_partition : ∀ Q R m n,
  (∀ x y, Lt x m → Lt y n →
     add (bool_select_nat (Q x y) 1 0) (bool_select_nat (R x y) 1 0) = 1) →
  add (sumRange (fun x => countRange (fun y => Q x y) n) m)
      (sumRange (fun y => countRange (fun x => R x y) m) n)
    = mul n m
```

Every object in that statement is a function plus a bound. `Q` and `R` are the
two half-planes; the first summand counts the rectangle row by row under `Q`,
the second counts it column by column under `R`. Nothing enumerates a set of
pairs, and no aggregate type is needed.

**Why the hypothesis is a pair of predicates rather than `setCompl Q`.**
`Nat.countRange_compl` already gives `countRange p n + countRange (setCompl p) n
= n`, so the `setCompl` form needs no hypothesis at all — and is unusable by the
consumer this exists for. Eisenstein's two predicates are `p·(y+1) < q·(x+1)`
and `q·(x+1) < p·(y+1)`: two STRICT inequalities, complementary only because no
lattice point sits on the line `p·y = q·x`, which holds only for
`1 ≤ x ≤ (p−1)/2`, `1 ≤ y ≤ (q−1)/2` and distinct primes. Demanding
`R = setCompl Q` would ask the consumer for a `Bool` equation it cannot have
unconditionally. So complementarity arrives as a BOUNDED hypothesis on the
selectors — one `Bool` case split per point for the consumer — and the
primality-dependent side condition stays where it belongs.

### What was missing, and it was one thing

`Nat.countRange` (`totient.rs`) and `Nat.sumRange` (`defs.rs`) are the SAME
`Nat.rec`: motive `fun _ => Nat`, base `zero`, step `fun j ih => add ih (g j)`,
differing only in what `g` is. So `Nat.countRange_eq_sumRange` is `Eq.refl` and
the counting and summing worlds were never actually separate.

The genuinely absent piece was **Fubini over ℕ**. Checked against the Nat
prelude's own name registry (900 registered names): no `sumRange_swap`, no
`sumRange_const`, no `countRange_eq_sumRange`, with `sumRange*` returning 11
names as a positive control. `Rat.sumRange_swap` exists — it is the whole
reindexing of the Laplace double cofactor expansion — and ℕ did not have it.

## What this does NOT prove, stated as precisely as ADR-1135 stated its wall

**Quadratic reciprocity is not proved. Neither step 1 nor step 2 is proved.**
What is proved is the counting skeleton step 2 is built on.

Three named residues, in the order a next lane should attack them:

1. **The row count is a floor.** `#{y < n : p·(y+1) < q·(x+1)} = ⌊q·(x+1)/p⌋`,
   given `⌊q·(x+1)/p⌋ ≤ n`. This is `countRange (fun y => ble (succ y) c) n =
   min n c` plus `Le (succ y) (div B p) ↔ Le (mul p (succ y)) B`. It fights the
   standing warning that `Nat.div`/`Nat.mod` are stuck at symbolic arguments,
   and the brief predicted a floor-sum argument would — correctly. **But the
   partition itself needs none of it**, which is why it landed today: the
   rectangle argument can be phrased entirely in counts, and division is needed
   only to *name* those counts as floors.
2. **The side condition.** `p·y ≠ q·x` for `1 ≤ x ≤ m`, `1 ≤ y ≤ n`, `p ≠ q`
   prime — what makes the two strict predicates complementary, and the only
   place primality enters step 2. Verified at 504 prime pairs (C5b below);
   the proof is `p ∣ q·x` with `p ∤ q` and `x < p`, i.e. Euclid's lemma, which
   this kernel has.
3. **Eisenstein's lemma — and this is the real obstruction.** The classical
   derivation is
   `(a−1)·Σk = p·(F + N) − 2·Σ_{neg} fold`, read mod 2. It needs SUBTRACTION
   inside a finite sum, so it wants `Int.sumRange`. **`Int` has `prodRange` and
   no `sumRange` at all** — checked by grepping the Int prelude's `pub` name
   fields, zero hits. That is a real gap, and it is a *different* gap from
   ADR-1135's: it is a missing construction over an existing carrier, not a
   missing carrier. `Nat.sumRange` exists, `Rat.sumRange` exists,
   `CReal.sumRange` exists. Nothing structural stops `Int.sumRange`; it has
   simply never been needed, because `Int`'s two big theorems (Wilson, Euler)
   both fold products.

So the honest sizing for the law is: **one new construction (`Int.sumRange`) and
its ~6 defining lemmas, one floor-counting lemma family, Euclid's lemma applied
to the side condition, and then step 1's mod-2 bookkeeping.** None of it is
blocked. It is several lanes of ordinary work, and the thing that could have
made it impossible — needing the lattice points as an object — does not.

## Numeric verification

Re-runnable, and **this is the command, not a claim that it passed**:

```sh
python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py
```

Eight claims (C1–C8) and ten controls (M1–M10). C1–C5 are the rectangle
partition, over 256 (family, bound) pairs, 256 (predicate, bound) pairs and 504
prime pairs; C6–C8 are Eisenstein's lemma and the assembled law, verified here
precisely so this ADR's statement of what REMAINS is measured rather than
asserted. Exit status depends on the finding: any surviving mutation exits 1.

**Two of the controls are recorded as SURVIVING, deliberately, and one of them
was the first draft's control.**

- **M3b** — on the SQUARE `m = n`, transposing the predicate (`Q y x` for
  `Q x y`) *and* the summation order together is the identity map on the set
  being counted, so the total is unchanged. The first draft used this as a
  control and it passed while checking nothing. It is kept, and reported as
  surviving, because that is the vacuous shape this repository warns about
  everywhere. What separates "swap the summation order" (Fubini, true) from
  "transpose the predicate" is not the TOTAL but which of the two sums is then
  identifiable with `(q|p)` — and no numeric total can see that.
- **M4** — `sumRange_const` with the multiplication transposed survives
  numerically, as it must: `Nat.mul` is commutative. The orientation `mul c n`
  is a *kernel defeq* constraint (`Nat.mul` recurses on its RIGHT argument, so
  `mul c (succ j) ≡ add (mul c j) c` is exactly `sumRange (fun _ => c) (succ j)`'s
  reduct), so this script structurally cannot pin it and the Rust proof must.

Also worth recording: the smallest Eisenstein instance, `(p,q) = (5,7)`, is a
**bad** test instance — its row count and complement column count are both `3`,
so dropping the complement still totals `6 = m·n` and the obvious negative
control is vacuous. The tests use `(5,13)`: `7 + 5 = 12` against `7 + 7 = 14`.

## Mutation table

<!-- MUTATION-TABLE -->

## Verification

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **313 passed, 0
  failed**, including `every_nat_declaration_is_checked_and_axiom_free`, which
  reads `kernel.environment()` rather than a literal list and so covers the five
  new declarations rather than merely listing them.
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **65 passed, 0
  failed** (the downstream prelude builds on this one).
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings` — clean.
- `rustfmt --edition 2024 --check` on all four touched files — clean.

## What the controls do NOT catch

Stated plainly, because every QR lane has been asked to and the list is the
useful part.

1. **Nothing constructs a `PrimeCond` proof, and nothing needs to** — this
   module has no primality hypothesis. That is a strength here rather than the
   usual caveat. But it means the tests say nothing about whether the
   *consumer's* side condition (`p·y ≠ q·x`) is dischargeable; that evidence is
   still outside the kernel.
2. **The argument ORDER of the corollary's two `Nat` binders is not pinned by
   any numeric test.** Swapping them consistently gives a true, admitted
   theorem, and the partition identity totals `m·n` either way — see M4 in the
   mutation table. Only reading the declared type catches it.
3. **`countRange_eq_sumRange` is `Eq.refl`**, so it cannot be wrong in the way a
   proved theorem can; its test value is that it pins the two definitions
   staying the same `Nat.rec`. If someone changed `countRange`'s step to
   accumulate on the left, this declaration would stop compiling — which is the
   point — but no test measures that intention.
4. **Every concrete test runs at one instance, `(5,13)`.** It was chosen to
   discriminate on the axis that matters (row count ≠ complement column count),
   and it is one instance. The 504-prime-pair sweep is in Python, outside the
   kernel.

## Corrections to the brief

- The brief said "**`Rat.sumRange`/`Int.sumRange` over a bound is what you
  have**". `Rat.sumRange` exists; **`Int.sumRange` does not** — the Int prelude
  has `prodRange` only. This matters more than a name: it is the specific reason
  Eisenstein's lemma (step 1) is blocked and the lattice count (step 2) is not.
- The brief said "`sumRange_swap` exists and was used for the determinant's row
  expansion". True of `Rat.sumRange_swap`. **`Nat.sumRange_swap` did not
  exist**, and it is the piece the counting argument needs; it is declared here.
- The brief warned that "a floor-sum argument will fight" the stuck-`Nat.div`
  problem. Correct, and the useful consequence is that **the partition needs no
  floors at all** — division enters only when naming a count as a floor, which
  is residue 1 above and is separable from the partition.

## Consequences

- `Nat.sumRange_swap` is general Fubini over ℕ and has no connection to
  reciprocity; anything folding a doubly-indexed `Nat` family can use it. The
  same is true of `Nat.sumRange_const`.
- `finite_set::compl_sum_eq` was private, built inline for
  `Nat.countRange_compl`'s induction step — hiding place 2 in the retrieval
  taxonomy. It is now `pub(super)` and reused rather than re-derived.
- The next lane's target is `Int.sumRange` plus its defining equations,
  `sumRange_add`, `sumRange_congr`, and a mod-2 reader. That unblocks step 1 and
  is the single highest-value increment toward the law.
