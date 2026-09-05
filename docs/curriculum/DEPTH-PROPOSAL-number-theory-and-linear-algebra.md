# A Spivak-shaped spine for number theory and linear algebra

**Status: a proposal.** Nothing here is in `curriculum.toml`, deliberately —
adopting it means adding ~30 nodes to a 24-node graph and every consumer of
that file (`scripts/lib/graph_dispatcher.py`, `scripts/gen-import-backlog.py`,
`scripts/validate-foundational-concepts.py`, the `mathtour.rs` Rust mirror and
`artifacts/ontology/foundational-concepts.json`) has to move with it. ADR-1075
records the decision to write the design first and land the graph change as its
own reviewed step. ADR-1140 re-measured the two rungs this proposal called the
open frontier and found both had since landed (below), and reaffirmed the
decision not to do the ~30-node surgery in that same pass — the two
`kernel_decls` corrections are in `curriculum.toml`, the graph shape is not.

**Correction, 2026-08-31 (ADR-1140).** Two rungs this proposal named as the
live frontier landed the same day it was written, in commits that postdate it:

- **L7, the general-`n` determinant, is done.** `Rat.det : (Nat → Nat → Rat) →
  Nat → Rat` (ADR-1120, `rat_prelude/matrix_det.rs`) is a cofactor recursion
  over the dimension bound, exactly the route this proposal named, with
  `det_eq_det2`/`det_eq_det3` proving it agrees with the fixed-size forms at
  `n = 2, 3`. `linear-algebra`'s `kernel_decls` moves 59 → 81 for this reason
  (`Rat.det*`, `matSkip`, `matMinor`, `altSign`, `matInv2*` — 22 declarations
  that a bug in `measure-curriculum-kernel-coverage.py`'s bucket pattern had
  silently mis-attributed to `rationals` until ADR-1140 fixed it).
- **N10's Euler's theorem is done.** `Int.euler_totient_theorem : ∀ n a,
  0 < n → Coprime a n → ModEq n (pow a (totient n)) 1` (ADR-1110,
  `int_prelude/euler_assembly.rs`) is exactly `a^φ(n) ≡ 1 (mod n)`, axiom-free,
  assembled from `Int.prodRangeIf_permute` and the residue-permutation
  ingredients this proposal already listed as landed.

L9 (eigenvalues) and N11 (quadratic reciprocity) remain the genuine open
frontiers on their respective spines; L3 (span) and N7′ (factorization
uniqueness, restated) remain as this proposal describes them below.

**Correction, 2026-08-31 (ADR-1205).** Re-measuring again after ADR-1140 found
a second instance of the same bucket-attribution bug ADR-1140 had just fixed,
this time on N11 itself: the second supplementary law
(`Int.secondSupplementaryLaw`, ADR-1150) and Gauss's lemma
(`Int.gaussLemmaSignCount`, ADR-1130) landed a real chunk of the quadratic-
residue apparatus — 29 declarations — and every one of them fell through
`number-theory`'s bucket pattern to the `naturals`/`integers` catch-alls,
because the pattern's only Gauss's-lemma alternative was the literal string
`gauss_fold_injective`, written when one declaration of that shape existed.
Fixed by widening the pattern (deliberately *not* to match bare `gauss_lemma`,
which is an unrelated divisibility theorem correctly filed under
`divisibility-and-euclid`); `number-theory`'s `kernel_decls` moves 108 → 137.
A parallel one-declaration miss on the linear-algebra side
(`Rat.sumRange_matSkip`, from ADR-1155's Laplace row-expansion layer) moved
`linear-algebra` 81 → 90. **N11's genuine open frontier is narrower than this
proposal's own text below still says**: not "quadratic reciprocity is absent"
in full, but specifically the general law relating two distinct odd primes —
Gauss's lemma and the second supplementary law are both landed routes toward
it. See the corrected N11 row and
[`03-destinations/number-theory.md`](03-destinations/number-theory.md) for the
current state. The ~30-node graph-surgery decision is unaffected: neither
addition is a status flip, both are `kernel_decls` corrections, and the reasons
ADR-1075/ADR-1140 gave for not doing the surgery (the consumer surface, and no
self-checking scenario family for the open rungs) are unchanged by this pass.

Every "kernel has it" claim below is grounded in one measurement, not in prose:

```sh
cargo run --release -p axeyum-lean-kernel \
  --example kernel_declaration_projection > /tmp/proj.tsv
python3 scripts/measure-curriculum-kernel-coverage.py /tmp/proj.tsv \
  --expect-attributed 2433
```

Run 2026-08-31 over 2,562 distinct declarations, every one axiom-free. Where a
rung says **have**, the named declarations were checked present in that
projection; where it says **absent**, the name was absent from it and a
same-kind positive control was present.

---

## Why the current graph is thin, and what Spivak does differently

The three destinations are terminal nodes. `number-theory` has four
prerequisites and nothing after it; `linear-algebra` has three; `calculus` has
three. Each is one box standing for an entire subject, so the graph can say
*"you need fields before linear algebra"* and cannot say anything about the
order of results **inside** linear algebra.

Spivak's *Calculus* is organised the opposite way. Its unit of structure is not
the subject but the **earned result**: a numbered theorem whose proof cites only
theorems with smaller numbers, so the book is a total order on a dependency
graph and every chapter is a contiguous stretch of it. The reason that matters
here is not pedagogical taste. It is that **the flywheel dispatches against
nodes**, and a node the size of "linear algebra" cannot be dispatched against —
there is no such thing as proving it, only proving things in it.

So the proposal is: give each destination an **ordered spine of results**, where
each rung names (a) what it needs from the rungs below, (b) what the kernel
already has, and (c) the specific construction that is missing. A rung is small
enough to be a lane's task and large enough to be worth a name.

Two constraints from this kernel shape every spine below, and both are
structural rather than a matter of effort:

- **There is no `List`, `Finset`, `Prod` or quotient-by-permutation.** The
  complete inductive list is `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/
  Decidable` + `Nat.le` + `Nat.Fin` + `Char` + `Nat.Pair`. A finite family is a
  **function plus a bound** (`Nat → Rat` with an `n`), which is exactly how
  `Rat.dotN`, `Nat.prodRange` and `Nat.countRange` are built. Anything whose
  statement needs a multiset — uniqueness of prime factorization, the
  characteristic polynomial's root multiset — is not merely unproved but
  unstatable in that form, and its expressible reformulation is a different
  rung.

  > **CORRECTION, 2026-08-31
  > ([ADR-1310](../research/09-decisions/adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md)):
  > "structural rather than a matter of effort" is wrong for this first
  > constraint.** The census is an INVENTORY: `Nat.Pair` landed 2026-08-29 and
  > `Nat.Primrec` 2026-08-31, `Kernel::add_inductive` is an ordinary gate, and
  > an inductive contributes **zero** rows to `Kernel::axiom_footprint`
  > (`Inductive`/`Constructor`/`Recursor` are filtered out). Nothing structural
  > forbids a `List`; the reason not to add one is that `Nat.Fin` already
  > exists with **zero non-test consumers**, so the development has already
  > declined an indexed finite type once.
  >
  > A finite family also does not need a type — it needs a **fold**, and a
  > fold is a function. `Int.sumMaps` sums over every map `[0,m) -> [0,n)`
  > with no function-space type, and `Int.prodRange_sumRange_expand` is an
  > admitted axiom-free theorem over that index set.
  >
  > **What survives, narrowed:** a statement comparing two *unordered*
  > collections — multiset equality, hence uniqueness of prime factorization
  > and the root multiset — genuinely quantifies over an aggregate rather than
  > folding over one, and no fold reaches it. That much is unstatable. It is a
  > claim about multiset equality, not about finite families.
- **`funext` is absent** (positive control: `congrFun'`, the other direction,
  is present). A conclusion that is an equation **between functions** —
  `(AB)C = A(BC)` as matrices, `A·A⁻¹ = I` — cannot be an `Eq`. It must be
  stated **pointwise**: `∀ i j, i < m → j < n → …`. A conclusion that is a
  **scalar** is unaffected, which is why `Rat.dotN_cauchy_schwarz` is stated as
  an ordinary `Eq` at general `n` while `Rat.matMul_assoc` -- equally landed --
  must carry its indices and bounds in the statement.

Neither is a reason to shrink the spine. They decide the *phrasing* of about a
third of the rungs, and a spine that ignores them proposes rungs that cannot be
stated.

---

## 1. Number theory — an eleven-rung spine

Today: one node, `number-theory`, with prerequisites
`divisibility-and-euclid`, `modular-arithmetic`, `induction`, `counting`.
Measured kernel attribution: 105 declarations to the destination, 151 to
divisibility, 104 to modular arithmetic, 66 to counting, 19 to cardinality —
**445 in the number-theoretic column**, second only to analysis.

The subject is the one where this repository is furthest ahead of its own map,
so the spine is mostly a matter of *naming what is already there* rather than
proposing work.

| # | rung | needs | kernel today |
|---|---|---|---|
| N1 | **Divisibility** — `∣` as a relation, transitivity, linearity | naturals, integers | **have.** `Nat.dvd`, `Int.dvd` with the standard closure lemmas |
| N2 | **Euclidean division** — existence and uniqueness of `(q, r)` | N1, induction | **have.** `Nat.divModState`, `Int.euclidean_decomposition`, `Int.euclid_of_nat` |
| N3 | **gcd and the Euclidean algorithm** | N2 | **have.** `Nat.gcd` (well-founded, via `WellFounded.fix`), `gcd_comm`, `gcd_dvd_left/right`, `gcd_greatest`, `gcd_mod_left_eq_gcd` |
| N4 | **Bézout** — `gcd a b = ax + by` with computed witnesses | N3 | **have.** `Nat.bezout`, `Nat.xgcdAux` + `xgcdAux_sound`, `Int.gcd_eq_gcd_ab`, `Int.gcdA/gcdB` |
| N5 | **Coprimality** — the calculus of `gcd = 1` | N4 | **have,** heavily: ~45 `Nat.coprime_*` lemmas, `gcd_cofactors_coprime`, `coprime_iff_isRelPrime` |
| N6 | **Euclid's lemma and primality** | N5 | **have.** `Nat.euclid_lemma`, `Int.euclid_lemma`, `Nat.gauss_lemma`, ~30 `Nat.prime_*` lemmas, `Nat.minFac` with `minFacAuxMinimal` |
| N7 | **Factorization — the existence half** | N6, induction | **have.** `Nat.exists_prime_dvd`, `Nat.exists_prime_factorization` |
| N7′ | **Factorization — the uniqueness half, restated** | N7, cardinality | **absent, and blocked by type theory, not difficulty.** Multiset equality has no carrier. The expressible form is *multiplicity agreement at each prime*, reachable via `Nat.countRange_permute`. This is a rung the current graph cannot even express the existence of. |
| N8 | **Congruences and modular arithmetic** | N2 | **have.** `Int.ModEq`, `Nat.modeq`, ~104 declarations |
| N9 | **CRT** | N5, N8 | **have, twice.** `Nat.crt_unique` (Nat-native) and `Int.crt_exists`/`Int.crt_unique`. Note the two live in `nat_prelude/crt.rs` and `int_prelude/crt.rs`; three separate triages checked only the Int one and concluded it did not transport |
| N10 | **The multiplicative group mod n** — Fermat, Euler, Wilson | N9, counting | **have.** `Nat.pow_prime_modeq_self` (Fermat, all `a`), `Int.wilson`/`wilson_converse`/`wilson_iff`, `Nat.totient` with `totient_mul_of_coprime`, `totient_prime_pow`, `totient_prime`, and **`Int.euler_totient_theorem` (`a^φ(n) ≡ 1 (mod n)`, ADR-1110)** — landed 2026-08-31, axiom-free, from the residue-permutation ingredients (`Int.prodRangeIf_permute` and friends) this row used to list as the missing piece |
| N11 | **Quadratic residues** | N10 | **partly, further than this row says (ADR-1205).** `Int.euler_criterion_pm_one` and its two implication halves, Gauss's lemma (`Int.gaussLemmaSignCount`, ADR-1130) and the second supplementary law (`Int.secondSupplementaryLaw`, ADR-1150) are all landed, axiom-free; **the general reciprocity law relating two distinct odd primes is absent** and is the subject's genuine frontier |

Two side spurs the spine should carry as nodes rather than as footnotes,
because both already have kernel content that nothing in the graph points at:

- **Arithmetic functions.** `Nat.totient`, `Nat.sumDivisors` (with
  `sumDivisors_prime`, `sumDivisors_two_pow_eq_geom_sum`), `Nat.Perfect`. The
  spine rung is *multiplicativity as a property*, which the kernel proves
  case-by-case and never states in general (there is no carrier for "an
  arithmetic function", so the general statement needs a `Nat → Nat` argument
  and a hypothesis, not a typeclass).
- **Integer sequences.** `Nat.fib`/`Int.fib` with `fib_cassini`, `fib_two_mul`,
  `fib_add`, `coprime_fib_succ`, `Rat.det2_fib`. This is where the Fibonacci
  work already lives and it currently attributes to `number-theory` only by
  accident of naming.

**What the spine changes about dispatch.** Today a lane sent at
`number-theory` has a four-prerequisite box. Under this spine the two
remaining open rungs are N7′ and N11's reciprocity (N10's Euler theorem
closed 2026-08-31, ADR-1110) — and each names its blocker precisely enough to
brief against. That is the whole argument for the decomposition.

---

## 2. Linear algebra — a nine-rung spine, and the honest gap

Today: one node, `covered`, `Family::LinearAlgebra`. Measured kernel
attribution (2026-08-31, post-ADR-1120; re-measured post-ADR-1155/ADR-1205):
**90 declarations** — the `Rat.det2`/`det3` fixed-size determinant theory plus
the **general-`n` determinant** (`Rat.det`, `matSkip`, `matMinor`, `altSign`,
`matInv2*`, ADR-1120) with its Laplace row-expansion layer (`sumRange_matSkip`
and friends, ADR-1155), `Rat.dotN` at general `n`, the matrix layer (`matMul`,
`matId`, `matTranspose`), Cramer's rule at 2×2 and the 2×2 adjugate inverse. Add
`Rat.sumRange_swap` and `Rat.sumRange_diagonal`, filed under `counting` because
that is their aggregate but load-bearing here, and `CPoint`'s 116 declarations,
a genuine 2-D inner-product space over the constructed reals, filed under
`complex` because that is its carrier.

**This number was 0 in my first pass and 25 in my second, and both were wrong
in the same direction.** The first probed `--name-like matrix|determinant|eigen`
and got ABSENT — a correct answer to a query this kernel's spelling cannot
match. The second read `linear-algebra.md`, which had `det2`/`det3`/`dotN` right
but declared the matrix layer unbuilt; that page was accurate on 2026-08-30 and
the matrix layer landed after it. Three readings, one measurement. Re-run the
command at the top of this file rather than quoting any of them.

| # | rung | needs | kernel today |
|---|---|---|---|
| L1 | **Scalars** — a field to work over | fields, rationals | **have** as ℚ concretely (`Rat.IsField`, `Rat.IsOrderedField`). No abstract `Field` carrier exists and none is proposed: everything below is stated over ℚ or over `CReal` |
| L2 | **Vectors as bounded families** — `v : Nat → Rat` with a dimension `n` | L1, relations-and-functions | **have** implicitly. `Rat.dotN` uses exactly this encoding. **The encoding itself is unnamed**, which is a small rung worth landing: a `Rat.Vec`-shaped abbreviation plus the pointwise-equality relation `∀ i, i < n → v i = w i`, since `funext` is absent and this predicate has to stand in for equality everywhere above |
<!-- absent: Rat.Vec -->
| L3 | **Linear combination and span** | L2, counting | **absent,** and cheap. Needs `Rat.sumRange` over an indexed family; `Rat.sumRange_swap`, `sumRange_delta`, `sumRange_mul`, `sumRange_split` are all present and `sumRange_swap` was the hard part |
| L4 | **Inner product** | L2 | **have,** at general `n`: `Rat.dotN` with `dotN_add_left`, `dotN_smul_left`, `dotN_comm`, `dotN_self_nonneg`, `dotN_succ`, `dotN_two`, `dotN_zero`, and **`Rat.dotN_cauchy_schwarz` at arbitrary `n`**. Reachable precisely because its conclusion is a scalar |
| L5 | **Matrices as `Nat → Nat → Rat`, and the product** | L2, L3 | **have.** `Rat.matMul`, `Rat.matId` (`matId_diag`, `matId_off_diag`), `matMul_assoc`, `matMul_id_left`/`_right`, `matMul_add_left`/`_right`, `matMul_smul_left`, `matMul_succ`, `matMul_zero`. Stated pointwise (`∀ i j, i < m → j < p → …`), as the absence of `funext` requires. Built on `Rat.sumRange_swap`, exactly as predicted |
| L6 | **Transpose, and `(AB)ᵀ = BᵀAᵀ`** | L5 | **have.** `Rat.matTranspose`, `matTranspose_mul`, `matTranspose_transpose` |
| L7 | **Determinant** | L5 | **have, at general `n` (ADR-1120, landed 2026-08-31).** `Rat.det : (Nat → Nat → Rat) → Nat → Rat`, a **cofactor recursion over the dimension bound** — exactly the route this row named, since a permutation sum needs permutations as data and there is no `List`. `det_zero`/`det_succ` (the recursion equations), `det_one`, and `det_eq_det2`/`det_eq_det3` (symbolic agreement with the fixed-size forms below). Plus the fixed-size theory this row originally described: `Rat.det2` (`det2_mul` multiplicativity, `det2_id`, `det2_swap_rows`, `det2_scale_row`, `det2_row_add`, `det2_eq_zero_of_lin_dep`), `Rat.det3` (`det3_cofactor_row1`, `det3_id`, `det3_scale_row`) |
| L8 | **Linear systems `Ax = b`** | L5, L7 | **have at 2×2 in the kernel** (`Rat.cramer2_x`, `cramer2_y`, `cramer2_solves`, `cramer_two_unique_x`/`_y`, and the adjugate inverse `inv2_*`/`mul_adj2_*`), and **the strongest row in the curriculum outside it**: `simplex::feasible`/`check_farkas`, `lra::FarkasCertificate::verify`, kernel reconstruction through `prove_unsat_to_lean_module`. **L7's precondition is now met**; the *general-`n`* solvability statement itself is still unbuilt and is the next rung to dispatch |
| L9 | **Eigenvalues** | L7, polynomials | **absent.** The characteristic polynomial at fixed size is expressible (`Rat.polyEval` exists); the general spectral theory is Mathlib-scale and out of range |

**The one recommendation that changed work rather than documentation, and it
has now landed:** the keystone was L7 at general `n`, not L5, and closing it
(ADR-1120) was exactly the cofactor-recursion route predicted here — the same
shape `Nat.choose` and `Nat.binaryRec` already use, not a permutation sum,
which this kernel cannot state for want of a `List`. **The remaining open
rungs are L3 (span, a cheap `Rat.sumRange` assembly) and L9 (eigenvalues,
Mathlib-scale); L8's general-`n` solvability statement is now unblocked and is
the natural next dispatch.**

An earlier draft of this file named L5 as the keystone and sized it as
"assembly over `sumRange_swap` rather than new mathematics". That sizing was
right and the work was already done.

**And one that stops work:** do not propose a rung whose conclusion is a
matrix equation stated as `Eq`. It cannot be admitted, `funext` will not
arrive, and the pointwise form is not a workaround — it is the statement.

---

## 3. A subject the graph has no node for at all

The measurement turned up something neither destination accounts for. The
`rationals` node's 251 declarations include **47 of probability and statistics**,
and there is no curriculum node they belong to:

- **Distributions.** `Rat.IsDistribution`, `Rat.uniform` with
  `uniform_is_distribution`, `Rat.bernoulli`, `Rat.indicator`, `Rat.prob_le_one`,
  `Rat.prob_complement`.
- **Expectation.** `Rat.expectation` with linearity (`expectation_add`,
  `expectation_smul`, `expectation_const`), monotonicity (`expectation_le`),
  positivity, and `expectation_sumVars`.
- **Variance and covariance.** `Rat.variance` (`variance_eq`, `variance_nonneg`,
  `variance_smul`, `variance_add_of_uncorrelated`, `variance_sumVars`),
  `Rat.covariance` with `covariance_sq_le_variance_mul` — Cauchy–Schwarz for
  random variables — and `Rat.PairwiseUncorrelated`.
- **The classical inequalities and a limit theorem.** `Rat.markov_inequality`,
  `Rat.chebyshev_inequality`, `Rat.chebyshev_sampleMean_uncorrelated`, and
  **`Rat.weak_law_of_large_numbers`** with `bernoulli_law_of_large_numbers`.

That is a coherent Spivak-shaped spine already built — distribution →
expectation → variance → Markov → Chebyshev → weak law — sitting entirely
outside the map. It is not a fourth destination this proposal argues for; it is
evidence for ADR-1075's general point, that the graph's blind spot is
*structural* rather than a matter of four stale summaries. A graph with no
`probability` node cannot record 47 axiom-free declarations, cannot dispatch
against the obvious next rung (the strong law, or Chebyshev without the
pairwise-uncorrelated hypothesis), and does not know it is missing anything.

## 4. What this does not propose

- **No status flips.** `covered` and `lean-horizon` are the scenario axis and
  both destinations are correctly labelled on it (ADR-1075). The kernel axis is
  `kernel_decls`, already landed in `curriculum.toml`.
- **No abstract algebra carriers.** `rings` and `fields` measure 0 kernel
  declarations and that is correct: this kernel proves things about ℕ, ℤ, ℚ,
  `CReal` and ℂ, not about arbitrary structures satisfying axioms. `Nat.isGroupOn`
  (with `modAdd_isGroup`, `symmetric_group_isGroupOnFn`, `group_left_cancel`) is
  the pattern that works — a *predicate* on a concrete carrier, not a typeclass —
  and the ten declarations it carries are the whole abstract-algebra column.
  A spine for abstract algebra would be a third proposal and this is not it.
- **No renumbering of the existing nodes** (23 when this proposal was written,
  24 since ADR-1082 added `probability`). The spines above sit *inside* the two
  destination nodes; the layer-0 through layer-2 nodes are unchanged, and
  `divisibility-and-euclid`, `modular-arithmetic` and `counting` are already the
  first six rungs of the number-theory spine under different names. Adopting the
  spine means promoting rungs to nodes where they earn it (N7′, N11, L3, L9 —
  N10 and L5/L7 no longer need promoting, having landed as content inside the
  existing `number-theory`/`linear-algebra` nodes), not rebuilding the graph.

## See also

- [ADR-1075](../research/09-decisions/adr-1075-the-curriculum-graph-measures-scenarios-not-the-kernel.md)
- [DEPTH.md](DEPTH.md) — the three coverage layers this adds a fourth to
- [graded-statement-families-number-theory-and-linear-algebra.md](graded-statement-families-number-theory-and-linear-algebra.md)
  — §3 for the four linear-algebra families and the type-theory verdict in full
- [03-destinations/number-theory.md](03-destinations/number-theory.md),
  [03-destinations/linear-algebra.md](03-destinations/linear-algebra.md)
