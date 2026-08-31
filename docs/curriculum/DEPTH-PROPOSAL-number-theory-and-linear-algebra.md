# A Spivak-shaped spine for number theory and linear algebra

**Status: a proposal.** Nothing here is in `curriculum.toml`, deliberately —
adopting it means adding ~30 nodes to a 23-node graph and every consumer of
that file (`scripts/lib/graph_dispatcher.py`, `scripts/gen-import-backlog.py`,
`scripts/validate-foundational-concepts.py`, the `mathtour.rs` Rust mirror and
`artifacts/ontology/foundational-concepts.json`) has to move with it. ADR-1075
records the decision to write the design first and land the graph change as its
own reviewed step.

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
| N10 | **The multiplicative group mod n** — Fermat, Euler, Wilson | N9, counting | **mostly have.** `Nat.pow_prime_modeq_self` (Fermat, all `a`), `Int.wilson`/`wilson_converse`/`wilson_iff`, `Nat.totient` with `totient_mul_of_coprime`, `totient_prime_pow`, `totient_prime`. **`a^φ(n) ≡ 1 (mod n)` itself is absent**, though both residue-permutation ingredients (`Int.euler_unit_coprime`, `Int.euler_unit_injective`) are landed |
| N11 | **Quadratic residues** | N10 | **partly.** `Int.euler_criterion_pm_one` and the two implication halves are landed; **quadratic reciprocity is absent** and is the subject's genuine frontier |

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
`number-theory` has a four-prerequisite box. Under this spine the three live
rungs are N7′, N10's Euler theorem, and N11's reciprocity — and each names its
blocker precisely enough to brief against. That is the whole argument for the
decomposition.

---

## 2. Linear algebra — a nine-rung spine, and the honest gap

Today: one node, `covered`, `Family::LinearAlgebra`. Measured kernel
attribution: **55 declarations** — the `Rat.det2`/`det3` fixed-size determinant
theory, `Rat.dotN` at general `n`, the matrix layer (`matMul`, `matId`,
`matTranspose`), Cramer's rule at 2×2 and the 2×2 adjugate inverse. Add
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
| L3 | **Linear combination and span** | L2, counting | **absent,** and cheap. Needs `Rat.sumRange` over an indexed family; `Rat.sumRange_swap`, `sumRange_delta`, `sumRange_mul`, `sumRange_split` are all present and `sumRange_swap` was the hard part |
| L4 | **Inner product** | L2 | **have,** at general `n`: `Rat.dotN` with `dotN_add_left`, `dotN_smul_left`, `dotN_comm`, `dotN_self_nonneg`, `dotN_succ`, `dotN_two`, `dotN_zero`, and **`Rat.dotN_cauchy_schwarz` at arbitrary `n`**. Reachable precisely because its conclusion is a scalar |
| L5 | **Matrices as `Nat → Nat → Rat`, and the product** | L2, L3 | **have.** `Rat.matMul`, `Rat.matId` (`matId_diag`, `matId_off_diag`), `matMul_assoc`, `matMul_id_left`/`_right`, `matMul_add_left`/`_right`, `matMul_smul_left`, `matMul_succ`, `matMul_zero`. Stated pointwise (`∀ i j, i < m → j < p → …`), as the absence of `funext` requires. Built on `Rat.sumRange_swap`, exactly as predicted |
| L6 | **Transpose, and `(AB)ᵀ = BᵀAᵀ`** | L5 | **have.** `Rat.matTranspose`, `matTranspose_mul`, `matTranspose_transpose` |
| L7 | **Determinant** | L5 | **have at fixed size only.** `Rat.det2` (`det2_mul` multiplicativity, `det2_id`, `det2_swap_rows`, `det2_scale_row`, `det2_row_add`, `det2_eq_zero_of_lin_dep`), `Rat.det3` (`det3_cofactor_row1`, `det3_id`, `det3_scale_row`). **General `n` is the live frontier.** A permutation sum needs permutations as data and there is no `List`; a **cofactor recursion over the bound** is expressible and is the honest route. Nothing else in this spine is blocked on it |
| L8 | **Linear systems `Ax = b`** | L5, L7 | **have at 2×2 in the kernel** (`Rat.cramer2_x`, `cramer2_y`, `cramer2_solves`, `cramer_two_unique_x`/`_y`, and the adjugate inverse `inv2_*`/`mul_adj2_*`), and **the strongest row in the curriculum outside it**: `simplex::feasible`/`check_farkas`, `lra::FarkasCertificate::verify`, kernel reconstruction through `prove_unsat_to_lean_module`. The *general-`n`* solvability statement is absent and waits on L7 |
| L9 | **Eigenvalues** | L7, polynomials | **absent.** The characteristic polynomial at fixed size is expressible (`Rat.polyEval` exists); the general spectral theory is Mathlib-scale and out of range |

**The one recommendation that changes work rather than documentation:** the
keystone is now L7 at general `n`, not L5. L3 (span) and L7-general are the two
open rungs, and L7-general is the one that unblocks L8-general and L9. Its
route is a cofactor recursion over the dimension bound — the same shape
`Nat.choose` and `Nat.binaryRec` already use — and *not* a permutation sum,
which this kernel cannot state for want of a `List`. L3 is a `Rat.sumRange`
assembly over an indexed family and is cheap.

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
- **No renumbering of the existing 23.** The spines above sit *inside* the two
  destination nodes; the layer-0 through layer-2 nodes are unchanged, and
  `divisibility-and-euclid`, `modular-arithmetic` and `counting` are already the
  first six rungs of the number-theory spine under different names. Adopting the
  spine means promoting rungs to nodes where they earn it (N7′, N10, N11, L5,
  L7), not rebuilding the graph.

## See also

- [ADR-1075](../research/09-decisions/adr-1075-the-curriculum-graph-measures-scenarios-not-the-kernel.md)
- [DEPTH.md](DEPTH.md) — the three coverage layers this adds a fourth to
- [graded-statement-families-number-theory-and-linear-algebra.md](graded-statement-families-number-theory-and-linear-algebra.md)
  — §3 for the four linear-algebra families and the type-theory verdict in full
- [03-destinations/number-theory.md](03-destinations/number-theory.md),
  [03-destinations/linear-algebra.md](03-destinations/linear-algebra.md)
