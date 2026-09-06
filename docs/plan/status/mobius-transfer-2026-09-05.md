# Lane: mobius-transfer — the mask belongs in the fold, and a divisor's valuation is bounded

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL — deliverable 1 in full, deliverable 2's named
prerequisite, deliverable 3 not at all`, mobius-transfer, 2026-09-06).** Roadmap
**W2-18**, third slice. ADR
[1671](../../research/09-decisions/adr-1671-the-mask-belongs-in-the-fold-not-in-a-hypothesis.md).

**Deliverable 1 — the transfer shape is decided, and the brief's shape does not
exist.** The brief asked to "restrict `sumSel` to predicates SUPPORTED on `m`
… with `sumSel_supported_congr`". That cannot be a congruence lemma at all: a
congruence changes the SUMMAND on the predicates the fold already visits, and
nothing about it can change WHICH predicates the fold visits. The double
counting is in the enumeration, so the mask has to be a parameter of the fold.
`Nat.Subsets.sumSubsetsOn P n F` and `sumSelOn P n F b` fold over the width as
before, except that an index outside `P` contributes only the "without it" half
of the split. All four unfolding equations stay `Eq.refl`, and the full mask
`fun _ => true` recovers the unrestricted folds by `Eq.refl` too. ADR-1671 §2
costs the alternative (position enumeration) at four theorems about an object
that does not otherwise exist, before a transfer can even be STATED.

**Landed: 12 declarations, all axiom-free, all registered in
`nat_prelude_tests::definition_names`/`theorem_names`.** Definitions
`Nat.Subsets.sumSubsetsOn` and `sumSelOn`; theorems
`Nat.Subsets.`{`sumSubsetsOn_zero`, `sumSubsetsOn_succ`, `sumSelOn_zero`,
`sumSelOn_succ`, `sumSubsetsOn_all`, `sumSelOn_all`, `sumSelOn_add`,
`sumSubsetsOn_card`, `sumSelOn_const_of_mem`} and
`Nat.Multiset.count_le_of_dvd_prod`. Every one was admitted on the FIRST
attempt.

Two of them carry the weight:

- **`sumSubsetsOn_card : sumSubsetsOn P n (fun _ => 1) = pow 2 (countRange P n)`
  is the only law here that a fold ignoring its mask fails.** The split law, the
  grading law `sumSelOn_add` and even the vanishing law all hold for that fold,
  because none of them compares the masked fold against anything that counts.
  The discriminating guard had to be designed in.
- **`sumSelOn_const_of_mem`** — a constant summand's even and odd halves agree
  as soon as one index below the width is masked. Its two branches are
  asymmetric: with the top index masked it is `add_comm` and the induction
  hypothesis is unused; without it the witness must move below the top index,
  which needs `i ≠ j`, and that comes from the mask itself. **So the case split
  has to be over the EQUATION `P j = false`, not `Bool.rec` on `P j`** — a
  `Bool.rec` branch does not hand you the equation it split on, so the
  contradiction is unreachable inside it. General rule: when a branch needs to
  CONTRADICT the value it split on, split on the equation.

**Deliverable 2 — ADR-1658's missing piece A landed; surjectivity did not, and
the blocker MOVED.** `Nat.Multiset.count_le_of_dvd_prod` says a divisor cannot
carry more copies of a prime than the multiset does. ADR-1658 sized it as "a
real but bounded induction, mostly in `multiset.rs`'s idiom — call it one lane";
it is **neither an induction nor in that idiom**. Both valuation halves already
existed, so it is one `Nat.lt_or_ge` (whose right half IS the goal) plus three
`dvd_trans`es in the left half. Surjectivity itself is now blocked on a
*different* primitive: with `s q := ble 1 (count (factorization d) q)` and a
squarefree `m` this theorem gives `count (restrict m s) q =
count (factorization d) q` at every `q`, but the two multisets have DIFFERENT
BOUNDS, so concluding `prodSel m s = d` needs a `prodRange` **range-stability**
law — `(∀ i, Le a i → f i = 1) → Le a b → prodRange f b = prodRange f a` — and
`Nat.Multiset.prod_eq_of_count_eq` on top of it. `prodRange_eq_one_of_below` is
the *collapse* law, not the stability law.

**RETRIEVAL COST, recorded because it was nearly paid.** `Le a b →
dvd (pow n a) (pow n b)` was budgeted as new work and **written in full** — an
induction on the upper exponent, base case through `le_antisymm` — before a grep
turned up **`Nat.pow_dvd_pow_of_le`** in `multiset.rs`, two files away, used
twice there. The duplicate was deleted unlanded. Hiding place 4 of
`finding-existing-lemmas.md`: a grep for the name you would have given it is not
a search.

**Deliverable 3 — not landed, and here is the precise obstruction for each.**

- **`Nat.dirichlet_assoc`.** Confirmed absent (`shape_search
  --include-constructed --name-like dirichlet`, `declarations=4755`, positive
  control `Nat.dirichlet` FOUND; only `dirichlet_comm`,
  `numDivisors_eq_dirichlet`, `sumDivisors_eq_dirichlet` exist). It is **not**
  reachable from anything this lane built and not a corollary of
  `dirichlet_comm`. The two sides are double sums over *triangular* index sets
  and the bijection `(d,e) ↦ (e, d/e)` is not a permutation of any square this
  prelude can fold over. It needs a **`sumRangeIf` reindexing law under a
  non-surjective injective map with matching predicates** (the inner
  substitution `d = e·c`), which has no analogue here.
  `Nat.Subsets.sumSel_swap` is subset-times-range and does not apply. Own lane.
- **`sum_moebius_divisors` and Möbius inversion.** Both sit behind ADR-1658's
  missing piece B, the range-to-subset transfer, which is unchanged. What
  changed is that the two sides now have the same CARDINALITY —
  `sumSubsetsOn_card` states it — where before no bijection could have existed.
- **The `p`-adic route** was re-examined rather than inherited. It needs
  `omegaCount (k·p) = omegaCount k + 1`, and `omegaCount` is
  `Multiset.card (factorization ·)`, so it needs **the same card-from-counts
  step** the surjectivity route needs for `prod`. That convergence is the
  finding: the range-stability law unblocks both routes and is the single
  highest-value next target on this shelf.

**Mutation: the result is the finding, for the second consecutive slice.** Both
mutants RUN in this lane's isolated worktree, in the foreground, restored
byte-for-byte (`md5sum` matched; `git status` clean). Mutant A (the fold ignores
its mask — double counting) killed 7 of 7 tests in `subset_sums_masked_tests`,
exit 101, **by a kernel rejection at the named step `equations`**, so
`sumSubsetsOn_card` and the `8` evaluation control never ran. Mutant B (the
vanishing law drops its mask hypothesis, the analogue of `sum_moebius_divisors`
at `n = 1`) likewise killed 7 of 7, exit 101, by a kernel rejection at the named
step `sumSelOn_const_of_mem` — and its `TypeMismatch` names the BASE case rather
than the branch that uses the hypothesis, which is the ordinary shape of a
dropped-binder mutation and a reminder that the error location is not a guide to
the cause. **No admitted-but-wrong mutant was found**, and the structural reason is stated rather than assumed: the
two `succ` equations are `Eq.refl` and mention the mask guard explicitly, so any
single-site change breaks an equation before a theorem is reached, and a
consistent change to definition AND equation then breaks `sumSelOn_add`, whose
branches are built from that guard's `Bool.rec`.

**Facts:** `F:nat-subsets-sum-subsets-on-card`,
`F:nat-subsets-sum-sel-on-const-of-mem`, `F:nat-multiset-count-le-of-dvd-prod` —
all `proved`, `axiom_footprint: []`, three evidence rows each (rendered-type
pin, contains-then-footprint, and an evaluation or NECESSITY control). The
vanishing law's necessity row is the one worth reading: at the empty mask its
conclusion is FALSE (even half `4`, odd half `0`), which is the same shape as
`Σ_{d∣n} μ(d) = 0` failing at `n = 1`.

**Partition check:** `Multiset`, `moebius`, `dirichlet`, `prodSel`, `sumSel` and
`Subsets` appear in NONE of
`artifacts/structural-index/held-out-exclusion-manifest.json`,
`artifacts/autogenesis/nursery-v2-extension.json`, or
`corpus/glaurung-proof-populations/`. Positive control: the same grep over the
same three paths returns the nursery extension for `squarefree`, whose family
`natural-factorial-choose-and-squarefree` is `train`. Every declaration here is
this repository's own construction, not an `ml430` mirror. No held-out family
was touched.

<!-- plan-section: landed-changes -->

| 2026-09-06 | mobius-transfer | `Nat.Subsets.sumSubsetsOn`/`sumSelOn`, four `refl` equations and the two full-mask bridges (`subset_sums_masked.rs`) — `beeef1e79` |
| 2026-09-06 | mobius-transfer | `sumSelOn_add`, `sumSubsetsOn_card` (the only law a mask-ignoring fold fails) and `sumSelOn_const_of_mem`, plus 7 evaluation tests with a NECESSITY control — `91dc6fb96` |
| 2026-09-06 | mobius-transfer | `Nat.Multiset.count_le_of_dvd_prod` (ADR-1658's missing piece A) and 3 tests; `Nat.pow_dvd_pow_of_le` found already present and the duplicate deleted unlanded — `fb81000a5` |
| 2026-09-06 | mobius-transfer | ADR-1671 and three facts; `dirichlet_assoc`, the range-to-subset transfer and Möbius inversion sized, not landed |
