# ADR-1671: The mask belongs in the FOLD, not in a hypothesis on the summand

Status: accepted
Date: 2026-09-06
Index-summary: ADR-1658 left one decision open: `Nat.Subsets.sumSubsets (bound m)` enumerates `2^(bound m)` predicates while a squarefree `n` has `2^(distinct primes)` divisors, so a divisor transfer onto it counts every divisor `2^(bound m − ω(n))` times, and the repair is either to restrict the enumeration to supported predicates or to enumerate the support into `[0,k)`. This ADR takes the first, and finds that "restrict the enumeration" cannot be a congruence lemma at all: a congruence changes the SUMMAND on the predicates the fold already visits and can never change WHICH predicates it visits, so the mask has to be a parameter of the fold itself. `Nat.Subsets.sumSubsetsOn P n F` and `sumSelOn P n F b` keep all four unfolding equations at `Eq.refl` and add `sumSubsetsOn_card : sumSubsetsOn P n (fun _ => 1) = pow 2 (countRange P n)`, which is the only law here that a fold ignoring its mask fails — the split law, the grading law and even the vanishing law all hold for that fold. `sumSelOn_const_of_mem` is the vanishing law, and its two branches are asymmetric: with the top index masked it is `add_comm` and the induction hypothesis is unused, without it the mask witness must move below the top index, which is what forces the case split to be over the EQUATION `P j = false` rather than `Bool.rec` on `P j`. ADR-1658's missing piece A also lands, and its sizing was wrong in a useful direction: `Nat.Multiset.count_le_of_dvd_prod` is not an induction at all but one `lt_or_ge` and three `dvd_trans`es over valuation halves that already existed. Surjectivity itself did NOT land, and the blocker moved: it is now a `prodRange` range-stability law, not a valuation bound. Two mutants RUN; both killed by the trusted gate before any evaluation control ran, and no admitted-but-wrong mutant was found — reported, not papered over.
Index-status: accepted

## Context

Roadmap **W2-18**, third slice.
[ADR-1658](adr-1658-a-multiset-is-selected-by-value-because-it-has-no-positions.md)
landed `Nat.Multiset.prodSel` — selection of a multiset by VALUE over
`[0, bound m)` — together with `prodSel_dvd_prod` (every selection is a divisor)
and `prodSel_injective` (two selections with the same product agree on the
support). It closed with an explicit open decision:

> with `prodSel` value-indexed and `sumSubsets` folding over `[0, k)`, the
> natural width is `bound m`, and `sumSubsets (bound m)` enumerates
> `2^(bound m)` predicates while a squarefree `n` has only
> `2^(number of distinct primes)` divisors. The counts do not match, and the gap
> is exactly the values below the bound that are not in the support. So either
> the transfer restricts the enumeration to supported predicates, or the support
> does after all have to be enumerated into `[0, k)`. **That choice is the next
> decision, and it is not made here.**

The lane brief for this slice named the first option as "restrict `sumSel` to
predicates SUPPORTED on `m` … with `sumSel_supported_congr`".

## Decision

### 1. "Restrict the enumeration" cannot be a congruence lemma

The brief's shape does not exist, and finding out why is the substantive part
of this decision.
[ADR-1624](adr-1624-a-subset-is-a-predicate-because-the-split-law-has-to-be-refl.md)'s
`Nat.Subsets.sumSel_congr` already says "two summands agreeing on the SUPPORTED
predicates give equal sums", where `Supported s n` means `s` is `false` at every
index `≥ n`. That is a statement about the width, and it is the strongest thing
a congruence can say: **a congruence lemma changes the summand `F` on the
predicates the fold already visits; nothing about it can change WHICH predicates
the fold visits.** The double counting is in the enumeration, so no hypothesis
on the summand reaches it — and in particular a summand of the form
`fun s => f (prodSel m s)` cannot be made to vanish on the unsupported
predicates, because `prodSel m s` names a genuine divisor there, just the same
one twice.

So the mask becomes a parameter of the fold:

```text
Nat.Subsets.sumSubsetsOn P 0        F = F empty
Nat.Subsets.sumSubsetsOn P (succ j) F
  = sumSubsetsOn P j F + (if P j then sumSubsetsOn P j (F ∘ insertAt j) else 0)

Nat.Subsets.sumSelOn P 0        F b = if b then F empty else 0
Nat.Subsets.sumSelOn P (succ j) F b
  = sumSelOn P j F b + (if P j then sumSelOn P j (F ∘ insertAt j) (notB b) else 0)
```

An index outside the mask contributes only the "without it" half of the split,
so the enumerated predicates are exactly the subsets of `{i < n : P i}`. All
four unfolding equations stay `Eq.refl` — ADR-1624's reason for choosing a
`Nat → Bool` subset over a `Nat.Finset` survives the change untouched — and the
full mask `fun _ => true` recovers the unrestricted folds, also by `Eq.refl`
(`sumSubsetsOn_all`, `sumSelOn_all`).

### 2. Why not position enumeration, with the cost of the other route stated

The alternative ADR-1658 named is to enumerate the support into `[0, k)`, which
is the position indexing ADR-1658 declined **at the multiset**, arriving from
the other side. Costed honestly:

| | masked fold (chosen) | position enumeration |
| --- | --- | --- |
| new definitions | 2 | 2 (`supportNth m`, its inverse or its bound) |
| equations | 4, all `Eq.refl` | none free — `supportNth` is a search, not a fold |
| before a transfer can be STATED | nothing | monotonicity, injectivity, surjectivity onto the support, and a `prodSel`-through-the-selector bridge |
| what it also buys | a general masked-subset primitive W2-19's inclusion–exclusion can use | nothing else |
| what it gives up | the fold's recursion still visits `bound m` levels though only `ω(n)` branch | nothing |

Four theorems about an object that does not otherwise exist, against two
definitions and four `refl`s. The reduction cost the masked fold gives up is
real and is a cost in *reduction*, never in a *statement*, which is why the
evaluation tests keep every numeral tiny.

### 3. `sumSubsetsOn_card` is the only law that can see the mask

```text
Nat.Subsets.sumSubsetsOn_card : sumSubsetsOn P n (fun _ => 1) = pow 2 (countRange P n)
```

This is worth stating as the point of the module rather than as a nicety. A
fold whose step takes the high half **unconditionally** — the double-counting
fold this whole ADR exists to avoid — satisfies the split law (it is `refl` in
any fold that recurses on the width), the grading law `sumSelOn_add`, and even
the vanishing law `sumSelOn_const_of_mem`. None of those compares the masked
fold against anything that counts. `sumSubsetsOn_card` does, and answers `2^n`
for that fold instead of two-to-the-masked-count.

This is CLAUDE.md's "six of seven guards rejected through one shared check" in
its constructive form: the guard that discriminates had to be *designed in*,
because the natural laws of the new fold are all satisfied by the wrong one.

### 4. The vanishing law's case split must be over the EQUATION

```text
Nat.Subsets.sumSelOn_const_of_mem : ∀ c P n i, Lt i n → P i = true →
  sumSelOn P n (fun _ => c) true = sumSelOn P n (fun _ => c) false
```

`Nat.Subsets.sumSel_const` (ADR-1624) is the special case at the full mask,
where the witness is free because the top index always qualifies. Here it has to
be carried, and the two branches are asymmetric:

- **Top index masked.** The split law sends `even (succ j)` to `even j + odd j`
  and `odd (succ j)` to `odd j + even j`, so `add_comm` closes it and **the
  induction hypothesis is never used**.
- **Top index not masked.** Both sides lose their high half, the goal becomes
  the statement at `j`, and the witness has to move below the top index — which
  needs `i ≠ j`.

`i ≠ j` comes from the mask itself: `P i = true` and `P j = false` cannot both
hold at one index. **That is what forces the case split to be over the equation
`P j = false` (via `bool_true_or_false` + `Or.rec` + `bool_transport`) rather
than `Bool.rec` on `P j`.** A `Bool.rec` branch does not hand you the equation
it split on, so the contradiction is unreachable inside it, and the false branch
cannot be closed at all. This is a reusable rule: **when a case split's branch
needs to CONTRADICT the value it split on, split on the equation, not the
value.**

### 5. ADR-1658's missing piece A lands, and its sizing was wrong

```text
Nat.Multiset.count_le_of_dvd_prod : (∀ x, 0 < count m x → prime x) →
  0 < d → dvd d (prod m) → Le (count (factorization d) q) (count m q)
```

ADR-1658 sized this as "a real but bounded induction, mostly in `multiset.rs`'s
idiom — call it one lane". It is **neither an induction nor in that idiom**.
Both valuation halves already existed (`Nat.Multiset.pow_count_dvd_prod` and
`not_pow_succ_count_dvd_prod`), so the argument is one `Nat.lt_or_ge` at the two
counts — whose right half IS the goal — plus three `dvd_trans`es in the left
half:

```text
q ^ (count m q + 1)  ∣  q ^ count (factorization d) q  ∣  prod (factorization d) = d  ∣  prod m
```

and `not_pow_succ_count_dvd_prod` says the first does not divide the last. `q`'s
primality falls out in exactly the branch that needs it, because the strict
inequality forces `0 < count (factorization d) q`, which is
`Nat.factorization_prime`'s hypothesis. And `Nat.lt n m` **is**
`Nat.le (succ n) m` definitionally here, so "strictly greater" becomes "at least
one more copy" for free.

The generalisable form, and it is the same one
[the finding-existing-lemmas guide](../../contributor-guide/finding-existing-lemmas.md)
states about blockers: **a handoff's sizing of what REMAINS is a hypothesis, and
when the remaining work is "compose two things that already exist", the sizing
is usually an over-estimate by an order of magnitude.**

## What did NOT land, and where the blocker moved

**Surjectivity itself.** With `s q := ble 1 (count (factorization d) q)` and a
squarefree `m` (every `count m q ≤ 1`), `count_le_of_dvd_prod` gives
`count (restrict m s) q = count (factorization d) q` at every `q` — the two
multisets agree pointwise. Concluding `prodSel m s = d` needs count-agreement to
imply prod-agreement, and the multiset carrier deliberately has no
extensionality
([ADR-1520](adr-1520-a-multiplicity-function-is-a-multiset-and-uniqueness-was-a-representation-problem.md)):
the two multisets have **different bounds**, so their `prodRange` folds run over
different ranges, and `Nat.Multiset.count_eq_of_prod_eq` runs the other way. The
missing lemma is a range-stability law —
`(∀ i, Le a i → f i = 1) → Le a b → prodRange f b = prodRange f a` — and then
`Nat.Multiset.prod_eq_of_count_eq` on top of it.
`Nat.prodRange_eq_one_of_below` (`factorization_multiset.rs`) is the *collapse*
law, not the stability law. So the blocker under surjectivity moved from a
valuation bound to a fold-range law, and it is a smaller and more reusable
target than the one ADR-1658 named.

**The range-to-subset sum transfer** (ADR-1658's missing piece B) is unchanged
and is still the hard one: `sumRangeIf (· ∣ n) f (n+1)` and
`sumSubsetsOn (support m) (bound m) (fun s => f (prodSel m s))` fold over
different index SHAPES, and this prelude's only cross-index law
(`Nat.countRange_bij`) is for counts over two `Nat` ranges. What this ADR
changes is that the two sides now have the same CARDINALITY, which
`sumSubsetsOn_card` states; before, no bijection could have existed.

**`Nat.dirichlet_assoc`.** Confirmed absent by `shape_search --include-constructed
--name-like dirichlet` (`declarations=4755`, positive control `Nat.dirichlet`
FOUND; only `dirichlet_comm`, `numDivisors_eq_dirichlet` and
`sumDivisors_eq_dirichlet` exist). It is NOT reachable from anything in this
ADR, and it is not a corollary of `dirichlet_comm`. Sized:
`dirichlet (dirichlet f g) h n = Σ_{d∣n} Σ_{e∣d} f e · g(d/e) · h(n/d)` against
`dirichlet f (dirichlet g h) n = Σ_{e∣n} Σ_{c∣(n/e)} f e · g c · h(n/(e·c))`,
and the bijection `(d,e) ↦ (e, d/e)` between the two triangular index sets is
not a permutation of any square this prelude can fold over. Reaching it needs an
inner reindex of `sumRangeIf` along `c ↦ e·c`, i.e. a
**`sumRangeIf` reindexing law under a non-surjective injective map with matching
predicates** — a new primitive with no analogue here, and a lane of its own.
`Nat.Subsets.sumSel_swap` is the subset-times-range swap and does not apply.

**`Σ_{d ∣ n} μ(d) = 0` and Möbius inversion.** Both sit behind the transfer.
The `p`-adic involution route ADR-1658 recorded as an alternative was
re-examined and is confirmed to need the two facts ADR-1658 named
(`Squarefree (k·p) ↔ Squarefree k ∧ p ∤ k`, `omegaCount (k·p) = omegaCount k + 1`)
— and `omegaCount` is `Multiset.card (factorization ·)`, so the second one needs
**the same card-from-counts step** the surjectivity route needs for `prod`.
That is a genuine convergence: the range-stability law unblocks both routes, and
it is the single highest-value next target for this shelf.

## Consequences

- Twelve new names: `Nat.Subsets.sumSubsetsOn`, `sumSelOn`, their four
  equations, `sumSubsetsOn_all`, `sumSelOn_all`, `sumSelOn_add`,
  `sumSubsetsOn_card`, `sumSelOn_const_of_mem`, and
  `Nat.Multiset.count_le_of_dvd_prod`. All registered in
  `nat_prelude_tests::definition_names`/`theorem_names`, so the
  every-declaration sweep covers them; all axiom-free.
- `Nat.Subsets.sumSubsets`/`sumSel` are NOT deprecated: they are the masked
  folds at the full mask, by `Eq.refl`, and general inclusion–exclusion
  (W2-19) wants the unrestricted ones.
- Three facts recorded: `F:nat-subsets-sum-subsets-on-card`,
  `F:nat-subsets-sum-sel-on-const-of-mem`,
  `F:nat-multiset-count-le-of-dvd-prod`.

## Mutation evidence, and what it actually showed

Both mutants were **RUN**, in the lane's own isolated worktree, in the
foreground, and restored byte-for-byte (`md5sum` matched the pre-mutation copy;
`git status` empty afterwards).

| Mutant | Site | Predicted | RUN result |
| --- | --- | --- | --- |
| A: the fold ignores its mask (double counting) | `subset_sums_masked.rs`, `declare_definitions`, `sumSubsetsOn` step: `bool_select_nat at_m high zero` → `high` | the `8` control in `the_masked_fold_visits_only_the_masked_indices` (`2^3` is what an unmasked fold gives), or `sumSubsetsOn_card` | killed, 7 of 7 tests in `subset_sums_masked_tests` failed, exit 101 — but by a **kernel rejection** at the named step `equations`, so the prelude never built and neither `sumSubsetsOn_card` nor the evaluation control ever ran |
| B: the vanishing law drops its mask hypothesis | `subset_sums_masked.rs`, `declare_sum_sel_on_const`, `motive_at`: `arrow(lt_ty, arrow(hit_ty, concl))` → `arrow(lt_ty, concl)` | a **kernel rejection** — the statement is FALSE (the necessity control `the_constant_vanishing_law_is_false_without_a_masked_index` exhibits the empty-mask witness: even half `4`, odd half `0`), and the `at_top` branch's contradiction is unreachable without the hypothesis | killed, 7 of 7 tests failed, exit 101, by a **kernel rejection** at the named step `sumSelOn_const_of_mem`. The rendered `TypeMismatch` names the BASE case, not the step: `expected` is the bare conclusion at width `0` while `got` still carries `(x0 : Eq Bool (P i) true) -> …`, because the base case's `absurd` is applied under a binder the mutated motive no longer declares. So the first thing to break was not the branch the hypothesis is used in — which is the ordinary shape of a dropped-binder mutation and the reason the error location is not a guide to the cause |

Mutant B is the exact analogue of the brief's second mutant —
`sum_moebius_divisors` at `n = 1` with `1 < n` dropped — transposed onto the
statement that actually landed. In both cases the hypothesis is what makes the
identity true at all, and the empty-mask instance is `n = 1`'s divisor set: one
divisor, sitting entirely on the even side.

**The finding is the same one ADR-1658 reported, and it is now the second
consecutive slice on this shelf to report it.** Every mutation attempted died at
the trusted gate before a single evaluation control ran, and **no
admitted-but-wrong mutant was found**. That absence is not a claim that none
exists — it is what was measured, and the reason it is hard to construct here is
structural: `sumSubsetsOn_succ` and `sumSelOn_succ` are `Eq.refl` and mention
the mask guard explicitly, so any single-site change to either definition breaks
an equation before any theorem is reached, and a consistent change to definition
AND equation then breaks `sumSelOn_add`, whose two branches are built from the
guard's `Bool.rec`. The evaluation tests are therefore **redundant with the
kernel today for these two definitions**, exactly as ADR-1658 found for
`prodSel`/`restrict`. They are kept anyway, because that redundancy is a
property of the current theorem set rather than of the definitions: a future
lane that generalises `sumSubsetsOn_succ` — say, to a version whose right-hand
side does not name the guard — would remove it silently.
