# ADR-1624: A subset is a predicate, because the split law has to be `refl`

Status: accepted
Date: 2026-09-05
Index-summary: `Nat.Subsets.sumSubsets n F` sums over the `2^n` subsets of `[0,n)` and its split law — the subsets of `[0,n+1)` are the subsets of `[0,n)` twice, once without `n` and once with it — is `Eq.refl`, because a subset here is a `Nat → Bool` predicate and the fold recurses on the WIDTH. Over ADR-1614's `decode`-by-bit-code enumeration the same law needs `testBit (2^n + k) i = testBit k i`, a `div`/`mod`-by-`2^i` development this prelude does not have; over a `Nat.Finset` it cannot be `refl` at all, because the carrier stores a bound. General inclusion–exclusion (W2-19) lands on that primitive as two `Nat` sums, and its two-set case is `Nat.countRange_union_add_inter` VERBATIM — checked by offering one statement to the kernel twice. Möbius inversion did NOT land; the missing piece is now smaller and is named. Two mutants were RUN and both were killed by the trusted gate, the second at a step that had not been predicted.
Index-status: accepted

## Context

Roadmap **W2-19** (general inclusion–exclusion) and the residue of **W2-18**.
Two prior lanes had left the work sized:

- [ADR-1614](adr-1614-searching-over-subsets-is-a-reflection-primitive-not-a-hall-detail.md)
  built `Nat.Finset.decode n k` — the `k`-th subset of `[0,n)`, read off the
  bits of `k < 2^n` — together with a reflection lemma in both polarities. That
  is a *search* primitive.
- [ADR-1619](adr-1619-the-divisor-map-is-a-permutation-only-if-it-fixes-the-non-divisors.md)
  §"What did not land" named the missing piece for both W2-19 and Möbius
  inversion in the same sentence: *"what is missing is a sum INDEXED BY
  SUBSETS, which needs `sumRange (fun code => …) (2^n)` together with the
  parity of `Nat.Finset.card (decode n code)`. That is a well-defined next
  slice."*

The slice is well-defined. The *shape* proposed for it is the one this ADR
rejects.

## Decision

### 1. The enumeration is a fold over the WIDTH, and a subset is a predicate

`crates/axeyum-lean-kernel/src/nat_prelude/subset_sums.rs`:

```text
Nat.Subsets.empty        := fun _ => false
Nat.Subsets.insertAt n s := fun i => if beq i n then true else s i

Nat.Subsets.sumSubsets n F              -- Σ over ALL subsets of [0,n)
  | 0      F = F empty
  | succ m F = sumSubsets m F + sumSubsets m (fun s => F (insertAt m s))

Nat.Subsets.sumSel n F b                -- Σ over subsets of PARITY b
  | 0      F b = if b then F empty else 0          -- ∅ is even
  | succ m F b = sumSel m F b + sumSel m (fun s => F (insertAt m s)) (notB b)

Nat.Subsets.sumSelPos n F b             -- the same, over NON-EMPTY subsets
  | 0      F b = 0
  | succ m F b = sumSelPos m F b + sumSel m (fun s => F (insertAt m s)) (notB b)
```

so the deliverable — **the split law** —

```text
Nat.Subsets.sumSubsets_succ : ∀ F n,
  sumSubsets (succ n) F
    = sumSubsets n F + sumSubsets n (fun s => F (insertAt n s))
```

and its parity-graded twin `sumSel_succ` are both **`Eq.refl`**: the two halves
of the split are literally the two branches of the fold's own recursion.

**The alternative was measured, not assumed away.** Over `decode` the same law
splits the code range `[0, 2^(n+1))` at `2^n` via `sumRange_split` and then
owes two facts about adding a power of two to a bounded number:

```text
k < 2^n → ∀ i < n, testBit (2^n + k) i = testBit k i
k < 2^n →           testBit (2^n + k) n = 1
```

`testBit n i` is `testBitAux i n` with `testBit_zero : testBit n 0 = mod n 2`
and `testBit_succ : testBit n (succ i) = testBit (div n 2) i`, so both facts
are a `div`/`mod`-by-`2^i` induction. This prelude has `sum_testBit_lt`,
`sum_testBit_eq`, `eq_of_testBit_eq`, `lt_of_testBit` and
`testBit_eq_zero_of_lt` — and none of them is either of the two above. The
development was not attempted, so nothing here measures how long it would take;
what is measured is that the alternative costs **zero** and that it is the
alternative that makes the law usable at a symbolic width.

**A `Nat.Finset`-valued enumeration cannot have a `refl` split law at all**, and
that is a stronger statement than "it would be inconvenient". `finset.rs`'s own
module note records that two `Nat.Finset`s with the same members are not `Eq` —
the carrier stores a predicate *and a bound* — so `decode n k` and
`decode (succ n) k` are different terms for the same set, and any split law over
them carries a membership-congruence obligation on `F` in its statement.
ADR-1614 made exactly that obligation explicit in `forallSubset_of_search` and
was right to; the point here is that a SUM does not have to pay it, because the
sum never needs a carrier.

### 2. Nat has no negatives, so the alternating sum is a graded PAIR

`b = true` means EVEN, and the empty set is even. The signed sum
`Σ (−1)^|s| F s` is not writable, so every identity is stated
`even = odd + rest`:

```text
Nat.Subsets.sumSel_add   : sumSel n F true + sumSel n F false = sumSubsets n F
Nat.Subsets.sumSel_const : sumSel (succ n) (fun _ => c) true
                             = sumSel (succ n) (fun _ => c) false
```

This is [ADR-1619](adr-1619-the-divisor-map-is-a-permutation-only-if-it-fixes-the-non-divisors.md)'s
Möbius shape (`moebius_pos_add_neg`), reused rather than re-decided.

`sumSel_const` is **the alternating sum over a non-empty ground set vanishes**,
and its whole proof term is `Nat.add_comm` applied to the two halves at width
`n`. That is the return on §1: the split law sends `even (succ n)` to
`even n + odd n` and `odd (succ n)` to `odd n + even n`, and a constant summand
is unchanged by `insertAt` up to beta. Over the code enumeration this one-line
identity would sit behind the entire `testBit` development.

### 3. The support invariant is a HYPOTHESIS, and it is what inclusion–exclusion spends

`sumSel n F b` only ever applies `F` to predicates that are `false` at every
index `≥ n`:

```text
Nat.Subsets.Supported s n := ∀ i, Le n i → Eq Bool (s i) false

Nat.Subsets.sumSel_congr : ∀ n F G b,
  (∀ s, Supported s n → F s = G s) → sumSel n F b = sumSel n G b
```

A summand built from a width — a product over `[0,n)`, which is exactly what an
intersection indicator is — reads `s` only below that width, so its own width
can be moved independently of the fold's. That separation is the entire content
of the inclusion–exclusion induction step, and without `sumSel_congr` there is
no way to state it. Making the obligation a hypothesis rather than restricting
`F` to some `beq`-expressible class is the same choice ADR-1614 made and for the
same reason: it costs the consumer one lemma application and states the truth.

### 4. General inclusion–exclusion (W2-19)

`crates/axeyum-lean-kernel/src/nat_prelude/inclusion_exclusion.rs`, over a
family `A : Nat → Nat → Bool` of decidable subsets of `[0,m)`:

```text
Nat.Subsets.meetInd  A n s v := prodRangeIf s (fun i => if A i v then 1 else 0) n
Nat.Subsets.meetCard A n s m := sumRange (fun v => meetInd A n s v) m
Nat.Subsets.unionAt  A n     := fun v => anyOf (fun i => A i v) n
Nat.Subsets.ieSum    A n m b := sumSel    n (fun s => meetCard A n s m) b
Nat.Subsets.ieSumPos A n m b := sumSelPos n (fun s => meetCard A n s m) b

Nat.Subsets.inclusion_exclusion : ∀ A n m,
  ieSum A n m true + countRange (unionAt A n) m = ieSum A n m false + m

Nat.Subsets.inclusion_exclusion_pos : ∀ A n m,
  countRange (unionAt A n) m + ieSumPos A n m true = ieSumPos A n m false
```

The second is the classical statement; it is the first with the empty
subfamily's contribution — exactly `m`, since `meetCard A n empty m = m` —
cancelled off both sides by `add_left_cancel`.

The proof is **one swap and one per-element identity**. `sumSel_swap` turns the
sum over subsets of a sum over elements inside out; at a fixed ambient element
the inner subset sum is a product expansion,

```text
Nat.Subsets.sumSel_meetInd : ∀ A n b v,
  sumSel n (fun s => meetInd A n s v) b = prodPar (fun i => A i v) n b
```

and `prodPar` — a `Bool`-valued family's parity-graded product expansion,
recursing on the width — carries the argument in one induction:

```text
Nat.Subsets.prodPar_even : ∀ c n,
  prodPar c n true = prodPar c n false + noneOf c n
```

with `noneOf c n = 1` exactly when no `i < n` has `c i`. Summing that residue
over `[0,m)` counts the elements in no member of the family, and
`Nat.countRange_compl` converts it to `m` minus the union's size **without
writing a subtraction**. Taking the family `Bool`-valued rather than
`Nat`-valued removes the `g i ≤ 1` hypothesis the same argument would otherwise
carry: the dichotomy is `bool_true_or_false`, not a `Le`-elimination.

`sumSel_meetInd` is where §3 is spent, twice: once to drop the new element's
factor from the sets that do not contain it (a `Supported` application at
`le_refl`), once to expose it as a scalar on the sets that do, after which
`sumSel_mul_right` pulls it out and what remains matches `prodPar`'s own
recursion by `Eq.refl`.

### 5. The two-set case is the OLD lemma, and the kernel says so

```text
Nat.Subsets.inclusion_exclusion_two : ∀ A m,
  countRange (setUnion (A 0) (A 1)) m + countRange (setInter (A 0) (A 1)) m
    = countRange (A 0) m + countRange (A 1) m
```

is `Nat.countRange_union_add_inter`'s statement, derived from §4 at `n = 2`.

**How that is checked matters more than the theorem.** The test builds the
statement ONCE and offers it to the trusted gate TWICE — with the derived
theorem, and with `Nat.countRange_union_add_inter` applied at `A 0` and `A 1`.
Both are admitted, so the two are the same *type*; a reader is not being asked
to compare two rendered strings. A third offer, at the same statement with
`A 0` replaced by `A 1` on the right, is REJECTED, so the double acceptance is
not consistent with a statement anything proves.

One design choice exists only to make that specialisation free.
`Nat.Subsets.anyOf` is a fresh bounded existential rather than a reuse of
`Nat.Finset.allBelow` (which `Nat.Hall.anyBelow` already wraps), because its
base case is the literal `false` that makes

```text
anyOf c 2 ≡ if (if false then true else c 0) then true else c 1
          ≡ if c 0 then true else c 1
          ≡ setUnion (c 0) (c 1)
```

reduce by iota alone. Through `allBelow` the same collapse would be a lemma.
That is a real duplication and it is entered knowingly: the alternative is a
two-set case that needs its own argument, which is precisely what §5 is trying
to avoid.

## What did not land

Stated precisely so the next lane does not re-derive the obstruction.

- **Möbius inversion.** ADR-1619 named the missing bijection: for a squarefree
  `n`, the divisors are the products of the SUBSETS of its prime factors, and
  `Σ_{d ∣ n} μ(d) = [n = 1]` reads the alternating sum off it. The *alternating
  sum* half is now closed and is one line (`sumSel_const`, §2). The
  **bijection** is not, and this ADR does not shorten it: it needs
  `Nat.factorization` as a multiset, a product over a sub-multiset, and
  injectivity of that product from unique factorisation. `Nat.Multiset.card`,
  `Nat.factorization` and `Squarefree` all exist; nothing indexes a multiset by
  a `Nat → Bool` predicate, which is the join this construction needs. Read
  this ADR as removing one of the two halves, not as unblocking Möbius.
- **`Nat.dirichlet_assoc`.** Checked at the start of the lane and still absent
  (`arith_functions_family.rs` declares `dirichlet` and `dirichlet_comm` and no
  associativity). Möbius inversion `f = g * 1 ⟹ g = f * μ` needs it. It was not
  attempted, because the bullet above blocks the theorem it would serve.
- **The two subset enumerations are not related by any theorem.** ADR-1614's
  `decode` and this ADR's `sumSubsets` range over the same `2^n` subsets in the
  same binary order — `sumSubsets_card` pins the count and the evaluation tests
  pin the order at `n ≤ 3` — but no declaration says so, and the bridge costs
  exactly the `testBit (2^n + k)` development §1 avoided. A consumer that needs
  both (a *search* for a subset, then a *sum* over subsets) has to carry the
  translation itself.
- **Inclusion–exclusion is stated over PREDICATES, not `Nat.Finset`s.** That is
  what makes the two-set case `countRange_union_add_inter` rather than
  `Nat.Finset.card_union_add_card_inter`, and it is deliberate. A `Finset`
  wrapper would need `card_eq_countRange_add` to reconcile per-set bounds
  against a common ambient `m`; it is mechanical and it was not built.

## Consequences

**What this costs.** Forty-one declarations — fourteen definitions (one of them
the `Prop`-valued `Supported`) and twenty-seven theorems, which is the whole
`Nat.Subsets` namespace as `nat_theorem_inventory Subsets.` reports it — with
every axiom footprint empty. Twenty-one tests in two suites. The
`nat_prelude::` sweep went from 581 to 592 to 602 across the lane's commits and
stays under a minute.

**What it enables.** Any argument of the form "sum something over the subsets of
a finite index set" is now a fold with a `refl` split law and a stated support
obligation. The nearest consumers are the ones ADR-1614 already listed for the
search primitive — Dilworth, Turán, and the extremal half of the subject — plus
the Möbius route above and the Bonferroni inequalities, which are the same
induction stopped early.

**What must not be inferred.** `sumSubsets n F` visits `2^n` subsets and every
`Nat` numeral here is unary, so it is not an evaluation strategy: the tests stay
at `n ≤ 3` and `m ≤ 4`. Its value, exactly as with `anySubset`, is that a `Prop`
mentioning it never reduces it, so the LAWS are usable at a symbolic width even
though the fold is not runnable there.

## Mutation table

**Two mutants were RUN.** Both were killed by the trusted gate, and the second
was killed at a step this ADR's author had not predicted — which is the row
worth reading.

| mutant | outcome | measured? |
|---|---|---|
| `sumSel`'s base branches exchanged (the empty set counted ODD), definition ONLY | **killed 11 of 11.** The whole `Nat` prelude fails to build: `declare_subset_sums_all` reports `step \`equations\` REJECTED: DeclarationValueMismatch`, because `sumSel_zero`'s `Eq.refl` no longer type-checks. Every test in the suite dies at `build_nat_prelude(…).expect(…)` | **RUN**, `--release --test-threads=4` |
| the same flip, COORDINATED across five sites: the definition, `sumSel_zero`'s statement, and the parity of both `sumSelPos` bridges | **killed 11 of 11 — but not where predicted.** The prediction was that `pos_split` would catch it. It was caught two steps EARLIER, at `step \`sumSel_congr\` REJECTED: TypeMismatch`: that lemma's base case proves `F ∅ = G ∅` and then transports it through the context `fun x => bool_select_nat b x 0`, which hard-codes which branch the empty set's value sits in. So the parity convention is pinned by a *congruence context inside a proof*, not only by the equation that states it | **RUN**, restored byte-for-byte afterwards (`git status` clean on the path) |
| a fully consistent parity RELABELLING (`true` ↔ `false` everywhere) | **NOT ATTEMPTED, and no claim is made about it.** Tracing the second mutant's failure identified at least nine sites that would have to move together — the definition, `sumSel_zero`, `sumSel_congr`'s base context, `sumSel_mul_right`'s and `sumSel_swap`'s base `goal_at` plus their two `refl_case`s each, `sumSel_add`'s base (`add_zero` becomes `zero_add`), and both `sumSelPos` bridges including their step bodies — and `prodPar`, `prodPar_even` and the two inclusion–exclusion statements in the other file on top | predicted only |
| `sumSubsets`'s step reading `ih F + ih F` (the same half twice) | predicted to be refuted by `sumSel_add`, which ties the graded fold to the ungraded one: at `succ j` it would assert `x+y+z+w = 2(x+y)`. **NOT RUN.** This mutant is the reason the doc comment on `sumSubsets_card` was corrected — `= pow 2 n` holds under it (both halves are `2^(n-1)`), so that law does NOT pin the halves' distinctness, and the evaluation test `sumSubsets 2 card = 4` (which such a fold answers `0`) does | predicted only; the doc correction it forced is real |
| a theorem's STATEMENT slid by one small term | **caught by thirteen accept/reject pairs that run on every green build**, each offering the SAME already-declared constant at the slid statement and requiring the trusted gate to REJECT it: the split law with its halves exchanged; the graded split law without the `notB`; `sumSel_zero` with its branches exchanged; `sumSel_congr`'s hypothesis at `succ n`; `sumSel_mul_right` with the product commuted; `sumSel_add` with the halves exchanged; `sumSel_true_eq_empty_add_pos` at ODD parity; `supported_insertAt` un-widened; and, in the other file, `inclusion_exclusion` with its right-hand summands exchanged, `inclusion_exclusion_pos` with the parities swapped, `inclusion_exclusion_two` with `A 0` replaced by `A 1`, `prodPar_even` with the residue moved to the even side, and `meetCard_empty` returning the family width | RUN on every build (21 passing tests) |
| a new declaration added and left unwatched | **caught by construction**: `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free` derives its subject from the live environment, so all forty-one names had to be registered before the suite went green. A law cannot be quietly *dropped* either — the same list names every declared constant, so deleting one makes the list reference a name that no longer exists | RUN |

**The finding, and its honest limit.** In this module the kernel is the mutation
detector, and it is *over*-determined: every mutant designed here — including
the deliberately coordinated one — is refuted by one of the algebraic laws
before any test asserts a number. `sumSel_add` ties the graded fold to the
ungraded one; `sumSel_congr`'s base pins the parity convention inside a proof
term. **No mutant that the kernel admits was constructed**, so this ADR does not
claim the evaluation tests are load-bearing against any of them. They are the
readable pin, and the only artefact that names the wrong answer
(`sumSubsets 2 card` is `4` and not `3`; `sumSel 1 (fun s => if s 0 then 7
else 2) true` is `2` and not `7`; the eight three-set intersections are
`4,2,2,2,1,0,1,0`). That is the same limit ADR-1614 recorded, reached
independently.

## Verification

- `nat_prelude::subset_sums_tests` — 11 passed, 0 failed
  (`--release --test-threads=4`). Nonzero count confirmed.
- `nat_prelude::inclusion_exclusion_tests` — 10 passed, 0 failed. Nonzero count
  confirmed.
- `nat_prelude::` (the whole prelude sweep) — 602 passed, 0 failed.
- `cargo check --workspace --all-targets` — clean. Run because a `NatPrelude`
  field addition breaks the generated consumer in `axeyum-py`;
  `python3 scripts/gen-py-prelude-fields.py` was regenerated (`nat` 1234+113 →
  1252+113) and `--check` is OK.
- `python3 scripts/validate-facts.py` — 2820 facts, 0 errors, after
  `check-fact-depends-derived.py --fix` added four edges the proof terms already
  carried (`add_comm`, `add_assoc`, `add_left_cancel`).
- The `shape_search` sweep this ADR quotes was run against a binary rebuilt at
  this lane's base commit: `declarations=3000`, positive control
  `--name Nat.sumDivisorsBy_reindex --expect 1` FOUND, exit 0. `--name-like`
  returned ABSENT for `sumSubsets`, `subsetSum`, `evenB`, `isEven`, `withTop`
  and `Bool.or`, and FOUND for `testBit`, `setUnion`, `orB` and `parity` — which
  is why this lane built none of the latter. Rebuilt at the lane's head the same
  binary reports `declarations=3041`, i.e. exactly the forty-one this ADR
  claims; that difference is an independent count, not the source-side one.
