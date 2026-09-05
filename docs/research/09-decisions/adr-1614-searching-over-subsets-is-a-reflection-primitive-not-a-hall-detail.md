# ADR-1614: Searching over subsets is a reflection primitive, not a Hall detail

Status: accepted
Date: 2026-09-04
Index-summary: `Nat.Finset.anySubset` enumerates the `2^n` subsets of `[0,n)` by a `Nat` code and `existsSubset_of_search`/`forallSubset_of_search` read the verdict back — the two-dimensional twin of `allBelow_false_witness`/`allBelow_true_at`, and the piece ADR-1608 named as the real blocker on Hall's sufficiency. `Nat.testBit` already existed, so the enumeration is `decode n k := mk (bitB k) n` rather than a new bit decoder. `Nat.strongInduction` is named at last. Hall's sufficiency did NOT land; the remaining obstruction is now the FAMILY, not the search, and it is sized.
Index-status: accepted

## Context

[ADR-1608](adr-1608-the-graph-carrier-forces-symmetry-and-irreflexivity.md)
landed Hall's marriage theorem in its **necessity** direction and stopped at a
named obstruction. Its §4 lists three missing pieces and says which is the real
one:

> **Choosing the critical subfamily — this is the real one.** The split needs
> *some* critical `t` or a proof that none exists, which is a search over the
> `2^(bound s)` subsets of `s`. This kernel has no classical choice, so the
> subset must be COMPUTED, together with its own reflection lemma. Nothing of
> that shape exists. `Nat.Finset.allBelow_false_witness` is the
> one-dimensional analogue and is the model to copy […] a lane should size that
> primitive first and treat items 1 and 2 as consequences.

This ADR builds that primitive. It also builds ADR-1608's item 1
(`Nat.strongInduction`), which the same sweep measured absent. It does **not**
land Hall's sufficiency, and the last section says exactly what now stands in
the way — which is a different obstruction from the one this lane removed.

## Decision

### 1. The enumeration is a `Nat` code, and `Nat.testBit` already existed

`crates/axeyum-lean-kernel/src/nat_prelude/subset_search.rs`:

```text
Nat.Finset.bitB k i        := beq (Nat.testBit k i) 1
Nat.Finset.decode n k      := Nat.Finset.mk (bitB k) n
Nat.Finset.encodeFrom f n j                     -- recursion on the WIDTH n
  | f 0        j = 0
  | f (succ m) j = Nat.bit (f j) (encodeFrom f m (succ j))
Nat.Finset.encode t n      := encodeFrom (Nat.Finset.memB t) n 0
Nat.Finset.anySubset P n   := notB (allBelow (fun k => notB (P (decode n k)))
                                             (Nat.pow 2 n))
```

**The single largest saving in this lane came from searching for the STEP
rather than the NAME.** `shape_search --name-like` at 2,832 declarations
(positive control `Nat.Rado.IsRadoNumber`, FOUND) returns ABSENT for `decode`,
`encode`, `subsets`, `powerset`, `enumerate`, `bitAt` and `strong` — all the
words a "subset enumeration" lane would try. It returns **FOUND 15** for
`testBit`. `Nat.testBit : Nat → Nat → Nat` with `testBit_zero`, `testBit_succ`,
`testBit_le_one`, `testBit_eq_zero_of_lt`, `eq_of_testBit_eq`, `lt_of_testBit`,
`sum_testBit_eq` and `sum_testBit_lt` has been in `binary.rs`/`bit_order.rs`
all along, and `Nat.bit`, `bit_div_two`, `bit_mod_two`, `bit_false` and
`bit_lt_bit` are in `bits.rs`/`bit_decode.rs`/`bit_extra.rs`. So the decoder is
one definition (`bitB`) over an existing one, and the encoder's two laws are
`bit_mod_two` and `bit_div_two` read inside a `Bool` context.

Three choices worth recording:

**(a) `encodeFrom` recurses on the WIDTH and carries the start index upward,
rather than recursing on the index.** The alternative — `encode t n` by
recursion on `n` with index `n` as the new high bit — needs
`encode t (succ n) = encode t n + (if memB t n then 2^n else 0)`, which forms
`2^n` inside a *definition*. Every `Nat` numeral here is unary, so that is a
definition that cannot be evaluated. With the width recursion the only
arithmetic in the definition is `Nat.bit`, and `pow 2 n` appears **only in
statements**, where it is never reduced. Measured: `anySubset` evaluates at
`n = 2` in the test suite; the same definition with `pow` inside would not.

**(b) `Nat.pow 2 n` rather than a private doubling function.** `pow` exists and
the bit lemmas that bound a value by its magnitude (`testBit_eq_zero_of_lt`)
are already stated at `pow 2 j`, so a private `pow2` would have needed its own
copy of every bridge. `encodeFrom_lt_pow` costs three lemma applications
(`bit_lt_bit`, `bit_false`, `pow_succ` + `mul_comm`) because `bit_lt_bit` is
stated for *arbitrary* bits on both sides — no case split on `f j` at all.

**(c) `anySubset` is `notB ∘ allBelow ∘ notB`, matching `Nat.Hall.anyBelow`.**
`allBelow` is the only bounded loop with all three laws (build, read a `true`
back, extract a `false` witness), and both polarities of the reflection lemma
come out of two of them. A separate existential loop would need its own three.

### 2. The reflection lemma, in both polarities — and this is the deliverable

```text
Nat.Finset.existsSubset_of_search :
  ∀ (P : Nat.Finset → Bool) (n : Nat),
    Eq Bool (anySubset P n) true →
    Exists (fun t : Nat.Finset =>
      And (Eq Nat (Nat.Finset.bound t) n) (Eq Bool (P t) true))

Nat.Finset.forallSubset_of_search :
  ∀ (P : Nat.Finset → Bool) (n : Nat),
    (∀ u v, (∀ i, Eq Bool (memB u i) (memB v i)) → Eq Bool (P u) (P v)) →
    Eq Bool (anySubset P n) false →
    ∀ t, Le (Nat.Finset.bound t) n → Eq Bool (P t) false
```

`existsSubset_of_search` is `allBelow_false_witness` lifted through `decode`:
the search picks a code, the kernel recomputes `P` at the decoded set, and
`bound (decode n k)` is `n` by `refl` because `decode` builds it. Nothing about
the search is trusted.

`forallSubset_of_search` is the half Hall's sufficiency actually consumes — an
exhausted search is a *refutation* of every subset — and it needs the
exhaustiveness lemma:

```text
Nat.Finset.memB_decode_encode : ∀ t n i, Le (bound t) n →
  Eq Bool (memB (decode n (encode t n)) i) (memB t i)
```

**Stated at EVERY index, not only below `n`.** Below the width it is
`bitB_encodeFrom` plus `zero_add`; at or above it, both sides are `false` —
the decoded set because `decode`'s bound is `n`, and `t` because its own bound
is at most `n` — through `memB_of_bound_le`, which holds of every
`Nat.Finset` with no side condition precisely because `memB` truncates inside
its own definition (ADR-1577's first design choice, cashed in here). The two
sets therefore agree *extensionally*, not merely on the searched window, and
that is what lets the congruence premise be stated without an index bound.

**The congruence premise is explicit, and that is the honest form.** Two
`Nat.Finset`s with the same members are not `Eq` at the carrier — `finset.rs`
says so in its own module note, and it is a consequence of computing the
carrier rather than extracting it. So a search that ranges over `decode`d sets
cannot conclude anything about a set the caller supplies unless the searched
property respects membership. The alternatives were to hide the obligation
inside a `beq`-based statement (which would have restricted `P` to properties
expressible as a bounded loop, excluding the `card`-based property Hall needs)
or to quantify the conclusion over `decode`d sets only (which pushes the same
obligation onto every consumer, unstated). Making it a hypothesis costs the
consumer one lemma application and states the truth.

That lemma is now provided:

```text
Nat.Finset.card_congr_of_memB : ∀ u v,
  (∀ i, Eq Bool (memB u i) (memB v i)) → Eq Nat (card u) (card v)
```

filed in `finset.rs`, not in `subset_search.rs`, deliberately —
[ADR-1608 §2](adr-1608-the-graph-carrier-forces-symmetry-and-irreflexivity.md)
recorded "general infrastructure filed under its first consumer's module" as a
hazard it entered knowingly, and this is the same hazard declined. It is a
plain `Nat.Finset` law: fold both sets over the common bound
`bound u + bound v` through `card_eq_countRange_add`, apply
`countRange_congr_lt` pointwise, and collapse each side back, with one
`add_comm` because the two applications name the common bound in opposite
orders. Nothing in `finset.rs` could relate two sets that were not `Eq` before
it.

### 3. `Nat.strongInduction`, named

`crates/axeyum-lean-kernel/src/nat_prelude/strong_induction.rs`:

```text
Nat.strongInduction.{u} :
  ∀ (motive : Nat → Sort u),
    (∀ n, (∀ m, Lt m n → motive m) → motive n) → ∀ n, motive n
  := WellFounded.fix.{1,u} Nat Nat.lt motive Nat.lt_well_founded

Nat.strongInduction_eq.{u} : ∀ motive step n,
  strongInduction motive step n = step n (fun m _ => strongInduction motive step m)
  := WellFounded.fix_eq.{1,u} …
```

ADR-1608 measured this absent and it still is: `--name-like strong` returns
ABSENT at 2,832 declarations, and `Nat.base_induction` is a different
statement. Eight modules in this prelude (`gcd`, `bezout`, `factorization`,
`irrational`, `base_induction`, `count_range_reversal`, `totient_dvd_chain`,
`totient_gcd_mul`) already spell the five-argument `WellFounded.fix`
application by hand. The motive is **explicit**, because there is no elaborator
here and every application is built positionally; the universe is `Sort u`
(reusing the existing anonymous `u` level-parameter name), because
`WellFounded.fix` is already polymorphic and a `Prop`-only wrapper would not
cover the course-of-values *definitions* the same eight modules build.

`strongInduction_eq` is not decoration. `strongInduction motive step n` does
not reduce at a symbolic `n` — `lt_well_founded n` is stuck — so the unfolding
equation is the only way a proof about a strongly-recursive definition gets
past its own first step.

### 4. Hall's sufficiency did NOT land, and the obstruction has MOVED

This is a negative result and it is stated as precisely as the positive ones.

ADR-1608's three missing pieces were (1) strong induction, (2) the subset
search, (3) deleting from a family. **(1) and (2) are now closed.** (3) is not,
and having built (2) sharpens what (3) actually costs. The textbook step splits
on whether some proper non-empty `t ⊆ s` is critical, and with
`forallSubset_of_search` in hand the split itself is now available. What is not
available is either branch's *recursion*, and the reason is specific:

- **The searched property `P` must be membership-congruent, and only half of
  it now is.** `P t` is a conjunction of "`t` is non-empty", "`t ⊆ s`",
  "`t ≠ s`" and `card t = card (unionOver nb t)`. `card_congr_of_memB` (above)
  discharges the `card t` half and the three membership conjuncts are pointwise
  already. `card (unionOver nb t)` is **not** discharged: `unionOver nb t`
  computes its bound as `unionBound nb (bound t)`, which reads `t`'s stored
  bound and not its members, so two membership-equal `t` with different bounds
  give unions with different bounds — and no lemma says their memberships
  agree. The missing lemma is
  `Nat.Hall.memB_unionOver_congr : (∀ i, memB t i = memB t' i) →
  ∀ v, memB (unionOver nb t) v = memB (unionOver nb t') v`, which needs
  `Nat.Hall.anyBelow`'s **elimination** rule (a `true` `anyBelow` yields a
  witness) — declared with its introduction rule only in ADR-1608, and now a
  one-dimensional instance of `allBelow_false_witness` rather than of anything
  missing. That one is bookkeeping.
- **Transporting Hall's condition across a deleted family is not.** Both
  branches build `fun i => Nat.Finset.sdiff (nb i) (unionOver nb t)` and a new
  index set, and must re-establish `HallCondition` for it. That is a genuine
  counting argument — `card (unionOver nb' t') ≥ card (unionOver nb (t ∪ t')) −
  card (unionOver nb t)` — over a union whose bound changes at every step, and
  it is the piece that is neither a search nor bookkeeping.
- **Gluing two matchings into one `f : Nat → Nat`** needs the two images to be
  disjoint, which is where the critical subfamily's *definition* is finally
  consumed. `Nat.Finset.card_le_of_injOn` (ADR-1593) is the right tool and it
  exists; nothing relates the two images yet.

So the honest statement of where Hall stands: **the choice problem is solved,
the counting problem is not.** A lane taking the next slice should not size the
search again — it should size `unionOver` under family modification, and should
expect that to be the whole of the remaining work.

## Consequences

**What this costs.** Twelve new declarations (six definitions, six theorems, of
which `card_congr_of_memB` sits in `finset.rs`). The `nat_prelude::` sweep is
unchanged in shape: `anySubset` is never evaluated by the prelude build itself,
and the eleven new tests add ~0.4 s to a ~1.7 s targeted run because every
statement is over a variable `n` and only the tests instantiate.

**What it enables, beyond Hall.** Any "find a subset with property `P`, or
prove none exists" argument is now a two-line application. The nearest
consumers are the ones the combinatorics reviewer's file already lists —
Dilworth's theorem (an antichain is a subset), Turán (an independent set is a
subset), and the extremal half of most of the subject. `Nat.strongInduction`
is unconditionally reusable and eight existing modules could be rewritten
against it, though this lane rewrote none of them.

**What must not be inferred.** `anySubset P n` is a *bounded* search over `2^n`
codes and every numeral here is unary, so it is not an evaluation strategy for
anything beyond toy widths. Its value is that a `Prop` mentioning `pow 2 n`
never reduces it, so the LAWS are usable at a symbolic width even though the
search is not runnable there. A consumer that wants the search to actually
*run* is limited to about `n ≤ 4`.

## Mutation table

The general finding of ADR-1608 holds here and is worth restating, because it
is what makes the evaluation tests necessary rather than decorative: **almost
every mutation of a definition in this lane is caught by the kernel at
prelude-build time, not by a test**, since each definition is named by a
theorem whose proof term mentions its unfolding. The tests were written for the
residue the kernel *cannot* see — the pure value choices no theorem constrains.

| mutant | what happens | signal |
|---|---|---|
| `bitB` compares `testBit k i` against `0` instead of `1` | `bitB_encodeFrom`'s bottom-bit leaf runs on `beq (bool_select_nat b 1 0) 1 = b`, whose two literal branches become `beq 1 0 = true` and `beq 0 0 = false`. Neither is `refl`, so the theorem fails to type-check and the whole `Nat` prelude fails to build | caught by the KERNEL. `subset_search_tests::bit_b_reads_the_binary_digit` is the *readable* pin, not the only one — and it is the one that names the wrong answer (all four indices inverted) |
| `encodeFrom` recurses with `ih j` instead of `ih (succ j)` | `bitB_encodeFrom`'s step needs `succ_add j i`; with the start index frozen it would need `add j i = add j i` at the wrong offset and the `Nat` prelude fails to build | caught by the kernel |
| `decode n k` swaps its two arguments | `memB_decode_encode`'s `small` branch applies `memB_of_lt` at `bound (decode k n)`, which is `k`, not the `n` the hypothesis bounds; prelude fails to build | caught by the kernel |
| `anySubset` drops the OUTER `notB` (so it is the universal, not the existential) | both reflection lemmas invert: `existsSubset_of_search`'s `not_b_true_elim` no longer applies. Prelude fails to build | caught by the kernel; `any_subset_is_the_existential_over_subsets` is the readable pin and fails in BOTH directions (`true` becomes `false` at card 2, `false` becomes `true` at card 3) |
| `encode t n` uses start index `1` instead of `0` | nothing in the *statements* pins the start index: `memB_decode_encode` would then need `memB t (1 + i)`, so the kernel catches this one too — but the discriminating READABLE evidence is `encode_from_starts_at_its_index_and_walks_upward`, which pins `encodeFrom (hits 1) 2 0 = 2` against `encodeFrom (hits 1) 2 1 = 1` and names each as the other's wrong answer | caught by the kernel AND by a test that distinguishes the two codes |
| a theorem's STATEMENT slid by one small term | not visible to the kernel at all | caught by five accept/reject pairs, each offering the SAME proof term at the slid statement and requiring REJECTION: `bitB_encodeFrom` at `f (i + j)`; `encodeFrom_lt_pow` with the width and start index exchanged; `memB_decode_encode` with `Le n (bound t)` reversed; `existsSubset_of_search` at a `false` verdict and `forallSubset_of_search` at a `true` one (each is the other's control); `strongInduction_eq` unfolding at `succ n` while recursing below `n` |
| a new declaration added and left unwatched | not visible to any test that lists its own subject | caught by `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`, which derives its subject from the live environment. It **failed on its first honest run against this diff**, naming all twelve new declarations by name — a real observed failure, and the way the registration list was built |

## Verification

- `nat_prelude::subset_search_tests` — 11 passed, 0 failed (`--release`,
  `--test-threads=4`). Nonzero count confirmed.
- `nat_prelude::nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`
  derives its subject from the live environment and FAILED on the first honest
  run against this diff, naming `Nat.Finset.bitB`, `decode`, `encodeFrom`,
  `encode`, `anySubset`, `bitB_encodeFrom`, `encodeFrom_lt_pow`,
  `memB_decode_encode`, `existsSubset_of_search`, `forallSubset_of_search`,
  `Nat.strongInduction` and `Nat.strongInduction_eq`. All are now registered
  and so are covered by the kind, determinism and axiom-footprint sweeps.
- Every new `Definition` has an evaluation test at concrete small arguments
  (`n ≤ 3`) with a named wrong formula, and every new theorem an accept/reject
  pair; see the mutation table.
- The `shape_search` sweep this ADR quotes was run against a binary rebuilt at
  this lane's base commit: `declarations=2832`, positive control
  `--name Nat.Rado.IsRadoNumber --expect 1` FOUND, exit 0.
