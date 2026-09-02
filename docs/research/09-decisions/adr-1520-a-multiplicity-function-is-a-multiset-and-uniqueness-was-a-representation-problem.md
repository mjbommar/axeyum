# ADR-1520: a multiplicity function is a multiset, and "uniqueness is not expressible here" was a representation problem

Date: 2026-09-02
Status: Accepted
Lane: `nat-multiset`

Index-summary: `docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
§6 concedes that uniqueness of prime factorization "is not expressible here at
all" — no `List`, no `Finset`, no quotient by permutation — and
`nat_prelude/factorization.rs`'s module doc says the same about the route it
takes. The concession is about a REPRESENTATION, not about the theorem. A
multiset over ℕ is a multiplicity function that is eventually zero, and
"eventually zero" is witnessed by a `Nat` bound; both are expressible in this
kernel today. `Nat.Multiset` (`nat_prelude/multiset.rs`) is a one-constructor
inductive `mk : (Nat → Nat) → Nat → Multiset` whose `count` **truncates at the
bound in its own definition**, and
`Nat.Multiset.count_eq_of_prod_eq : ∀ m₁ m₂, (every element of m₁ prime) →
(every element of m₂ prime) → prod m₁ = prod m₂ → ∀ p, count m₁ p = count m₂ p`
is a checked, axiom-free theorem. Nothing in the kernel changed. Order is never
represented, so there is nothing to quotient by; that is why the trusted surface
stays empty (`Kernel::axiom_footprint` = [] for all ten `Nat.Multiset.*`
theorems, read from the kernel, not from a list). ADR-0603's graded statement
family: this is ROW 1, the general constructive form. The COMPUTED form — a
`Nat.factorization` by trial division with `prod (factorization n) = n` — is
deliberately NOT part of this and was not attempted; it needs a product-splitting
law across two different bounds, which is separate work and is sized below.
Index-status: Accepted

## Context

Two places in the tree record uniqueness of prime factorization as out of reach.

`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
§6, on the third domain:

> uniqueness of prime factorization … is not expressible here at all: no
> `List`, no `Finset`, no quotient by permutation

`crates/axeyum-lean-kernel/src/nat_prelude/factorization.rs`'s module doc, which
proves the EXISTENCE half:

> Uniqueness needs multiset equality of the factor list, which needs a type this
> kernel does not have, and is **not attempted here**.

Both statements are accurate about the object they are talking about.
`factorization.rs` represents a factorization as an anonymous pair `(k, f)`
inside an `Exists` — a length and an indexing function — and two of those really
can only be compared by exhibiting a permutation between the index ranges, which
really does need machinery this kernel does not have.

What neither says, and what this ADR decides, is that a factorization does not
have to be represented that way.

## Decision

**Represent a multiset over ℕ as a multiplicity function together with a bound,
and state uniqueness as multiplicity agreement.**

```text
inductive Nat.Multiset : Type
  | mk : (Nat → Nat) → Nat → Nat.Multiset

Nat.Multiset.count m p := if p < bound m then raw m p else 0
Nat.Multiset.prod  m   := prodRange (fun q => q ^ count m q) (bound m)
```

Three design choices carry the whole thing, and each is a decision rather than a
detail.

### 1. `count` truncates inside its own definition

The alternative is a well-formedness predicate — "this function is zero above
this bound" — carried as a hypothesis on every downstream statement, and as a
proof obligation on every use of `mk`. Truncating instead makes

```text
Nat.Multiset.count_eq_zero_of_bound_le : ∀ m p, bound m ≤ p → count m p = 0
```

a THEOREM about every multiset with no side condition. Nothing downstream threads
an "is bounded" premise; `Nat.Multiset.mk` applies to any function at any bound.

The cost is that `raw` is not observable above the bound, and that is the correct
semantics rather than a compromise: two multisets that agree below their bounds
and disagree above them ARE the same multiset. The test file pins this in both
directions (`raw (mk (fun _ => 1) 2) 7 = 1` while `count … 7 = 0`), so a `count`
defined as `raw` and a `raw` defined as `count` both fail.

### 2. Uniqueness is stated at the level of counts, not as an `Eq` of multisets

```text
Nat.Multiset.count_eq_of_prod_eq :
  ∀ m₁ m₂,
    (∀ q, 0 < count m₁ q → prime q) →
    (∀ q, 0 < count m₂ q → prime q) →
    prod m₁ = prod m₂ →
    ∀ p, count m₁ p = count m₂ p
```

Two multisets with equal counts everywhere are NOT `Eq` at type `Nat.Multiset` —
their `raw` functions may differ above the bound, and their bounds may differ.
Making them `Eq` would need function extensionality plus a quotient, i.e. exactly
the machinery the concession says is absent. Stating the conclusion pointwise
needs neither, and it is the stronger-in-practice statement: every consumer of
"the factorizations agree" wants the multiplicity of a particular prime.

`Nat.Multiset.beq` exists as a `Bool`-valued bounded loop, with `beq_refl` and
`beq_comm` and NOTHING else claimed about it. In particular there is no
`beq m₁ m₂ = true ↔ ∀ p, count m₁ p = count m₂ p`; that is a real theorem and it
is not asserted here.

### 3. Primality is spelled inline, matching `euclid_lemma`'s convention

`2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`. This prelude has no `Prime` predicate, and
`Nat.euclid_lemma`, `Nat.exists_prime_dvd` and `factorization.rs` all already
spell it this way. Introducing one here would have made every existing prime
lemma need a bridge.

## What the carrier deliberately does not provide

- **No permutation quotient**, and none is needed: order is never represented.
  This is why no `propext` and no `Quot.sound` appears anywhere in the module and
  the axiom footprint of all ten `Nat.Multiset.*` theorems is `[]`, read from
  `Kernel::axiom_footprint` (`theorem_axiom_footprint` prints size 0 and an empty
  axiom column for each) rather than from a maintained list.
- **No `Finset`.** The support is bounded by construction and every fold is
  `Nat.prodRange` / `Nat.sumRange` over `[0, bound)`.
- **No extensional equality of multisets**, per §2 above.
- **No `Nat.factorization`.** See "what was not attempted".

## The proof, and the two general lemmas it produced

`Nat.Multiset.pow_count_dvd_prod` (no hypotheses) and
`Nat.Multiset.not_pow_succ_count_dvd_prod` (with primality) together say that
`count m p` IS the `p`-adic valuation of `prod m` — this prelude's own
`Nat.valuationAt p (prod m) (count m p)`, which existed as a definition with no
uniqueness lemma. Uniqueness is then that a valuation is determined by the value
it is a valuation of.

Two lemmas fell out that mention no multiset and are declared in `multiset.rs`
only because it is their first consumer:

- **`Nat.exponent_unique_of_exact_dvd`** — `p^c₁ ∣ n`, `¬ p^(c₁+1) ∣ n`, and the
  same at `c₂`, force `c₁ = c₂`. It needs NO primality: `c₁ < c₂` already makes
  `p^(c₁+1)` divide `p^c₂` and hence `n`.
- **`Nat.prime_pow_dvd_of_dvd_mul_of_not_dvd`** — `p` prime, `p ∤ b`,
  `p^c ∣ a·b` ⊢ `p^c ∣ a`. An induction on the EXPONENT with `a` quantified
  inside the motive (the step replaces `a` by `a/p`), using only `euclid_lemma`
  and left-cancellation.

The second is a finding about the prelude, not a stylistic choice. It does not
route through `Nat.Coprime` because it cannot: this prelude has
`prime_coprime_pow_of_not_dvd` (a prime coprime to a POWER) and nothing giving
coprimality of a prime POWER with anything, which is exactly what
`coprime_dvd_mul_right` would need. Anyone reaching for a coprime-cancellation
argument over prime powers here should reach for this lemma instead.

## What was NOT attempted, and what it would cost

The brief for this lane also asked for a computed factorization:

1. `Nat.factorization : ℕ → Multiset` by trial division with fuel,
2. `prod (factorization n) = n` for `n > 0`,
3. `0 < count (factorization n) p → prime p`.

**None of these landed, and none was started.** They are not blocked by anything
this ADR decides, but they are not cheap either, and the reason is worth
recording so the next lane does not re-derive it:

`factorization` by trial division is naturally `add (singleton (minFac n))
(factorization (n / minFac n))` — `Nat.minFac` and `Nat.minFacAux` already
exist — and proving `prod` of that equals `n` needs

```text
prod (add m₁ m₂) = prod m₁ * prod m₂
```

which is a product-regrouping law across THREE different bounds (`bound m₁`,
`bound m₂` and their sum), not a corollary of anything in this module.
`Nat.prodRange_split` exists on the `Int` side (`Int.prodRange_split`) and the
`Nat` side has `Nat.prodRangeIf`; whether either transports is an open question
this lane did not test. Note also that the sibling route — converting
`Nat.exists_prime_factorization`'s `(k, f)` witness into a multiset by
`countRange (fun i => beq (f i) q) k` — needs the same regrouping law, so it is
not a way around it.

Uniqueness does not depend on any of that, which is why it landed first.

## Consequences

- **`docs/formalized-math-2026-08/09-…md` §6's concession is now false as
  written** for the uniqueness row, and the fact
  `F:nat-multiset-prime-factorization-unique` records the replacement. The
  document is not edited by this lane; whoever next revises §6 should read this
  ADR and the fact rather than the old sentence.
- `external_status` on that fact is `proved`. Uniqueness of prime factorization
  is classical mathematics and nothing here is a new mathematical result; the
  only novelty claimed is that this system can now state and check it.
- Seven facts registered, all `epistemic_status: proved` with empty
  `axiom_footprint` and checkers whose exit status depends on the finding
  (each verified by running the command with the theorem name perturbed and
  requiring a non-zero exit before the fact was written).
- `Nat.Multiset` adds a fourth non-`Prop` inductive to this prelude
  (`Nat`, `Nat.Fin`, `Nat.Pair`, `Nat.Multiset`). It is the first one carrying a
  FUNCTION field. Positivity is trivial (`Nat → Nat` does not mention the
  carrier) and large elimination is available, so `raw` and `bound` are ordinary
  `Multiset.rec` projections.
- `Nat.Multiset.add`'s bound is the SUM of the two bounds, not the maximum.
  `Nat.max` lives in the `Max` namespace here (`minmax.rs`) and its comparison
  lemmas are stated there; `Nat.add` needs none of them, is at least as large,
  and leaves `count_add` unchanged. The price is that `beq_comm` takes two steps
  (swap the functions at a fixed width with `eqBelow_comm`, then move the width
  with `add_comm`) instead of one.

## Alternatives considered

- **Add `List` and a permutation quotient.** This is what the concession assumes
  is required. It is a much larger change — a new inductive family, a
  `Perm` relation, a quotient, and `Quot.sound` in the trusted surface — and it
  buys a statement no stronger than the one above for this purpose.
- **State uniqueness over the existing `(k, f)` representation.** This is the
  route `factorization.rs` correctly describes as needing a permutation. Nothing
  about it is wrong; it is simply the expensive way to reach the same conclusion.
- **Carry boundedness as a hypothesis instead of truncating.** Rejected under §1:
  it puts a premise on every downstream statement and a proof obligation on every
  `mk`, in exchange for making `raw` observable above the bound, which is not a
  property anyone wants.
