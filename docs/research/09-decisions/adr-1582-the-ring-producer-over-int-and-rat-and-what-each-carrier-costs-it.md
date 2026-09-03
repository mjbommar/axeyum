# ADR-1582: the ring producer over ℤ and ℚ, and what each carrier costs it

Date: 2026-09-03
Status: Accepted
Lane: `ring-tactic-2`

Index-summary: `ring::int` and `ring::rat` extend ADR-1580's ℕ ring producer
to the constructed integers and rationals, closing the ℤ/ℚ gap that ADR-1580
left unbuilt. Along the way: ADR-1580's own ℕ producer had a documented,
tested incompleteness — no intra-monomial factor sorting, so `x*y = y*x`
declined — fixed here by `sort_factors`, `sort_items`'s multiplicative twin,
ported to all three carriers; ℤ needed `neg`/`sub` as real ring operations
(not declined, unlike ℕ's truncated `sub`), which forced two internally
derived primitives (`neg_neg`, `neg_mul`, both retirement targets of this
same producer and therefore unusable as its own primitives, ADR-1580's first
finding recurring on a second carrier) and a new capability ℕ never needed —
`cancel_pairs`, cancelling an adjacent `x + (-x)` after sorting, found
retiring `diff_of_squares`; ℚ needed **no** internal derivation (`Rat.neg_neg`
and `Rat.neg_mul` are already public theorems, cheaper to prove over a field
via `neg_eq_of_add_eq_zero`'s uniqueness argument) but got a **tighter**
coefficient cap than ℕ/ℤ's `MAX_COEFF = 4` — `count ∈ {-1, 0, 1}` — because
`Rat`'s numerals are normalized `num/den` pairs with no `succ`/`ofNat`-style
structural recursion to split for free, and none of its five retirement
targets need more. Ten more hand-written ring-rearrangement proofs retired
across the two carriers (five ℤ, five ℚ), one per carrier a declared theorem
(`Int.mul_sub`), the rest private proof-construction helpers, two of them
(`int_prelude/gcd.rs::neg_neg` and `int_prelude/fibonacci.rs::neg_neg`)
independent hand-written copies of the identical identity — the same
duplicated-helper shape ADR-1580 found eight of over ℕ, now confirmed on ℤ.

Index-status: Accepted

## Context

ADR-1580 landed `crate::ring` — a commutative-ring decision procedure over
ℕ that emits kernel proof terms rather than hand-written ones — and recorded
two things it did **not** finish: the ℤ/ℚ slice the design brief scoped, and
a documented sized incompleteness (no intra-monomial commutativity, so
`x*y = y*x` declined `NotAnIdentity`). Both were left as concrete next steps,
not open questions; this ADR closes them.

Step 0 (grepping `int_prelude`/`rat_prelude` for the same three-or-more
consecutive `add_assoc`/`add_comm`/`mul_comm`/`mul_assoc`/`left_distrib`
pattern ADR-1580's own step 0 used) found the ℤ analogue of ADR-1580's
`add_regroup_four` discovery almost immediately —
`int_prelude/fibonacci.rs::add_regroup_four`, the exact `(w+x)+(y+z) =
(w+y)+(x+z)` identity again — but it was **not** taken as a retirement
target: `linarith::int` (ADR-1576) already proves pure `add`/`neg`/`sub`
identities with no multiplication in them (confirmed directly —
`int_prelude/add_basics.rs::declare_add_left_comm` is already retired
through `linarith::declare`, not a hand chain), and lane `linarith-2` owns
order-chain sites in these same files concurrently. Every target actually
chosen below needs `mul` — the one thing `linarith` cannot reach
("`Int.mul` is not in this fragment at all", `linarith/int.rs`'s own module
docs) — so there is no territory overlap.

## Decision

### 1. The ℕ sized incompleteness is fixed: `sort_factors`

`ring::nat::Problem::sort_factors` ports `sort_items`'s adjacent-transposition
trick (`mul_assoc`/`mul_comm`/`symm(mul_assoc)`, three steps per swap) from
the outer additive sum to a monomial's own factor list, and
`combine_items`'s `Mono*Mono` branch now sorts the merged factor list before
returning it. `x*y = y*x` is now proved
(`ring::nat::tests::commuting_two_products_is_now_an_identity`), with a
negative control over the same factor set (`x*y = x*x`, still
`NotAnIdentity`). The identical construction — bubble-sort a factor list
with the three-step swap, `mul_assoc`/`mul_comm` in place of `add_assoc`/
`add_comm` — is reused verbatim in `ring::int` and `ring::rat`; two of the
five ℚ targets (`middle_swap`, `scale_sq`) need it directly, and it is what
makes ℤ's `diff_of_squares` (via `a*a`) and `int_prelude/gcd.rs::factor_out`
correct.

### 2. ℤ: `neg`/`sub` are real ring operations, and two primitives had to be derived internally

Unlike ℕ's truncated `sub` (declined, not a ring operation), `Int.sub a b :=
add a (neg b)` is a plain `Definition`, and `neg` distributes fully:
`flatten_neg` recognizes `neg` of a sum (`neg_add`), a product (`mul_neg`,
reversed), a double negation, or an atom, and rewrites accordingly — a
stronger commitment than `linarith::int`'s own choice to treat `neg` of a
compound as an opaque atom (sound for a certificate search; not sound enough
to retire the identities below, which need the full distribution).

`right_distrib`'s ℕ story repeats: `Int.add_left_comm`
(`int_prelude/add_basics.rs`) turned out to already be retired — through
`linarith::declare`, ADR-1576's own producer, not a hand chain — confirming
ADR-1580's caution that a producer's dependency list constrains what it can
retire generalizes past a single carrier. The two genuinely new primitives
this carrier forced are `neg_neg` (`neg (neg x) = x`) and `neg_mul` (`(neg
a)*c = neg (a*c)`): both are needed internally (`neg_neg` inside
`flatten_neg`'s double-negation case and `negate_fold`'s sign-flip; `neg_mul`
inside `apply_mono_signs`' sign-combination), and both are **also** among
this producer's own retirement targets
(`int_prelude/gcd.rs::neg_neg`/`neg_mul`,
`int_prelude/fibonacci.rs::neg_neg`) — exactly ADR-1580's "a producer cannot
retire its own primitives" trap, recurring on the second producer rather than
being an artifact of `linarith` specifically. The fix is the same shape too:
derive them **once, internally**, from lemmas that are not themselves
targets (`neg_one_mul`/`mul_assoc`/`mul_comm`/`one_mul`/the public
`mul_neg`), and route the retirement sites through the producer rather than
depending on the producer's own derivation.

### 3. ℤ needed a capability ℕ never did: cancelling `x + (-x)`

Retiring `int_prelude/wilson.rs::diff_of_squares` (`(a-1)*(a+1) = a*a - 1`)
against a normal form that only sorts and re-associates left an extra
`a + (-a)` pair on the left side (`a*a + a + (-a) + (-1)` versus the clean
`a*a + (-1)` on the right) — the hand proof's own last step,
`int_prelude/modeq.rs::cancel_common_addend`, is exactly this cancellation,
and `sort_items`/`sort_factors` alone do not perform it (ℕ has no negation,
so no ℕ target could ever have exposed this gap). `ring::int::Problem::
cancel_pairs` is a second fixpoint pass, after sorting: it walks adjacent
items, and whenever two are the same sorted monomial with opposite sign,
removes the pair via `add_neg` (`x + (-x) = zero`), `add_assoc`, and
`add_zero`/an internally derived left-`zero_add` (`Int` has no `zero_add`,
only the right-handed `add_zero`; `Rat` has both, so `ring::rat` never needed
this derivation). Two negative controls pin it: `a + (-a) + a = a` (must
**not** over-cancel into `0`) and cancellation at a genuinely interior
position (nonempty prefix and suffix), not just the head-of-list case
`diff_of_squares` itself exercises.

### 4. ℚ needed no internal derivation, but a tighter coefficient cap

`RatPrelude` already carries `neg_neg` and `neg_mul` as public theorems
(`Rat.neg_neg`/`Rat.neg_mul`, proved from `neg_eq_of_add_eq_zero`'s
additive-inverse-uniqueness argument — cheaper over a field than `ring::int`'s
`neg_one_mul`/`mul_assoc` chain), so `ring::rat`'s `flatten_neg` and
`apply_mono_signs` use them directly with no internal derivation at all. What
ℚ does **not** have is `ring::int::scale_unsigned`'s free numeral-splitting
reduction: `Int.add` between two `ofNat` applications reduces via a closed
iota/delta chain regardless of magnitude, which is what lets `ring::int`
unroll a coefficient by induction; `Rat`'s numerals are normalized `num/den`
pairs (`Rat.mk`/`Rat.normalize`), and `Rat.add` between two of them
cross-multiplies and re-normalizes through a genuine GCD computation — not a
`succ`-style structural recursion with a free reduction to lean on. Building
that bridge would need a `Rat`-numeral-arithmetic lemma this producer does
not have. None of the five ℚ targets need it, so `ring::rat::scale_item` is
capped at `count ∈ {-1, 0, 1}` — tighter than ℕ/ℤ's `MAX_COEFF = 4` — and
`as_numeral` itself only ever recognizes that range (`Rat.zero`/`Rat.one`/
`neg` of either), so the `CoefficientTooLarge` decline is currently
unreachable from any goal the producer's own recognizer can construct: a
literal `2` spelled `add one one` goes through the ordinary additive route
instead and still proves `2*t = t+t`
(`ring::rat::tests::a_numeral_two_spelled_as_one_plus_one_is_still_proved`).
A sound, documented, sized restriction — the fragment's own version of
ADR-1580's "no speculative capability with no test exercising it honestly"
rule, applied to the cap itself rather than to a missing feature.

### 5. Ten more retirements, five per carrier

**ℤ** (`int_prelude`): `gcd.rs::factor_out` (`A*mp + neg(A*mn) =
A*(mp+neg mn)`, private), `gcd.rs::neg_neg` and the independent duplicate
`fibonacci.rs::neg_neg` (`neg(neg x) = x`, both private — the same
"duplicated helper, unreachable to a name search" shape ADR-1580 found eight
copies of over ℕ), `fibonacci.rs::mul_two_eq_add_self` (`2*t = t+t`,
private), `wilson.rs::diff_of_squares` (`(a-1)*(a+1) = a*a-1`, private), and
the declared theorem `Int.mul_sub` (`sub.rs::declare_mul_sub`).

**ℚ** (`rat_prelude`): `matrix.rs::mul_sub_right_rev` (`k*x - k*y =
k*(x-y)`, private), `matrix.rs::factor_k_out_of_three` (`(k*x-k*y)+k*z =
k*((x-y)+z)`, private, built by chaining `mul_sub_right_rev` plus one more
`left_distrib` by hand — now one `ring::rat::prove_eq_at` call),
`matrix.rs::middle_swap` (`w*(x*y) = x*(w*y)`, private — needs
`sort_factors`), `matrix.rs::zero_mul` (`zero*x = zero`, private), and
`probability.rs::scale_sq` (`(a*w)*(a*w) = (a*a)*(w*w)`, private — also
needs `sort_factors`). All five are private proof-construction helpers with
no declared name; each test re-derives the exact statement and requires the
kernel to admit it as a fresh declaration, `ring::nat`'s
`retire_regroup_four` convention.

All ten route through `ring::int::prove_eq_at` / `ring::rat::prove_eq_at`
(or `declare`, for `Int.mul_sub`) uniformly, not only where an argument is
currently known to be non-ring — `ring::nat::prove_eq_at`'s own lesson
(ADR-1580 §2) that a retirement site's arguments must go through the generic
route regardless.

## The cost datum, beside `linarith`/`ring::nat`

Measured `--release`, `cargo run --release -p axeyum-lean-kernel --example
ring_cost`, 200 emissions per shape, prelude built once per shape:

| goal shape | search + emit | + kernel recheck |
| --- | ---: | ---: |
| `Int  A*mp + neg(A*mn) = A*(mp+neg mn)` | 1.945 ms | 2.468 ms |
| `Int  (a-1)*(a+1) = a*a - 1` | 3.189 ms | 3.507 ms |
| `Rat  w*(x*y) = x*(w*y)` | 3.051 ms | 3.989 ms |
| `Rat  (a*w)*(a*w) = (a*a)*(w*w)` | 4.400 ms | 5.086 ms |

A single unpinned run on a shared box, the same caveat ADR-1580's and
`linarith`'s own data carry: order-of-magnitude, not a ratchet baseline. The
ℤ shapes track ADR-1580's own ℕ figures (0.7-2.4 ms); the two ℚ shapes cost
roughly 1.5-2x the ℤ ones, tracking the deeper `RatPrelude` (Rat is
constructed over Int, so every `Rat` lemma application also carries the
embedded `Int`/`Nat` machinery `d.int()` reaches through) rather than
anything about `sort_factors` itself — both measured ℚ shapes exercise it.

## Consequences

- `ring::int` and `ring::rat` are the fourth and fifth ring-fragment
  producers in the ADR-0601 sense (ℕ, ℤ, ℚ), all behind
  `Kernel::add_declaration`.
- `ring::int::Problem::cancel_pairs` is sound and intentionally narrow: only
  *adjacent*, *syntactically opposite-signed*, *same-sorted-monomial* pairs
  cancel. `x + y + (-x)` with something genuinely between `x` and `(-x)`
  after sorting does not arise (sorting always makes same-monomial items
  adjacent), but a pair that is opposite-signed only up to a further
  normalization this producer does not do (e.g. `2*x + (-x) + (-x)`,
  needing coefficient accumulation across separately-arising summands) is
  outside what either `ring::int` or `ring::rat` compares as equal — sound,
  and not exercised by any of the ten new targets.
- `ring::rat::scale_item`'s `CoefficientTooLarge` branch is dead code under
  the producer's own `as_numeral` today — kept because `combine_items`'s
  `Num*Num` overflow check is the same kind of defensive bound, and because
  a future ℚ retirement target or a richer numeral recognizer could reach it;
  not a claim that any test currently exercises its failing side.
- ℤ and ℚ's declared-theorem/private-helper mix is asymmetric by nature of
  what each prelude's file organization already contained, not a producer
  choice: ℤ has one natural declared-theorem target (`Int.mul_sub`) among
  its five; ℚ's five are all private helpers, so `ring::rat::theorem`/
  `declare`/`RingError`/`Problem::parse_eq_goal` currently have no production
  call site (kept for API parity with `ring::nat`/`ring::int`, `#[allow(
  dead_code)]`'d with that reasoning stated inline rather than silently).

## Alternatives considered

- **A single sign-and-carrier-generic `Item`/`Problem` shared across
  `nat`/`int`/`rat`.** Rejected for the same reason ADR-1580 rejected a
  shared `+`/`*` normalizer skeleton: `ring::int` and `ring::rat` already
  diverge in real, carrier-forced ways (`ring::int` derives `neg_neg`/
  `neg_mul` internally and needs `cancel_pairs`; `ring::rat` uses public
  primitives and caps coefficients at magnitude 1; `ring::nat` has no sign at
  all and leans on raw ι-reduction for its own numeral unroll where neither
  of the other two can). Abstracting the shared bubble-sort skeleton across
  all three would have hidden three independently-motivated divergences
  behind one interface, which is worth keeping visible per ADR-1580's own
  "computed, not extracted" note (2026-08-27 architecture review).
- **Building `Rat`'s numeral-splitting bridge to lift the coefficient cap to
  `MAX_COEFF = 4`.** Deliberately not done: it needs a genuine `Rat`
  arithmetic lemma this producer does not have, none of the five targets
  need it, and an unexercised capability with no honest test is exactly the
  shape this repository's own standing rule asks contributors to avoid
  (ADR-1580's "no speculative `sort_factors` on ℕ" reasoning, now applied a
  second time to a different gap on a different carrier).

## Cross-references

- [ADR-1580](adr-1580-a-second-tactic-lands-and-its-own-primitives-cannot-be-its-targets.md)
  — the ℕ ring producer this ADR extends; every "found the hard way" finding
  above either confirms or extends one of ADR-1580's own three.
- [ADR-1576](adr-1576-a-tactic-is-a-producer-and-its-return-is-measured-in-retired-proofs.md)
  — `linarith`, whose ℤ fragment already owns pure `add`/`neg`/`sub`
  identities in these same files; this producer's five ℤ/five ℚ targets are
  chosen to need `mul`, which `linarith` cannot reach at all.
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) — producers
  behind one trust anchor.
