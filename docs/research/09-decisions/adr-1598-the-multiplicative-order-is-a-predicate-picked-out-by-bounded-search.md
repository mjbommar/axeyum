# ADR-1598: The multiplicative order is a predicate picked out by bounded search, not a computed function

Status: accepted
Date: 2026-09-04
Lane: `primitive-roots`

Index-summary: Roadmap item W1-7 (the number theorist's first request: the
structure of `(ℤ/n)*`). `Int.IsOrder n a k` is a **predicate** — `0 < k` and
`a^k ≡ 1 (mod n)` and no smaller positive exponent does — not a `Nat`-valued
function, because a function would need either an abstract group carrier
(blocked on `Quot.sound`, W0-1) or a fresh modular-exponentiation definition
whose correctness proof is strictly more work than the whole rest of the
task. Existence is supplied by `Nat.lnp_bounded_search` at
`Q j := a^(succ j) ≡ 1` with bound `Nat.totient n`; the decidability
hypothesis is discharged by `Int.eq_em` (`ModEq` unfolds to an `Int`
equation, so deciding it is not excluded middle) and the bound by
`Int.euler_totient_theorem`. Eleven declarations landed axiom-free:
`Int.one_pow`, `Int.IsOrder`, `Int.pow_modeq_one_of_dvd`,
`Int.order_dvd_of_pow_modeq_one`, `Int.pow_modeq_one_iff_order_dvd`,
`Int.order_unique`, `Int.order_exists`, `Int.order_dvd_totient` (Lagrange in
the concrete case), `Int.IsPrimitiveRoot`, `Int.order_pow_eq_of_le` and
`Int.primitive_root_pow_injective` (the powers of a primitive root are
pairwise incongruent). Existence of a primitive root modulo a prime did NOT
land; the measured obstruction is `∑_{d|n} φ(d) = n`, which needs a sum over
the divisor set and there is no divisor-set aggregate in either prelude.
Index-status: accepted

## Context

`docs/math-department/01-number-theory.md` records the reviewer's verdict:
the elementary shelf is complete up to about 1830, and "primitive roots and
the structure of `(ℤ/n)*`... is elementary, it is reachable, and its absence
is the most surprising one given what is present." It is their first Next
Five item and roadmap item W1-7, gated on nothing.

Step 0 (`shape_search`, fresh build, `declarations=2674`, positive control
`Nat.Finset.pigeonhole` which landed the same day at `f91ded0c2`) confirms
absence: `--name-like primitiveroot`, `--name-like multorder` and
`--name-like ordn` all return ABSENT, and `--name-like order` returns only
the `Alg.OrderedRing` family, which is *order* in the relational sense.

What already existed and is reused rather than rebuilt:

- `Int.pow` with `pow_zero`/`pow_succ`/`pow_add`/`pow_mul` (`defs.rs`,
  `ring.rs`). The exponent is a `Nat` and `Int.pow` recurses on it.
- The `Int.ModEq` family (`modeq.rs`), 38 declarations, including
  `modEq_pow`, the unconditional `mod_eq_mul_general`, `modEq_cancel` and
  `mod_eq_dvd`.
- `Int.euler_totient_theorem` (`euler_assembly.rs`) and the whole
  `Nat.totient` family (20 declarations).
- `Nat.lnp_bounded_search` / `Nat.lnp_decidable` (`least_number.rs`).
- `Nat.div_mod_exists` with `Nat.divMod d n q r := n = d*q+r ∧ r<d`.
- `super::euler_totient::coprime_of_modeq_inverse`, already `pub(super)`
  precisely so a second consumer could reuse it.

## Decision

### 1. The order is a predicate, not a function

`Int.IsOrder : Int → Int → Nat → Prop` unfolds to

    fun n a k => 0 < k ∧ (ModEq n (pow a k) one ∧
                          ∀ j, 0 < j → j < k → ¬ ModEq n (pow a j) one)

Three routes were available and two were rejected.

**Rejected: an abstract `orderOf` over a group carrier.** This is the
textbook definition — the order of an element of the group `(ℤ/n)*` — and it
is the one that generalizes. It needs `(ℤ/n)*` as a carrier, which needs
quotients, which needs `Quot.sound`, which is W0-1 and undecided.
`01-number-theory.md` names this as the algebraic-number-theory blocker; the
whole point of W1-7 is that the elementary material does not have to wait for
it. **Cost of the rejected route: the entire W0-1 decision plus a quotient
construction, for material that is provably reachable without either.**

**Rejected: a computable `Nat`-valued `Int.orderOf n a` by structural
search.** This is what "defined by bounded search" most literally suggests
and it is what would make `ord_8(3) = 2` a one-line `Eq.refl` test. It costs:
a modular-exponentiation definition (`Int.pow` alone overflows the unary
numeral budget — `3^6 = 729` must be *formed*, and the search evaluates every
exponent up to `φ(n)`), a least-search combinator that does not exist as a
`Definition` (`Nat.lnp_bounded_search` is a THEOREM producing an
existential), and then a correctness proof relating the function to the
predicate — which is exactly the predicate-level work below, plus the
function. **Measured cost of the rejected route: strictly greater than the
whole delivered slice, for a strictly weaker deliverable, because every
theorem below would still have to be proved about the predicate.** The
concrete evaluation the function would have bought is bought instead by
`Kernel::def_eq` batteries in `mult_order_tests.rs`, which compute
`3^m mod 8` and `3^m mod 7` directly and assert BOTH the hits and the misses.

**Accepted: the predicate, with existence proved separately.**
`Int.order_exists` says every unit has an order; `Int.order_unique` says it
has only one. Together they are exactly the content of a function, without
the definition.

### 2. `Q` is stated at `succ j`, not at `j`

`Nat.lnp_bounded_search` finds the least `j` below a bound with `Q j`. At
`Q j := a^j ≡ 1` the answer is always `j = 0`, since `a^0 = 1` for every `a`.
Shifting to `Q j := a^(succ j) ≡ 1` makes the search's answer `mm` and the
order `succ mm`, which is positive by construction — the `0 < k` conjunct
needs no separate argument. The re-indexing cost is one step: a positive `j`
below `succ mm` is `succ i` with `i < mm`
(`Nat.zero_or_succ` then `Nat.le_of_succ_le_succ`).

### 3. Decidability is `Int.eq_em`, and that is not excluded middle

`Nat.lnp_bounded_search`'s decidability hypothesis is the one thing
separating it from the excluded middle it would otherwise imply
(`least_number.rs`'s own module doc; ADR-0603 row 2). Here it is discharged
constructively: `Int.ModEq n x y` is a `Definition` unfolding to
`Eq Int (emod x n) (emod y n)`, and `Int.eq_em` decides `Int` equations. So
`Int.order_exists` carries an empty axiom footprint and is not an
excluded-middle consumer in disguise.

### 4. Coprimality of `a^i` comes out of the order relation, not a
### multiplicativity lemma

`Int.primitive_root_pow_injective` needs `Int.modEq_cancel` at `a^i`, hence
`Coprime (a^i) n`. The development has no "`Coprime` is multiplicative"
lemma, and building one is a real slice. It is not needed: for `i ≤ t` write
`t = i + f`, and `a^t = a^i · a^f ≡ 1` says `a^f` IS a modular inverse of
`a^i`. `euler_totient.rs`'s already-`pub(super)`
`coprime_of_modeq_inverse` turns exactly that into `Coprime (a^i) n`. The
Bézout certificate was already sitting inside the order relation.

### 5. `Nat.lt zero n` is passed where `Int.lt zero (ofNat n)` is expected

The two are definitionally the same proposition. This is not a new
observation of this lane — `euler_assembly.rs` already feeds its `Nat.lt`
hypothesis straight to `Int.modEq_cancel` — but it is recorded here because
it is what makes `Int.order_dvd_totient` a one-liner rather than a lemma plus
a bridge.

## Evidence

Every declaration is read from the kernel, never from source text.

- `int_prelude::int_prelude_tests::every_int_declaration_is_checked_and_axiom_free`
  passes with all eleven names registered in
  `derived_laws`/`definition_names`. That test derives its population from
  `Kernel::environment()`, so an unregistered name fails it; both of this
  lane's intermediate runs did fail it, naming exactly the new declarations,
  which is the non-vacuity evidence that the registration is real.
- `int_prelude::mult_order_tests::mult_order_declarations_are_axiom_free`
  reads `Kernel::axiom_footprint` for each of the eleven and asserts the
  environment contains it first, so an absent name cannot pass as
  footprint-free.
- `is_order_unfolds_to_the_intended_conjunction` asserts the definition is
  `def_eq` to the intended conjunction AND **not** `def_eq` to the variant
  with the positivity comparison transposed. Without the second half the
  first proves nothing.
- `three_mod_eight_is_killed_by_exactly_the_even_exponents` computes
  `3^m mod 8` for `m ∈ {0,1,2,3,4,5}` and requires the hits at `{0,2,4}` and
  the misses at `{1,3,5}`. The misses are the negative control for
  `Int.pow_modeq_one_of_dvd`: at `m = 1` and `m = 3` the divisibility
  hypothesis fails and so does the conclusion, so a version of that theorem
  with the hypothesis dropped is refuted here.
- `multiplicative_order_of_three_mod_seven_is_six_by_reduction` is the
  brief's second case: misses at `m = 1..5`, hit at `m = 6`.
- `three_has_multiplicative_order_two_mod_eight` builds a kernel-checked
  `IsOrder (ofNat 8) (ofNat 3) 2` **and** a kernel-checked refutation of
  `IsOrder (ofNat 8) (ofNat 3) 4`. `φ(8) = 4`, so `4` is a genuine killing
  exponent and only the minimality conjunct separates it from the order: a
  definition that lost minimality would admit both and this test would fail.
- `primitive_roots_at_concrete_moduli` proves `IsPrimitiveRoot 3 2` and
  refutes `IsPrimitiveRoot 8 3`. The refutation is the discriminating case:
  `φ(8) = 4` while `ord_8(3) = 2`.

## Alternatives

Beyond the two rejected definitions in §1:

- **Stating everything over `ℕ` with `Nat.modEq`.** `Nat.modEq` exists and has
  a family of its own, but cancellation is the one step it cannot supply —
  `wilson.rs`'s module doc records that the transport is `ℕ → ℤ` only, which
  is why Fermat itself is kept over `ℤ`. The order development needs
  cancellation twice.
- **A `Coprime`-is-multiplicative lemma over `ℤ`.** Rejected per §4: not
  needed, and the route that avoids it is three lines.
- **Proving `ord_7(3) = 6` as a full kernel term.** Rejected on build cost:
  it would form `3^6 = 729` as a unary numeral *inside a proof term the
  prelude carries*, and it would need five separate refutations. The same
  mathematical content is asserted by reduction in a test that builds no
  proof term.

## Consequences

**What this unblocks.** `01-number-theory.md`'s Next Five item 1 is closed
for items 1–4 of the brief. The reviewer's stated ceiling ("everything present
is elementary number theory... and never leaves") is unchanged — this is more
elementary number theory — but the specific hole they called "the most
surprising one" is filled.

**What did NOT land, and why.** Existence of a primitive root modulo a prime
(item 5 of the brief, the real theorem). The standard route counts elements
of each order using `∑_{d|n} φ(d) = n`. The measured obstruction is that
identity's left-hand side: it is a sum over the **divisor set** of `n`, and
neither prelude has a divisor-set aggregate. `Nat.sumRange` folds over a
contiguous `[0,n)`; `Nat.countRange` counts a `Bool` predicate over a
contiguous range; `Int.prodRangeIf` (built for Euler's theorem) folds a
product over a predicate-restricted contiguous range. A sum of `φ(d)` over
`{d : d ∣ n}` can be *expressed* as `sumRange (fun d => if d ∣ n then φ(d)
else 0) (succ n)`, but every step of the standard proof then needs the
divisor-pairing bijection `d ↦ n/d` as a reindexing of that restricted sum —
and `euler_totient.rs`'s module doc already records that the analogous
restricted-product reindexing needed a remove-one-element induction that had
to be built from scratch. That is a slice of comparable size to this whole
ADR, and it is the honest next step for W1-7. It is **not** blocked on any
decision.

**Cost.** `mult_order.rs` is 1,689 lines for eleven declarations, of which
`Int.order_exists` (the bounded search, with two nested `Nat.zero_or_succ`
case splits and three `Exists` eliminations) and `Int.order_pow_eq_of_le`
(the cancellation argument) are roughly half. Nothing here needed a new
`Nat` lemma; every ingredient existed.
