# Lane: chebyshev-pi — the primorial landed; the counting form is a held-out family

<!-- plan-section: lane-status -->

**The primorial and the sharp odd central binomial bound landed; Chebyshev's
lower bound in the counting form did NOT, and the obstruction is a blind
evaluation population rather than mathematics** (`WIP`, chebyshev-pi,
2026-09-05, ADR-1637).

`Nat.primorial n = prodRangeIf (fun i => beq (minFac i) i) (fun i => i)
(succ n)` — the product of every prime `p ≤ n` — with both `Eq.refl` defining
equations, the two-direction bridge `minFac n = n ↔ prime_condition n`, the
prime/composite successor equations, positivity and monotonicity; and
separately `Nat.choose_two_mul_succ_le_four_pow : ∀ m,
choose (succ (add m m)) m ≤ 4^m`, which is STRICTLY sharper than what
`Nat.choose_le_two_pow` gives at that row (`2^(2m+1) = 2·4^m`) and is the
arithmetic half of Erdős's proof.

**The predicate is `minFac`, not the `Nat.isPrime` already in the prelude.**
`Nat.isPrime` is a divisor COUNT and `prime_counting.rs` declares no theorem
about it (ADR-0653), so bridging it to `prime_condition` is a counting argument
in its own right. `min_fac_dvd.rs` already carries `min_fac_dvd`,
`min_fac_two_le` and `min_fac_prime`, and those three give both directions of
the `minFac` bridge with no new induction. `minFac 1 = 1` lets `i = 1` through
the predicate; it contributes the factor `1`, so the product is unchanged —
pinned by the evaluation test at `1, 1, 2, 6, 6, 30, 30, 210`.

**Deliverables 2 and 3 of the brief are held back on a partition check, and
this is the finding worth carrying forward.** Both are statements about
`Nat.primeCounting`. Five of the ten rows of the preregistered held-out family
`discrete-step-and-counting-bounds` are exactly the `Nat.primeCounting` shelf
(`monotone_primeCounting`, `monotone_primeCounting'`,
`primeCounting'_eq_zero_iff`, `primeCounting_add_le`, `primeCounting'_add_le`),
every one `partition: "held-out"`, and the family has never been scored — the
only committed evaluation record scores `integer-absolute-value`. The isolation gate PASSES with the primorial
shelf in the tree (`held_out=216 settled=0 references=0`); the objection is
ADR-0653's rule that *a family may be blind only if its mathematics is
unpublished*, and stating Chebyshev's lower bound over `Nat.primeCounting`
publishes the whole `Nat` half of `Mathlib.NumberTheory.PrimeCounting`.

**Measured, and worth the coordinator's attention: two of the ten rows are one
existing-lemma application away from the environment as it already stands.**
`Nat.primeCounting' = Nat.count Nat.isPrime`, `Nat.count` is definitionally
`Nat.countRange`, and `Nat.countRange_le_of_le : ∀ f m n, Le m n →
Le (countRange f m) (countRange f n)` has been in this prelude since the
counting shelf landed — that IS `Monotone Nat.primeCounting'` at
`f := Nat.isPrime`, and `Monotone Nat.primeCounting` follows through
`primeCounting n = primeCounting' (succ n)`. Nothing was declared, so nothing
is spent; but the family's blindness rests on nobody having written two lines,
not on difficulty. **W3-11's headline inequality cannot be landed by any lane
until the family is scored or amended (ADR-0542); that is a coordinator
decision, not a lane one.**

**Deliverable 3 already exists in its non-counting form.**
`Nat.exists_prime_gt : ∀ n, ∃ p, n < p ∧ prime p` — Euclid's theorem — is
admitted and axiom-free (`F:nat-exists-prime-gt`). Only its restatement as
`∀ k, ∃ n, k ≤ primeCounting n` touches the held-out family, and only that
restatement is missing.

**What is still open on deliverable 1, sized.** `Nat.primorial_le_four_pow`
did not land. Its strong induction and even step are both available; the odd
step needs `(∏ {p prime, m+1 < p ≤ 2m+1}) ∣ choose (2m+1) m`, i.e. a
divisibility law for a product over a predicate-restricted range with a
coprimality side condition. `subset_product.rs`'s module doc records that
`Nat.prodRange` has neither permutation invariance nor a swap lemma and that
the `Int` counterparts span ~650 lines and "took three drafts to close". That
is a lane of its own, not an addition to `primorial.rs`.

<!-- /plan-section -->
