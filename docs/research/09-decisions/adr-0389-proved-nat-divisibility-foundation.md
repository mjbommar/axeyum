# ADR-0389: Proved Nat divisibility as the first Rado library extension

Status: accepted

Date: 2026-08-13

Requirements:
[`lean-kernel-requirements-2026-08-13.md`](../../plan/lean-kernel-requirements-2026-08-13.md),
R4.3 / R7.1.

## Context

The zero-axiom Nat prelude has checked addition, multiplication, powers, and a
minimal `le` relation. The Rado capability development separately proved that
the kernel can define divisibility with `Exists`, introduce a multiplication
witness, and eliminate two witnesses to prove closure under addition. That
code lived only in one test namespace, so neither the next Rado theorem nor a
different mathematical consumer could depend on it as shared library surface.

All three paper theorems need divisibility. `thm:sharp`, the selected first
target, uses explicit facts such as `a | N`, `b | N`, `a | u`, and `a | Z`;
the later rigidity proof also needs congruence expressed through common
divisibility witnesses. Promoting the already checked core is therefore the
smallest dependency-ordered R4 increment with direct theorem demand.

## Decision

**Extend `build_nat_prelude` with the definition
`Nat.dvd a n := Exists (fun q => n = a * q)` and the checked theorems
`Nat.dvd_mul` and `Nat.dvd_add`, retaining zero axioms and whole-package
transactionality.**

The contract is:

1. `Nat.dvd` is a reducible definition, not a primitive proposition or axiom.
   The witness orientation is fixed as `n = a * q`.
2. `Nat.dvd_mul : forall a q, dvd a (a * q)` uses `Exists.intro` with witness
   `q` and definitional equality.
3. `Nat.dvd_add : forall a m n, dvd a m -> dvd a n -> dvd a (m + n)` uses two
   `Exists.rec` eliminations. Its witness is `q1 + q2`; the equality proof uses
   checked congruence and `Nat.left_distrib`.
4. The three names are part of the exact Nat prelude snapshot. Repeat builds
   must return the same handles, and a conflict anywhere in the package must
   retain the R1 rollback behavior.
5. No divisibility cancellation, transitivity, antisymmetry, modulo operation,
   Euclidean division, gcd, valuation, or decidability is implied. Each is a
   later proved-library increment.

## Evidence

- The earlier `rado_shell_arithmetic` capability probe independently admitted
  the same definition and two theorem shapes through the trusted kernel gate.
- Prelude tests classify `Nat.dvd` as a definition and both lemmas as checked
  theorems, render the complete deterministic package, and continue to find
  zero `Declaration::Axiom` rows.
- Positive consumer controls check `2 | 6` by `dvd_mul` and `2 | 10` by
  `dvd_add` from checked proofs of `2 | 4` and `2 | 6`.
- A negative control applies the valid `dvd_add` proof to the unrelated false
  target `2 | (4 * 6 + 1)` and requires a typed kernel rejection with no
  environment insertion.

## Alternatives

### Keep divisibility test-local until the whole number-theory library exists

Rejected. It would force each theorem development to duplicate the same
definition and witness-elimination proof, defeating the prelude boundary
established by ADR-0385.

### Add a Boolean or decidable divisibility test

Rejected. The theorem developments need propositions and witnesses, while a
computable decision procedure would introduce quotient/remainder dependencies
which R4 orders later.

### Add all familiar divisibility lemmas in one change

Rejected. Transitivity and cancellation have distinct proof dependencies and
negative controls. The two already executed lemma shapes form a smaller
reviewable base.

### Import Mathlib's divisibility layer

Rejected for this increment. R5's pinned closure and imported-axiom decision
remain open, while these three declarations are small, constructive, and
already proved in the in-tree kernel.

## Consequences

R4.3's prelude-level-definition requirement is met for the foundational
introduction/addition slice, and later divisibility lemmas can share one stable
meaning. The Nat prelude remains zero-axiom and pure Rust. `thm:sharp` is still
unproved: it also needs the R4.1 order/range fragment, R4.4 congruence, R4.5
interval/color membership, and R4.6 finite-sum/reindexing facts.
