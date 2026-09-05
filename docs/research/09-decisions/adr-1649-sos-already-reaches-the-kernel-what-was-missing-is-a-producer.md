# ADR-1649: The sum-of-squares route already reaches the kernel; what was missing is a producer

Status: accepted
Date: 2026-09-05
Index-summary: Measured: an SOS certificate ALREADY becomes a term admitted by `Kernel::add_declaration`, axiom-free over the ordered-ring telescope and instantiable at `CReal` — for exactly one shape, and only as a REFUTATION. The gap was the positive direction, so this ADR adds `crate::psatz`, a Positivstellensatz producer over ℚ that takes the goal `a ≤ b` and returns a theorem, with a typed refusal and a checked dual witness for the Motzkin case.
Index-status: accepted

## Context — the claim this lane was briefed on, and what measuring it found

The lane brief and the board carried the claim: *"the sum-of-squares results
already exist as certificates; nothing reconstructs them."* Deliverable 0 was to
find out whether that is true by RUNNING the routes, before designing anything.

**It is false in the direction that matters and true in a different one.** Both
halves are worth writing down, because the design follows from the difference.

### What was run

| command | exit |
| --- | --- |
| `scripts/cargo-serialized.sh build --release -j 4 -p axeyum-solver --features full --example ordered_ring_refutation` | 0 |
| `./target/release/examples/ordered_ring_refutation --require-empty --footprint-table` | 0 |
| `./target/release/examples/ordered_ring_refutation --require-empty --constructed-reals` | 0 |
| `scripts/cargo-serialized.sh test -j 4 -p axeyum-solver --features full --test sos_lean_reconstruct --test nra_sos --test sos_evidence -- --test-threads=8` | 0 |

The three suites ran **9 + 5 + 14 = 28** tests, none filtered out, all passing.

### What the measurement says

**An SOS certificate DOES become a term admitted by `Kernel::add_declaration`
today.** The `ordered_ring_refutation` example's `sos-square` fixture (`x*x < 0`)
is admitted three times over:

```
real-specific   axeyum.reconstruct.lra.refutation.2       footprint 10
    AxReal, AxReal.le, AxReal.lt, AxReal.lt_irrefl, AxReal.lt_of_le_of_lt,
    AxReal.mul, AxReal.sq_nonneg, AxReal.zero,
    axeyum.reconstruct.lra.hyp.1, axeyum.reconstruct.lra.x.0
ordered-ring    axeyum.reconstruct.lra.ordered_ring_refutation.3   footprint 0
```

and, from the `--constructed-reals` run:

```
--- sos-square      x*x<0
    over AxReal: closed False -- footprint 32 of which 30 are CARRIER axioms
    over CReal : closed False -- footprint 2 of which 0 are CARRIER axioms  <== NONE
    setoid form: 39 ring binders -- footprint 0; kernel-`Eq` constants in the proof term: 0
```

So: the carrier is `AxReal` for the original, **zero carrier axioms** once
generalized over the 30-binder ordered-ring telescope, and the generalized
statement instantiates at the constructed reals with a footprint of 2 (the
variable and hypothesis constants, no carrier axioms). The route through
`generalize_over_ordered_ring` is `add_declaration(Declaration::Theorem)` twice,
with `Kernel::axiom_footprint` measured on the result and `--require-empty`
making the exit status depend on it.

### Three things the same measurement makes visible

1. **Exactly ONE SOS shape reaches `add_declaration`.** The
   `ordered_ring_refutation` fixture list is five entries and only `sos-square`
   is an SOS one. The wider family —
   `reconstruct_sos_multi_unit_square`, `reconstruct_sos_rational_weight`,
   `reconstruct_sos_rational_weight_gt`, `reconstruct_am_gm_two_var` — is gated
   only by `infer` + `def_eq False` inside `reconstruct_sos_to_lean_module` and
   then rendered to a Lean module STRING. Those terms are never declared and
   never footprint-measured.

2. **It is a refutation, not a theorem.** Every one of these routes takes an
   asserted `p < 0` and builds `False`. What comes out is a discharged
   contradiction. Nothing in the tree takes the positive goal `a ≤ b` and
   returns a proof of it, which is the shape a library cites and the shape the
   fact ledger records.

3. **There is a contentless fallback on the same path, and no test
   distinguishes it.** When `reconstruct_sos_proof` returns `UnsupportedTerm`,
   `reconstruct_sos_to_lean_module_raw` falls through to
   `reconstruct_sos_certificate_wrapper_to_lean_module`, which mints an opaque
   `Prop` constant, an axiom asserting it, and a second axiom `Not` of it, and
   applies one to the other. That term genuinely infers to `False` — and carries
   none of the mathematics. Both routes render through `LEAN_MODULE_THEOREM =
   "axeyum_refutation"`, and every content assertion in
   `crates/axeyum-solver/tests/sos_lean_reconstruct.rs` is
   `source.contains("axeyum_refutation")` or `fragment == ProofFragment::Sos`
   (the latter comes from `scan_proof_fragment`, which classifies the QUERY, not
   which route succeeded). *This last point is read from the source, not run: no
   command here demonstrates a wrapper module being accepted by a passing test.
   It is recorded as a code reading and as a suggested follow-up, not as a
   measurement.*

**Is the route registered as a producer under ADR-0602?** No. `evidence.rs`'s
`produce_nra_sos_evidence` builds an `Evidence::UnsatSos` carrying the
certificate and an OPTIONAL Lean module (`reconstruct_sos_to_lean_module(...).ok()`
— a failure silently becomes `None`). That is a retrospective receipt in exactly
ADR-0602's sense. `artifacts/autogenesis/producer-contracts/` held six contracts
before this lane and none of them was about SOS, nonlinear arithmetic, or any
`Rat`/`Real` order goal.

## Decision

1. **The existing SOS reconstruction stays as it is.** It is a refutation route,
   it works, and one of its shapes is measured axiom-free at `CReal`. This ADR
   does not touch it.

2. **Add `crate::psatz`, a Positivstellensatz PRODUCER**, in
   `axeyum-lean-kernel` beside `decide`/`linarith`/`ring`/`simp` — the four that
   ADR-1576 and ADR-1582 established as producers in ADR-0601's sense. Its
   contract:

   - **Input**: a goal `Rat.le lhs rhs`, plus zero or more hypotheses
     `Rat.le Rat.zero hᵢ`, and an optional dual witness.
   - **Output**: `Ok(ExprId)` — an unchecked term the caller pushes through
     `Kernel::add_declaration` — or `Err(psatz::Decline)`.
   - **No trusted surface of its own.** Every step of the emitted term applies a
     `RatPrelude` theorem, and the identity `M·(rhs − lhs) = Σ …` is proved by
     `ring::rat::prove_eq`, never asserted.

3. **The carrier is ℚ, not `CReal`**, and the reason is not the lemma inventory
   — both carriers have `sq_nonneg`, `mul_nonneg`, `add_nonneg`, `add_le_add`,
   and both are axiom-free. It is that **`ring::rat` exists**. The certificate's
   identity is the crux of every proof this producer emits, and `ring::rat` is
   the only ring normalizer in this kernel that closes one at a field carrier.
   `CReal`'s equality is the defined relation `CReal.Equiv`, so the same
   construction there needs a *setoid* ring producer this kernel does not have.
   The search, the certificate and the division step are all carrier-agnostic
   and live in `psatz.rs`; only `psatz/rat.rs` names `Rat`.

4. **The refusals are typed, and two of them are FINDINGS**, documented as such:

   - `NotPsd { pivot }` — the goal is FALSE. Sound because at total degree ≤ 2
     the Gram matrix over the affine basis `(1, x₁, …, xₙ)` is unique: there is
     no other matrix the search could have tried, and rational LDLᵀ decides
     PSD-ness exactly.
   - `PsdNotSos` — a supplied dual moment functional was **verified**: its
     moment matrix over the degree-`d` monomials is PSD and it is strictly
     negative on the difference, so the difference is not a sum of squares of
     degree-`d` forms.

   Every other variant (`GoalNotLe`, `HypothesisNotNonneg`, `NonPolynomial`,
   `DegreeUnsupported`, `DualWitnessInvalid`, `ScaleTooLarge`,
   `CertificateTooLarge`, `Overflow`, `Ring`) is a refusal to produce and says
   nothing about the goal.

5. **The producer CHECKS a non-SOS witness; it does not search for one.**
   Finding a dual moment functional is a semidefinite program. Verifying one is
   a PSD test on a small rational matrix plus one linear evaluation — and the
   PSD test is the same rational LDLᵀ the primal side already needed. So above
   degree 2 the producer declines `DegreeUnsupported` ("we did not look") unless
   a witness is supplied AND verifies, in which case it declines `PsdNotSos`
   ("this is not a sum of squares"). Those are different claims and the two
   variants keep them different.

6. **A denominator-clearing SCALE is part of the certificate**, and this is
   forced rather than convenient. `ring::rat` recognizes only the literals
   `{-1, 0, 1}` — a ℚ literal is a normalized `num/den` pair with no free
   structural reduction, so it is an opaque ATOM to the normalizer and a
   rational-weight identity would not close. The certificate therefore states
   `M·p = Σ (kₖ copies of ℓₖ′²)` with `M` and every `kₖ` a positive integer and
   every `ℓₖ′` integer-coefficient, and `divide_by_scale` takes `M` back out
   with `le_or_lt` plus a strict fold so it never reaches the statement.
   `a² + b² + c² ≥ ab + bc + ca` is what forces this: its Gram matrix has
   half-integer off-diagonals, so **no** unit-weight integer-form decomposition
   of it exists, and `4p = (2a−b−c)² + 3(b−c)²` is a fact about the polynomial,
   not about the implementation.

7. **The producer's output lands as prelude theorems**, in
   `rat_prelude/psatz_inequalities.rs`, with **no hand-written fallback**. If
   the producer stops finding these certificates the prelude does not build. A
   fallback would make "searched, not written" unfalsifiable.

## Coverage, and what is not covered

Discharged, each declared through `Kernel::add_declaration` and each measured
axiom-free:

| statement | certificate | scale |
| --- | --- | --- |
| `Rat.two_mul_le_sq_add_sq : ∀ x y, (x·y)+(x·y) ≤ x·x + y·y` | `(x−y)²` | 1 |
| `Rat.mul_add_le_sq_add_sq_three : ∀ a b c, (a·b + b·c) + c·a ≤ (a·a + b·b) + c·c` | `(2a−b−c)² + 3(b−c)²` | 4 |
| `Rat.four_mul_le_sq_add : ∀ a b, ((a·b+a·b)+(a·b+a·b)) ≤ (a+b)·(a+b)` | `(a−b)²` | 1 |

Refused, with the reason pinned by a test:

- **The Motzkin form** `x⁴y² + x²y⁴ + z⁶ − 3x²y²z²` refuses `PsdNotSos`, with
  the CAS's dual functional (`axeyum_cas::sos::corpus::motzkin_psd_not_sos`)
  transcribed and **verified in the producer**: the moment matrix over the ten
  degree-3 monomials is block-diagonal by parity into three singular PSD 3×3
  blocks plus the singleton `L(x²y²z²) = 9`, and `L(M) = 9 + 9 + 8 − 3·9 = −1 <
  0`. Without a witness the same goal refuses `DegreeUnsupported { degree: 6 }`,
  and with a broken witness `DualWitnessInvalid`. Three different answers to
  three different situations, each pinned.

The **Positivstellensatz step beyond pure SOS** lands exactly one shape:
`p = hᵢ·hⱼ + (a sum of squares)` for two supplied nonnegativity hypotheses,
discharged by `mul_nonneg` folded in beside the squares. The worked instance is
`0 ≤ x → 0 ≤ y → 0 ≤ x·y`, where `x·y` is provably not a sum of squares (Gram
matrix `[[0,½],[½,0]]`, indefinite) so the pure route reports `NotPsd` and only
the product closes it.

**Not covered, and declined rather than guessed at**: more than one product
term; a product of three or more hypotheses; a product carrying a multiplicity;
a product whose remainder is not itself degree ≤ 2; total degree > 2 with no
witness; `Rat.sub`/`Rat.inv`/`Rat.div`/`Rat.pow` anywhere in the goal (they are
definitions the ring normalizer does not unfold either); a scale above 64; a
form coefficient above 8; more than 32 squares; and any `i128` overflow in the
exact arithmetic, which stops the search rather than wrapping a coefficient into
a certificate the search would then believe.

`0 ≤ x → 0 ≤ y → 0 ≤ x·y` is **not** added as a prelude theorem or a fact: it is
`Rat.mul_nonneg`, which already exists and which the producer USES to discharge
the product shape. Recording it as a new result would be circular. It is a
covered shape, tested, and not a new theorem.

## Consequences

- The flywheel's reconstruction arrow now closes in the positive direction too:
  a goal in, a library theorem out, with nobody writing the proof.
- `tactic::rat` gains a `Psatz` arm and a second hypothesis list. The lists are
  separate because `linarith::generic` parses `Alg.OrderedRing` selector
  applications and `psatz::rat` parses `Rat.le`/`Rat.add`/`Rat.mul` directly
  (the terms `ring::rat` parses); one shared list would mean one producer
  silently seeing hypotheses it cannot read.
- `producer-contract-psatz-sum-of-squares-v1` is **born retired**, like
  `ring-identity-v1` and `linear-arithmetic-v1` beside it, and for the same
  structural reason: measured 2026-09-05 at ledger digest `ff28d776…`, the shape
  matches 91 facts and all 91 are already `proved`; the ledger holds 330
  `Rat`-fragment facts and **zero** open ones. The dispatch queue is empty
  because `Rat`'s order algebra was finished first, by hand. What the contract
  schema cannot see is that the producer added three theorems the day it landed
  that nothing in this kernel could previously produce.
- The `DegreeUnsupported` boundary is where the next slice is. Above degree 2
  the Gram matrix is not unique and the search becomes an SDP; a rational
  SDP over the free directions would take the producer from "quadratic forms"
  to "SOS", and the dual-witness checker is already the falsification side of
  it.

## Suggested follow-up, not done here

`reconstruct_sos_certificate_wrapper_to_lean_module` is a route that succeeds
with a module whose entire content is two axioms, and it renders under the same
theorem name as the real one. A test that counts `Declaration::Axiom`s in the
returned module — or asserts the module mentions the carrier's `sq_nonneg` —
would separate the two populations. It belongs to whoever owns
`crates/axeyum-solver/src/reconstruct.rs`, which this lane was told not to
restructure.
