# Lane: psatz-producer — the SOS route already reached the kernel; the missing half was the positive direction

<!-- plan-section: lane-status -->

**A Positivstellensatz producer over ℚ landed, and three inequalities now sit in
the `Rat` prelude with proof terms nobody wrote** (`DONE`, psatz-producer,
2026-09-05, ADR-1649).

## Deliverable 0 first, because the brief's premise was measurable and wrong

The board and the lane brief carried "the sum-of-squares results already exist
as certificates; nothing reconstructs them". Running the routes says otherwise.
`./target/release/examples/ordered_ring_refutation --require-empty
--footprint-table` (exit 0) shows the `sos-square` fixture `x*x < 0` admitted by
`Kernel::add_declaration` at `AxReal` with footprint 10, **generalized over the
30-binder ordered-ring telescope with footprint 0**, and the
`--constructed-reals` run (exit 0) instantiates it at `CReal` with footprint 2,
of which zero are carrier axioms. The three SOS suites ran 9 + 5 + 14 = 28
tests, all passing.

What is actually missing is narrower and more useful to name:

1. **Exactly one SOS shape reaches `add_declaration`.** The rest of the family
   (`_multi_unit_square`, `_rational_weight`, `_rational_weight_gt`, the
   hard-coded two-variable AM–GM) is gated only by `infer` + `def_eq False` and
   then rendered to a string. Never declared, never footprint-measured.
2. **Every one of those routes is a REFUTATION.** Asserted `p < 0` in, `False`
   out. Nothing took the positive goal `a ≤ b` and returned a proof of it — and
   that is the shape a library cites and the fact ledger records.
3. **Nothing was registered as a producer under ADR-0602.**
   `produce_nra_sos_evidence` carries an *optional* Lean module
   (`reconstruct_sos_to_lean_module(...).ok()`, so a failure is silently
   `None`), which is a retrospective receipt; none of the six existing producer
   contracts was about SOS or any order goal.

A fourth observation is recorded in the ADR as a **code reading, not a
measurement**: `reconstruct_sos_certificate_wrapper_to_lean_module` succeeds by
minting an opaque `Prop`, an axiom asserting it and an axiom `Not`-ing it, and
renders under the same `axeyum_refutation` theorem name as the real route — so
the content assertions in `sos_lean_reconstruct.rs` cannot separate the two
populations. Left as a follow-up for whoever owns `reconstruct.rs`, which this
lane was told not to restructure.

## What landed

`crate::psatz` — the fifth tactic-layer producer, beside
`decide`/`linarith`/`ring`/`simp`.

- `psatz.rs`, carrier-agnostic: checked `i128` rationals (an overflow declines
  rather than wrapping a coefficient into a certificate the search would then
  believe), multivariate polynomials, a rational LDLᵀ that **decides** positive
  semidefiniteness, the denominator-clearing pass, and a checker for a dual
  moment functional witnessing non-SOS-ness.
- `psatz/rat.rs`: parse, search, emit over `RatPrelude`. ℚ and not `CReal` for
  one reason — **`ring::rat` exists**, and the certificate's identity is the
  crux of every proof emitted. `CReal`'s equality is the defined relation
  `CReal.Equiv`, so the same construction there needs a setoid ring producer
  this kernel does not have.
- `tactic::rat` gains `Tactic::Psatz` and `Decline::Psatz`, plus its own
  hypothesis list — separate from `linarith`'s because that one parses
  `Alg.OrderedRing` selector applications and this one parses `Rat.le`/`Rat.add`
  /`Rat.mul` directly.
- `rat_prelude/psatz_inequalities.rs` declares three theorems whose proof terms
  the producer FOUND. **No hand-written fallback**: if the producer declines,
  the prelude does not build, because a fallback would make "searched, not
  written" unfalsifiable.

| theorem | certificate | scale |
| --- | --- | --- |
| `Rat.two_mul_le_sq_add_sq` | `(x−y)²` | 1 |
| `Rat.mul_add_le_sq_add_sq_three` | `(2a−b−c)² + 3(b−c)²` | **4** |
| `Rat.four_mul_le_sq_add` | `(a−b)²` | 1 |

The scale is **forced**, not chosen. The Gram matrix of `a²+b²+c²−ab−bc−ca` has
half-integer off-diagonals, so no unit-weight integer-form decomposition of it
exists at all; and the scale has to be cleared because `ring::rat` recognizes
only the literals `{-1, 0, 1}` — a ℚ literal is a normalized `num/den` pair with
no free structural reduction, so a rational weight is an opaque ATOM to the
normalizer and the identity would not close. `divide_by_scale` takes it back out
with `le_or_lt` plus a strict fold, so it never reaches the statement.

## The two refusals that are claims, and the one that is a check

`NotPsd { pivot }` says the goal is FALSE, and is sound because at total degree
≤ 2 the Gram matrix over `(1, x₁, …, xₙ)` is unique — there is no other matrix
the search could have tried. `PsdNotSos` says a supplied dual moment functional
**verified**. The producer never searches for one (that is an SDP); it checks
one, with the same rational LDLᵀ the primal side already needed. The Motzkin
form gets all three answers depending on what it is given: `DegreeUnsupported {
degree: 6 }` with no witness ("we did not look"), `PsdNotSos` with the CAS's
functional (`L(M) = 9+9+8−27 = −1 < 0` against a PSD moment matrix), and
`DualWitnessInvalid` with a broken one.

## Sized, and not done

- **Degree > 2 with no witness.** The Gram matrix stops being unique and the
  search becomes a rational SDP over the free directions. The dual-witness
  checker is already the falsification side of that, so the missing half is the
  primal search.
- **More than one Positivstellensatz product term**, a product of three or more
  hypotheses, a product carrying a multiplicity, or one whose remainder is not
  itself degree ≤ 2. The enumeration is bounded at unordered pairs on purpose.
- **`CReal`.** Needs a setoid ring producer; the search, the certificate and the
  division step are already carrier-agnostic and would move unchanged.
- **The `producer-contract-psatz-sum-of-squares-v1` dispatch queue is empty and
  the contract is born retired**, like `ring-identity-v1` beside it. Measured at
  ledger digest `ff28d776…`: the shape matches 91 facts and all 91 are already
  `proved`; 330 `Rat`-fragment facts, zero open. The whole open population is
  178 `Nat` + 80 `Int` Mathlib mirrors, carriers this producer does not serve.

## The mutation table — all six RUN, twice, none PREDICTED

Registered as `SUITES["psatz"]` in `scripts/tests/mutation_controls.py`. Run
once before the prelude theorems landed and once after, so the table records
what MOVED and why. Baseline 29 tests both times; exit 0 both times; `git
status` clean afterwards, with no diff in `psatz.rs` or `psatz/rat.rs`.

| mutant | before | after |
| --- | --- | --- |
| a cleared form's coefficient sign reaches the emitted term (the brief's first) | killed 5 | killed 12 |
| the verified-witness refusal is `PsdNotSos` and not something else (the brief's second) | killed **exactly 1** | killed **exactly 1** |
| a supplied dual witness is verified rather than believed | killed 1 | killed 1 |
| a negative LDL pivot is a `NotPsd` finding | killed 7 | killed 7 |
| a zero pivot beside a nonzero entry is a `NotPsd` finding | killed 3 | killed 3 |
| the denominator-clearing scale is divided back out | killed 1 | killed 12 |

The two rows that MOVED are the two whose mutation now also breaks
`build_rat_prelude` — which is precisely what the no-fallback design predicts,
and is better evidence for it than the prose in the module docs. The four that
did not move are exercised entirely by the search's own tests.

## Facts

Three, one per discharged inequality, `evidence` naming the producer:
`F:rat-two-mul-le-sq-add-sq`, `F:rat-mul-add-le-sq-add-sq-three`,
`F:rat-four-mul-le-sq-add`. Each carries a `kernel-term` row (the producing
`Kernel::add_declaration` plus a `rat_theorem_inventory` re-list), an
`exhaustive-enumeration` footprint row, and an `instance-pin` on the mutation
suite — with that last one explicitly saying it pins the PRODUCER's guards and
settles nothing about the statement, which the kernel-term row is what does.

`depends_on` is the measured direct-edge set from
`theorem_dependency_inventory`, one name per invocation, and every edge turned
out to be a registered ledger fact so nothing was dropped in the mapping. The
edge sets are themselves a finding: only the scale-4 theorem cites
`Rat.le_or_lt`, `Rat.le_of_lt`, `Rat.add_lt_add_of_le_of_lt`, `Rat.zero_add`,
`Rat.lt_of_le_of_lt` and `Rat.lt_irrefl` — the `divide_by_scale` lemma set —
and only it and nothing else does, so the division step is visible in the
ledger rather than only in the prose.

`0 ≤ x → 0 ≤ y → 0 ≤ x·y` is deliberately NOT a fact and NOT a prelude theorem:
it is `Rat.mul_nonneg`, which already exists and which the producer USES to
discharge the Positivstellensatz product shape. Recording it would be circular.
It is a covered shape with a test, not a result.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `23df33a55` | `crate::psatz`: checked `i128` rationals, multivariate polynomials, a rational LDLᵀ that DECIDES positive semidefiniteness, the denominator-clearing pass, and a checker for a dual moment functional witnessing non-SOS-ness. `psatz/rat.rs` is the ℚ instantiation — parse, search, emit — resting only on `RatPrelude` theorems plus `ring::rat::prove_eq` for the certificate's identity, which is proved and never asserted. |
| 2026-09-05 | `e2b0aa66d` | 27 tests: three discharges declared through `Kernel::add_declaration` and asserted axiom-free after `Environment::contains`; the Motzkin form refusing `PsdNotSos` with the CAS's dual functional VERIFIED here, `DegreeUnsupported` without one and `DualWitnessInvalid` with a broken one; and an adversarial fixture that flips a certificate weight's sign with the producer's own identity check off, so the KERNEL is the refuser — with a control declaring the honest certificate down the same path. |
| 2026-09-05 | `e94c8483c` | `Tactic::Psatz`/`Decline::Psatz` in `tactic::rat`, with its own hypothesis list because `linarith::generic` parses `Alg.OrderedRing` selector applications and `psatz::rat` parses `Rat.le`/`Rat.add`/`Rat.mul` directly. Two registry tests: `First([Decide, Ring, Linarith, Psatz])` closes `2xy ≤ x²+y²` with each of the first three asserted to decline individually, and the combinator forwards a psatz FINDING unchanged rather than flattening it. |
| 2026-09-05 | `94f0c6bc8` | ADR-1649 with the deliverable-0 measurement, and `producer-contract-psatz-sum-of-squares-v1`, born retired at a measured live population of zero (91 shape matches, all already `proved`; 330 `Rat` facts, none open). |
| 2026-09-05 | `0dfbb0606` | `Rat.two_mul_le_sq_add_sq`, `Rat.mul_add_le_sq_add_sq_three`, `Rat.four_mul_le_sq_add` — three prelude theorems with no hand-written proof body, declared LAST in `build_rat_prelude` because the producer reads twelve of its order/ring theorems and `ring::rat` nine more. Plus `examples/rat_theorem_inventory.rs`, the missing ℚ member of the `nat_`/`int_theorem_inventory` family: 454 derived, 454 axiom-free, 0 asserted, and a named filter matching nothing exits 1. |
| 2026-09-05 | `ed94ff551` | `SUITES["psatz"]` — six mutants, all killed, twice. |
