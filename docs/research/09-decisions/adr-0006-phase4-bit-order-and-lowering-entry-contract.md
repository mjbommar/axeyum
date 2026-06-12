# ADR-0006: Phase 4 Bit Order And Lowering Entry Contract

Status: accepted
Date: 2026-06-11

## Context

Phase 4 starts the pure Rust path from bit-vector terms to SAT. The
foundational DAG requires the bit-order convention, circuit representation, CNF
encoding shape, and model-lift obligations to be recorded before public
bit-lowering APIs exist. Without that contract, bit-blasting can appear to work
while silently reversing bits, losing lift maps, or accepting assignments that
only satisfy the lowered formula.

This closes the Phase 4 entry questions:

- whether the first bit-blaster produces an AIG layer or direct CNF;
- what bit-order convention is public across evaluator values, wire vectors,
  DIMACS lift maps, and model reconstruction;
- whether AIG is the first circuit representation in the architecture.

## Decision

Use LSB-first bit-vector wire order, lower through an AIG layer before Tseitin
CNF, and preserve explicit lift maps from original terms to bits, AIG literals,
CNF variables, SAT assignments, and reconstructed Axeyum models.

Details:

1. A lowered `BV(w)` is an ordered vector of `w` Boolean wires where element
   `i` denotes SMT-LIB bit index `i` and numeric weight `2^i`. Element 0 is the
   least significant bit. A lowered `Bool` is a single Boolean wire. `Bool` and
   `BV(1)` remain distinct at the IR boundary; `BV(1)` lowers to a one-element
   bit-vector.
2. Constants and models convert through one shared value-to-bits routine and
   one inverse bits-to-value routine. These routines define the only public
   conversion between `Value::Bv` and wires. They are numeric conversions, not
   byte-order conversions: endianness of host bytes is irrelevant.
3. Operator lowering follows the LSB-first convention:
   - bitwise operators are pointwise over equal-index wires;
   - addition/subtraction ripple from index 0 upward and discard final carry
     according to fixed-width BV semantics;
   - equality reduces pairwise bit equality;
   - unsigned and signed comparisons inspect from the highest index downward;
   - `extract hi lo` returns source wires `lo..=hi`, reindexed to element 0;
   - `concat high low` returns all `low` wires first, then all `high` wires;
   - zero/sign extension appends high-order zero or sign wires;
   - ITE lowers to pointwise muxes for BV and one mux for Bool;
   - shifts and rotates use the shift-amount bit-vector's numeric value under
     the same LSB-first conversion. The exact symbolic-shift circuit shape is a
     later implementation choice, but it must satisfy the evaluator semantics.
4. The first circuit layer is AIG, not direct CNF. AIG literals use complemented
   edges, constants, inputs, and structurally hashed AND nodes. Deterministic
   node IDs and canonical ordering for commutative AND inputs are part of the
   contract. AIGER export is a debugging format after the circuit evaluator
   exists; it is not the semantic authority.
5. The first CNF encoder is simple Tseitin over AIG literals. More aggressive
   encodings are deferred until the simple path has evaluator checks, DIMACS
   round trips, lift-map replay, and benchmark artifacts. Direct term-to-CNF
   lowering is not a public Phase 4 path.
6. Every SAT result must lift through explicit maps:
   - original `TermId` plus bit index to AIG literal;
   - AIG literal to CNF variable plus polarity;
   - CNF assignment to AIG evaluation;
   - AIG bit values to Axeyum `Value`;
   - reconstructed model to original query replay.
7. `sat` is accepted only after the reconstructed Axeyum model evaluates the
   original pre-lowering query. `unsat` remains lower-assurance until a proof
   checker exists; the CNF encoder may report `unsat`, but high-assurance
   claims need the later proof path.

## Evidence

- The ground evaluator already defines the executable semantics for Bool and
  scalar BV, including shifts, rotations, division, and width edge cases.
- The Phase 3 exit audit records that default rewrites are exact-denotation,
  generated rewrite equivalence passes, query slicing replays models against
  original assertions, and benchmark artifacts carry enough provenance to add
  later bit-blaster/CNF fields.
- The bit-blasting and circuits/CNF notes already identify ordered wire
  vectors, model reconstruction, AIG structural hashing, Tseitin CNF, and
  reversible maps as the required shape.
- LSB-first order matches the numeric interpretation used by BV constants and
  makes ripple arithmetic and model reconstruction direct. It also makes each
  serialized lift-map entry unambiguous when paired with an explicit bit index.

## Alternatives

- Store wire vectors MSB-first. This aligns with some printed binary strings,
  but it makes arithmetic carry direction and SMT-LIB bit-index mapping more
  error-prone. Rejected because the evaluator and lowering should share one
  numeric bit-index convention.
- Lower terms directly to CNF first. This is initially tempting, but it loses a
  separately checkable circuit evaluator, AIGER debug path, and reusable
  structural hashing layer. Rejected for Phase 4.
- Treat AIG literals or CNF variables as the public bit-vector representation.
  Rejected because it would leak a lower encoding layer into bit-blaster APIs
  and make future circuit/CNF alternatives harder to slot in.
- Implement optimized encodings first. Rejected until the simple Tseitin path
  has correctness artifacts and baseline measurements.

## Consequences

Phase 4 implementation should start with shared value-to-bits and
bits-to-value helpers, then an AIG graph with evaluator tests, then bit-lowered
operator tests against the ground evaluator, then Tseitin CNF with DIMACS
round-trip and lift-map replay tests. Public support for an operator is not
complete until its lowered assignment lifts back to a model that satisfies the
original query.

Artifact schemas must gain bit-order, bit-blaster version, circuit encoder
version, CNF encoder version, lift-map digest or reference, assignment replay,
and later proof-checker fields as those layers become producers.
