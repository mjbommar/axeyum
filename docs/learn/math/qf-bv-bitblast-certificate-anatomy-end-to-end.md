# End To End: QF_BV Bit-Blast Certificate Anatomy

This lesson follows one finite-field resource from source claim to SMT-LIB,
bit-blasted CNF, emitted DRAT evidence, and corrupted-certificate rejection. It
uses [finite-fields-v0](../../../artifacts/examples/math/finite-fields-v0/).

Concept rows:

- `curriculum_fields`, `curriculum_modular_arithmetic`, and `curriculum_rings`
  in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_abstract_algebra` and `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `prime-field-inverse-table` | `sat` | replay-only |
| `prime-field-distributivity-no-counterexample` | `unsat` | checked |
| `composite-modulus-nonfield` | `unsat` | checked |
| `composite-modulus-nonfield-qf-bv-drat` | `unsat` | checked DRAT |

The checked proof-object source claim is fixed-width and finite:

```text
There is a 3-bit residue inv with inv < 6 and (2 * inv) mod 6 = 1.
```

This is the bit-vector version of the false claim that `2` has a multiplicative
inverse modulo `6`. The finite replay row can reject the claim by enumerating
residues. The QF_BV row instead lowers the fixed-width formula to CNF and
checks a DRAT refutation of that CNF.

## Source Artifact

The committed SMT-LIB artifact is:

```text
artifacts/examples/math/finite-fields-v0/smt2/composite-modulus-nonfield-bitblast-conflict.smt2
```

It contains the fixed-width obligation:

```smt2
(set-logic QF_BV)
(declare-fun inv () (_ BitVec 3))
(assert (bvult inv (_ bv6 3)))
(assert
  (= (bvurem (bvmul (_ bv2 6) ((_ zero_extend 3) inv)) (_ bv6 6))
     (_ bv1 6)))
(check-sat)
```

The width choices matter:

```text
inv          : 3 bits, enough to represent residues 0..7
inv < 6      : restricts the candidate to residues 0..5
zero_extend  : lifts inv to 6 bits before multiplication
2 * inv      : exact product for this finite domain
bvurem 6     : residue modulo 6
```

The assertion demands the impossible residue equation `(2 * inv) mod 6 = 1`.

## Bit-Blast And DRAT Certificate

The QF_BV route lowers the original bit-vector formula through deterministic
steps:

```text
BV term -> AIG -> Tseitin CNF -> SAT search -> DRAT proof
```

The DRAT certificate proves that the generated CNF is unsatisfiable. The
promoted resource regression is:

```sh
cargo test -p axeyum-solver --test math_resource_bv_routes finite_fields_composite_nonfield_emits_checked_drat
```

That test parses the source SMT-LIB artifact, checks the obligation is `unsat`,
exports the bit-blasted DIMACS plus DRAT proof, runs `UnsatProof::recheck`, and
then runs `Evidence::check` against the original assertions.

The important boundary is explicit: a plain DRAT proof checks the clausal
refutation of the generated CNF. The modular lowering, bit-blast, and Tseitin
steps are named trust steps until Lean reconstruction covers this source shape
end to end.

## Corrupted Certificate Rejection

The same source artifact has a tamper regression:

```sh
cargo test -p axeyum-solver --test math_resource_bv_routes qf_bv_resource_route_rejects_tampered_drat_certificate
```

It checks the genuine DIMACS/DRAT pair first, then removes the final nonempty
DRAT line. Without the final refutation step, the certificate must reject. If
the truncated proof still checked, the route would not be a trustworthy small
checker.

## Trust Boundary

Trusted:

- exact parsing of the committed source SMT-LIB artifact;
- pack-local finite replay of prime-field inverse tables and composite-modulus
  residue checks;
- deterministic exposure of the generated DIMACS and DRAT text;
- DRAT checking of the generated CNF;
- rejection of a truncated DRAT proof.

Not trusted by itself:

- the SAT search that found the contradiction;
- an unchecked DRAT certificate;
- the bit-blast/Tseitin lowering as a Lean-kernel proof of the original formula;
- finite-field replay as a proof of general field theory.

Reusable pattern:

- fixed-width finite rings and fields;
- small residue arithmetic where the width is part of the lesson;
- bounded graph-coloring encodings;
- bounded number-theory residue searches.

Remaining horizon:

- Lean reconstruction of the full original BV formula for this route;
- arbitrary-width or unbounded integer versions of the same arithmetic claim;
- general finite-field, algebraic-closure, and field-extension theorems.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-fields-v0
cargo test -p axeyum-solver --test math_resource_bv_routes finite_fields_composite_nonfield_emits_checked_drat
cargo test -p axeyum-solver --test math_resource_bv_routes qf_bv_resource_route_rejects_tampered_drat_certificate
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```
