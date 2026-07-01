# End To End: Bounded Number Theory

This lesson follows one bounded number-theory resource from CRT compatibility
to residue, square-sum, and Diophantine checks. It uses the
[number-theory-v0](../../../artifacts/examples/math/number-theory-v0/) pack.

Concept rows:

- `curriculum_number_theory`, `curriculum_divisibility_and_euclid`, and
  `curriculum_modular_arithmetic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `crt-compatible-noncoprime-witness` | `sat` | checked |
| `quadratic-residue-witness` | `sat` | checked |
| `quadratic-nonresidue-rejected` | `unsat` | checked |
| `quadratic-nonresidue-qf-bv-drat` | `unsat` | checked |
| `bad-square-witness-rejected` | `unsat` | checked |
| `bad-square-witness-qf-bv-drat` | `unsat` | checked |
| `sum-two-squares-witness` | `sat` | checked |
| `sum-two-squares-mod4-rejected` | `unsat` | checked |
| `bounded-diophantine-witness` | `sat` | checked |
| `diophantine-gcd-obstruction-qf-lia` | `unsat` | checked |

The pack is a bounded compute-and-check surface. It does not claim the full
Chinese remainder theorem, quadratic reciprocity, the two-squares theorem, or
the infinitude of primes.

## Replay A Non-Coprime CRT Witness

The CRT row records:

```text
x = 8
x == 2 mod 6
x == 8 mod 10
```

The validator checks both congruences and checks compatibility modulo the gcd:

```text
gcd(6, 10) = 2
2 == 8 mod 2
```

The witness works even though the moduli are not coprime.

## Replay And Reject Quadratic Residues

The residue witness records:

```text
4^2 == 5 mod 11
```

The validator recomputes `16 mod 11 = 5`. The negative row asks for:

```text
x^2 == 3 mod 7
```

The validator enumerates all residues modulo `7` and finds no square root for
`3`.

The promoted solver-facing row encodes the same finite claim as QF_BV:

```text
x < 7
(x * x) mod 7 = 3
```

`x` is a 3-bit residue and the square is computed at 6-bit width before
`bvurem 7`, so the bit-vector formula is an exact finite-domain encoding. The
route test exports the bit-blasted CNF, checks a DRAT refutation, and leaves
modular lowering plus bit-blast/Tseitin as explicit trust steps for future Lean
reconstruction.

The pack also rejects a malformed proposed witness:

```text
2^2 == 2 mod 7
```

The validator recomputes `2^2 mod 7 = 4`. The QF_BV row computes the same
fixed-width product and refutes the false target by requiring the reduced
product to equal both `4` and `2`.

## Replay And Reject Two-Squares Claims

The positive row records:

```text
65 = 1^2 + 8^2
```

The validator recomputes the equality exactly. The negative row asks for:

```text
7 = a^2 + b^2
```

The trusted check uses the fixed mod-4 obstruction:

```text
7 == 3 mod 4
squares mod 4 are only 0 or 1
```

So no sum of two integer squares can equal `7`.

## Replay A Diophantine Witness

The linear Diophantine witness records:

```text
14*x + 21*y = 7
x = -1
y = 1
```

The validator checks:

```text
14*(-1) + 21*1 = 7
```

The QF_LIA row records the matching unsatisfiable shape:

```text
14*x + 21*y = 5
gcd(14, 21) = 7
7 does not divide 5
```

The SMT-LIB artifact encodes the fixed equation. Axeyum emits
`UnsatDiophantine` evidence and rechecks the gcd-divisibility obstruction
against the original terms. Together, the two rows show both sides of the
bounded Diophantine boundary: a satisfiable equation with a witness and an
impossible equation with a small certificate.

## Name The Lean Horizon

The pack explicitly leaves deeper number theory to proof reconstruction:

```text
quadratic reciprocity
full two-squares theorem
unique factorization
infinitely many primes
```

The bounded rows are still useful because each has a small checkable artifact:
a witness, a finite residue enumeration, or a modular obstruction.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/number-theory-v0
cargo test -p axeyum-solver --test math_resource_bv_routes number_theory_quadratic_nonresidue_emits_checked_bv_drat
cargo test -p axeyum-solver --test math_resource_bv_routes number_theory_bad_square_witness_emits_checked_bv_drat
cargo test -p axeyum-solver --test math_resource_lia_routes number_theory_diophantine_gcd_obstruction_emits_checked_diophantine_evidence
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's current number-theory resource pattern:

```text
untrusted fast search -> residue, square-sum, or Diophantine candidate
trusted small checking -> exact integer replay, finite enumeration, mod obstruction, checked DRAT or UnsatDiophantine
```

The first graduation steps are now landed for residue checks: the modulo-7
nonresidue search and the bad square-root witness are tied to deterministic
QF_BV/DRAT evidence. The Diophantine obstruction now also has checked QF_LIA
evidence. Remaining graduation work is carefully scoped BV/LIA artifacts for
CRT or two-squares examples that add new solver pressure.
