# End To End: Diophantine Certificate Anatomy

This lesson follows one modular-arithmetic resource from source claim to
SMT-LIB, emitted Diophantine evidence, and corrupted-certificate rejection. It
uses
[modular-arithmetic-v0](../../../artifacts/examples/math/modular-arithmetic-v0/).

Concept rows:

- `curriculum_modular_arithmetic`, `curriculum_divisibility_and_euclid`, and
  `curriculum_fields` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_number_theory` and `field_abstract_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `crt-coprime-witness` | `sat` | replay-only |
| `modular-inverse-witness` | `sat` | replay-only |
| `composite-nonunit-no-inverse` | `unsat` | replay-only |
| `qf-lia-nonunit-diophantine` | `unsat` | checked |
| `qf-lia-incompatible-crt-diophantine` | `unsat` | checked |
| `fermat-units-mod-prime` | `unsat` | replay-only |

The checked proof-object source claim is finite and exact:

```text
There are integers b and k such that 2*b - 6*k = 1.
```

That equation is the solver-form version of the false modular inverse claim:

```text
2*b == 1 mod 6
```

The finite replay row can reject this by enumerating residues modulo `6`. The
Diophantine row proves the stronger integer obstruction directly: every value
of `2*b - 6*k` is divisible by `2`, but `1` is not.

The same pack now also checks an incompatible CRT pair by reducing
`x == 1 mod 4` and `x == 2 mod 6` to `4*a - 6*b = 1`, then replaying the
`gcd(4,6) = 2` non-divisibility obstruction.

## Source Artifact

The committed SMT-LIB artifact is:

```text
artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-diophantine-conflict.smt2
```

It contains the complete integer equality system:

```smt2
(set-logic QF_LIA)
(declare-fun b () Int)
(declare-fun k () Int)
(assert (= (- (* 2 b) (* 6 k)) 1))
(check-sat)
```

In normalized row form, this is:

```text
2*b + (-6)*k = 1
```

The coefficient gcd is:

```text
gcd(2, -6) = 2
```

Since `2` does not divide `1`, the row has no integer solution.

## Diophantine Certificate

An `UnsatDiophantine` certificate records enough data for the checker to
rebuild the contradiction from the original equalities:

```text
original equalities -> integer multipliers -> combined row
combined row        -> coefficient gcd     -> divisibility failure
```

For this one-row artifact, the combined row is already the source row:

```text
1 * (2*b - 6*k = 1)
```

The small checker re-derives the row and verifies:

```text
gcd(2, -6) = 2
2 does not divide 1
```

The promoted resource regression is:

```sh
cargo test -p axeyum-solver --test math_resource_lia_routes modular_nonunit_inverse_emits_checked_diophantine_evidence
```

That test parses the source SMT-LIB artifact, checks the obligation is `unsat`,
emits `Evidence::UnsatDiophantine`, and runs `Evidence::check` against the
original assertions.

## Corrupted Certificate Rejection

The same source artifact has a tamper regression:

```sh
cargo test -p axeyum-solver --test math_resource_lia_routes qf_lia_resource_route_rejects_tampered_diophantine_certificate
```

It checks the genuine certificate first, then changes the recorded
contradiction-row constant. The checker recomputes the row from the source
equalities, sees the mismatch, and rejects the certificate. If that corrupted
row still checked, the route would not be a trustworthy small checker.

## Trust Boundary

Trusted:

- exact parsing of the committed source SMT-LIB artifact;
- pack-local finite replay of CRT witnesses, modular inverse witnesses, and
  finite residue-search rows;
- integer Diophantine certificate checking against the original equalities;
- rejection of a tampered contradiction row.

Not trusted by itself:

- the integer search or elimination procedure that found the obstruction;
- an `UnsatDiophantine` certificate that has not been rechecked;
- finite modular enumeration as a proof of the general modular-inverse theorem;
- Fermat-style finite checks as a proof of Fermat's little theorem.

Reusable pattern:

- gcd obstructions in integer equations;
- nonunit modular inverse claims;
- parity and count contradictions;
- coefficient contradictions from finite generating-function or polynomial
  rows;
- integer boundary coefficients in finite homology rows.

Remaining horizon:

- arbitrary modular arithmetic theorems;
- full Chinese remainder theorem proofs;
- Fermat, Euler, and algebraic number theory results;
- integer nonlinear arithmetic beyond the current linear certificate route.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
cargo test -p axeyum-solver --test math_resource_lia_routes modular_nonunit_inverse_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_lia_routes modular_incompatible_crt_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_lia_routes qf_lia_resource_route_rejects_tampered_diophantine_certificate
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```
