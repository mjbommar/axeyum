# End To End: Proof Object Anatomy

This lesson follows one finite proof resource from mathematical claim to source
CNF, emitted proof objects, and corrupted-proof rejection. It uses
[proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/).

Concept rows:

- `curriculum_proof_methods`, `curriculum_propositional_logic`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `php-2-2-sat` | `sat` | checked |
| `php-3-2-unsat` | `unsat` | checked |

The source claim is finite:

```text
There is no injective placement of 3 pigeons into 2 holes.
```

Axeyum should not trust a solver saying `unsat` by itself. The trusted path is
the original CNF plus independently checked DRAT/LRAT proof objects.

## Source Claim

For `PHP(3,2)`, introduce one Boolean variable per pigeon/hole pair:

```text
1 = x_p0_h0
2 = x_p0_h1
3 = x_p1_h0
4 = x_p1_h1
5 = x_p2_h0
6 = x_p2_h1
```

The finite source constraints are:

```text
each pigeon chooses at least one hole
each pigeon chooses at most one hole
no two pigeons share one hole
```

The committed source artifact is:

```text
artifacts/examples/math/proof-methods-refutation-v0/cnf/php-3-2.cnf
```

It contains 6 variables and 12 clauses. The pack validator separately
enumerates all `2^6 = 64` Boolean assignments, so the educational source claim
is already checked before the proof-object route runs.

## Proof Objects

The Boolean proof route then treats the same CNF as the original obligation:

```text
source CNF -> proof-producing SAT search -> DRAT proof -> LRAT proof
```

The SAT search is useful but untrusted. The DRAT checker verifies that the
proof derives the empty clause against the source CNF. The LRAT checker follows
explicit hint chains and does less search than DRAT checking.

The promoted resource regression is:

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_emits_checked_drat_and_lrat
```

That test parses the source DIMACS artifact, emits a DRAT proof, elaborates it
to LRAT, checks both proof objects, serializes and reparses LRAT, and checks the
reparsed proof again.

## Corrupted Proof Rejection

A proof-object route is not useful unless bad evidence is rejected. The same
resource now has a tamper regression:

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_rejects_tampered_drat_and_lrat
```

It checks the good proof first, then corrupts the evidence in two direct ways:

```text
DRAT: remove the final empty-clause step
LRAT: clear the first addition's hint list
```

Both corrupted certificates must fail. If either corrupted proof still checked,
the route would not be a trustworthy small checker.

## Trust Boundary

Trusted:

- exact parsing of the committed source CNF;
- finite assignment replay in the pack validator;
- DRAT and LRAT proof checking against the source CNF;
- rejection of tampered proof objects.

Not trusted by itself:

- the SAT search that found the contradiction;
- a proof object that has not been checked;
- a future domain-to-CNF lowering unless its lowering evidence is explicit.

Remaining horizon:

- Lean reconstruction of the general Boolean proof route;
- general proof-system soundness theorems;
- arbitrary mathematical encodings whose source-to-CNF step is not yet checked.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_emits_checked_drat_and_lrat
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_rejects_tampered_drat_and_lrat
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```
