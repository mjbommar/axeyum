# End To End: Proof Method Patterns

This lesson follows one proof-methods resource from small Boolean proof
obligations to replayed result and proof/evidence status. It uses the
[proof-methods-patterns-v0](../../../artifacts/examples/math/proof-methods-patterns-v0/)
pack.

Concept rows:

- `curriculum_proof_methods` and `curriculum_propositional_logic` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `direct-proof-modus-ponens-witness` | `sat` | checked |
| `contrapositive-equivalence-no-counterexample` | `unsat` | checked |
| `proof-by-cases-no-counterexample` | `unsat` | checked |
| `contradiction-refutation-unsat` | `unsat` | checked |
| `invalid-converse-counterexample` | `sat` | checked |
| `general-natural-deduction-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite Boolean assignment or truth-table rows. The pack
also carries a CNF proof regression for the contradiction/refutation row. It
does not claim soundness for a full natural-deduction calculus, sequent
calculus, or proof reconstruction engine.

## Encode

Each proof pattern is encoded as a finite Boolean obligation:

```text
direct proof:       p, p -> q therefore q
contrapositive:     p -> q iff !q -> !p
proof by cases:     (p -> r) and (!p -> r) imply r
contradiction:      p and (p -> q) and !q is unsat
invalid converse:   p -> q does not imply q -> p
```

SAT rows replay a listed assignment. No-counterexample rows enumerate every
assignment over the named variables.

## Replay Direct Proof

The direct-proof witness is:

```text
p = true
q = true
```

The checker verifies:

```text
p = true
p -> q = true -> true = true
q = true
```

So the concrete modus-ponens row is accepted.

## Check Contrapositive Equivalence

The contrapositive row searches for an assignment separating:

```text
p -> q
```

from:

```text
!q -> !p
```

The validator enumerates all four assignments for `p,q` and finds no
separating row. So the counterexample search is checked `unsat`.

## Check Proof By Cases

The proof-by-cases row asks whether this can happen:

```text
p -> r       is true
!p -> r      is true
r            is false
```

The validator enumerates all assignments to `p` and `r`. If `p` is true, the
first implication forces `r`; if `p` is false, the second implication forces
`r`. No assignment keeps both implications true while making `r` false.

## Check Contradiction

The contradiction row asks whether all of these can hold at once:

```text
p
p -> q
!q
```

If `p` and `p -> q` are true, then `q` must be true. That conflicts with `!q`.
The validator confirms this by enumerating every assignment to `p,q`, so the
premise set is checked `unsat`.

The CNF proof route encodes the same premise set as:

```text
p
not p or q
not q
```

This DIMACS artifact lives at
[`contradiction-refutation.cnf`](../../../artifacts/examples/math/proof-methods-patterns-v0/cnf/contradiction-refutation.cnf).
The proof-producing SAT core is untrusted search; the accepted evidence is the
independent DRAT check and the elaborated LRAT check.

## Replay An Invalid Converse Counterexample

The invalid-converse row uses:

```text
p = false
q = true
```

The checker evaluates:

```text
p -> q = true
q -> p = false
```

So the alleged inference from `p -> q` to `q -> p` is rejected by a concrete
counterexample.

## Name The Lean Horizon

The final row records the future proof-assistant target:

```text
soundness of direct, contrapositive, cases, contradiction, and
contradiction-elimination proof rules for a formal proof system
```

Finite Boolean obligations teach the executable shapes. A general proof
calculus needs a kernel-checked route.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_contradiction_refutation_emits_checked_drat_and_lrat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for proof methods:

```text
untrusted fast search -> candidate Boolean proof obligation or counterexample
trusted small checking -> assignment replay, truth-table enumeration, DRAT/LRAT checks, horizon row
```

The contradiction row now has a concrete CNF/DRAT/LRAT proof-object route. The
general proof-system soundness row still requires Lean artifacts that check the
broader theorem.
