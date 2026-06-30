# End To End: Finite Predicate Logic

This lesson follows one finite predicate-logic resource from explicit predicate
tables to replayed result and proof/evidence status. It uses the
[finite-predicate-v0](../../../artifacts/examples/math/finite-predicate-v0/)
pack.

Concept rows:

- `curriculum_predicate_logic` and `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_logic_and_proof` and `field_set_theory_and_foundations` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `forall-predicate-finite-replay` | `sat` | checked |
| `exists-predicate-finite-replay` | `sat` | checked |
| `forall-implies-exists-finite` | `unsat` | checked |
| `exists-not-forall-counterexample` | `sat` | checked |
| `binary-relation-symmetry-counterexample` | `sat` | checked |
| `general-first-order-lean-horizon` | `not-run` | lean-horizon |

The checked rows are finite-domain predicate-table rows. The pack does not
claim first-order validity over arbitrary or infinite domains, completeness,
compactness, or Lowenheim-Skolem-style theorems.

## Encode

The pack uses explicit finite universes. For a unary predicate `P` over
universe `U`:

```text
forall x in U. P(x)  ==  and_{u in U} P(u)
exists x in U. P(x)  ==  or_{u in U} P(u)
```

The validator rejects predicate tables whose keys do not exactly match the
universe. Quantifiers are checked by expanding them over the finite list of
elements.

For binary predicates, a relation is a table of true pairs:

```text
R(x,y) is true iff [x,y] appears in the pair list
```

## Replay A Universal Predicate

The universal witness has:

```text
U = {a,b,c}
P(a) = true
P(b) = true
P(c) = true
```

The checker expands:

```text
forall x. P(x)
```

to:

```text
P(a) and P(b) and P(c)
```

All entries are true, so the row is accepted as `sat`.

## Replay An Existential Predicate

The existential witness has exactly one true entry:

```text
P(a) = false
P(b) = true
P(c) = false
witness = b
```

The checker confirms `b` is in the universe and `P(b)` is true, so:

```text
exists x. P(x)
```

holds for this finite predicate table.

## Check Forall Implies Exists On A Non-Empty Finite Universe

The implication row searches for a unary predicate over `{a,b}` such that:

```text
forall x. P(x) holds
exists x. P(x) fails
```

The validator enumerates all four predicate valuations:

```text
P(a)=false, P(b)=false
P(a)=false, P(b)=true
P(a)=true,  P(b)=false
P(a)=true,  P(b)=true
```

None has all entries true while also having no true entry, so the
counterexample search is checked `unsat`.

The promoted solver-facing artifact records the same fixed expansion as CNF:

```text
P(a)
P(b)
not P(a)
not P(b)
```

That source DIMACS lives at
`artifacts/examples/math/finite-predicate-v0/cnf/forall-implies-exists.cnf`.
Axeyum's Boolean resource regression parses it, emits a DRAT proof, elaborates
that proof to LRAT, and checks both proof objects against the original CNF.
This proves the finite counterexample search is empty for this concrete
non-empty universe; it does not prove arbitrary-domain first-order validity.

## Replay Exists But Not Forall

The counterexample row uses:

```text
U = {a,b}
P(a) = true
P(b) = false
```

The checker verifies:

```text
exists x. P(x)   holds, with witness a
forall x. P(x)   fails, with counterexample b
```

This is why the reverse implication is false even in a tiny finite domain.

## Replay A Symmetry Counterexample

The binary relation row has:

```text
R(a,b) = true
R(b,a) = false
```

Symmetry would require:

```text
R(a,b) -> R(b,a)
```

The validator confirms the forward pair is present and the reverse pair is
absent, so it accepts the finite symmetry counterexample.

## Name The Lean Horizon

The last row is metadata:

```text
first-order semantic validity and completeness over arbitrary domains
```

Finite quantifier expansion is a useful executable slice. It is not a proof of
general first-order validity.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_predicate_forall_implies_exists_emits_checked_drat_and_lrat
```

Expected output:

```text
validated 1 foundational example pack(s)
```

## Trust Boundary

This lesson shows Axeyum's resource pattern for finite predicate logic:

```text
untrusted fast search -> finite universe, predicate table, witness/counterexample
trusted small checking -> finite quantifier expansion, valuation enumeration, relation replay, checked DRAT/LRAT for source CNF
```

General first-order reasoning over arbitrary domains requires stronger proof
routes or Lean/mathlib-scale proof support.
