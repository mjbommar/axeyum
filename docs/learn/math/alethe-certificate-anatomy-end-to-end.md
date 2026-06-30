# End To End: Alethe Certificate Anatomy

This lesson follows one equality-heavy finite-structure resource from source
claim to SMT-LIB, emitted Alethe evidence, and corrupted-certificate rejection.
It uses
[equivalence-classes-v0](../../../artifacts/examples/math/equivalence-classes-v0/).

Concept rows:

- `curriculum_relations_and_functions`, `curriculum_sets`, and
  `curriculum_cardinality` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_set_theory_and_foundations` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `equivalence-relation-classes-witness` | `sat` | replay-only |
| `quotient-map-fiber-witness` | `sat` | replay-only |
| `partition-relation-roundtrip` | `sat` | replay-only |
| `bad-equivalence-rejected` | `unsat` | checked |
| `qf-uf-quotient-congruence-alethe` | `unsat` | checked |

The checked proof-object source claim is finite and exact:

```text
Equal elements cannot be sent to different class labels by the same quotient
map q.
```

The finite replay rows validate concrete equivalence classes, partitions, and
quotient-map fibers. The Alethe row isolates the pure congruence obligation
behind that story: if `a = c`, then functional congruence forces
`q(a) = q(c)`. A row that also asserts `q(a) != q(c)` is inconsistent.

## Source Artifact

The committed SMT-LIB artifact is:

```text
artifacts/examples/math/equivalence-classes-v0/smt2/quotient-map-congruence-conflict.smt2
```

It contains the entire proof obligation:

```smt2
(set-logic QF_UF)
(declare-sort Element 0)
(declare-sort Class 0)
(declare-fun a () Element)
(declare-fun c () Element)
(declare-fun q (Element) Class)
(assert (= a c))
(assert (not (= (q a) (q c))))
(check-sat)
```

There is no arithmetic, finite enumeration, or hidden quotient construction in
this artifact. It is the core equality reason that many finite-function and
finite-algebra resources reuse.

## Alethe Certificate

The Alethe certificate replays the equality reasoning instead of trusting an
Ackermannized rewrite or a solver verdict. The proof route must derive the
missing congruence step:

```text
a = c
therefore q(a) = q(c)
```

That derived equality contradicts the asserted disequality:

```text
not (q(a) = q(c))
```

The promoted resource regression is:

```sh
cargo test -p axeyum-solver --test math_resource_uf_routes equivalence_classes_quotient_map_congruence_emits_checked_alethe
```

That test parses the source SMT-LIB artifact, checks the obligation is `unsat`,
emits `Evidence::UnsatAletheProof`, and runs `Evidence::check` against the
original assertions. The route is zero-trust for this row: the congruence step
is derived inside the proof object, not accepted as a trusted preprocessing
step.

## Corrupted Certificate Rejection

The same source artifact has a tamper regression:

```sh
cargo test -p axeyum-solver --test math_resource_uf_routes qf_uf_resource_route_rejects_tampered_alethe_certificate
```

It checks the genuine Alethe proof first, then removes the closing proof
command. Without the closing step, the checker must reject the proof. If the
truncated certificate still checked, the route would not be a trustworthy small
checker.

## Trust Boundary

Trusted:

- exact parsing of the committed source SMT-LIB artifact;
- pack-local replay of finite equivalence relations, partitions, and quotient
  map fibers;
- Alethe proof checking against the original EUF assertions;
- rejection of a truncated Alethe proof.

Not trusted by itself:

- the EUF search procedure that found the conflict;
- an Alethe proof that has not been checked;
- finite-table generation when the row being claimed is a proof-object row;
- arbitrary quotient-set or quotient-type theorems outside the fixed finite
  artifact.

Reusable pattern:

- function single-valuedness in finite relation/function packs;
- composition application in finite function-composition packs;
- operation congruence in finite groups and monoids;
- homomorphism preservation, quotient representative congruence, module and
  tensor-map consistency, group actions, and finite preimage membership.

Remaining horizon:

- quotient constructions over arbitrary sets;
- extensional equality theorems for arbitrary functions;
- general algebra, topology, and category-theoretic quotient theorems;
- broader Lean reconstruction for shapes not yet covered by the current
  Alethe-to-Lean path.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
cargo test -p axeyum-solver --test math_resource_uf_routes equivalence_classes_quotient_map_congruence_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes qf_uf_resource_route_rejects_tampered_alethe_certificate
```

Expected validator output:

```text
validated 1 foundational example pack(s)
```
