# Proof Route Learner Snippets

This page gives reusable learner-facing snippets for the checked evidence
routes used across the math resource packs. Use these snippets when a focused
pack page needs to explain why a negative row is trusted without repeating a
full certificate-anatomy lesson.

The shared shape is:

```text
source finite object -> untrusted search/encoding -> small checked evidence
```

Do not use these snippets to upgrade a theorem claim. A finite row stays finite;
an exact rational row stays exact rational; a fixed-width row stays fixed-width.

## Route Matrix

| Route | Use When | Canonical Anatomy Lesson | Query |
|---|---|---|---|
| Boolean CNF/LRAT | The source claim is a finite Boolean obstruction. | [Proof Object Anatomy](proof-object-anatomy-end-to-end.md) | `routes --route CNF` |
| QF_LRA/Farkas | The source claim is an exact rational linear contradiction. | [Farkas Certificate Anatomy](farkas-certificate-anatomy-end-to-end.md) | `routes --route Farkas` |
| QF_UF/Alethe | The source claim is equality-heavy congruence over finite structures. | [Alethe Certificate Anatomy](alethe-certificate-anatomy-end-to-end.md) | `routes --route Alethe` |
| QF_LIA/Diophantine | The source claim is an integer equality or divisibility obstruction. | [Diophantine Certificate Anatomy](diophantine-certificate-anatomy-end-to-end.md) | `routes --route Diophantine` |
| QF_BV/DRAT | The source claim is fixed-width arithmetic or a bit-vector encoding. | [QF_BV Bit-Blast Certificate Anatomy](qf-bv-bitblast-certificate-anatomy-end-to-end.md) | `routes --route qf-bv` |

## Boolean CNF/LRAT

Use this for pigeonhole, graph, finite set-family, finite topology, and small
Boolean refutations.

Reusable snippet:

```text
The finite source object is encoded as CNF. The SAT search and DRAT/LRAT
production are useful but untrusted. The trusted part is checking the emitted
DRAT/LRAT proof against the committed source CNF, plus rejecting a corrupted
proof object.
```

Name explicitly:

- source object: graph, set family, finite topology, or pigeonhole instance;
- source artifact: DIMACS file or deterministic CNF generator;
- trusted check: DRAT/LRAT proof checking against the source CNF;
- horizon: source-to-CNF lowering unless the page explains why it is
  independently checked.

Good anchors:

- [Proof Object Anatomy](proof-object-anatomy-end-to-end.md)
- [Proof By Refutation](proof-methods-refutation-end-to-end.md)
- [Graph Matching And Augmenting Paths](graph-matching-end-to-end.md)
- [Finite Topology](finite-topology-end-to-end.md)

## QF_LRA/Farkas

Use this for exact rational linear conflicts: LP thresholds, matrix rows,
probability and measure tables, finite geometry, finite optimization steps,
and exact algorithm-step bounds.

Reusable snippet:

```text
The source row is an exact rational linear system. Axeyum may search for the
conflict, but the trusted part is an independently checked Farkas certificate:
nonnegative multipliers combine the source inequalities into an impossible
constant inequality.
```

Name explicitly:

- source object: exact rational table, matrix, inequality system, or algorithm
  step;
- source artifact: SMT-LIB file, pack-local table, or exact replay row;
- trusted check: exact-rational Farkas certificate checking;
- horizon: nonlinear, floating-point, convergence, duality, or theorem-level
  claims not covered by the finite row.

Good anchors:

- [Farkas Certificate Anatomy](farkas-certificate-anatomy-end-to-end.md)
- [Linear Optimization](linear-optimization-end-to-end.md)
- [Finite Probability](finite-probability-end-to-end.md)
- [Finite Gradient Descent Checks](finite-gradient-descent-end-to-end.md)

## QF_UF/Alethe

Use this for equality-heavy finite structures: quotient maps, functions,
homomorphisms, monoids, group actions, modules, tensors, finite topology maps,
and cohomology shadows.

Reusable snippet:

```text
The finite table replay explains the source object. The Alethe route isolates
the equality conflict: congruence or functional consistency forces one
equality, while the bad row asserts its negation. The trusted part is checking
the Alethe proof against the original EUF assertions.
```

Name explicitly:

- source object: finite relation, function, quotient, operation table, module,
  tensor, or topology map;
- source artifact: small QF_UF SMT-LIB conflict or pack-local finite table;
- trusted check: Alethe proof checking against the original assertions;
- horizon: arbitrary quotient, algebra, topology, or category-theoretic
  theorem claims.

Good anchors:

- [Alethe Certificate Anatomy](alethe-certificate-anatomy-end-to-end.md)
- [Equivalence Classes](equivalence-classes-end-to-end.md)
- [Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md)
- [Finite Tensor Products](finite-tensor-products-end-to-end.md)

## QF_LIA/Diophantine

Use this for integer equalities, gcd/divisibility obstructions, modular
inverse failures, incompatible CRT rows, finite homology coefficients, exact
count contradictions, and finite traversal counters.

Reusable snippet:

```text
The source row is an integer equality system. Axeyum may find the obstruction,
but the trusted part is a Diophantine certificate: integer row combinations
produce a combined equality whose coefficient gcd does not divide the constant.
```

Name explicitly:

- source object: modular equation, count equation, coefficient row, homology
  boundary row, or bounded integer counter;
- source artifact: QF_LIA SMT-LIB file or exact integer replay row;
- trusted check: Diophantine certificate checking against the original
  equalities;
- horizon: nonlinear integer arithmetic, full number-theory theorems, or
  unbounded induction.

Good anchors:

- [Diophantine Certificate Anatomy](diophantine-certificate-anatomy-end-to-end.md)
- [Integer Linear Arithmetic](integer-lia-end-to-end.md)
- [Modular Arithmetic](modular-arithmetic-end-to-end.md)
- [Finite Chain Complex Torsion](finite-chain-complex-torsion-end-to-end.md)

## QF_BV/DRAT

Use this when fixed width is part of the mathematical claim: residue arithmetic,
finite fields/rings, small graph-color encodings, and bounded bit-vector
searches.

Reusable snippet:

```text
The source row is fixed-width. Axeyum lowers the bit-vector formula to AIG/CNF
and emits DRAT evidence for the generated CNF. The trusted part is checking the
DRAT proof against that CNF; the bit-blast and Tseitin lowering remain explicit
trust steps unless a stronger reconstruction route covers the original formula.
```

Name explicitly:

- source object: finite residue, finite field/ring row, or fixed-width graph
  encoding;
- source artifact: QF_BV SMT-LIB file plus generated DIMACS/DRAT evidence;
- trusted check: DRAT checking of the generated CNF and original-term evidence
  replay where available;
- horizon: unbounded arithmetic, arbitrary-width algebra, and general finite
  field/ring theorems.

Good anchors:

- [QF_BV Bit-Blast Certificate Anatomy](qf-bv-bitblast-certificate-anatomy-end-to-end.md)
- [Finite Fields](finite-fields-end-to-end.md)
- [Modular Arithmetic](modular-arithmetic-end-to-end.md)
- [Triangle Coloring](graph-coloring-end-to-end.md)

## Query Commands

From the repository root:

```sh
python3 scripts/query-foundational-resources.py routes --route CNF
python3 scripts/query-foundational-resources.py routes --route Farkas
python3 scripts/query-foundational-resources.py routes --route Alethe
python3 scripts/query-foundational-resources.py routes --route Diophantine
python3 scripts/query-foundational-resources.py routes --route qf-bv
```

To find checked rows for a page:

```sh
python3 scripts/query-foundational-resources.py checks --route Farkas --proof-status checked --limit 10
python3 scripts/query-foundational-resources.py checks --route Alethe --proof-status checked --limit 10
```

## Run It

For docs-only snippet refreshes:

```sh
./scripts/check-foundational-resources.sh
./scripts/check-links.sh
```

For a new checked evidence row, also run the route-specific cargo regression
named in [Proof Upgrade Frontier](../../foundational-resources/PROOF-UPGRADE-FRONTIER.md)
and validate the affected pack:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
```
