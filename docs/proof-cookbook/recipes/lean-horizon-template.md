# Lean Horizon Template

## Problem Shape

Typical horizon shape:

```text
for every epsilon > 0, there exists delta > 0, ...
```

or:

```text
every finite-additive measure on a finite table replays now,
but countable additivity and convergence theorems need a proof assistant.
```

Expected result: not a solver verdict yet. The resource should record
`lean-horizon` until a concrete Lean module and checker command exist.

## Solver Route

The current route is deliberately split:

- finite or bounded shadows use
  [Finite Model Replay Evidence](finite-model-replay.md);
- arithmetic subgoals may use Farkas, Diophantine, DRAT/LRAT, Alethe, or other
  checked routes;
- the general theorem remains a Lean/mathlib-scale proof target.

This template is not a claim of current Lean coverage. It is the vocabulary for
resources that teach where SMT-style checking stops and theorem proving begins.

## Evidence Artifact

Current artifact requirements for a horizon resource:

- metadata with `proof_status: "lean-horizon"` or explicit graduation criteria;
- a finite shadow example whose bounded replay validates, when available;
- a named target theorem shape;
- a future command that will check the Lean module without `sorry`.

Until a Lean artifact exists, no resource may call the general theorem proved.

## Checker

Current checks are metadata and finite-shadow checks:

- foundational concept validation;
- example-pack validation;
- docs link checking.

Future graduation requires a Lean command that checks the module and audits
`#print axioms` for the exported theorem. A module depending on `sorryAx` does
not graduate.

## Lean Reconstruction

Status: planned per theorem family.

Examples that should stay under this template until a real module exists:

- arbitrary-domain first-order validity, completeness, and model theory;
- real completeness, least-upper-bound theorems, and epsilon-delta analysis;
- general sequence convergence, Cauchy completeness, and compactness theorems;
- differentiability from limits, mean value theorem, integration, and the
  fundamental theorem of calculus;
- induction schemas beyond bounded base/step obligations;
- epsilon-delta limits and continuity;
- compactness, connectedness, and general topology;
- countable additivity, integration, and convergence theorems;
- Banach/Hilbert-space and general Chebyshev-space theorems;
- holomorphicity, contour integration, residues, and analytic continuation.

## Trust Boundary

Trusted:

- not prose descriptions of the theorem;
- not a bounded finite shadow as evidence for the unbounded theorem;
- not a Lean file with `sorry` or an unaudited axiom dependency.

Checked today:

- finite examples linked from the same resource;
- metadata that keeps the horizon explicit.

Downgrade behavior:

- if no Lean artifact exists, keep `lean-horizon`;
- if a proposed Lean artifact uses `sorryAx`, keep `lean-horizon`;
- if the finite shadow fails replay, mark the finite resource invalid too.

## Commands

Current resource checks:

```sh
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py
./scripts/check-links.sh
```

Future Lean checks should be written as concrete commands beside the graduated
resource.

## Links

- [Math Curriculum Resource Buildout](../../foundational-resources/MATH-CURRICULUM-BUILDOUT.md)
- [Math Field Taxonomy](../../foundational-resources/MATH-FIELDS.md)
- [Proof Gap Dashboard](../../foundational-resources/generated/proof-gap-dashboard.md)
- [Finite Predicate pack](../../../artifacts/examples/math/finite-predicate-v0/)
- [Real Algebra RCF Shadow pack](../../../artifacts/examples/math/reals-rcf-shadow-v0/)
- [Sequence And Limit Shadow pack](../../../artifacts/examples/math/sequence-limit-shadow-v0/)
- [Calculus Algebraic Shadow pack](../../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
- [Induction Obligations pack](../../../artifacts/examples/math/induction-obligations-v0/)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [north star](../../research/00-orientation/north-star.md)
