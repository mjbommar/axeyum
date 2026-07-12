# ADR-0109: Closed-subterm sharing for Lean export

Status: accepted
Date: 2026-07-11

## Context

ADR-0108 produces a kernel-checked proof DAG for `006-cbqi-ite`, but the Lean
source exporter recursively prints every incoming edge as a full syntax tree.
The resulting module is about 152 MB although the in-tree kernel hash-conses
every expression. Reconstruction and rendering take about 18 seconds, and the
artifact is too large for routine inspection or transfer. This is an export
problem, not a decision or checking problem.

Lean's own implementation distinguishes expression size with and without
sharing and advises sharing common expressions before expensive checking.
Top-level definitions provide a source-level sharing primitive that Lean's
elaborator and kernel already understand.

Naively hoisting an arbitrary repeated expression is unsound as a serializer:
an expression containing loose de Bruijn variables or free locals depends on
its surrounding binder context. Reprinting it as a closed top-level definition
would change its meaning or fail to elaborate.

## Decision

Add an opt-in compact self-contained-module renderer. Keep the existing
`render_lean_module` and `render_lean_module_with_inductives` byte-for-byte
unchanged.

The compact renderer:

1. computes saturated occurrence counts over the reachable hash-consed proof
   DAG rather than recursively walking the expanded tree;
2. selects only repeated compound expressions above a fixed minimum structural
   size;
3. requires every selected expression to have no loose de Bruijn variables and
   no free variables according to the kernel's cached metadata;
4. emits selected expressions once as deterministic top-level `def`s in
   child-before-parent order;
5. renders later definitions and the final theorem through those names; and
6. retains the same reachable environment declarations, theorem goal, proof
   semantics, and `#print axioms` audit.

The compact route is formatting only. It cannot grant a solver result or make
an invalid proof valid: reconstruction still runs `Kernel::infer` and
definitionally compares the proof type with `False` before export. A real Lean
binary remains the independent checker of the rendered source when installed.

ADR-0108 uses the compact renderer first because it is the measured artifact
with material duplication. Other reconstructors may opt in after their output
is compared and external Lean coverage remains green.

## Acceptance

- Unit tests show deterministic sharing of a repeated closed proof subterm,
  no sharing of an open/binder-dependent subterm, and byte-identical legacy
  rendering.
- The compact module retains every required declaration and the final axiom
  audit, and an available external Lean binary accepts representative output.
- The `006-cbqi-ite` module remains kernel-checked and shrinks substantially
  from the 152 MB ADR-0108 baseline without changing evidence, verdict, or trust
  steps.
- Quantified-LIA remains 12/12 decided/certified/checked/dominant and 8/8 Lean
  UNSAT with no mismatch, timeout, audit error, replay failure, or trust hole.
- Workspace tests, Clippy, warning-denied rustdoc, links, foundational
  resources, formatting, and generated matrices pass.

## Alternatives

- **Hoist every repeated expression.** Rejected: open terms depend on binder
  context and cannot be named safely without lambda lifting.
- **Lambda-lift open terms immediately.** Deferred: it requires recovering and
  serializing the complete local context for each occurrence. Closed sharing is
  simpler, independently useful, and measurable first.
- **Split the proof into query-specific axioms.** Rejected: this would reduce
  text by expanding the trusted base and destroy the proof-assurance claim.
- **Emit a binary `.olean` or custom DAG format.** Deferred: source remains the
  most portable independently inspectable artifact, and linked Lean is not a
  product dependency.

## Consequences

- Large proof DAGs can preserve source-level sharing without changing the
  kernel or solver evidence contract.
- The first slice may leave duplication under open binder contexts. If the
  measured residual remains material, a later ADR can add checked lambda
  lifting or a binary proof container.
- Compact and legacy renderers coexist, so existing golden and external Lean
  tests do not change implicitly.

## Validation

- `006-cbqi-ite` retains the same 119-case checked cover and kernel-accepted
  `False` proof, while its rendered module shrinks from 151,845,067 bytes to
  2,682,977 bytes (98.23%). Release audit reconstruction falls from 17.74
  seconds to 10.75 seconds (39.43%) under the same 60-second cap.
- The fresh quantified-LIA audit remains 12/12 decided, certified, rechecked,
  and dominant, with Lean UNSAT 8/8 and zero mismatches, audit errors, timeouts,
  replay failures, or trust holes.
- The public release regression requires a real emitted `Bool` inductive,
  rejects an opaque `Bool.rec` axiom, requires compact share definitions, caps
  the module below 3 MB, and rejects `sorryAx`.
- Renderer tests prove deterministic reuse of a repeated closed proof term and
  reject hoisting a repeated expression with a loose de Bruijn variable. The
  legacy renderer remains on its original code path and deterministic output.
- No external Lean binary is installed on this host or present in the cloned
  Lean checkout, so external source acceptance remains explicitly unverified;
  the in-tree kernel gate and existing optional external-Lean tests remain the
  available checks.
- Lean kernel 154/154, solver library 830/830, evidence 69/69, bench 7/7,
  capability/support goldens 2/2 and 12/12, workspace all-target/all-feature
  Clippy, warning-denied rustdoc, links, foundational resources, formatting,
  and diff checks pass. The known Sturm nontermination still precludes a
  whole-workspace aggregate claim.
