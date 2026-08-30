# ADR-0717: Library construction is graph-directed through an artifact-compatible trust anchor

Status: accepted
Date: 2026-08-30
Index-summary: Graph-directed library construction, artifact compatibility, and independent replay precede broad Lean source compatibility

## Context

Axeyum now has three substantial but partly disconnected products: a solver/CAS
stack, an independent Lean-core checker with an axiom-free mathematical
library, and an autogenesis/fact-ledger loop.  Mathlib v4.30 supplies a pinned
statement frontier, but target choice is still dominated by the small curated
nursery and by whichever neighboring goals a lane can currently state.  That
has produced valuable arithmetic, but it does not measure which missing
definition, theorem, datatype, or producer unlocks the most downstream work.

The Lean compatibility programme also contains several different goals under
one name.  Axeyum can check and exchange selected elaborated declarations, and
Python/Rust already provide productive programming surfaces.  It does not parse
or elaborate general Lean source, reproduce Mathlib's typeclass/tactic
environment, or behave as a Lake package.  Full source compatibility would be a
large independent implementation programme and is not required for the
library/solver flywheel to operate.

Finally, kernel acceptance proves that a term has a type in an environment.  It
does not prove that the type is the intended proposition, that hypotheses are
non-vacuous, that a checker covered the claimed subject, or that Axeyum's own
kernel has no shared semantic defect.  The existing footprint, mutation, and
real-Lean checks address parts of this boundary but are not yet one universal
credit contract.

## Decision

The next library-construction programme is ordered around one thin waist:
content-addressed elaborated declarations and independently checkable kernel
terms.  Work proceeds in this order:

1. build a complete, versioned declaration/type/proof graph for the selected
   Mathlib population and join it to Axeyum's ledger, representability,
   producer, obstruction, and destination data;
2. select definitions, infrastructure, producers, and theorems by measured
   downstream leverage and destination relevance, not degree or local
   dispatchability alone;
3. make every credited theorem pass a coverage-bearing safety contract that
   binds statement identity, excludes target contamination, measures reached
   trust, falsifies meaningful mutations, and independently replays in pinned
   Lean where representable;
4. make definition and proof discovery declarative and reusable, with Python as
   an untrusted orchestration plane and the Rust kernel as the single admission
   anchor;
5. add a thin Lean goal/proof adapter before broad source compatibility; add
   parser, elaborator, typeclass, tactic, or workflow features only when a
   preregistered population demonstrates that the feature is the binding
   constraint.

Upstream proof-dependency edges are evaluation and sequencing data.  They are
kept physically and logically separate from proof-isolated producer inputs
unless an experiment explicitly studies proof reuse and cannot earn autonomous
production credit.

## Evidence

The pinned Mathlib v4.30 module graph on server5 contains 8,094 modules and
25,495 internal direct-import edges.  Its direct hubs are infrastructure such
as `Mathlib.Init`, ring/group/field definitions, finite big operators, order,
sets, and polynomial algebra maps.  It also contains 1,476 module sinks,
including aggregators such as `Mathlib.Tactic`; consequently neither raw
indegree nor sink status is a sufficient priority rule.

Axeyum's existing selected dependency projection covers only a small
Nat/Int candidate population and deliberately omits external edges.  It is a
leakage-control artifact, not a complete leverage graph.  The curriculum audit
also found that local proof-graph selection concentrated work in five
arithmetic nodes while intended destinations remained thin.

The current compatibility authority records bounded K0/K1 capability while
native source, checked tactics, workflow, runtime, and ecosystem compatibility
remain open.  Real-Lean differential tests, fact-ledger mutation controls, and
kernel-derived footprints demonstrate that the proposed universal safety
contract can be assembled from already exercised mechanisms.

## Alternatives

**Pursue full Lean source compatibility now.** Rejected because parser,
elaboration, typeclasses, tactics, macros, termination, packages, and editor
behavior are a large programme whose early slices do not necessarily increase
library production or trust.

**Use PyO3 as the only interoperability surface.** Rejected because it does not
provide Mathlib declarations, Lean elaboration, Lean-user workflow, or
independent Lean-kernel acceptance.

**Choose the highest-degree theorem next.** Rejected because degree conflates
file organization, proof reuse, and destination value; high-degree nodes can be
unrepresentable or expensive, while a lower-degree datatype or producer may
dominate the reachable Axeyum frontier.

**Continue local open-fact dispatch.** Retained only as the within-cluster
selector after the programme has chosen a destination and shared capability.

## Consequences

The detailed exits and lane boundaries live in the four companion roadmaps:

- [`library-artifact-compatibility-roadmap-2026-08-30.md`](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md)
- [`graph-directed-library-roadmap-2026-08-30.md`](../../plan/graph-directed-library-roadmap-2026-08-30.md)
- [`trusted-library-safety-roadmap-2026-08-30.md`](../../plan/trusted-library-safety-roadmap-2026-08-30.md)
- [`definition-discovery-efficiency-roadmap-2026-08-30.md`](../../plan/definition-discovery-efficiency-roadmap-2026-08-30.md)

The generated root plan becomes the ordering authority for this programme.
Complete Lean source/ecosystem parity remains a long-horizon compatibility
target, not a prerequisite for the next library increments.
