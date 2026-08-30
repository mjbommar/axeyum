# Graph-directed mathematical library roadmap

Status: accepted programme under ADR-0717
Date: 2026-08-30

## Outcome

Choose the next shared definition, abstraction, producer, or theorem by the
mathematical work it unlocks.  Local dependency readiness remains useful inside
the chosen cluster; it no longer decides which subject or capability receives
the next lane.

## Evidence baseline

The pinned Mathlib v4.30 module graph measured on server5 has 8,094 modules and
25,495 internal direct-import edges.  Direct hubs include `Mathlib.Init` (193
importers), `Mathlib.Tactic.Common` (69), `Mathlib.Algebra.Ring.Defs` (43),
finite big-operator basics (41), field/group/order definitions (38 each), and
polynomial algebra maps (32).  There are 1,476 no-importer sinks; the largest
direct-import sink, `Mathlib.Tactic`, is an aggregator with 336 imports.

This establishes where to investigate, not what to copy.  Module edges conflate
file organization, tactics, and mathematics.  The declaration graph is the
decision input.

## Graph model

The generated graph must expose separate, joinable layers:

1. Mathlib module imports;
2. declaration type dependencies;
3. declaration proof/value dependencies, isolated from producers;
4. Axeyum theorem dependencies read from the kernel;
5. fact-ledger authored `depends_on` edges;
6. representability and vocabulary requirements;
7. producer applicability and typed declines;
8. curriculum/destination paths;
9. trust and compatibility blockers;
10. measured effort and outcomes from prior lanes.

Definitions, datatypes, proof schemas, and theorems are all candidate
investments.  A theorem-only ranking misses the most valuable missing
infrastructure.

## Priority function

Publish every component rather than hiding policy in one magic number.  The
initial ordering is lexicographic:

1. wrong-verdict, trust, or coverage defect;
2. a missing definition/datatype/operation that makes multiple destination
   facts unstatable;
3. a shared producer or proof schema demanded by multiple open clusters;
4. a graph dominator or high descendant-unlock node on a named destination
   path;
5. an individual dependency-ready fact.

Within tiers, generate an advisory score:

```text
benefit = destination_weight
        * newly_statable_or_dispatchable
        * downstream_descendants
        * cross_family_reuse
        * evidence_value

cost = estimated_dependencies
     * missing_feature_weight
     * historical_decline_cost
     * trust_surface_cost

priority = benefit / max(cost, 1)
```

Degree is one feature.  Also compute transitive descendants, dominators,
betweenness, weak components, prerequisite depth, and the marginal change to
the current Axeyum frontier.  All scores must show their raw inputs.

## Phases and exits

### G0 — Reproduce the module baseline

Vendor no Mathlib checkout.  Commit a compact receipt containing source
identity, parser identity, module/edge totals, top-degree rows, sink count, and
hashes for the external source.

**Exit:** two runs reproduce the receipt; source or parser drift fails.

### G1 — Build the declaration graph

Execute C1 of the artifact roadmap.  Compute direct and transitive metrics over
types and proofs separately.  Mark proof-derived data as forbidden producer
input.

**Exit:** complete selected-population coverage, resolved endpoints, acyclicity
where required, typed cycle handling where not, and deletion mutations for rows
and edges.

### G2 — Join Axeyum state

Resolve Mathlib declarations to fact IDs, kernel declarations, statement
vocabulary, destination nodes, producers, declines, and trust footprints.
Unresolved links remain explicit and count against coverage.

**Exit:** generated dashboard reports all join populations and unresolved
counts; no theorem-name similarity silently creates an identity.

### G3 — Publish the infrastructure frontier

Produce four queues:

- missing language/definition infrastructure;
- missing reusable proof producers;
- high-leverage theorem dominators;
- local dependency-ready leaves.

For each proposed increment show the top downstream facts, current blockers,
estimated cost, destination paths, and whether the gain is statability,
dispatchability, proof, or independent assurance.

**Exit:** every selected lane brief cites one frozen queue row and preregisters
the metric expected to move.

### G4 — Run three pilot clusters

Run one pilot in each category:

1. finite collections/big operators or another high-degree missing substrate;
2. a shared congruence/rewrite/induction producer from the obstruction graph;
3. a destination bridge toward linear algebra, polynomials, or analysis.

Each pilot must compare graph selection against the best local-ready
alternative and record actual unlocked facts, producer reuse, time, and safety
cost.

**Exit:** retain the ranking only if at least two pilots move their
preregistered downstream metric without a worse trust boundary.  Otherwise
revise weights; do not rationalize the score after seeing outcomes.

### G5 — Make graph selection the ordinary dispatcher

The curriculum chooses the destination, the infrastructure frontier chooses
the capability, and `fact-frontier.py` chooses the specific legal target inside
that cluster.  A lane can override the ordering only with an evidence note.

## Breadth and depth policy

Breadth is not theorem count.  Track the number of destination areas with a
usable definition and producer path.  Depth is not file size.  Track longest
closed prerequisite chains, reusable algebraic structures, and independently
checked headline theorems.

Allocate three concurrent lanes by default:

- one substrate/definition lane;
- one reusable producer lane;
- one destination/theorem lane using already-landed substrate.

Do not place all lanes in one theorem family.  Do not allow the destination
lane to invent missing substrate privately; it records the blocker for the next
graph refresh.

## Metrics

- newly statable, dependency-ready, dispatchable, and proved facts—separate;
- transitive descendant mass unlocked;
- facts and families served per new producer;
- unresolved graph joins and proof-isolation violations;
- destination breadth and prerequisite depth;
- actual versus estimated effort;
- theorem-specific helpers versus multi-target infrastructure;
- graph-selected pilot dominance over a preregistered local baseline.
