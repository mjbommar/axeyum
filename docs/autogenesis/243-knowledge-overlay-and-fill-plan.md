# 243 — The knowledge overlay: connective tissue for knowledge-guided Autogenesis

Date: 2026-08-24

## Decision

Axeyum now has a backward-compatible, versioned knowledge overlay joining its
facts and operations to reusable capabilities and to selected identifiers from
the sibling `math-education` graph. The sibling is a **read-only reference
corpus**. This increment changes no file in `../math-education`, vendors none of
its bulk corpus, and adds no required field to an existing Axeyum fact,
operation, claim, or kernel declaration.

The implementation is:

- [`autogenesis-knowledge-overlay.schema.json`](../../artifacts/ontology/autogenesis-knowledge-overlay.schema.json)
  — the structural contract;
- [`knowledge-overlay-v1.json`](../../artifacts/autogenesis/knowledge-overlay-v1.json)
  — the first small, reviewed overlay;
- [`validate-autogenesis-knowledge.py`](../../scripts/validate-autogenesis-knowledge.py)
  — typed relation, local-resolution, and external-pin validation;
- [`test_validate_autogenesis_knowledge.py`](../../scripts/tests/test_validate_autogenesis_knowledge.py)
  — negative controls proving that unknown facts, missing external pins,
  relation-domain errors, and unknown overlay entities are rejected.

The checker is part of both aggregate gates through the existing
`autogenesis-knowledge-controls` recipe. A graph that cannot reject a false
edge is not scheduler knowledge.

## Why a sidecar instead of changing the fact schema

The fact ledger, operation registry, claim ledger, kernel environment, and
external concept graph have different owners and different rates of change.
The theorem-construction lane is currently moving the kernel library from the
700s toward 1,000 declarations. Adding required semantic fields to those
objects would make unrelated construction commits rewrite shared records and
would turn an optional planning annotation into proof-admission coupling.

The overlay therefore follows four compatibility rules:

1. **Owning records remain authoritative.** A fact's status and proof route
   still come from `artifacts/facts/`; an operation's executable contract still
   comes from `operations.json`; a theorem still exists only because the kernel
   accepted it.
2. **References do not grant authority.** A `formalizes` or `uses-technique`
   edge cannot admit a fact, relax a checker, transport a proof, or change an
   axiom footprint.
3. **New knowledge is additive.** Missing overlay coverage means “not yet
   classified,” not false, unsupported, or unavailable. Existing consumers can
   ignore the new artifact entirely.
4. **Schema evolution is versioned.** Version 1 is closed under its declared
   keys. A future incompatible representation becomes version 2 beside it;
   migration never silently reinterprets a version-1 edge.

This is the same reason `math-education` separates authored source from derived
catalogs and orders **encounters**, not whole concepts: a useful view should not
force its consumers to own or rewrite its source objects.

## Requirements derived from Autogenesis

The scheduler needs more than a topic hierarchy. It needs to answer five
different questions without conflating them.

### Identity: what are these two records about?

Stable endpoints must cover:

- mathematical concepts and cognitive-depth encounters;
- formal facts and kernel declarations;
- pinned external declarations;
- operations, producers, and checkers;
- capabilities and obstructions;
- execution episodes and evidence artifacts;
- representations and curriculum nodes.

An endpoint is `(namespace, kind, id)`, not a bare string. `C:induction` and a
kernel declaration named `Induction` cannot collide, and a producer cannot be
mistaken for the operation that authorizes it.

### Semantics: what does the edge claim?

The first relation vocabulary distinguishes:

- `realizes-capability` — executable mechanism versus reusable ability;
- `established-by` — credited fact transition versus mere applicability;
- `formalizes` — exact or qualified formal content versus topic mention;
- `uses-technique` — algorithmic implementation of a mathematical method;
- `blocked-by` — a measured or proposed obstruction;
- `unlocks` — newly reachable or cheaper, explicitly not “already solved.”

Relation definitions declare allowed source and target kinds. The validator
rejects a fact where an operation is required, even if both identifiers exist.

### Epistemics: how do we know an edge?

Every link carries two separate fields:

- `assurance`: formal-derived, independently-checked, registry-derived,
  mechanically-observed, human-reviewed, heuristic, or proposed;
- `provenance.method` plus the exact source artifacts used.

This separation is load-bearing. A human-reviewed concept mapping may be
excellent scheduler guidance while remaining categorically weaker than a
kernel-derived theorem dependency. A heuristic similarity must never be
rendered as a prerequisite merely because both are graph edges.

### Qualification: how much does it cover?

The sibling graph's best design lesson is that a concept is not learned once.
It uses encounters such as `C:parity@understand` and `C:parity@analyze` because
requiring mastery of a whole concept is either too strong or meaningless.

Axeyum needs the analogous restraint. A theorem may be:

- an exact formalization;
- one defining law;
- a supporting lemma;
- a finite instance;
- a counterexample;
- a representation bridge;
- a partial approximation.

The seed links therefore say `coverage: supporting-law` and
`completeness: partial`. Proving `Int.ModEq.refl` does not mean that Axeyum has
formalized all of modular arithmetic.

### Time and external identity: which source did we mean?

The overlay pins the sibling source at
`ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c`. Every external endpoint repeats
that revision. If the sibling checkout is absent, validation remains possible
from the committed pin and identifier syntax. If it is present at that exact
commit, the checker also resolves referenced concept and technique files. If a
different sibling revision is mounted, the checker warns and refuses to use it
as resolution evidence.

This lets Axeyum copy or adapt selected knowledge deliberately without creating
a build dependency on a mutable sibling repository.

## What was adapted from `math-education`

Live inspection of the pinned sibling found:

- 1,567 concepts and 2,303 cognitive-depth encounters;
- 2,943 prerequisite edges, with a deepest chain of 21;
- typed concepts, encounters, techniques, misconceptions, lessons, and
  curriculum objects;
- distinct `requires`, `related`, taxonomy, delivery, technique, and bridge
  relations;
- qualified prerequisites carrying `strict` or `helpful` strength and a written
  reason;
- epistemic statuses separating axiom, proved, computed, empirical,
  conjectured, and open;
- stable retirement rather than identifier deletion.

We adapted the principles, not the corpus:

1. typed endpoints;
2. relation domains and ranges;
3. written reasons for consequential edges;
4. qualified relations rather than overloaded booleans;
5. stable external identities with explicit revision pins;
6. concepts separated from depth-specific encounters;
7. epistemic status separated from graph topology.

We added what Autogenesis needs and a pedagogical graph does not:

- proof and checker assurance;
- producer capabilities and failure obstructions;
- fact-transition credit;
- kernel-derived versus registry-derived provenance;
- compute-budget and assurance-floor attributes;
- representation and transport identities;
- the rule that no link grants admission authority.

## The seed is deliberately small

Version 1 contains two capability entities:

- bounded structural induction;
- definitional equivalence-relation combinators.

Eight seed links demonstrate all important boundary shapes:

- operation → capability;
- capability → external mathematical technique;
- fact → credited operation;
- fact → external concept with partial-coverage qualifiers.

These are examples and controls, not a coverage claim. Bulk-importing 1,567
concepts or manufacturing links from string similarity would produce a large
graph whose meaning nobody had reviewed.

## What to fill next

### F0 — Preserve the contract while construction continues

Exit criteria:

- no required change to `fact.schema.json` or `operations.json`;
- no write to `../math-education`;
- every external endpoint pinned;
- every local endpoint resolves;
- every edge carries assurance, reason, and provenance;
- all four negative controls remain live.

Do not add a generator until at least two manually reviewed batches expose the
real repetition. Premature generation would encode our first guesses as policy.

### F1 — Complete the current autonomous-production crosswalk

Add links for every fact credited to a multi-target operation, then every fact
credited to a capsule. For each fact record:

- credited operation;
- reusable capability, if one genuinely exists;
- exact concept or encounter mappings;
- mathematical technique;
- coverage qualifier;
- evidence and assurance source.

Measure separately:

```text
facts with a concept mapping
facts with a technique mapping
facts with a reusable capability
autonomous facts with all three
```

The current ledger has 350 facts but only 91 embedded `concept_refs`; the
overlay must not pretend the other 259 are unrelated.

### F2 — Import the kernel-observed dependency view

Create endpoints or projections for the 700–1,000 kernel declarations and add
direct `depends-on` links derived from accepted proof terms. Keep them separate
from the fact ledger's human planning dependencies.

Required distinctions:

- direct versus transitive dependency;
- theorem versus definition versus inductive recursor;
- kernel-derived versus imported dependency;
- reached trusted declaration versus merely declared trusted surface;
- identical theorem re-admitted in multiple preludes.

The existing `check-fact-depends-derived.py` proves that this distinction is not
theoretical: deriving dependencies already found missing ledger edges.

**F2 result (2026-08-24):** the generated
[`kernel-dependency-projection-v1.json`](../../artifacts/autogenesis/kernel-dependency-projection-v1.json)
now records the full constructed-prelude surface as canonical declaration nodes
and direct theorem-dependency edges. See the
[projection result](244-kernel-dependency-projection-result.md). It deliberately
does not rewrite the fact ledger: the next phase is typed producer-obstruction
data, not hand-transcribing the kernel graph into planning edges.

### F3 — Turn decline records into an obstruction graph

Normalize each producer episode into:

```text
goal
→ adapter outcome
→ producer outcome
→ reconstruction outcome
→ checker outcome
→ typed obstruction
```

An obstruction should record:

- first observed blocker and complete known blocker set separately;
- affected population and partition;
- number of facts blocked;
- candidate capability that could remove it;
- whether that candidate already exists internally;
- resolution commit and measured before/after funnel.

This graph supplies the scheduler's highest-leverage question: “Which reusable
capability removes the largest measured cluster?”

### F4 — Add representation and transport chains

Materialize the identity chain already scattered through manifests:

```text
Mathlib declaration
→ pinned source statement
→ lean4export NDJSON root
→ proof-free statement adapter
→ imported kernel goal
→ Axeyum fact
→ candidate proof
→ checked evidence
→ admitted declaration
```

Every transformation edge must carry input/output digests, tool version,
visibility of proof bodies, and its trust classification. Alpha-equivalent or
definitionally equivalent statements are links, not identity collapse.

### F5 — Build concept coverage as a derived view

Join facts and kernel declarations outward through `formalizes` and upward
through the sibling prerequisite graph. Publish at least:

- exact formal coverage;
- partial supporting-law coverage;
- checked computation only;
- assumption-bearing coverage;
- autonomous-producer coverage;
- one-fact-away and one-capability-away encounters;
- concepts with no formal anchor.

Coverage must never roll these into one green badge. A computed finite example,
an axiom-free universal theorem, and a pedagogical mention are different
results.

### F6 — Add scheduling value and cost observations

Only after F1–F5 provide reliable inputs, derive heuristic observations:

- probability of producer success by goal features;
- median and tail cost;
- descendants unlocked;
- concepts and encounters reached;
- decline-cluster reduction;
- proof-plan shortening through reuse;
- human proof-affecting interventions.

Heuristic edges remain explicitly `heuristic`. They may rank untrusted search;
they may never authorize admission.

### F7 — Close the knowledge-guided loop

The first decisive overlay-backed result is:

1. select a dependency-ready fact using fact readiness plus capability fit;
2. choose a producer from typed features rather than target ID;
3. construct and independently check a proof;
4. apply the fact transition;
5. update kernel dependencies, capability evidence, concept coverage, and
   obstructions;
6. observe a newly unlocked fact or encounter;
7. select the next target without human proof-affecting intervention;
8. reproduce the sequence from the same pinned inputs and budgets.

That is knowledge-guided Autogenesis. The graph improves search, but the kernel
still decides knowledge.

## Collision policy for the 700 → 1,000 construction lane

Until that lane finishes:

- do not edit its prelude sources, theorem inventories, or generated theorem
  count ledger;
- do not require new fields in its declarations or facts;
- add overlay links in batches whose endpoints already exist on `main`;
- validate against live local IDs immediately before commit;
- rebase or merge latest `origin/main`, rerun the focused checker, and push each
  bounded batch;
- treat a disappearing declaration as a failed endpoint, never silently retarget
  it by name similarity.

The sidecar can lag construction safely. It cannot lead construction by
asserting nonexistent local entities.

## ADR disposition

No ADR is required for version 1 because it adds optional planning metadata and
a validator without changing a public operator, rewrite, encoding, backend,
evidence format, logic fragment, solver trait, kernel rule, admission policy, or
trusted boundary. The overlay explicitly carries no admission authority.

An ADR becomes mandatory before any of these later changes:

- the scheduler treats an overlay edge as authorization rather than a ranking
  hint;
- an overlay relation changes fact readiness or admission;
- a kernel or evidence checker consumes the overlay as trusted input;
- the overlay replaces an owning registry rather than joining it;
- an external concept mapping is used to transport a theorem or proof.

## Immediate next batch

F1 is now complete for the current multi-target facts. Its generated,
reproducible [coverage census](../plan/generated/autogenesis-knowledge-coverage.md)
reports two authoritative multi-target operations, nine applicable facts, all
nine with qualified `formalizes` mappings, and seven fact-evidence-backed
`established-by` credits. The remaining two applicability entries were settled
by earlier one-target operations, so the census deliberately does not misstate
them as credits to the later reusable producer.

The completed bounded batch was:

1. regenerate the production provenance ledger first, because its committed
   value was recently stale;
2. enumerate every fact credited to the two multi-target operations;
3. map the five bounded-induction facts to factorial, recursion, base case, and
   induction encounters with explicit partial-coverage qualifiers;
4. map the four ModEq facts to modular arithmetic and equivalence-relation laws;
5. add the symmetry/transitivity/direct-proof techniques where exact;
6. publish a coverage census from the overlay and add mutation controls for a
   false “complete concept coverage” edge.

F2 should now consume the kernel's actual dependency inventory rather
than manually mapping hundreds of declarations. The sequence is intentional:
first prove the link semantics on nine well-understood facts, then scale the
mechanical parts without scaling ambiguity.
