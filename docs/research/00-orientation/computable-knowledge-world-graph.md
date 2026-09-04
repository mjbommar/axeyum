# Computable Knowledge: extending the flywheel from Mathlib to the world

Status: flag-planting orientation note; no implementation exists yet
Last updated: 2026-09-04
Author context: a conversation on 2026-09-04 that started from
[OpenGloss](https://huggingface.co/datasets/mjbommar/opengloss-v1.3-dictionary)
and its generator, and asked what "extending Mathlib to the real world" would
mean for this repository.

> This note defines a destination and the reasoning behind it. It is not a
> plan, a schedule, or a status ledger. Nothing here is built. When something
> is, it will be recorded in a lane status file and an ADR, and this note will
> link to them.

## 1. The claim in one paragraph

What made the Mathlib rebuild inside this kernel work was never the
mathematics. It was a shape: untrusted fast search, trusted small checking,
and a ledger that separates *what we established* from *what the world
asserts*, with a checker that can refuse a claim and a metric that nobody can
inflate. A dictionary or knowledge graph produced by a language model is the
untrusted-search half of that shape, done at scale, with no checking half.
"Computable knowledge" is therefore not about turning the world into
theorems. It is about finding, for each kind of claim about the world, the
smallest thing that can refuse it, and putting that thing behind the one
trust anchor this repository already has.

## 2. Background

### 2.1 What this repository already is

Axeyum is a Rust automated-reasoning stack whose north star is a complete
framework for reasoning, logic, and proving
([north star](north-star.md)). Its identity is *untrusted fast search,
trusted small checking*: solvers, a CAS, and producer tactics search; a small
kernel (`Kernel::add_declaration`) checks; every admitted theorem carries an
axiom footprint read from the kernel, never from text.

The parts that matter for this note:

- **The fact ledger** (`artifacts/facts/`): one JSON file per proposition,
  with a formal statement, two independent status axes (`epistemic_status`,
  what we established; `external_status`, what mathematics knows), evidence,
  and the axiom footprint. A proved fact with nothing checked fails
  validation.
- **The flywheel**: library → solver → reconstruction → kernel → library, and
  a concept DAG that says what to prove next. The cycle has closed end to
  end; making it automatic is the work.
- **Three producers, one trust anchor** (ADR-0601): autogenesis, the CAS, and
  the importer are all producers behind the same kernel; imports are labeled
  scaffolding and never headline.
- **Graded statement families** (ADR-0603): a classical theorem lands as a
  family, one fact per statement: the general constructive form, a boundary
  refutation, a decidable-fragment exact form, and a labeled import.
- **Blind evaluation**: held-out families whose value is spent the moment
  anyone reads them, with irreversible amendments when that happens
  (ADR-0542).
- **Checker discipline**: a checker that cannot fail is worse than none; touch
  a checker, delete a guard, and exactly one test must die
  ([evidence and checker discipline](../../contributor-guide/evidence-and-checker-discipline.md)).

### 2.2 What OpenGloss is

OpenGloss v1.3 is a synthetic encyclopedic dictionary and semantic graph for
English: about 206,000 lexemes, 8.5 million typed edges (synonym, antonym,
hypernym, hyponym, collocation, etymology, inflection, derivation),
encyclopedic text and etymology on nearly every entry, reading-level
renditions, and domain tags. Every field was produced by a language model
under a schema.

The clean-room generator (`../opengloss-generator`, schema v3) adds the
structure a graph needs to be checked at all: a `kind` discriminator on every
lexeme; a controlled ~150-leaf domain taxonomy (law and government alone has
a dozen leaves); one typed `relations` list per sense whose targets *resolve*
to sense ids; `instance_of` and `entails` and `causes` beside the WordNet
relations; proper nouns with an entity type (including `SPECIES`) and a
Wikidata QID; structured examples with spans; per-call cost accounting under
a hard budget; and free post-passes (`resolve`, `relation-reconcile`,
`contrasts`) that begin to act as checkers.

What it does not have is the trusted half. An edge is an assertion. Nothing
refuses a hypernym cycle, a synonym that is also an antonym, or a meronym
that is really a hyponym. The eight and a half million is a count, not a
claim, for exactly the reason the axeyum ledger insists on: at scale the
ledger is the product, and a graph nobody can refute manufactures
unfalsifiable edges at full speed.

### 2.3 The predecessors, and why each stalled

Every earlier attempt at a computable world graph got some of the shape and
missed the rest.

- **The semantic web** (RDF, OWL, SPARQL, description logics) got global
  identifiers, typed edges, and the open-world default right. It could not
  count: no units, dates, arithmetic, or probability. Its reasoners were
  trusted-large (no proof objects, so a reasoner bug is invisible). It had no
  epistemics: a triple is an assertion and provenance was bolted on later.
  And production was hand labor.
- **Cyc** had the ambition and forty years of hand encoding, and never escaped
  the cost of hand encoding.
- **Wolfram Alpha** is the closest existing thing: curated data plus a CAS. It
  is closed, trusted-large, has no proof objects, and has no ledger.
- **Lean and Mathlib** have the trust and the proofs, and no world.

The union this note proposes is Cyc's ambition, Wolfram's computation, Lean's
trust, the semantic web's identifiers, and the language model's production
rate. What is new is not any one of those. It is having cheap untrusted
production and small trusted checking *at the same time*, which no
predecessor had and which is the same pair that made the math flywheel close.

## 3. Three kinds of claim, three kinds of checker

Real-world knowledge splits cleanly once you ask what could reject a claim.

1. **Definitional claims.** "A sedan is a car." "Every equilateral triangle
   is isosceles." These follow from meanings. Their checker is consistency
   and, where the definitions compile, proof: hypernymy is a DAG, synonym and
   antonym never share an edge, meronymy and hyponymy are disjoint,
   entailment is transitive, and a hypernym edge between two predicates is a
   universally quantified implication the kernel can check.
2. **Computable claims.** "Prime number." "Leap year." "Net present value."
   "This registry's inbreeding coefficient." "Tax under this code with these
   facts." The gloss compiles to a definition with a decision procedure or an
   exact computation behind it, and the checker is the kernel plus the
   producers that already exist (`linarith`, `ring`, `simp`, `decide`, the
   CAS).
3. **Empirical and contested claims.** "France's population in 2020." "This
   drug is effective." "Carnivora is a clade." No kernel exists. The honest
   structure is the ledger's second axis: what sources assert, versioned and
   citable, with the metric being *re-derivability* (did a machine recompute
   it from a cited source) rather than truth.

Everything in the rest of this note is an application of that split.

## 4. The three-layer decomposition

Across every domain examined, a body of knowledge decomposes into the same
three layers, in different proportions:

| layer | what it holds | how it is checked | status axis |
|---|---|---|---|
| **authority** | identities and definitions by fiat: Euclid's axioms, the NCBI taxonomy, SI constants, a statute as codified on a date | pinned import: version, digest, citation; lookup against the pin | external, labeled scaffolding (ADR-0601) |
| **computable** | everything exactly derivable from the authority layer: proofs, closures, arithmetic, decision procedures | the kernel; the footprint names which authority items were assumed | epistemic: established |
| **external** | typicality, measurement, interpretation, regime validity | none; only provenance and re-derivability | external only, never proved |

The single mechanism that keeps the middle layer honest in every domain is
**the axiom footprint**. A derived fact carries the names of what it assumed,
whether that is a Euclidean axiom, a clade membership at an NCBI version,
Newton's third law, or a section of a tax code. The kernel learned to do this
with mathematical axioms. Nothing about the mechanism cares what the axiom is
about. There is no axiom-free physics and no axiom-free law, and the honest
statement of a derived result in either is its footprint.

## 5. Worked examples

These were talked through concept by concept. The point of each is not the
answer but which layer each piece lands in, and what the data model has to
do about it.

### 5.1 Geometry: point, segment, triangle

The kernel already has `CPoint` (a pair of constructed reals),
`Collinear`, `NonCollinear`, `distSq`, `midpoint`, and CAS-certified facts
about medians and centroids. It has no segment and no triangle type.

- **Point.** The dictionary has one geometry sense (and four others: decimal
  point, point of an argument, to score a point). The kernel has one
  *declaration*, and it is the concept in one carrier; rational points in the
  CAS bridge are a different declaration for the same word. **First mapping
  rule: an OpenGloss sense is a concept; an axeyum declaration is a
  concept-in-a-carrier; one sense fans out to many declarations.** Polysemy
  lives entirely on the language side.
- **Line segment.** As data, a pair of points. As extension, the set of
  points between them, which needs a betweenness predicate. The dictionary's
  hypernym edge "segment is a kind of line" is true in the extension view (set
  inclusion) and meaningless in the data view (unrelated types with a map).
  This is the *computed, not extracted* pattern from the architecture review:
  **a hypernym edge has two formal readings, and compiling it forces the
  choice.**
- **Triangle.** Three points plus the hypothesis that they are not collinear.
  The degenerate case the dictionary hand-waves is a hypothesis the kernel
  must carry. Over the reals, "not collinear" cannot be a negation; it must be
  a positive apartness witness (the same lesson the setoid spine taught with
  `Equiv` versus `Eq`). Over rational points it is decidable. So "triangle" is
  a graded family in the ADR-0603 sense: constructive form over ℝ, decidable
  form over ℚ, and the boundary refutation that the degenerate triple is
  excluded. The dictionary sense names the family.
- **Hyponyms of triangle** (equilateral, isosceles, scalene, right, acute,
  obtuse). Six predicates on the type. The edges to "triangle" are
  definitional and carry nothing. The edges *among* them carry everything:
  every equilateral triangle is isosceles; no triangle is both right and
  obtuse. **A hypernym edge between two predicate senses is a universally
  quantified implication, provable and checkable, with footprint zero.**
  OpenGloss has 1.3 million hyponym edges and can express none of them as
  anything but an assertion.
- **Hypernyms of triangle** (polygon, plane figure, shape). Polygon needs a
  new data structure and an injection; that is kernel work. "Plane figure"
  and "shape" have no definition anyone would write. The chain goes informal
  after one rung, and *how many hypernym steps above a computable sense the
  graph stays computable* is a number worth measuring.
- **Meronymy** (sides, vertices, angles) maps most cleanly: fields and
  derived projections of the structure; "three sides" is the arity of a
  constructor.

### 5.2 Animals: dog, mammal, animal

No kernel content exists, and the chain goes the other way: long and
formal-looking, with the formality coming from a different source.

- **Animal.** Two senses that disagree (Animalia includes humans; the
  everyday sense does not). Neither compiles: Animalia is a clade, a
  membership claim in a tree that a body maintains. **The checker for "X is an
  animal" is a lookup in a versioned authority, not a proof.**
- **Mammal.** Two definitions in one sense: characteristic (hair, milk, three
  middle-ear bones) and cladistic (descendants of one ancestor). They coincide
  on the known tree by construction and are different intensions; the
  platypus is the standing reminder that live birth was never in either. In
  kernel terms: two predicates and a fact that they agree on a snapshot,
  which is a finite decidable check that goes false the day a fossil moves.
  **So the fact carries a version, exactly as settled-statement pins carry a
  digest.**
- **Dog.** *Canis familiaris* or *Canis lupus familiaris*; the answer changed
  in 2005 and 2021. The hypernym edge "dog is a kind of wolf" is neither true
  nor false: it is a decision of a naming authority on a date. **This is the
  largest single difference from geometry: a geometry hypernym edge is a
  theorem; a taxonomy hypernym edge is membership by fiat, external,
  versioned, citable.**
- **Hyponyms of dog.** Breeds are not natural kinds; a breed is a standard
  written by a kennel club, closer to a legal definition than to a clade, and
  registries disagree. Below breeds sit individuals, and `instance_of` is the
  right edge. Instances host the one genuinely derivable fact: transitive
  closure ("Lassie is a dog, dog is under mammal, so Lassie is a mammal"),
  computed rather than asserted, with a checker that rejects a closure that
  skips a step.
- **Hypernyms of dog.** Canis, Canidae, Carnivora, Mammalia, Vertebrata,
  Chordata, Animalia, then organism, entity. Every rung to Animalia has an
  NCBI integer id. The chain is long *and* the formality is a data structure,
  not a theorem. Checkable: that the tree is a tree, that the graph's edges
  agree with the authority at a version, that closure is computed correctly.
  Not checkable: whether Carnivora is "really" a clade.
- **Properties** are where the domains split hardest. "Mammals have four
  limbs" is typical; whales and three-legged dogs are the normal texture of
  biology, not edge cases. A kernel has no default logic. So a typical
  property becomes a graded family: the universal form only when the tree
  makes it universal (every dog has a spine, because Mammalia sits under
  Vertebrata); otherwise the counterexample is the fact (a boundary
  refutation) and the typical claim stays external with a frequency and never
  earns a proved status. **That is not a limitation to route around; it is
  the honest shape of the knowledge.**

### 5.3 Physics: force, meter, momentum

- **Force.** A vector quantity with dimension mass · length · time⁻². That is
  a type. **Dimensional analysis is type checking, literally**: a quantity is
  a number tagged with an exponent vector over the seven base dimensions;
  addition requires equal tags; multiplication adds them. The kernel refuses
  "velocity plus acceleration" the way it refuses `Nat` plus `Bool`. It is
  the cheapest and most valuable check in the domain.
- **Meter.** Since the 2019 SI redefinition, c, h, e, and k_B are exact by
  fiat and the units are derived from them. "Meter" is now a definition
  chain with nothing empirical in it; the empirical content moved entirely
  into measured quantities. CODATA at a version is the authority snapshot and
  the SI brochure edition is its digest.
- **Hyponyms of force** (gravitational, electromagnetic, normal, friction)
  are not predicates on one type the way isosceles is; they are different
  laws producing values of one type. **Momentum's hypernym "conserved
  quantity" is a theorem, not an edge**: conservation of momentum follows from
  Newton's third law, and conservation laws follow from symmetries by
  Noether. That is real mathematics over ℝ, in reach of the constructed-real
  prelude's limits and integrals.
- **Computation.** Projectile range, escape velocity from energy
  conservation, orbital period, error propagation, order-of-magnitude
  checks: algebra and calculus over ℝ with the laws as hypotheses. **A
  physical law is an axiom and the footprint is the honest statement of a
  derived result.** Escape velocity carries "Newtonian gravitation, energy
  conservation"; the relativistic correction carries a different footprint.
  Regimes of validity are a graded family: the Newtonian form, the
  relativistic form, and the boundary fact stating where they diverge by more
  than a tolerance.
- **External.** The measured value of G with its uncertainty; whether a law
  holds in an untested regime; whether a model applies to a system. The
  kernel certifies the derivation, never the applicability.

### 5.4 Law: contract, negligence

Law has the identity structure of taxonomy (an authority snapshot with a
date) and the computational structure of physics (exact reasoning over
imported premises). It is the union of the two hard cases.

- **Contract.** Elements: offer, acceptance, consideration, capacity,
  legality. A conjunction over a fact pattern is the basic computation of
  the domain. The definition is by authority at a version: jurisdiction,
  Restatement, year.
- **Negligence.** Duty, breach, causation, damages. Hyponyms: negligence per
  se, gross negligence, the comparative-fault regimes. Hypernyms: tort, civil
  wrong. The regimes show how law differs from biology *in our favor*:
  **biology has typicality with no rule for exceptions; law makes exceptions
  explicit.** "Enforceable unless a listed defense applies" is default logic
  with a closed exception set for a jurisdiction at a date, which the kernel
  can hold as a universal statement over an explicit finite list. Catala, the
  language built for French tax law, is the existing proof that this shape
  compiles.
- **Computation**, more of it than people expect and most of it exact:
  limitations periods with tolling and deadline rules that skip weekends and
  holidays; tax, where a code section is a total function from a fact
  pattern to a rational number and the return is a program; expectation
  damages, prejudgment interest, comparative-fault apportionment as a
  piecewise function with the jurisdiction as a parameter; cap tables, where
  dilution and liquidation-preference waterfalls are piecewise-linear
  functions over ℚ and "this term sheet's waterfall matches the model at every
  exit value" is a statement the ordered-ring `linarith` and `ring` producers
  can already discharge; UCC priority ordering, sentencing grids, support
  formulas. In each case the footprint names the statute sections and the
  jurisdiction snapshot, the computation is exact and checked, and
  interpretation stays external. "Under the 2024 code as codified, with these
  facts, the tax is X" is established. "The agency agrees" is asserted.

### 5.5 Computation over dogs, and what it needs from the stack

Very little of it is "Lassie is a mammal"; OWL did that in 2004. The
computations people want are:

| computation | shape | what the kernel certifies | what stays imported |
|---|---|---|---|
| pedigree consistency | DAG check plus date arithmetic | the registry is acyclic and dates are ordered | the registry itself |
| inbreeding coefficient | Wright's sum over ancestor paths, rational | the registry's number is the formula's value | the pedigree |
| Mendelian ratios | finite probability model over ℚ | two merle parents give 1/4 double merle | that the trait is single-locus dominant |
| dosing | mg/kg with a species ceiling; dimensional analysis | the inequalities and the units | the ceiling, the MDR1 allele frequency by breed (typicality) |
| allometry | metabolic rate ∝ mass^0.75 | the algebra | the exponent |
| breed-specific legislation | elements test under a statute | the fact pattern satisfies or fails the elements | the statute text, the interpretation |
| quarantine windows | interval arithmetic over dates | the window | the schedule |

In every row the premise is imported and versioned, the computation is
exact, and the checker certifies the computation, never the premise. The
semantic web could hold the premise and not the computation. A CAS could do
the computation and not the trust. The union does both and keeps them in
separate columns.

### 5.6 The four domains side by side

| domain | authority layer | computable layer | external layer |
|---|---|---|---|
| geometry | Euclid's axioms, tiny | nearly everything | almost nothing |
| animals | NCBI tree, huge | closure and pedigree arithmetic, thin | typicality, large |
| physics | laws and SI constants | derivations, large; needs calculus over ℝ | measurement and regime validity |
| law | codified text by jurisdiction and date | application (tax, deadlines, damages, waterfalls), large | interpretation |

## 6. The data-model mapping

One line per piece, as the conversation settled it:

- An OpenGloss **sense** is a concept. It fans out to kernel declarations by
  carrier, and links to a **family** of declarations with the carrier as an
  edge attribute, not to one canonical carrier, because "triangle" over ℝ and
  over ℚ are provably different objects and ADR-0603 already made this call
  for classical theorems.
- A **definition** compiles to a `Definition` plus a graded fact family, with
  the degenerate case refuted explicitly.
- A **hypernym edge between predicates** compiles to a universally
  quantified implication: a fact, provable, checkable, footprint-named.
- A **hypernym edge to a non-predicate** (triangle → polygon) compiles to an
  injection between types.
- A **hypernym edge between natural kinds** (dog → Canidae) compiles to a
  membership in an authority snapshot, checked by lookup against a pinned
  version and digest.
- A **derived hypernym** is a computed transitive closure with a checker that
  can fail.
- A **meronym edge** compiles to a projection (geometry, structures) or to a
  typicality (organisms).
- A **property edge** is a universal fact only when the authority layer
  makes it so; otherwise it is external with a frequency, and its
  counterexample is recorded as a boundary refutation.
- An **instance edge** (`instance_of`) is where an individual enters the
  graph, and it inherits by closure.
- An **authority snapshot** is a fourth producer in the ADR-0601 sense, beside
  autogenesis, the CAS, and the importer: its evidence is a lookup against a
  pinned digest, it sits behind the same trust anchor, and its imports are
  labeled scaffolding, never headline. This keeps "every dog is a mammal" from
  ever being counted with "every equilateral triangle is isosceles."
- An edge that compiles to none of the above is the **informal boundary**,
  and the ledger records it as external status only.
- A natural-kind sense carries an **authority key** (Wikidata QID, NCBI
  taxid). OpenGloss v3 already carries QIDs on proper nouns with entity type
  `SPECIES`; the schema move is extending the key to common-noun natural
  kinds.

## 7. What is genuinely new, and what is not

Not new: identifiers, typed edges, open world, subsumption, closure. The
semantic web had all of it.

New, on one axis: **self-extension bounded by a checker that cannot be
inflated.** A knowledge graph is a record. This repository's math library is
a cycle: the concept DAG says what to prove next, producers produce, the
kernel checks, the ledger records, and nobody can pad the metric. The
taxonomy of a world graph asks what to generate next, and the concept DAG
asks what to prove next, and the argument of this note is that they are the
same object seen from two sides. Whether the cycle closes over the world the
way it closed over ℕ is the open bet.

## 8. First experiments

Ordered by how much of the stack already exists for them.

1. **The computable-sense rate.** Take the OpenGloss senses tagged
   mathematics (a few thousand). For each, try to resolve the gloss to an
   axeyum declaration by *shape* (`examples/shape_search.rs`), not by name.
   Report the fraction that compile, the fraction that compile to the wrong
   thing, and the fraction with no target. That number says how far the
   kernel currently reaches into ordinary language, and it is a
   blind-evaluation exercise: hold out a family of senses first, and never
   let the generator see them.
2. **Hypernym depth to the informal boundary.** For every computable sense
   from (1), count hypernym steps until an edge compiles to nothing. For
   triangle the number is one.
3. **Geometry as the first graded families over a world concept.**
   `Segment`, `Triangle`, and the six hyponym predicates over `CPoint`, with
   the apartness form over ℝ, the decidable form over ℚ, and the degenerate
   refutation. Every hyponym-to-hyponym edge lands as a fact with footprint
   zero.
4. **Law as the first non-math domain.** Its computable layer is large,
   exact, valuable, and mostly arithmetic the producers already handle; its
   authority layer is text rather than a tree; the domain expertise exists in
   house; and the OpenGloss taxonomy already has a dozen law leaves. The first
   artifact is a fact whose footprint names a statute section. A
   liquidation-preference waterfall over ℚ is a candidate the ordered-ring
   producers can discharge today.
5. **Physics after the calculus rungs.** Dimensional analysis as a typed
   quantity carrier is cheap and could land early; derivations wait on the
   constructed-real prelude's limits, derivatives, and integrals.
6. **Biology last.** Its computable layer is thin; what it mostly needs is
   the authority-snapshot producer and the typicality status, which are
   infrastructure the other domains need anyway.

## 9. Constraints this note inherits

- **One trust anchor.** No world-graph producer gets its own admission path.
  Everything lands through `Kernel::add_declaration` or stays external.
- **The metric is the trusted base.** The headline numbers stay: assumptions
  remaining per prelude, and results the system established with nobody
  writing the proof. An imported authority row never counts toward either.
- **Blind populations.** A held-out family of senses is spent the moment a
  producer reads it; the ADR-0542 amendment discipline applies unchanged.
- **Checkers that can fail.** Every consistency rule over the graph ships
  with a mutation that kills exactly one test, or it is not a checker.
- **Determinism.** Stable iteration order over the graph, explicit seeds for
  any sampling, explicit resource limits. No hash-map order in an export.

## 10. Open questions

- Whether a sense should link to a family of declarations or to one
  carrier (this note argues family; see §6).
- How to represent typicality without either pretending it is universal or
  discarding it: a frequency with provenance is the current answer, and it is
  not a proof of anything.
- Whether an authority snapshot's digest belongs in the axiom footprint
  itself (so "assumed NCBI 2026-06" reads out of the kernel) or beside it in
  the ledger. The footprint reading is more honest and harder to build.
- How the OpenGloss cost model (per-call budget, renditions, walk) composes
  with a checker that rejects: a rejected edge is a cost with no product, and
  the walk needs to learn from refusals the way the flywheel learns from
  declines.

## Related

- [North star](north-star.md), [mission and scope](mission-and-scope.md)
- ADR-0601 [three producers, one trust anchor](../09-decisions/adr-0601-three-producers-one-trust-anchor.md)
- ADR-0603 [classical theorems land as graded statement families](../09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
- ADR-0542 [held-out partition breach repair](../09-decisions/adr-0542-held-out-partition-breach-repair.md)
- [Evidence and checker discipline](../../contributor-guide/evidence-and-checker-discipline.md)
- [The cost model and Pareto position](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
- OpenGloss: [paper](https://arxiv.org/abs/2511.18622), [v1.3 dataset](https://huggingface.co/datasets/mjbommar/opengloss-v1.3-dictionary)
