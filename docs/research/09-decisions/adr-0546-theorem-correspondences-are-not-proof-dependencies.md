# ADR-0546: A theorem correspondence is a first-class artifact, and it is not a proof dependency

Status: accepted
Date: 2026-08-24
Index-summary: `artifacts/correspondences/*.json` states that two settled facts are the same mathematical content, on the `artifacts/facts/` one-file-per-claim pattern. Not `depends_on` — the gate refuses any pair the ledger's transitive dependency closure already connects, in either direction. `carrier-transport` is checked structurally by erasing the carrier and comparing statements; the two status axes (`derivation_status` / `external_status`) mirror the ledger's and each must be backed by what is in the document. 39 mutations, 39 killed, one test each.
Index-status: accepted

## Context

Two lanes landed `Int.fib_cassini` and `Rat.det2_mul` hours apart on 2026-08-24
without referring to each other. They are the same theorem: with
`M = [[1,1],[1,0]]`, `Mⁿ` has entries `[[fib(n+1), fib(n)], [fib(n), fib(n−1)]]`
and `det M = −1`, so multiplicativity gives `det(Mⁿ) = (−1)ⁿ`, which expands to
exactly Cassini's identity. The chain continues — `M`'s characteristic
polynomial `λ² − λ − 1` **is** the recurrence under `f(n) ↦ λⁿ`, whose roots are
φ and ψ — so "Fibonacci", "linear recurrence", "matrix power", "determinant",
"eigenvalue" and "golden ratio" name one structure. Nothing in the data model
could say any of that, and a user asked whether they could navigate it.

**The existing vocabulary was checked first, and it does not suffice.** This is
the finding that decided the shape of everything below.

`artifacts/facts/*.json` has `depends_on` — 114 of 358 facts, 159 edges — and it
is the wrong relation on purpose. It says one **proof** used the other, which is
a statement about proof order. Cassini's kernel proof is an induction that never
mentions a determinant, so no `depends_on` edge will ever connect the two, no
matter how much more mathematics lands.

`artifacts/autogenesis/knowledge-overlay-v1.json` declares eight relation types.
Measured 2026-08-24, none of them can carry this edge, and the reasons are
structural rather than incidental:

| relation | domain → range | why not |
|---|---|---|
| `formalizes` | fact, kernel-declaration → concept, encounter | target must be a `math-education` concept; and every edge is required to be `completeness: partial`, so two of them joined through a shared concept cannot say the two are the same idea. It is a **join**, not an edge, and it loses direction and the transport. |
| `exemplifies` | fact, operation, capability → concept, encounter, technique | same range restriction; a theorem cannot be a target. |
| `unlocks` | fact, capability → fact, capability, concept, encounter | the only fact-to-fact relation, and its semantics are *reachability*: "establishing the source makes the target newly reachable or measurably cheaper". That is planning, which is the thing to be distinguished from. |
| `direct-theorem-depends-on` | kernel-declaration → kernel-declaration | read from accepted kernel terms. Trustworthy, and structurally blind to this: Cassini's term contains no determinant. |
| `blocked-by`, `established-by`, `realizes-capability`, `uses-technique` | — | connect a result to an obstruction, an operation, or a capability. |

**A briefed premise was wrong and is worth correcting.** The brief reported that
`technique` and `concept` are "first-class node kinds with zero instances". They
have zero rows in the overlay's `entities` array, but that array holds only
`overlay-entity`-resolved rows, and both kinds are declared under the
`math-education` namespace with `resolution: external-pinned`. Measured: 19
`formalizes` and 3 `exemplifies` links point at `C:` concepts, and 2
`uses-technique` links at `TQ:` techniques — 24 instantiated endpoints. They are
resolved next door by design, not missing. So the answer to "is this instances,
not schema?" is **no**, and for a sharper reason than an empty table.

**The sibling corpus already ran the experiment this decision depends on.**
`../math-education` has `bridges_to`, a typed cross-domain edge carrying a
`domain_area` and a prose `reason`. Measured over its 1,567 concepts: 1,263
bridges, **100% carrying a reason**, lengths 75–328 with a median of 190. And
`graph/QUALITY.md` records that `volume.md` shipped a bridge to `C:pi` whose
reason text was **entirely about density**. It validated cleanly because both
fields were well-formed. Its `epistemic_status` field tells the same story from
the other side: 586 of 1,567 concepts are labelled `axiom`, including
"abstraction" and "file-system", because the vocabulary has no `definitional`
term and membership is all the validator checks. Two lessons, both load-bearing
here: **a required prose field is not evidence**, and **a status vocabulary
checked only for membership will be misused at scale**.

That corpus also has no same-theorem edge at all. Its closest structured thing
is `deliberately_distinct_from` — an adjudicated *non*-merge with a mandatory
reason — and the strongest same-theorem claim in either of the two files the
brief pointed at ("A Schur number is the Rado number of the single equation
x + y = z") is prose buried inside a `requires.reason`.

## Decision

**A correspondence is one JSON file per adjudicated claim under
`artifacts/correspondences/`, schema
`artifacts/ontology/theorem-correspondence.schema.json`, gated by
`scripts/validate-correspondences.py`.** Its endpoints are exactly two fact ids.
It is validated by rules that recompute something, and it is refused whenever
the fact ledger already relates its endpoints.

Six decisions, each with its reason.

1. **A directory of files, not rows in the overlay.** The overlay is one file
   that every lane would append to, which is this repository's most expensive
   documented failure mode — twelve clobbering incidents, `PLAN.md` and the ADR
   index both made generated because of it. `artifacts/facts/` is the proven
   pattern for a population many lanes extend, and this follows it exactly.
   Nothing in any existing artifact changed.

2. **Endpoints are FACTS, not kernel declarations.** A fact is the only object
   here that carries a formal statement. A `kernel-declaration` endpoint would
   resolve against `kernel-dependency-projection-v1.json`, whose rows carry an
   id, a declaration kind and an axiom footprint — **and no type**. A
   correspondence anchored on a projection row could not be checked against
   anything, which is precisely the unfalsifiable-edge failure this gate exists
   to prevent.

3. **The correspondence and `depends_on` are mutually exclusive, and the gate
   enforces it over the TRANSITIVE closure.** Direct edges are not enough: if A
   depends on B and B on C, A's proof reaches C, and an "A ≡ C" correspondence
   is still a statement about proof order. A rejected pair gets a message naming
   `depends_on` as the field that belongs there.

   This is checkable against the committed ledger rather than a fixture.
   `F:ml430-int-fib-add-two` **already** `depends_on` `F:ml430-nat-fib-add-two`,
   because the ℤ proof genuinely goes through the ℕ one — a pair that looks
   exactly like a carrier transport and is a proof dependency. The control pins
   that refusal.

4. **`carrier-transport` is checked structurally.** Erase every spelling of the
   carrier from both formal statements; the results must be equal.
   `∀ {n : ℕ}, Nat.fib n = 0 ↔ n = 0` and `∀ {n : ℤ}, Int.fib n = 0 ↔ n = 0`
   both erase to `∀ {n : ⟨C⟩}, ⟨C⟩.fib n = 0 ↔ n = 0`. This is the answer to
   math-education's `volume.md` bug: the pairing is a computation, not a
   reading. A fragment with no carrier spelling in the map **fails**, rather
   than skipping the check — an unmeasured claim is not a passing one.

5. **Two status axes, mirroring the ledger, each backed by the document.**
   `derivation_status` is what we established about the correspondence,
   `external_status` what mathematics knows. `asserted` holds **exactly** when
   `via` is empty (checked both ways); `route-recorded` requires every non-null
   `via` ref to resolve to a fact or to a declaration the kernel projection has
   actually observed; `mechanized-here` additionally forbids a null ref and
   requires a checker command. Evidence at all requires `mechanized-here` —
   the same shape as the ledger's rule that an `open` fact carries an **empty**
   evidence array. `external_status: novel-here` requires `mechanized-here`.

   A `null` ref is a **named gap**, and naming it is what separates
   `route-recorded` from a longer paragraph.

6. **The gate reports the zeroes.** `CORRESPONDENCES|...|kinds=...` prints every
   vocabulary term including the ones nobody instantiated, so a declared-but-empty
   kind is visible rather than merely declared. That is the defect the overlay's
   own unpopulated kinds illustrate, made impossible to miss here.

## Evidence

Landed with three instances, all `route-recorded`, none inflated:

- `X:varignon-two-independent-formalizations` — Varignon's theorem is in the
  ledger **twice**, by `cas-certificate` over NRA and by `kernel-lean` over
  `CPoint`. Neither cites the other and neither could: different languages,
  different carriers, and different equalities (`Eq` versus `CPoint.Equiv`, a
  defined Prop relation). The ledger already reports how many *evidence rows*
  were re-derived by two independent checkers and reads it as assurance; this is
  the same measure one level up, on a whole theorem, and the data model had no
  way to notice it. Measured: it is the **only** such pair — ten NRA geometry
  facts, five CPoint ones, one overlap.
- `X:fib-eq-zero-across-nat-and-int` and `X:fib-dvd-across-nat-and-int` —
  carrier transports whose structural check passes, whose endpoints the ledger
  does not connect, and whose third `via` step (`Int.ofNat` injectivity;
  `↑a ∣ ↑b ↔ a ∣ b`) has a `null` ref because no fact states it.

Gate output before and after this change:

```
python3 scripts/validate-facts.py
  358 facts checked, 0 errors  (computed=2 conjectured=3 open=191 proved=158 refuted=4)     [before]
  358 facts checked, 0 errors  (computed=2 conjectured=3 open=191 proved=158 refuted=4)     [after]

python3 scripts/validate-autogenesis-knowledge.py
  AUTOGENESIS_KNOWLEDGE_OK|entities=6|links=33|relations=8|sources=2                        [before]
  AUTOGENESIS_KNOWLEDGE_OK|entities=6|links=33|relations=8|sources=2                        [after]

python3 scripts/validate-correspondences.py                                                 [new]
  CORRESPONDENCES|checked=3|facts=358|kernel_declarations=1142
    |kinds=carrier-transport:2,independent-formalization:1,specialization:0
    |derivation=asserted:0,route-recorded:3,mechanized-here:0
    |external=classical:3,folklore:0,novel-here:0,unclassified:0|violations=0
```

Mutation controls — `python3 scripts/tests/mutation_controls.py correspondences`:
**39 mutations, 39 killed, each exactly one of 45 tests**, baseline green. One
blunt test initially killed 2 because its fixture named nonexistent endpoints;
the fixture now keeps real ones and the comment records why.

## The motivating example is NOT landed, and that is a finding

`Int.fib_cassini ↔ Rat.det2_mul` — the pair this whole decision exists for — is
**not in `artifacts/correspondences/`**, and the reason is not the schema.

Neither theorem is an addressable object in this repository's data model:

- Neither has a fact. `Rat.det2_mul` appears only inside the *evidence* of
  `F:cramer-rule-forward-direction-over-constructed-rationals`, whose statement
  is Cramer's rule. `Int.fib_cassini` appears in no fact at all.
- Neither is in `kernel-dependency-projection-v1.json`. That artifact was
  refreshed at `e256492c2` **on 2026-08-24**, and `git merge-base --is-ancestor
  aa3e8ea24 e256492c2` is **false**: the linear-algebra commit is not an
  ancestor of the refresh. The projection holds 195 `Rat.*` declarations and
  zero matching `det2`, `cramer` or `fib`.

Writing the edge anyway would have required either forging a row in a
kernel-derived artifact, or inventing a fact whose `checker_command` this lane
never ran. Both are the exact defect the gate is built against, and neither is
worth the appearance of completeness. **The prerequisite is one fact each, with
real evidence rows; the correspondence is then a single JSON file.** Until then
`specialization` is a declared kind with zero instances, and the gate prints
that zero on every run.

Related correction: the projection's staleness is a live blind spot beyond this
decision. Any `kernel-declaration` endpoint anywhere in the knowledge overlay
inherits it, and a theorem proved today is invisible to every consumer of that
artifact until a lane spends a `cargo run` on the refresh.

## Alternatives rejected

- **Reuse `unlocks` for it.** Rejected: its semantics are reachability, and the
  single most important property of this edge is that it is *not* about proof
  order or planning. Overloading it would have made both meanings unreadable and
  would have put the new claim behind a relation whose existing 0 instances say
  nothing about how it is meant.
- **Join two `formalizes` edges through a shared `math-education` concept.**
  Rejected: it is a join rather than an edge, it loses direction and the
  transport entirely, it requires the sibling corpus to have the concept, and
  every `formalizes` edge is *required* to be `completeness: partial` — so two
  of them cannot compose into "these are the same".
- **Add the relation to `knowledge-overlay-v1.json`.** Rejected on this
  repository's own evidence: one file every lane appends to is the shared
  append point that produced twelve clobbering incidents and made two files
  generated. The overlay can adopt `corresponds-to` later by pointing a
  namespace at this directory; nothing here forecloses it.
- **Allow `kernel-declaration` endpoints.** Rejected: projection rows carry no
  type, so nothing about such an edge could be checked. Revisit if the
  projection ever carries statements — that is the single change that would make
  it worth reopening.
- **A symmetric edge, as `bridges_to` is declared.** Rejected on measurement:
  next door `symmetric: true` is declared in the vocabulary, `owl:SymmetricProperty`
  in the ontology, **and nothing reads either** — 13% of undirected pairs are
  reciprocated. A symmetry claim nothing enforces is decoration. Here the array
  is ordered, `specialization` uses the order, and one adjudication per unordered
  pair is enforced.
- **Regenerate the kernel projection to make Cassini addressable.** Rejected:
  it needs a workspace `cargo run` in a tree five lanes are actively editing,
  from a cold target directory, and it would rewrite a generated artifact whose
  census counts other documents quote. The staleness is recorded above instead.
- **A prose `reason` field and set-membership checks, as next door.** Rejected
  on that corpus's measured outcome: 100% reason coverage did not catch a bridge
  whose reason was about the wrong subject, and 586 `axiom` labels did not
  survive contact with a vocabulary lacking the term people needed. Prose stays
  in the file — it is what a human reads — but it is the least load-bearing part
  of it, and the ADR says so out loud.

## Consequences

- A lane can now record that two results are the same idea, and cannot record it
  where `depends_on` belongs. The two populations stay disjoint by construction.
- The 20 cross-carrier ℕ/ℤ pairs already in the ledger (`modeq-*`, `fib-*`,
  `gcd-greatest`, `add-modeq-*`) are the immediate backlog, and the structural
  check makes each one cheap to adjudicate and impossible to fake. Some of them
  will be **refused** as dependencies, which is the useful half of the answer.
- The Varignon pair gives a new assurance question a home: *which theorems does
  this repository hold by two independent routes?* Today the answer is one.
- **What this does not do.** It moves no existing metric. It adds no theorem, no
  axiom-freedom, and no capability. It is a vocabulary plus a gate, and this
  repository has a documented failure mode of shipping exactly that
  (`docs/autogenesis/228-capsule-lane-retrospective.md`). The defence is that
  the gate refuses things — including, today, the example it was built for.
- Widening the endpoint kinds, adding a correspondence kind, or adding a status
  value all need this ADR revisited, because each of the three vocabularies is
  small on purpose and each has a rule that has to be written alongside it.
