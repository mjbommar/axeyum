# Axeyum top-three focus plan

Date: 2026-08-25

This plan converts the current architecture audit into three priorities. It is
not another inventory of possible work. Each priority has a product outcome, a
measured starting point, an ordered implementation path, and an exit that must
be demonstrated by executable evidence.

Axeyum's product identity is:

> An evidence-native reasoning system in which heterogeneous, untrusted search
> proposes results; small independent checkers decide what becomes durable
> knowledge; and that knowledge makes the next search more capable.

Z3/cvc5, Lean/Mathlib, computer algebra systems, program analyzers, and language
models are therefore peers, sources, or untrusted engines. Axeyum owns the typed
semantics, evidence, provenance, checking, and compounding knowledge loop.

## Current measured boundary

- The pure-Rust reasoning stack has real end-to-end SMT, CAS, kernel, program
  verification, and proof-artifact routes, but its coverage and assurance are
  uneven by fragment.
- The generated kernel projection currently contains 1,552 declarations: 1,206
  theorems, 242 definitions, 29 constructors, 22 inductives, 22 recursors, and
  30 axioms. It reports 1,522 axiom-free declarations and 6,838 direct
  theorem-dependency edges. This is a substantial checked library, but it is
  not an autonomous-production count.
- The fact ledger contains 696 propositions: 502 proved, 4 refuted, 2 computed,
  185 open, and 3 conjectured. Its 26 authoritative/counterfactual operation
  rows contain only 2 reusable multi-target producers and name only 33 fact
  IDs. Most checked theorems therefore remain human-constructed, and most
  ledger facts have no reusable producer assigned.
- Sixteen live agent episodes exist. Two produced axiom-free proofs re-derived
  in a second kernel, but the current producer vocabulary closes only a tiny
  frontier.
- The kernel, fact ledger, tactic catalog, obstruction graph, and concept graph
  are separately useful, but do not yet form one lemma-search substrate.
- The generated lemma index now covers all 1,206 kernel theorems and their 6,838
  direct edges, but only 325 theorems link exactly to 329 fact records. It keeps
  74 unresolved evidence IDs explicit rather than guessing, leaving 881
  theorems without exact fact links.
- The Rust and Python surfaces are broad, but integration churn can leave
  `main` red and evidence fixtures can be mistaken for production populations.

### Landed autonomous-loop increment

The first action against this plan moved three facts through the authoritative
path rather than adding proof code for new targets:

1. the frontier selected open `Nat.ModEq.symm`; the existing multi-target
   producer reconstructed it, independent checking accepted it, and the
   crash-safe transaction admitted it;
2. a fresh frontier selected and admitted `Nat.ModEq.trans` through the same
   operation;
3. the durable symmetry admission made `Nat.ModEq.comm` dependency-ready, so
   the previously deferred target was added to the unchanged producer's
   source-bound family, selected by a fresh frontier, and admitted.

Reusable multi-target production credit consequently rose from 8 to 11 facts,
and the family now covers eight Int/Nat targets. This demonstrates durable
state changing later scheduling. It does **not** yet satisfy the stronger
proof-compounding exit: the commutativity producer reconstructs Eq/Iff symmetry
directly and records zero theorem dependencies, so the admitted symmetry fact
does not occur in its checked proof closure. The next producer increment must
consume a selected library lemma rather than merely being scheduled by it.

The first deterministic bridge for that next increment is now implemented.
The agent's `lemma_candidates` read tool joins an open goal's authored
`depends_on` edges to exact fact-to-kernel links in the generated lemma index.
For `Nat.fib` monotonicity it returned the proved dependency
`Nat.fib_le_succ` as an axiom-free kernel candidate. A reference composition
now closes that stronger theorem by eliminating its order derivation and
chaining the adjacent-step lemma; the kernel records direct dependencies on
`Nat.fib_le_succ` and the new target-agnostic
`Nat.monotone_of_le_succ` combinator, and the ledger is settled from that
axiom-free term. The combinator itself derives full monotonicity for any
`Nat → Nat` function from its adjacent-step proof by eliminating the order
derivation. Unlinked dependencies remain explicit rather than repaired by
name similarity. This proves mathematical compounding through the connected
graph, but not autonomous construction: the reference constructor was written
by hand and production provenance correctly counts the result among the 472
settled facts with no authoritative operation.

## Comparative position

Axeyum should not be described as a replacement for any one neighboring
project. It combines narrower versions of several systems around a different
unit of value: a checked, provenance-bearing result that becomes searchable
input to the next bounded production attempt.

| Neighbor | What it is far ahead on | Axeyum's distinct strength | Axeyum's present weakness |
|---|---|---|---|
| Lean and Mathlib | Mature elaboration, tactics, IDE experience, ecosystem, and a research-scale mathematical library | Independent Rust checking, explicit axiom footprints, and treating imported Lean as one evidence route inside a heterogeneous system | Much smaller library, partial Lean-core coverage, little interactive elaboration, and minimal user community |
| Z3 and cvc5 | Solver performance, theory breadth/depth, quantifier heuristics, proof production, and industrial use | Route-specific evidence reports, original-query model replay, and a path from solver evidence into durable kernel theorems and a fact ledger | Uneven proof assurance across logics, incomplete theory combination, and many routes that still have no transferable proof |
| Isabelle/Sledgehammer-style systems | Mature interactive proving plus external-prover orchestration and large proof corpora | A more explicit machine-readable ledger/operation/episode model aimed at measuring autonomous compounding | No comparably mature proof language, IDE, simplifier ecosystem, or broad automated premise-selection results |
| AlphaProof/LLM proof agents | Learned proof search at enormous training and compute scale | Deterministic non-LLM producers, typed declines, strict held-out controls, and a checker/transaction boundary designed to remain authoritative when models change | Two successful production episodes out of sixteen is evidence of a functioning seed, not yet a productive autonomous system |
| Standalone CAS and program analyzers | Deep domain algorithms and mature domain workflows | One evidence/provenance vocabulary spanning CAS, SMT, kernel proofs, BMC, symbolic execution, and property checking | Breadth creates maintenance cost; many integrations are shallow relative to the specialist tools and lack one polished product front door |

The strategic wager is therefore credible but unproved: Axeyum is strongest in
trust-boundary design and connective tissue, competitive only on selected
narrow reasoning fragments, and weak in autonomous conversion rate, specialist
algorithm depth, library scale, and product ergonomics. The next milestone must
raise the first of those weaknesses without weakening the first strength.

## Priority 1: autonomous reusable proof production

### Outcome

The system repeatedly proves previously open facts through a reusable producer,
checks each proof in a second kernel, admits it through the transaction route,
and uses an admitted result in a later proof.

### Why first

This is the differentiating product claim and the present bottleneck. More
hand-built theorems, metadata, or solver fragments do not demonstrate the
flywheel. The current general producers cover structural induction and a small
definitional-equivalence family; remaining open facts require unfolding,
bounded lemma selection, transport, and composition.

### Ordered work

1. Convert producer declines into a ranked, typed strategy backlog.
2. Build a kernel-derived lemma-search index with exact dependency and
   visibility information; do not ask an LLM to invent the available library.
3. Expose the checked `Nat.monotone_of_le_succ` combinator through an operation
   that recognizes the adjacent-step monotonicity schema without naming
   Fibonacci or the target theorem.
4. Generalize that implementation into bounded best-first lemma composition.
5. Let an LLM propose lemma applications only across the untrusted boundary;
   the same kernel and footprint checks retain authority.
6. Admit successful results through the existing crash-safe transaction and
   repeat from a clean checkout.

### Exit evidence

- At least one new authoritative operation covers three or more previously open
  sibling facts without per-target proof code.
- Those facts are axiom-free and independently rechecked.
- One newly admitted fact occurs in the checked dependency closure of a later
  autonomously produced proof.
- Held-out evaluation remains uncontaminated and at least one held-out member is
  eventually proved without proof-affecting intervention.

## Priority 2: one connected theorem and strategy graph

### Outcome

Every constructed-kernel theorem is discoverable as a candidate lemma with
kernel-observed dependencies, reverse consumers, prelude visibility, assurance,
and any fact/concept/strategy links that actually exist. Missing links remain
explicit rather than being inferred from names.

### Why second

The library cannot compound if producers cannot query it. Today the kernel
inventory, fact ledger, operation registry, tactic catalog, obstruction graph,
and concept overlay use different populations. Human semantic enrichment is
valuable, but mechanical identity and dependency connectivity must not require
manual review.

### Ordered work

1. Generate a versioned lemma-search index from the accepted kernel declaration
   projection, including reverse use counts and dependency depth.
2. Bind exact kernel evidence IDs from fact records to declaration IDs and
   publish linked/unlinked populations separately.
3. Join active tactic preconditions and capabilities without granting them
   applicability authority they have not earned.
4. Expose deterministic neighborhood queries through Rust/Python.
5. Feed successful proof dependencies and typed declines back into the index.

### Exit evidence

- Kernel theorem count agrees exactly with the theorem-production authority.
- Every theorem appears exactly once in the lemma-search index.
- Every exact fact-to-kernel link resolves both endpoints; unresolved records
  are counted and retained.
- A producer selects a lemma from this index and the final checked proof records
  that dependency.

## Priority 3: stable and honest product integration

### Outcome

A user can install or build Axeyum, solve/replay through one supported CLI or
Python path, and trust that a green integration result covered the relevant
surface and only counted production evidence.

### Why third

Trust architecture is not a product property when the integration branch is
frequently red, optional dependency groups are omitted by CI, or illustrative
fixtures make an evidence population look nonempty. The breadth of the codebase
now makes release discipline a prerequisite for further scale.

### Ordered work

1. Separate production agent episodes from illustrative fixtures in the gate;
   checking zero production episodes must fail.
2. Make Python dependency groups and wheel smoke tests explicit CI authorities.
3. Preserve one stable SMT/evidence CLI and one typed Python front door; classify
   other examples as experimental.
4. Publish a generated product-health summary from actual gate and artifact
   populations rather than prose.
5. Reduce shared append points and oversized bespoke modules when a real product
   boundary has been exercised.

### Exit evidence

- The production episode gate excludes fixtures and reports a nonzero real
  population.
- Current `origin/main` has green Rust, Python, docs, and evidence gates.
- A clean install runs one SAT/model-replay case and one independently checked
  UNSAT or kernel-proof case.
- No product claim depends on a skipped, warning-only, zero-population, or stale
  gate.

## Sequencing

The critical path is not three independent projects:

```text
honest production gates
        -> connected lemma-search index
        -> reusable producer
        -> checked admission
        -> graph update
        -> next producer search
```

Priority 3 supplies trustworthy measurements. Priority 2 supplies the library
substrate. Priority 1 converts both into compounding output. Work may proceed in
parallel only when each increment preserves those dependencies and lands with
its own evidence.

## Stop-doing rules

- Do not count theorem volume as autonomous yield.
- Do not register one operation per theorem and call it a producer.
- Do not manually annotate connectivity that the kernel can derive.
- Do not add a new solver/CAS/prover route without an evidence and product
  consumer.
- Do not call a warning, skipped toolchain, fixture-only population, or running
  CI job green.
