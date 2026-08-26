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
- A live high-stack production inventory reported 1,184 distinct theorems with
  empty measured axiom footprints. The committed declaration projection was
  stale at 1,100; regenerating it from current code now agrees exactly at 1,184.
  After merging the next constructive-real and rational increments, the
  projection and search index advanced together to 1,191. The production-
  provenance ledger credits
  only 8 established facts to reusable
  multi-target operations; most theorems remain human-built.
- Sixteen live agent episodes exist. Two produced axiom-free proofs re-derived
  in a second kernel, but the current producer vocabulary closes only a tiny
  frontier.
- The kernel, fact ledger, tactic catalog, obstruction graph, and concept graph
  are separately useful, but do not yet form one lemma-search substrate.
- The Rust and Python surfaces are broad, but integration churn can leave
  `main` red and evidence fixtures can be mistaken for production populations.

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
3. Implement the first measured family extension: unfold a relation such as
   `ModEq`, select bounded arithmetic lemmas, and compose the proof term.
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
