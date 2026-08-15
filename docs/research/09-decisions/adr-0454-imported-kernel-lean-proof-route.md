# ADR-0454: `imported-kernel-lean` is a separate proof route from `kernel-lean`

Status: accepted
Date: 2026-08-15
Index-summary: Foreign proof terms our kernel admits get their own `proof_route`, and cannot claim `axiom_footprint: []`.

## Context

The `formalized-math-2026-08` strand ingests proof terms this project did not
author: `axeyum-lean-import` reads an official `lean4export` NDJSON stream and
puts every translated declaration through `Kernel::add_declaration`, the same
trusted gate the hand-built preludes use. The gate re-derives each declaration's
type from its proof term, so a successful import is a real machine check by a
second, independent kernel.

That makes the label tempting: `proof_route: kernel-lean` already means "a proof
term an independent kernel type-checks", and an import satisfies that sentence
verbatim. The fact ledger has 23 facts carrying it.

Reusing it would be wrong, and the strand's own brief names the failure mode:
*an imported declaration is not the same epistemic object as one we proved.* The
ledger already separates `epistemic_status` (what we established) from
`external_status` (what mathematics knows); `proof_route` is where the third
distinction belongs, because it is the field `axiom_footprint` is scoped to.

## Decision

**`imported-kernel-lean` is a distinct `proof_route`, and it is not
`AXIOM_FREE_CAPABLE`.** A fact whose proof term was translated from a foreign
export and admitted by our kernel uses it; a fact whose proof term this project
constructed keeps `kernel-lean`. The validator additionally requires
`provenance.prior_art` on the imported route.

Two things differ between the routes, and both are the kind of difference
`axiom_footprint` exists to keep visible.

**Authorship.** Every `kernel-lean` fact is a proposition this project
constructed a proof of. That is the number the self-extension loop exists to
raise and the number the project publishes. An import raises no such number, and
a single shared label would let the headline count be inflated by ingestion — at
a rate bounded only by how fast a corpus streams. `validate-facts.py` therefore
reports the imported count on its own line, explicitly labelled "not evidence of
construction".

**Trust base.** `axiom_footprint: []` on `kernel-lean` means a measured fact
about a kernel environment: it admits no `Axiom`, `Opaque` or `Quotient`. An
import can reach that state *inside the imported environment* — three of the
five facts landed with this ADR do — and still rest on assumptions the
constructed route does not make:

1. the exporter faithfully rendered the source system's environment;
2. our translation of the wire format into kernel terms preserves meaning;
3. the delivered bytes are the producer's intended export. Format 3.1 has **no
   footer**, so completion is relative to the bytes handed over. This is not a
   hypothetical we invented for the ADR — `axeyum-lean-import`'s own
   documentation says it, and the README says import success "is not a claim of
   complete Lean compatibility or producer-stream authenticity."

So `[]` is unavailable here, the validator rejects it, and an imported fact's
footprint names those assumptions alongside whatever trusted declarations the
Lean proof term itself reaches.

### The two systems do not agree on how to spell a footprint

Measured 2026-08-15 on the pinned `classical-em.ndjson` stream: Lean's
`#print axioms Classical.em` reports three names (`Classical.choice`,
`propext`, `Quot.sound`), while `Kernel::axiom_footprint` on the same imported
declaration reports **six** — it adds `Quot`, `Quot.mk` and `Quot.lift`, because
our kernel classifies the entire quotient package as `Declaration::Quotient` and
counts all of it as trusted surface.

Ours is the more conservative reading and it is recorded verbatim. It must not
be silently reconciled to Lean's, which is another reason the routes cannot
share a footprint vocabulary: the same theorem, checked by two kernels, has two
correct footprints of different length.

## Consequences

- `artifacts/ontology/fact.schema.json` gains the enum value and the reasoning.
- `scripts/validate-facts.py` gains the route, the `prior_art` requirement, and
  a separate imported-count report line.
- Five facts land on the new route
  (`F:nat-le-refl`, `F:nat-le-succ`, `F:list-nil-append`, `F:bool-and-comm`,
  `F:prop-excluded-middle-classical`), each re-derived by two independent
  checkers: `cargo test -p axeyum-lean-import --test imported_fact_evidence`
  (our kernel) and `scripts/check-imported-fact-lean-axioms.sh` (a real Lean
  4.30.0 `#print axioms`).
- A future foreign system (OpenTheory, Metamath, Rocq) admitted through a
  *different* kernel would need its own route rather than this one, for the same
  reason: its trust base is different again. This ADR does not pre-authorise
  that; it establishes the pattern.
- **This ADR does not create a path for an imported fact to become a
  `kernel-lean` one.** If this project later constructs its own proof of the
  same proposition, that is a new fact (or a new evidence row plus a route
  change), and the change must be visible in the diff.

## Alternatives rejected

- **Reuse `kernel-lean`.** Rejected above: it conflates authorship and trust
  base, and it makes the project's headline metric ingestible.
- **Use `none` and explain in `notes`.** `none` means no machine established
  it, which is false — a kernel did. Prose in `notes` is exactly what
  `proof_route` was created to replace, after two footprint vocabularies
  coexisted in the ledger with nothing marking the difference.
- **Record imports as `evidence` rows on existing facts rather than as facts.**
  Attractive for propositions we already hold, and still available for those;
  but a fact carries exactly one `proof_route`, so an imported evidence row on a
  `kernel-lean` fact would sit under a route label that does not describe it.

  The question is **not** hypothetical, and it was answered by checking rather
  than by assuming. A sixth candidate, `Nat.not_succ_le_zero`, was dropped from
  this set on discovering that our own Nat prelude already proves it, axiom-free,
  on `kernel-lean` (`nat_theorem_inventory` and `theorem_axiom_footprint`,
  measured 2026-08-15). Landing it as an import would have understated what this
  project holds. Note also that the two are the same *proposition* and not the
  same *statement* — ours is over the kernel's own `Nat.le`, Lean's goes through
  the `LE` class as `LE.le.{0} Nat instLENat` — so an imported evidence row could
  not simply be attached to our fact either. That is the alignment problem, and
  it needs its own decision rather than being settled here.
