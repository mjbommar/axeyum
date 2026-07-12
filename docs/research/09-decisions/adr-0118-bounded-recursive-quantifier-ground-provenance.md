# ADR-0118: Bounded recursive quantifier ground provenance

Status: accepted
Date: 2026-07-11

## Context

ADR-0117 checks detached equality-clause literals only when every false sibling
is justified by original quantifier-free assertions. A generated complete
universal instance or earlier checked detached literal may become a real ground
equality/disequality premise in a later round, but ADR-0117 deliberately falls
back to another complete instance because it cannot replay that generated
premise from the original query.

Z3's online quantifier justification recursively connects an instantiated
clause to SAT/e-graph antecedents. Axeyum's fresh-QF round architecture needs the
same logical chain as an explicit arena-bound artifact before direct online
clause insertion can share it.

A recursive `Box<Certificate>` at every reason site would duplicate common
subproofs and make unused proof material hard to reject. False siblings already
name exact reason terms. A sorted per-certificate derivation table for only the
non-source terms preserves that identity and gives the checker one deterministic
lookup boundary.

## Decision

Add two public artifacts:

1. `QuantifierInstanceCertificate`: original universal, ordered binding tuple,
   and exact reconstructed ground instance;
2. `QuantifierGroundDerivation`: either an exact instance certificate or a boxed
   earlier `QuantifierClausePropagationCertificate` whose conclusion is its
   propagated literal.

Extend `QuantifierClausePropagationCertificate` with a sorted
`derived_reasons` table. Existing false-sibling reason vectors remain exact
ground `TermId`s. Original assertions need no table entry; every named reason
not present in the untouched assertion set requires exactly one derivation whose
conclusion is that term.

The checker:

1. validates exact universal substitution for every instance derivation;
2. recursively validates every propagation derivation against the same original
   assertion set;
3. enforces strictly increasing unique derivation conclusions and rejects unused
   entries;
4. caps recursion depth at 16 and total checked derivation nodes at 4,096;
5. evaluates each false sibling in a fresh e-graph containing only its named,
   successfully derived reasons; and
6. evaluates the complete source clause against the union of those reasons,
   requiring the carried detached literal to be the unique undetermined literal.

The retained loop records provenance whenever it admits a generated ground term:

1. complete urgent/deferred instance → exact instance certificate;
2. checked detached literal → checked propagation certificate;
3. rejected propagation → its complete exact-instance fallback.

When e-graph explanation or disequality lookup names a generated term, certificate
construction clones its retained derivation into the sorted table. Provenance is
monotonic with the ground set and is never inferred from term shape alone.

## Acceptance

- ADR-0117 source-only certificates remain byte-for-byte meaningful with an
  empty derived table and pass the same tamper gates.
- Generated complete equality/disequality instances can justify a later detached
  positive or negative literal; earlier detached literals can justify another
  propagation at the next round.
- Wrong assertion/tuple/instance/conclusion, missing/duplicate/unused derivation,
  wrong variant, reordered table, over-depth, over-node, and nested tampering
  reject and fall back to complete source instances.
- A three-or-more-stage chain returns the same verdict and witness set as
  complete-instance mode while reducing generated query DAG/tree volume or
  optimized end-to-end time.
- Quantified-BV/LIA decisions, replay, direct-Z3 differential results, and PAR-2
  do not regress; public evidence generation remains source-query based.
- Solver, bounded-instance, evidence, MBQI, bench, Clippy, rustdoc, links,
  foundational resources, formatting, and generated-matrix gates pass.

## Acceptance result

Accepted on 2026-07-11. `QuantifierInstanceCertificate` binds an original
universal, ordered ground tuple, and exact reconstructed instance.
`QuantifierGroundDerivation` carries either that artifact or a prior boxed
checked propagation. Every admitted generated ground term retains one such
derivation; later equality explanations and disequality lookup may name it only
when that retained entry exists. Failed batch replay still admits only complete
exact-instance fallbacks.

The checker reconstructs every instance recursively from the untouched
assertions, requires the derived-reason table to contain exactly the non-source
named reasons in strict `TermId` order, replays each sibling from only its named
facts, and checks the complete clause is unit under their union. Equality and
disequality instance reasons and prior propagation reasons pass. Missing,
duplicate, unused, reordered, wrong-conclusion, wrong-variant, wrong tuple,
nested tampering, depth overflow, and node-budget exhaustion reject. Source-only
ADR-0117 certificates retain an empty table and unchanged meaning.

The committed six-stage target has four extra false literals per source clause.
Complete-instance and recursive-detached queries both refute, while reachable
DAG nodes fall 54→17 (68.5%) and tree nodes 117→33 (71.8%). A separate
three-stage target checks a propagation whose reason recursively owns the prior
two checked implications. Depth 16 accepts and the next level rejects; the
checker-wide node budget is independently pinned.

The cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown / 11
unsupported with zero status mismatches, errors, or replay failures and PAR-2
7.46909 s. Three quantified-LIA runs remain 12/12 with PAR-2 means
0.11739/0.11756/0.11813 s (median 0.11756 s). All 600 direct-universal and 400
nested-polarity Z3 cases agree through the hermetic `z3-static` path, and the
900 bounded-instance cases agree with their independent oracle. The Bitwuzla
slice retains four expected UNSAT decisions and its pre-existing SAT model-replay
rejection.

E-graph 35/35, quantifier matching/propagation 52/52, solver library 856/856,
evidence 69/69, MBQI 13/13, and bench 7/7 pass, as do solver
all-target/all-feature Clippy and the focused formatting/diff gates. Workspace
rustdoc, links, foundational resources, generated matrices, formatting, and the
26-reference checkout census are final acceptance gates recorded in the live
plan.

## Alternatives

- **Keep source-only propagation.** Rejected: it leaves the explicit next plan
  boundary and prevents useful multi-round unit chains.
- **Treat every generated ground term as trusted.** Rejected: that is exactly the
  provenance hole ADR-0117 was designed to avoid.
- **Embed a recursive proof at every sibling reason.** Rejected: shared reasons
  duplicate recursively and unused proof material becomes ambiguous.
- **Use term shape to recognize generated instances during checking.** Rejected:
  an exact ground term is not evidence of which source quantifier entailed it.
- **Remove resource caps because Rust boxes cannot cycle.** Rejected: acyclic but
  adversarially deep/wide proof trees can still exhaust checker resources.

## Consequences

- Checked detached propagation becomes compositional across quantifier rounds.
- Certificates remain arena-bound and deterministic but may recursively own
  prior propagation certificates; explicit caps bound replay.
- Direct CDCL(T) clause insertion can consume the same derivation object next.
- Cross-certificate proof-DAG interning, non-equality theory antecedents, and
  serialized/Alethe/Lean forms remain separate work.
