# Family: the certificate chain

**This family has no board row, and that is the point.** The parity board
counts decisions. This counts whether a decision arrives with something a
checker can verify. A division can reach parity while its certificates stay
empty, and nothing on the board would show it.

## The chain, and where it is whole

| Stage | Produces a checkable artifact? | Note |
|---|---|---|
| Preprocessing / rewriting | **no** | see below — the open hole |
| Bit-blasting to CNF | yes | replay maps are retained by hard rule |
| Propositional search | **yes** | DRAT by construction, checked by our own DRAT and LRAT checkers |
| Theory reasoning (CDCL(T)) | **contract only** | ADR-1704 defines it; nothing emits it yet |
| Model lifting (`sat`) | yes | every `sat` replays against the original term |

## The open hole: preprocessing

`axeyum-rewrite` is preprocessing, and preprocessing produces no evidence.
In the crate today `RewriteRuleId` is documented as being for "logs and future
certificates" and `ProofObligation` as a "future proof obligation checked
outside the rewriter". **The placeholders exist and nothing fills them.**

So every canonicalization, array elimination, integer blast and quantifier
expansion is a gap in the chain, between an input we were given and a formula
we actually refuted.

**The literature does not hand us a solution.** The published form of our own
two-stream contract states that it does not cover preprocessing. And the one
mature production system in this space needs a dedicated rewrite-rule language
and a proof-granularity flag to manage it, which says a from-scratch producer
loses coverage on rewrite steps before anywhere else. Design the manifest for
that rather than discovering it.

## The theory half: contract landed, producer not

ADR-1704 adopted the two-stream design — a propositional refutation checked
over the CNF extended by the enumerated theory lemmas, with the lemma count
read off the artifact and a distinct trust level for a refutation modulo N
lemmas. The boundary is pinned by tests. **No route emits it**, so today every
CDCL(T) `unsat` carries no checked artifact. S7 is where that changes, and S7
gains a checked Boolean half on day one.

Per-lemma checkability, read from the code rather than from prose: linear real
arithmetic has an exact-rational Farkas verifier; difference logic already
*builds and verifies* a Farkas object per conflict and then discards it because
the explanation type has no slot for it; the e-graph has congruence chains plus
an independent re-checker the online path never calls. Strings and the
nonlinear theories have whole-query refutations rather than per-lemma objects.
**The structural gap is one trait slot, not new proof theory.**

## Prior art we do not cite

ADR-1704's design is the published eDRAT approach (FMCAD 2024). The ADR cites
no prior art. Either we made a choice they rejected or we reached theirs
independently, and the comparison is cheap.

## What the cost of all this actually is

Measured externally in 2026, not speculated: a kernel-checked bit-vector
pipeline pays a **median 6.9%** for the kernel check itself and runs a **median
8.7x** slower overall than the uncertified reference. **Trusted checking is
cheap; proof-producing search is what costs.** A slice that makes checking
faster is working in the cheap half.

## Format decisions

The legacy checker format is settled as dead — its repository has not been
pushed since September 2023 and its signature set omits bit-vectors, arrays and
datatypes entirely. The live choices are the native format of the current
reference checker and Alethe for interoperability, the latter carrying a
maintenance cost because its specification describes itself as evolving.

## Open defects in this family, found 2026-09-06 and not yet fixed

Both were found by the math-department's reconstruct lane while it changed how
the sum-of-squares attestation renders, and both are in `axeyum-solver`. **They
are reported here as that lane measured them; this coordinator confirmed the
shape in the source but has NOT re-run either.** Treat the sizes as claims until
someone does.

1. **A producer's doc comment promises more than the producer delivers.**
   `evidence::produce_nra_sos_evidence` stores the Lean module with no content
   gate, under a doc comment describing a kernel-checked proof. For a fallback
   query that description is false. A doc comment is not a gate, and a producer
   that stores whatever it is handed cannot be relied on by a consumer reading
   the comment. Fix is a content gate, or a comment that says what actually
   happens.

2. **Two fixtures are named for coverage they do not provide.**
   `tests/evidence.rs::qf_nra_sos_certificate_wrapper_carries_lean_module` and
   `tests/lean_crosscheck.rs::qf_nra_sos_certificate_audit_rows_check_in_real_lean`
   are named for the wrapper path but measured to take the honest route. The
   first asserts only that a Lean module exists and carries no `sorryAx`; if the
   wrapper path broke, it would still pass. **A test whose name claims a case it
   does not exercise is worse than no test**, because it makes the case look
   covered. Fix is either a fixture that actually reaches the wrapper, or names
   that match what runs — and the durable form ties the two together by
   asserting the rendered module name, so the name cannot drift from the route
   again.

Related context: the attestation now renders as `axeyum_attested_refutation`
when its axiom footprint is non-empty, derived from the footprint rather than
chosen, so an honest reconstruction's bytes are unchanged. That change is what
made the misnaming visible.

## Next actions

1. Cite the prior art in ADR-1704 and record the comparison.
2. S7 — emit the two-stream artifact from one theory route, gaining the checked
   Boolean half.
3. Fill one preprocessing obligation end to end (canonicalization is the
   smallest) to learn what the manifest actually needs.

## Owning documents

- [ADR-1704](../../../research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), sections 1.3-1.5
- [Evidence and checker discipline](../../../contributor-guide/evidence-and-checker-discipline.md)
