# ADR-0357: Preregister checked finite-profile quantified-UF models

Status: proposed
Date: 2026-07-22

## Context

The almost-uninterpreted MBQI model finder can establish satisfiability for one
top-level `forall x. body` over `Int` or `Real` when every occurrence of `x` is
a direct uninterpreted-function argument. Its finite-profile argument is sound:
a finite function table plus its default has only finitely many behaviours as
`x` ranges over the infinite domain.

The result representation does not yet satisfy Axeyum's public evidence
contract. Search returns an ordinary `Model` without a quantified certificate.
Consequently, canonical `check_model` rejects the original universal with
`UnsupportedQuantifierDomain`, and `Evidence::Sat` plus the benchmark replay
path cannot credit the result. The existing integration tests sample the body
at many concrete points, but do not call the public original-query checker.
This is the same representation boundary identified in the research-question
register and solved for affine Skolem witnesses by ADR-0096.

The immediate critical task is therefore not a wider MBQI fragment. It is to
make the already-landed fragment independently and canonically checkable before
granting it more public SAT surface.

## Decision

**Keep finite-profile MBQI search untrusted, add a source-bound
`QuantifiedUfModelSatCertificate` to `Model`, and grant SAT only when a separate
small checker re-derives the complete finite-profile proof from the exact
original assertion and the returned function model.**

The first accepted slice remains deliberately unchanged:

- exactly one top-level universal binder over `Int` or `Real`;
- a quantifier-free body;
- every occurrence of the binder is a direct argument of an
  uninterpreted-function application, with at least one such occurrence;
- a total finite-table-plus-default interpretation for every relevant function;
- a deterministic cap of 4,096 checked profile representatives.

The certificate stores the exact original assertion and binder identity, not a
search trace. The checker independently re-matches the source shape, finds the
exact function argument positions occupied by the binder, verifies model
signature agreement, derives every special value from those table-key
positions, chooses one same-sort generic value outside that finite set, and
evaluates the untouched body under every representative. Any malformed source,
missing interpretation, signature mismatch, cap overflow, substitution error,
or non-true evaluation rejects the certificate.

`prove_unsat_by_mbqi` may attach a certificate only after this checker accepts
the candidate. `check_model` counts and rechecks the new certificate family and
rejects stale, extra, or mismatched certificates. The unified `solve` front
door must not return an MBQI SAT result that fails replay against the caller's
original assertion sequence; exact preprocessing combinations not yet covered
by the certificate degrade to `unknown` rather than exposing an unreplayable
model.

This ADR does not broaden to multiple binders, nested quantifiers, interpreted
binder occurrences, uninterpreted carrier sorts, arbitrary function-model
repair, serialization, or Lean reconstruction. Those remain follow-ups after
the current public contract is green.

## Evidence gates

Acceptance requires all of the following:

1. Existing positive `Int` and `Real` MBQI model-finder cases return SAT and
   pass canonical `check_model` on the exact original assertions.
2. Existing UNSAT and out-of-fragment behaviour is unchanged.
3. Focused tests reject a stale assertion ID, wrong binder, missing function
   interpretation, wrong function signature, a table-entry violation, an
   interpreted binder occurrence, a nested quantifier, and an extra
   certificate.
4. A mixed-arity function test proves that candidate extraction uses the exact
   binder argument positions, including repeated binder positions.
5. `Evidence::Sat::check` accepts a genuine certificate and rejects a tampered
   model or certificate.
6. Focused solver/model/evidence suites, workspace Clippy, rustdoc, foundational
   resources, and documentation links are green.

## Alternatives

- **Keep the sampled integration replay.** Rejected: finite sampling is useful
  differential evidence but is not a proof over `Int` or `Real`, and it bypasses
  the public checker used by consumers.
- **Teach `check_model` to trust any MBQI-shaped model without a certificate.**
  Rejected: result provenance would be implicit, and unsupported quantified SAT
  models could be silently promoted.
- **Store the search-generated candidate list as trusted evidence.** Rejected:
  the checker can derive the complete representative set from source syntax and
  the model; trusting a search list could omit a violating profile.
- **Broaden to multi-binder MBQI in the same step.** Deferred: Cartesian profile
  coverage and prefix handling are a useful next increment, but only after the
  already-claimed single-binder result passes canonical replay.
- **Downgrade all almost-uninterpreted SAT results to `unknown`.** Safe but
  rejected as the end state: it removes useful real functionality whose small
  proof obligation can be checked directly.

## Consequences

The existing almost-uninterpreted SAT direction becomes a real public
capability rather than a search-side claim: its model checks through the same
API used by evidence and benchmarks. The additional model field remains behind
the existing lazily allocated quantified-certificate aggregate. Unsupported
shapes remain honest `unknown`. Multi-binder finite profiles become the next
natural capability increment, with this checker as their trusted foundation.
