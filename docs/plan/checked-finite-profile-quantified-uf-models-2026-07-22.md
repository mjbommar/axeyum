# Checked finite-profile quantified-UF models

Status: implemented; final branch-wide gate pending
Date: 2026-07-22
Decision: [ADR-0357](../research/09-decisions/adr-0357-preregister-checked-finite-profile-quantified-uf-models.md)
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Outcome

The existing almost-uninterpreted MBQI SAT result now satisfies Axeyum's public
model/evidence contract. Search can still propose a finite-table UF model, but
it receives SAT credit only after a separate checker validates the exact source
universal. The returned `Model` carries that source binding, canonical
`check_model` re-runs the proof, and `Evidence::Sat::check` uses the same route.

This repairs a concrete functionality gap. Before this increment, the MBQI
finder could return `CheckResult::Sat`, while `check_model` rejected the same
original assertion because the model had no quantified certificate. Existing
tests sampled many concrete integers but did not exercise the consumer-facing
checker over the infinite source domain.

## Accepted fragment

The checker accepts exactly one top-level `forall` binder per assertion:

- the binder sort is `Int` or `Real`;
- the body is quantifier-free;
- every binder occurrence is a direct argument of an uninterpreted function;
- every relevant function has a total, signature-matching finite-table-plus-
  default interpretation in the model; and
- the complete representative set fits the 4,096-profile cap.

For each function occurrence, the checker records the exact argument positions
occupied by the binder. It derives the special representatives from those
positions in every finite table key, then adds one same-sort value outside the
finite set. Every table match can occur only at a special representative; at
the generic representative every relevant function takes its default. Direct
evaluation of the substituted body at all representatives is therefore
exhaustive for the model's finite profiles.

## Trust boundary

`mbqi_model_finder.rs` is now only the search-to-certificate adapter. The small
checker lives separately in `quant_uf_model_sat_cert.rs` and reconstructs its
inputs from the untouched assertion and returned model. The certificate stores
only the exact assertion and binder identity; it does not store or trust the
searcher's candidate list.

`Model` keeps the new certificate family inside the existing lazily allocated
quantified aggregate. `check_model` rejects stale and extra certificates and
requires every unsupported infinite-domain assertion to have one matching,
valid certificate. The unified `solve` front door also rechecks an MBQI SAT
candidate against the caller's original assertion sequence. If exact
preprocessing prevents source coverage, it returns `Unknown(Incomplete)` rather
than an unreplayable SAT model.

## Tests and controls

The focused suite covers:

- canonical `check_model`, `Evidence::Sat::check`, and `produce_evidence` on a
  genuine integer model;
- genuine integer and real models, predicate composition, and two-UF bodies;
- conflicting ground points and table-entry violations remaining UNSAT;
- stale assertion, wrong binder, missing function, wrong function signature,
  bad default, and extra-certificate rejection;
- exact repeated argument positions, including an irrelevant off-diagonal
  table entry and a rejecting diagonal violation;
- interpreted binder occurrences and nested quantifiers declining; and
- deterministic profile-cap overflow declining.

Current completed gates:

- `cargo test -p axeyum-solver --all-features --lib -j1`: 894 passed;
- `cargo test -p axeyum-solver --all-features --test mbqi_model_finder -j1`:
  12 passed;
- `cargo test -p axeyum-solver --all-features --test instantiation -j1`:
  15 passed;
- capability ledger generation/check: 2 passed.

The existing quantified-UFLIA direct-Z3 differential and branch-wide gates are
recorded here after completion; no broader decide-rate claim is inferred from
the focused cases.

## Deliberate boundary and next action

This increment does not accept multiple universal binders, nested quantifiers,
interpreted binder occurrences, uninterpreted carrier binders, arbitrary model
repair, serialized proof exchange, or Lean SAT reconstruction. The next
capability increment is multi-binder Cartesian finite-profile checking, but only
after this one-binder evidence boundary remains green under differential and
branch-wide validation.
