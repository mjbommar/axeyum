# ADR-0134: Checked query-scoped QF_BV universal instances

Status: accepted
Date: 2026-07-13

## Context

After ADR-0133, `psyco-107-bv` was the sole unsupported row in the 54-row
public cvc5 quantified-BV slice. Its 217-node assertion DAG contains one large
positive Bool/BV universal below ground Boolean structure. A separate ground
assertion supplies the fact needed to refute it, so ADR-0127's
single-containing-assertion certificate cannot close the query. ADR-0133's
bounded CEGIS already discovers useful complete source instances, but correctly
declined when those instances made the query skeleton UNSAT because they had no
query-scoped proof status.

cvc5's BV CEGQI instantiator projects model values and equality boundaries into
complete typed tuples before handing them to the common instantiation layer.
Z3's model-based quantifier checkers solve a negated model body in an auxiliary
context, extract complete bindings, and add the corresponding source instance.
Those mechanisms justify the search strategy, but Axeyum still needs an exact,
independently replayable artifact for the final verdict.

## Decision

**Add a query-scoped certificate containing complete source bindings for a
bounded set of positive Bool/BV universal instances and a DRAT/LRAT proof of
the exact rebuilt ground query.**

The independent checker:

- binds the exact ordered source assertion sequence;
- reuses ADR-0133 admission, including positive-polarity `forall` only,
  Bool/BV sorts, unique binders disjoint from free symbols, no applications or
  free BVs in quantified assertions, and the existing source caps;
- accepts nonquantified assertions only when they are ground QF_BV;
- requires 1 through 256 unique source instances;
- requires each instance to name an assertion in the query and carry every
  binder exactly once, in deterministic source traversal order, with the exact
  source sort;
- rebuilds a sound ground weakening by replacing admitted positive universals
  with `true`, then independently regenerates every complete concrete source
  instance; and
- rechecks the carried `UnsatProof` against exactly that rebuilt skeleton plus
  those instances.

The source query entails both the positive-universal weakening and every
complete instance. Therefore a checked QF_BV refutation of their conjunction
proves the original query UNSAT. Candidate models, quantifier erasure, boundary
projection, and instance selection remain untrusted search. Any heuristic
candidate block, duplicate non-progressing instance, mixed certificate mode,
deadline expiry, unsupported source shape, or failed replay forces decline.
The proof-producing route also declines on `wasm32` until the shared proof
exporter has a browser-safe deadline contract.

## Evidence

The design was checked against:

- `references/cvc5/src/theory/quantifiers/cegqi/ceg_bv_instantiator.cpp`;
- `references/cvc5/src/theory/quantifiers/cegqi/ceg_instantiator.cpp`;
- `references/cvc5/src/theory/quantifiers/instantiate.cpp`;
- `references/z3/src/sat/smt/q_mbi.cpp`; and
- `references/z3/src/smt/smt_model_checker.cpp`.

`psyco-107-bv` now returns certified UNSAT. Five release corpus solve samples
are 109.528079, 112.048587, 108.817031, 108.590204, and 104.763955 ms
(median 108.817031 ms). Five direct evidence diagnostics are 101.938, 103.544,
103.781, 103.525, and 102.888 ms (median 103.525 ms); every sample is certified,
rechecked, and has no trust steps or holes.

The full public slice is now 36 SAT / 18 UNSAT / 0 unknown / 0 unsupported,
with 54 expected-status agreements and no disagreement, error, or replay
failure. Five PAR-2 samples are 0.0334462169, 0.0338140011, 0.0328719061,
0.0330305167, and 0.0327350909 seconds (median 0.0330305167 seconds). The
external Z3 binary compares 52 rows with zero disagreement and skips two rows
unsupported by that comparison path.

The complete dominance audit checks and certifies 54/54 decisions, reports
zero mismatches, audit errors, and timeouts, and retains 44/54 dominant
candidates. The new target is not marked dominant: evidence production is
about 101 ms while the measured Z3 solve is about 33 ms. Lean reconstruction
remains 8/18 UNSAT. ADR-0135 subsequently adds a genuine source-instantiation
route for the bounded shape, while retaining this count until the corpus-scale
target proof meets a bounded gate.

Seven focused tests cover the public target; exact query, source, binding, proof,
duplicate, and cap tampering; free/bound capture and negative-quantifier,
existential, function, and mixed-arithmetic rejection; deadline expiry; a
formula requiring two distinct source instances; and 32 direct-Z3 cases split
between certified UNSAT and SAT controls. A mixed unsupported quantified sibling
also confirms failed admission declines instead of surfacing a backend error.
Cumulative quantified-BV direct-Z3
coverage is 1,912 cases and controls with no disagreement.
The complete `just check` gate passes, including formatting, strict workspace
Clippy, all-feature tests, rustdoc warnings, foundational-resource validation,
generated-contract checks, and documentation link validation.

## Alternatives

- **Trust the CEGIS skeleton UNSAT result.** Rejected: the skeleton includes
  search-only transformations and must be rebuilt independently.
- **Extend ADR-0127 across assertions.** Rejected: the query-scoped contract is
  materially different and may carry multiple instances.
- **Carry only instantiated terms.** Rejected: complete source bindings are
  required so the checker can regenerate terms from the untouched source.
- **Accept heuristic Boolean candidate blocks in the proof.** Rejected: only
  source consequences may enter the final refutation.
- **Claim general QSAT completeness.** Rejected: admission remains a bounded
  positive-universal, application-free Bool/BV subset.

## Consequences

The committed public cvc5 quantified-BV slice is fully decided and every
decision is independently checked, but this is corpus completion rather than
general quantified-BV completeness. The remaining depth work is broader
nested/alternating QSAT, functions and quantified UF, nonvacuous existential
relations, performance of proof-producing instance search, and corpus-scale
Lean proof sharing for the source-instantiation plus QF_BV refutation. ADR-0135
accepts the bounded source theorem and small external-Lean route.
