# ADR-0374: Admit Bool free symbols in quantified-BV model certificates

Status: accepted

Date: 2026-07-29

## Context

`quantified_bv_differential_fuzz::boolean_discharge_of_opaque_bv_closures_matches_z3`
has been failing on `main`, and `just check` with it. It was masked twice over:
`gen-lean-complete-parity.py --check` had independently been failing
`parity-docs` since `fe8ba9af`, and the full run aborted earlier on an
`axeyum-smtlib` integration test that sorts before `axeyum-solver`. The failure
reproduces at `ffc466b4`, so it predates the 2026-07-28 Phase 0 work.

The failing case is `case=19, width=32`: the assertion is
`not (forall x. (p or bvult(x, y)))` with a free `Bool p` and a free
`BitVec 32 y`. Axeyum answers `sat`, z3 agrees `sat`, and the returned model
(`p = false`, `y = 0`) is genuinely correct — `forall x. (false or bvult(x, 0))`
is false because nothing is unsigned-less-than zero, so its negation holds.

The defect is **missing evidence, not a wrong verdict**. `normalize` rewrites
`not (forall x. B)` to `exists x. not B`, `skolemize_top_existentials` replaces
that with `not B[x := s]` for a fresh constant, and the query is then
quantifier-free — so `solve` returns the quantifier-free `sat` directly. That
model interprets the Skolem constant, so it *is* the existential witness, but
nothing records it. `check_model` replays against the **original** assertion,
where discharging `forall x` means enumerating `x`'s domain. That succeeds at 1,
2, 8 and 16 bits and is impossible at 32 — exactly the observed boundary.

The machinery to record the witness already exists:
`QuantifiedBvModelSatProof::NegatedUniversalWitness` (ADR-0130/0131) carries the
binders and one exact value each, and `check_negated_universal_witness`
independently evaluates the body at that assignment and requires `false`. But
`source_shape` admits a certificate only when **every free symbol is
`BitVec`**, and this assertion has the free `Bool p`. The certified search
therefore declines, and the uncertified skolemized `sat` is what escapes.

This is the one remaining `just check` blocker on `main`.

## Decision

**Admit `Bool` free symbols alongside `BitVec` in quantified-BV model
certificates, and attach a witness certificate to a `sat` that top-level
skolemization decided.**

Three changes:

1. `source_shape` (`quant_bv_model_sat_cert.rs`) accepts a free symbol of sort
   `Bool` or `BitVec` instead of `BitVec` only. Binders remain restricted
   exactly as before.
2. `value_term` (`quant_bv_model_sat_search.rs`) can pin a `Value::Bool` to a
   constant, so the witness search can hold a `Bool` free symbol fixed while it
   solves for the binder values.
3. `certify_skolemized_negated_universals` (`auto.rs`) runs on the
   quantifier-free `sat` that follows top-level skolemization. For each
   **original** assertion that is a directly negated universal and carries no
   certificate yet, it re-derives the witness through the existing checked route
   and attaches the result.

## Why this is sound

The proofs in this module are evaluation-based. A free value is only ever
written into an `Assignment`, after which the body is evaluated and required to
be `false`. A `Bool` free symbol is therefore checked exactly as strongly as a
`BitVec` one — nothing in `check_negated_universal_witness` is width- or
sort-specific. `checked_free_values` independently enforces that every supplied
value's sort matches its symbol's declared sort, so a mismatched or fabricated
value is rejected regardless of this widening.

Step 3 is strictly additive and cannot weaken a verdict. It only ever *adds* a
certificate to a model that is already being returned; a shape that does not
match, a free symbol the model does not bind, a declined witness search, or a
witness that fails its own independent check all leave the result byte-identical.
It does not turn `unknown` into `sat`, and it does not change which queries are
decided.

The verdict itself continues to rest on skolemization, which is trusted and
equisatisfiable, exactly as before. What changes is that the answer now carries
evidence a caller can check, at every width rather than only where the domain
happens to be enumerable.

## Consequences

`boolean_discharge_of_opaque_bv_closures_matches_z3` moves from a panic to
`certified_sat=32, agreed_unsat=16, safe_controls=16` over its 64 cases, and the
whole `quantified_bv_differential_fuzz` binary is 9/9 with `disagree=0` on every
sweep it reports (quantified-BV 600 compared, nested-polarity 400 compared,
source-term Skolem 48 certified).

The gain is in *evidence coverage*, not decide-rate: results that were correct
but unverifiable are now verifiable. That is the axis the project treats as its
differentiator, so it is worth stating separately from a decide-rate claim — no
benchmark moves from `unknown` to a verdict because of this ADR.

## Alternatives rejected

**Return `unknown` instead of an uncertified `sat`.** This is what the standing
rule would demand if the witness were unrecoverable, and the test does accept
`unknown` for this shape. Rejected because it discards a correct answer when the
witness is in fact sitting in the model — declining is the right response to
absent evidence, not to unrecorded evidence.

**Plumb the binder-to-Skolem map out of `skolemize_top_existentials`.** This
would avoid re-deriving the witness. Rejected as the larger change for no extra
assurance: the certificate has to be independently re-checked either way, and
re-deriving through the existing validated route keeps candidate search and
checking separate, which is the module's stated design.

**Widen the binder sorts too.** Out of scope. Only free-symbol sorts are
widened here; binder admission is untouched.
