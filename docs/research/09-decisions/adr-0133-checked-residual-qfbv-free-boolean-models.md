# ADR-0133: Checked residual-QF_BV free-Boolean models

Status: accepted
Date: 2026-07-12

## Context

After ADR-0132, `psyco-001-bv` is the smallest unsupported row in the public
cvc5 quantified-BV slice. Its assertion combines 14 free Boolean symbols with
a positive universal over four `BV32` values, four Boolean write selectors,
and eleven additional `BV32` values. A satisfying free model disables three
write guards; the remaining universal matrix is a valid guarded ITE/equality
implication.

The existing ADR-0107/0123 free-Boolean model checker deliberately treats BV
predicates as opaque and accepts them only when surrounding Boolean structure
alone proves the quantified assertion. Its candidate search erases quantifiers
and blocks at most 256 complete free-Boolean assignments. That is sound but
cannot prove this residual BV validity and need not discover the useful model
among 14 free Booleans.

cvc5's finite-model engine checks active universals against each candidate
model and adds concrete instantiations when exhaustive/model-based checking
finds a failure. Its MBQI enumerator substitutes candidate terms and rechecks
the resulting query in a subsolver. Z3's model checker substitutes the
candidate interpretation, replaces quantified variables by fresh skolems,
asserts the counterexample query in an auxiliary context, and turns a
satisfying counterexample model into a new instantiation. Z3 accepts the model
only when the complete counterexample query is unsatisfiable. These mechanisms
guide search; Axeyum still requires a separately checkable final artifact.

## Decision

**Extend `QuantifiedBoolModelSatCertificate` with an explicit
`PositiveUniversalQfBv` proof mode: candidate search may refine on concrete
universal counterexamples, but SAT credit requires an independently rechecked
QF_BV refutation of the negated residual rebuilt from the untouched source.**

The existing `Structural` mode retains ADR-0107/0123 behavior unchanged. The
new mode admits an assertion only when:

- every reachable term has Bool or BV sort;
- every quantifier is a positive-polarity `forall` over Bool/BV;
- binders are unique, binder IDs are disjoint from free symbols, and every BV
  symbol is bound;
- every free symbol is Boolean and is covered exactly, in sorted order, by the
  certificate;
- function applications are absent; and
- the source has at most 128 binders, 4,096 distinct nodes, and depth 256.

The checker clones the untouched arena, substitutes the certificate's complete
free-Boolean assignment with Boolean constants, opens only the admitted
positive universal binders, and negates the resulting quantifier-free Bool/BV
formula. It then rechecks the carried `UnsatProof` against that exact residual
using the established term-to-CNF replay and DRAT/LRAT checker. The enclosing
`Model` must agree with every carried Boolean value, and canonical
`check_model` remains the final gate.

Search is bounded CEGIS under the caller's shared deadline. Quantifier erasure
still supplies only the initial free-Boolean candidate skeleton. For each
candidate:

1. build the exact negated QF_BV residual under that candidate;
2. if it is satisfiable, read one complete defaulted binder assignment and add
   the corresponding concrete source instance to the candidate skeleton;
3. if it is unsatisfiable, generate and self-check an `UnsatProof`, attach it to
   the candidate certificate, and run the independent checker; and
4. decline after the existing 256-candidate cap, source caps, deadline expiry,
   unsupported residual, duplicate non-progressing instance, or failed replay.

Counterexample instances and quantifier erasure are untrusted search hints.
They cannot produce UNSAT or SAT credit. An UNSAT candidate skeleton without an
independently complete counterexample-cover certificate still declines.

## Evidence

Before this change, the 147-DAG-node `psyco-001-bv` row was expected SAT but
returned unsupported. The design was checked against:

- `references/cvc5/src/theory/quantifiers/fmf/model_engine.cpp`;
- `references/cvc5/src/theory/quantifiers/mbqi_enum.cpp`;
- `references/z3/src/smt/smt_model_checker.cpp`; and
- `references/z3/src/sat/smt/q_mbi.cpp`.

The row now returns replay-checked SAT. Five release corpus samples are
339.664335, 341.466781, 339.928031, 338.600498, and 342.665246 ms (median
339.928031 ms). Separate evidence-production samples are 759.687, 758.775,
766.378, 763.886, and 761.351 ms (median 761.351 ms); every sample is certified,
rechecked, and has an empty trust ledger.

The 54-row public cvc5 quantified-BV slice is now 36 SAT / 17 UNSAT / 0 unknown
/ 1 unsupported, with 53 expected-status agreements and no disagreement,
error, or replay failure. Five PAR-2 samples are 0.408176, 0.408413, 0.408171,
0.408370, and 0.408282 seconds (median 0.408282 seconds). Exactly
`psyco-001-bv` changes outcome; `psyco-107-bv` is the sole remaining
unsupported row. The external Z3 4.13.3 binary compares 51 rows with zero
disagreement and skips three unsupported-by-the-in-process-oracle rows.

The complete dominance audit certifies and checks all 53 decisions, marks
44/53 dominant candidates, and retains Lean coverage at 8/17 UNSAT. The target
evidence kind is `quantified-bool-model-sat`, with no trust steps or holes.

Sixteen focused tests cover the prior public model classes, the new public
target, proof/source/free-value/model tampering, positive-polarity and
Bool/BV-only admission, free-BV/function and binder/free capture rejection,
binder/node/depth caps, and 32 direct-Z3 cases: 16 certified SAT models that
require a counterexample refinement and 16 UNSAT controls. Cumulative
quantified-BV direct-Z3 coverage is 1,880 cases and controls with no
disagreement. Strict all-target solver Clippy passes. The complete workspace
`just check` gate passes, including all tests (notably the long
variable-divisor NIA and UFLIA differential fuzzers), warning-denied rustdoc,
foundational resources, generated documentation checks, and link validation.

## Alternatives

- **Raise the 256-candidate cap or enumerate all 16,384 free assignments.**
  Rejected: it does not address the missing BV-validity proof and scales in the
  wrong dimension.
- **Add target-specific write-guard pins.** Rejected: source instances from
  actual counterexamples are a more general and reference-aligned search
  refinement.
- **Trust quantifier erasure or accumulated instances.** Rejected: both are
  incomplete candidate constraints and carry no proof status.
- **Accept the QF solver's UNSAT result directly.** Rejected: the final
  certificate carries and rechecks the exact residual proof.
- **Extend structural opaque-BV discharge to reason heuristically about
  equality or ITE.** Rejected: a complete QF_BV refutation is simpler to audit
  and does not require a second partial equality calculus.
- **Open negative universals, existentials, free BVs, functions, or mixed
  arithmetic.** Deferred: each changes the model or proof contract and remains
  outside this increment.

## Consequences

Complete free-Boolean models can now certify bounded
positive Bool/BV universals whose residual validity is within the established
QF_BV proof path. The search gains a reusable counterexample-instance loop,
while the trusted result remains a small deterministic source transformation
plus the existing proof checker. This is not general QSAT, arbitrary MBQI,
negative quantifier handling, free-BV model construction, functions/arrays,
mixed arithmetic, proof serialization above the residual, or Lean SAT
reconstruction. The new proof-producing search route declines on `wasm32`
rather than replacing the existing browser-safe candidate clock with
`std::time::Instant`; enabling it there requires a wasm-safe deadline contract
in the shared proof exporter.
