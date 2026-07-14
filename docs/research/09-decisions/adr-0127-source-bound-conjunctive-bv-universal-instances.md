# ADR-0127: Source-bound conjunctive BV universal instances

Status: accepted
Date: 2026-07-11

## Context

After ADR-0126, the smallest unsupported UNSAT row in the public cvc5
quantified-BV slice is `cond-var-elim-binary` at 19 source DAG nodes. Its single
assertion is a conjunction of the free-symbol premise `k_332 < k_42` and a
universal Bool/BV formula. At the concrete universal value `x := 1`, the first
body disjunct is false because `x != 1` is false, and the second is false because
the ground premise says `k_332 < 1 * k_42`. The other binder is irrelevant and
may be zero. Thus the premise plus one exact universal instance is QF_BV-UNSAT.

ADR-0100 cannot certify this row because its evaluator contract deliberately
rejects free symbols. ADR-0124 cannot certify it because there is no following
existential block. General QSAT or quantifier elimination is unnecessary: a
positive universal conjunct entails each of its ground instances.

The local reference implementations reinforce the polarity boundary. cvc5's
`QuantPhaseReq::computePhaseReqs` marks children of a positively asserted
conjunction as required true, and Z3's SMT context activates universal
quantifiers asserted with positive input polarity. Search strategy remains
untrusted; only the exact source entailment and residual proof belong in the
certificate contract.

## Decision

**Certify UNSAT when replacing one unique positive universal conjunct by one
complete concrete Bool/BV instance yields a source-regenerated QF_BV formula
with a checked DRAT/LRAT refutation.**

The public certificate carries the original top-level assertion, the exact
universal conjunct, one `(SymbolId, Value)` pair per leading universal binder in
outer-to-inner order, and an `UnsatProof` for the weakened source assertion. The
checker requires:

- the assertion belongs to the original query and is Bool-sorted;
- the selected universal occurs exactly once and is reachable from the
  assertion root only through nonempty binary `BoolAnd` nodes, or is itself the
  assertion root;
- the universal has a nonempty unique prefix of at most 128 Bool/BV binders;
- its body is quantifier-free, application-free, Bool-sorted, and contains only
  Bool/BV terms; free Bool/BV symbols are permitted;
- the complete assertion DAG contains at most 4,096 distinct nodes;
- carried IDs, order, values, and sorts exactly match the source prefix; and
- after substituting typed constants into the untouched body and replacing the
  exact conjunct in a private arena clone, the carried proof rechecks against
  the regenerated single QF_BV assertion.

Replacing a true universal conjunct by one of its instances weakens the source
formula. If that weaker formula is UNSAT, the original conjunction is UNSAT.
The checker performs no solver search and does not trust a polarity rewrite,
candidate generator, or model.

Untrusted search tries the well-founded default tuple, then deterministic
single-binder perturbations drawn from same-sort source constants, under one
shared deadline and an explicit candidate cap. Each candidate must produce a
QF_BV proof and pass the independent checker before solver or evidence dispatch
returns UNSAT. The evidence has an empty trust ledger; Lean reconstruction is a
separate boundary.

## Lean reconstruction acceptance (2026-07-14)

The separate boundary is now accepted for the strict-conjunct route. Evidence
dispatch classifies a unique universal strictly below the source conjunction as
`BvConjunctiveUniversalInstance`; root universals remain owned by ADR-0135's
query-scoped route. Reconstruction rechecks the exact certificate, represents
the untouched assertion as the sole source axiom, projects the selected
conjunct, and applies the complete typed binding tuple before proving the exact
weakened QF_BV residual.

The residual proof uses the compact continuation-coded Alethe/RUP boundary.
LRAT hints are backward-trimmed to the conflict graph. Closed gate and clause
shares become transparent, kernel-checked definitions or theorem declarations;
open logical AIG gates remain explicit scoped `let`s. Deferred clauses are
aliases, and learned clauses never become axioms. The trusted kernel's
expression interner stores compact stable hashes across 64 shards, resolves
collisions by exact structural comparison, and allocates expressions and
metadata in fixed-size segments.

The ignored release-only `cond-var-elim-binary` stress gate checks routing,
self-contained theorem output, absence of `sorryAx`, and a module-size ceiling
of 128 MiB. Under `ulimit -v 4194304`, the authoritative test body passes in
196.98 seconds; the command takes 3:17.54 and peaks at 1,039,568 KiB RSS.
This raises the bounded public quantified-BV Lean UNSAT audit from 17/18 to
18/18.

## Evidence

The target instance `x := 1, y := 0` makes the weakened source formula
QF_BV-UNSAT exactly as described above. `cond-var-elim-binary` moves from
unsupported to checked UNSAT with five optimized backend samples of 0.354,
0.364, 0.820, 0.360, and 0.765 ms (median 0.364 ms).

The public cvc5 quantified-BV slice is now 32 SAT / 15 UNSAT / 0 unknown / 7
unsupported, with 47 expected-status agreements, no disagreement, error, or
model-replay failure. Five PAR-2 samples are 3.007967, 3.008263, 3.008571,
3.008363, and 3.008062 seconds (median 3.008263 seconds). The dominance audit
certifies and checks all 47 decisions. The target has taxonomy
`bv-conjunctive-universal-instance-unsat` and an empty trust ledger. At the
original certificate checkpoint, total dominance was 40/47 and Lean coverage
was 8/15 UNSAT; the later acceptance section records the reconstruction result.

Six focused tests cover the public target, source/binding/proof mutation,
non-conjunctive polarity and forbidden source contexts, duplicate occurrences,
both hard caps, a satisfiable neighbor, and 64 generated direct-Z3 controls.
Together with the previous quantified-BV matrices, 1,464 direct-Z3 cases and
controls agree with no disagreement.

## Alternatives

- **Extend ADR-0100 to evaluate open bodies.** Rejected: an evaluator cannot
  discharge the remaining free-symbol contradiction without a model or proof.
- **Treat any positive-polarity occurrence as an admissible instance site.**
  Deferred: conjunction has direct entailment semantics and covers the measured
  row; disjunction, implication, negation, and ITE need an explicit path/polarity
  certificate rather than an implicit rewrite.
- **Match the target's multiplication-by-one syntax.** Rejected: the generic
  residual QF_BV proof is smaller and avoids a theorem-specific arithmetic
  checker.
- **Trust successful candidate instantiation.** Rejected: search and source
  substitution remain outside the trusted core.
- **General QSAT/QE.** Deferred: this row needs one entailed source instance,
  not a complete quantified procedure.

## Consequences

Open Bool/BV universal contradictions under explicit conjunctive premises can
receive source-bound checked evidence. The route remains intentionally
incomplete for universals under other Boolean contexts, multiple selected
universals, nested quantifiers, functions, arrays, and arithmetic binders. The
strict-conjunct certificate now reconstructs to Lean under the bounded
acceptance gate above; broader cases require distinct polarity, combination, or
proof contracts rather than silent broadening.
