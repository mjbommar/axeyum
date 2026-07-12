# ADR-0119: Checked quantifier clauses in retained CDCL(T)

Status: accepted
Date: 2026-07-11

## Context

ADR-0117 and ADR-0118 can justify a detached equality/disequality literal from
an exact universal instance, original ground reasons, and recursively checked
generated reasons. The quantifier loop still appends that term to a ground
vector and calls the complete quantifier-free dispatcher again at the head of
the next round. Each call rebuilds Boolean lowering, SAT state, and theory state.

The generic `CdclT` driver already retains learned clauses, activities, phases,
and dynamic theory variables across `add_permanent_clause` calls. Its online EUF
theory already supplies the sound equality abstraction needed by the supported
quantifier-clause fragment. Two ownership gaps prevent direct reuse:

1. a completed SAT search may leave decision scopes open, while adding new
   e-graph nodes inside such a scope would give dynamic atoms rollback-unstable
   node ids;
2. a dynamic SAT clause is sound only if every generated literal or complete
   instance is independently tied to an original universal.

Z3's SAT+EUF quantifier plugin evaluates a binding, records its e-graph
evidence, internalizes the instantiated literals, and adds the resulting clause
to the live SAT solver. Axeyum can adopt that online ownership while preserving
its stronger explicit checker boundary.

## Decision

Add a retained quantifier-clause session over the existing `CdclT` and
`EufTheory`:

1. encode the original quantifier-free ground assertions once with the existing
   Boolean/equality skeleton encoder;
2. before each generated batch, backtrack the CDCL(T) trail to level zero while
   retaining input, permanent, and learned clauses plus VSIDS/phase state;
3. append newly encountered equality atoms to both the SAT/theory mapping and
   the root-scope EUF bridge, then add the generated equality clause directly;
4. accept a generated term for online insertion only after
   `QuantifierGroundDerivation` independently checks against the untouched
   assertion set;
5. normalize clauses deterministically, skip tautologies, and retain permanent
   clauses outside learned-clause reduction;
6. cap online variables, clauses, and dynamic literals before allocation; and
7. disable the accelerator and continue through the existing fresh-QF route on
   unsupported Boolean structure, failed derivation replay, mapping mismatch, or
   resource exhaustion.

The retained session is a refutation accelerator, not a new decision backend:

- online `Sat` means only that matching may continue;
- online `Unknown` disables the accelerator or propagates the existing deadline
  result, never fabricates a verdict;
- online `Unsat` is a candidate and returns product `Unsat` only after one
  ordinary QF check refutes the original ground assertions plus the exact set of
  admitted generated terms;
- final fixpoint behavior and public evidence remain source-query based.

`CdclT` gains a generic level-zero backtrack method. `EufTheory` gains a
root-only atom append method; it rejects append attempts while decision scopes
are open. Neither API exposes backend lifetimes or FFI state.

## Acceptance

- Source-only, exact-instance, recursively propagated equality, generated
  disequality, Boolean conflict, congruence conflict, and mixed full-clause/unit
  chains agree with fresh-QF mode.
- Wrong/missing derivations never enter the live clause database; unsupported
  or over-budget sessions preserve the existing result through fallback.
- Dynamic atoms survive repeated solve/backtrack/append cycles without stale
  e-node ids, atom/SAT-variable mismatch, or learned-clause corruption.
- Online `Sat` is never returned as product SAT; online `Unsat` must fail closed
  when final QF replay is intentionally withheld or changed.
- A committed multi-round target reduces Boolean/CNF rebuild volume and improves
  optimized end-to-end time or is rejected.
- Quantified BV/LIA/Bitwuzla public decisions, direct-Z3 and bounded-instance
  soundness, evidence, MBQI, solver, bench, Clippy, rustdoc, links, foundational
  resources, generated matrices, formatting, and reference-census gates pass.

Accepted results:

- a six-stage recursive-provenance target reduces complete QF rebuilds from 7
  to 2 while performing 6 retained solves and inserting 6 checked clauses;
  five optimized runs improve median end-to-end time from 0.560 to 0.351 ms
  (37.3%, 1.60x);
- exact-instance, recursive propagation, full-clause, dynamic disequality,
  congruence, tamper, unsupported-skeleton, initial/dynamic resource-cap,
  root-backtrack, root-only atom, and final-replay gates pass;
- the 54-row cvc5 quantified-BV slice remains 29 SAT / 9 UNSAT / 5 unknown /
  11 unsupported with no disagreement, error, or replay failure and PAR-2
  7.47183 seconds; quantified LIA remains 12/12 with three-run median PAR-2
  0.11770 seconds; and the Bitwuzla slice reproduces four expected UNSAT rows
  plus its known SAT model-replay alarm;
- all 1,000 direct-Z3 quantified-BV cases and 900 bounded-instance cases agree;
  solver, evidence, MBQI, benchmark, static-analysis, documentation, generated
  ledger, foundational-resource, formatting, and reference gates pass.

## Alternatives

- **Keep rebuilding QF state each round.** Rejected if the retained target is
  Pareto-positive: the repeated lowering cost is exactly the boundary exposed by
  ADR-0118.
- **Return `Unsat` directly from retained CDCL(T).** Rejected: current product
  evidence is source-query based, and the extra final replay is the independent
  resolution/theory gate until online proof serialization lands.
- **Use online `Sat` as a quantified SAT result.** Rejected: EUF is a weaker
  abstraction of BV/arithmetic semantics and finite matching is incomplete.
- **Add e-nodes under an arbitrary SAT decision scope.** Rejected: rollback can
  invalidate dynamic atom node ids.
- **Pre-enumerate every possible atom.** Rejected: later instantiations create
  terms not known before matching and would restore eager blowup.
- **Insert unchecked producer clauses and rely only on final QF UNSAT.** Rejected:
  QF replay proves the generated set contradictory, not that each generated
  clause follows from an original quantifier.

## Consequences

- Checked quantifier implications can participate in live Boolean propagation,
  conflict analysis, backjumping, phase saving, and learned-clause reuse.
- The fresh-QF route remains the complete compatibility fallback and final
  independent refutation gate.
- Online proof serialization, non-equality theory antecedents, SAT-trail-driven
  matching callbacks, and direct evidence export remain separate increments.
