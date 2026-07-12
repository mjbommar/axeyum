# ADR-0108: Checked counterexample covers for quantified UNSAT

Status: accepted
Date: 2026-07-11

## Context

ADR-0107 leaves one row in the 12-file quantified-LIA division undecided:
`006-cbqi-ite`. It is a ground Boolean network conjoined with one positive
universal over Bool/Int binders, followed by a ground assertion that excludes
the only Boolean configurations satisfying that universal. Z3 4.16 closes the
row in about 20 ms through its QSAT path; monolithic `qe` did not finish within
a 90-second exploratory budget. The local cvc5 and Z3 sources likewise use
incremental model-based instantiation/projection rather than whole-formula
elimination.

The rejected concrete-tuple prototype added complete 40--50-component instances
and repeatedly re-solved a growing arithmetic formula. It did not converge in
32 rounds. ADR-0107 subsequently added a stronger primitive for SAT checking:
from a concrete counterexample it traces a sufficient cube of free Boolean
values. Holding only that cube fixed preserves the same falsifying bound
assignment, so one counterexample can exclude a family of ground models.

Those cubes currently guide untrusted SAT search only. They can also form a
small independently checkable UNSAT artifact when they cover every model of the
ground skeleton.

## Decision

Add a bounded counterexample-cover refuter for positive universal Bool/Int
assertions with only free Boolean symbols.

Search proceeds deterministically:

1. replace positive universal subterms by `true` in a weakening used only as the
   ground search skeleton;
2. solve the skeleton plus accumulated blocking clauses;
3. under the candidate free-Boolean model, solve the negation of each untouched
   universal assertion after dropping its positive universal binders;
4. extract original binder values from a concrete counterexample and trace a
   sufficient free-Boolean cube through the untouched unquantified assertion;
5. add the negation of that cube as the next blocking clause; and
6. return `unsat` only when the blocked skeleton is unsatisfiable and a separate
   checker accepts the complete cover.

The arena-stable certificate stores only:

- the original assertion `TermId` for each case;
- one complete, binder-order-preserving list of original Bool/Int binder values;
  and
- one sorted, nonempty cube of original free-Boolean symbol values.

The independent checker clones the original arena and performs two obligations:

1. **Case validity.** For every case, instantiate every positive universal in
   its named assertion with the carried original binder values. Prove that the
   resulting exact source consequence conjoined with the cube is QF
   unsatisfiable. Arithmetic `ite` is lifted exactly; LIA-DPLL theory cores and
   any large propositional DIMACS/DRAT closure are source-bound and rechecked.
2. **Cover closure.** Replace positive universals by `true` in every original
   assertion, conjoin the negation of every checked cube, and prove this exact
   weakened skeleton QF-unsatisfiable through the same source-bound checker.

The two obligations imply the original conjunction is unsatisfiable: each
universal entails its checked source instance, each instance entails the
corresponding cube's negation, and the original formula entails the weakened
ground skeleton. Counterexample search, dependency tracing, cube ordering, and
candidate models are untrusted and cannot grant a verdict.

Admission retains ADR-0107's boundary: Bool/Int terms, no applications or free
non-Boolean symbols, positive universal positions only, at most 64 free Boolean
symbols, at most 256 cover cases, explicit node/binder limits, and one shared
caller deadline. Unsupported, incomplete, duplicate, malformed, over-budget,
or tampered artifacts decline to `unknown`/`false`.

This is a reusable finite-cover proof scheme, not a benchmark-name recognizer
and not general Presburger QE. Native solvers remain differential references;
the product and checker remain pure Rust.

For the first kernel reconstruction slice, flatten top-level conjunctions and
admit exactly one positive universal leaf. Free Boolean symbols become opaque
`Prop` atoms. Each cover case applies the original dependent-product universal
to its carried computational `Bool`/integer witnesses and proves the resulting
body false by signed connective reasoning plus integer-ring normalization and
literal-order proofs. A deterministic, 100,000-node-capped excluded-middle tree
then shows that every free-Boolean branch either violates an original ground
conjunct or matches a checked source case. Search results and evaluator truth
values guide construction only; the generated closed term must infer and be
definitionally equal to `False` in the in-tree Lean kernel.

## Acceptance

- `006-cbqi-ite` becomes checked/certified `unsat` within the committed
  10-second corpus budget, with DISAGREE=0 against its source status.
- The checker rejects changed assertions, missing or reordered binder values,
  enlarged/changed cubes that are not source-valid, dropped cases, and duplicate
  or over-cap cases.
- Synthetic tests exercise multi-binder Bool/Int covers, positive-context
  nesting, arithmetic `ite`, incomplete covers, and deterministic resource caps.
- Fresh quantified-LIA measurement is 12/12 with no replay failure, audit error,
  timeout, mismatch, or trust hole.
- The final UNSAT evidence reconstructs to kernel-checked `False`, preserving
  all-row Pareto proof credit rather than trading decide-rate for assurance.
- Focused tests, solver/evidence/bench splits, workspace Clippy,
  warning-denied rustdoc, links, foundational resources, formatting, and golden
  matrices pass; the known whole-aggregate limitation is recorded.

## Alternatives

- **Increase the concrete tuple/round budget.** Rejected: the prior prototype
  spent 30 seconds on 32 large instances and did not attack the repeated-solve
  cost or generalize equivalent free-Boolean candidates.
- **Run whole-formula QE.** Rejected for this path: the reference Z3 `qe` tactic
  exceeded 90 seconds while its incremental QSAT solver closed the row in about
  20 ms.
- **Trust dependency-traced cubes.** Rejected: every cube must be proved against
  a regenerated source instance, and the complete cover must be independently
  closed.
- **Recognize the benchmark's transition-system encoding.** Rejected: the
  source-instance/cube contract is smaller, reusable, and independently checks
  any admitted formula.

## Consequences

- ADR-0107's SAT-side counterexample analysis becomes a shared quantified
  search primitive instead of a one-directional heuristic.
- Quantified UNSAT gains a compact finite-cover artifact whose proof obligations
  reduce to already checked QF LIA/Boolean infrastructure.
- General symbolic arithmetic projection, clause watches, alternation, and
  function-valued models remain explicit P2.6 work after this finite cover.
- The first public proof remains explicitly bounded. Its initial tree-expanded
  Lean module was about 152 MB and took about 18 seconds to reconstruct.
  ADR-0109 now preserves closed kernel-DAG sharing in source, reducing the
  current artifact to 2.68 MB and reconstruction to about 10.75 seconds. Open
binder-context sharing remains a separate proof-export boundary.
- Kernel reconstruction separately caps unary source literals, carried integer
  witnesses, and expanded ground normalization at 4,096 units. This does not
  weaken executable cover checking; oversized checked covers simply receive no
  Lean artifact.

## Validation

- The committed 12-file quantified-LIA corpus now decides 12/12 (4 SAT, 8
  UNSAT), with DISAGREE=0 and no model/evidence replay failures. The target
  `006-cbqi-ite` produces 119 source cases (maximum cube width 6) and solves in
  about 1.2 seconds in the release measurement.
- The independent audit reports certified 12/12, checked 12/12, Lean-checked
  UNSAT 8/8, and dominant candidates 12/12, with zero mismatches, audit errors,
  timeouts, or trust holes. For `006-cbqi-ite`, evidence production took about
  1.18 seconds, evidence recheck about 0.26 seconds, and kernel reconstruction
  about 17.74 seconds under a 60-second audit cap. ADR-0109's follow-up audit
  preserves the same result while reducing kernel reconstruction to about
  10.75 seconds and the module from 151,845,067 to 2,682,977 bytes.
- Focused tests cover a multi-binder affine integer-`ite` source case, malformed
  and reordered bindings, duplicate/over-cap covers, dropped closure cases, a
  small kernel reconstruction, rejection of the multiple-universal near miss,
  zero-trust public evidence, and an explicit release-only public kernel test.
- A valid cover with an oversized integer witness is rejected before proof-term
  construction, pinning the distinction between evidence validity and bounded
  reconstruction.
- Reference-source inspection used Z3's QSAT/model-evaluation paths and cvc5's
  CEGQI arithmetic/instantiation paths. A linked Z3 4.16 diagnostic closed the
  target in roughly 13--22 ms; monolithic Z3 `qe` exceeded 90 seconds. No native
  solver is linked into the product route.
