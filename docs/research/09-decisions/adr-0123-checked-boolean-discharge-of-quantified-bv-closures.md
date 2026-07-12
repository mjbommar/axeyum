# ADR-0123: Checked Boolean discharge of quantified BV closures

Status: accepted
Date: 2026-07-11

## Context

ADR-0107 certifies quantified Bool/Int SAT when a complete free-Boolean model
makes every untouched assertion true. Its independent checker treats unresolved
arithmetic as unknown and grants SAT only through exact three-valued evaluation
or a source-bound LIA refutation. It currently rejects every BV term at the
admission boundary, even when BV semantics are irrelevant.

The remaining public cvc5 SAT unknown, `model_6_1_bv`, has the form

```smt2
(forall ((lambda (_ BitVec 32)))
  (or opaque-quantified-bv-branch
      (bvslt lambda 0)
      (not (and (not b22) (not b7) b5 (not b6)))))
```

Choosing the free Booleans all false makes the final disjunct true for every BV
assignment. Proving this does not require a value for any free BV symbol, an
interpretation of the inner existential, or BV QE. The existing checker already
computes exactly this proof if BV syntax is allowed through admission: every
unsupported BV predicate is `unknown`, while `unknown or true` is true.

## Decision

**Extend ADR-0107 admission to Bool/Int/BV syntax, while keeping BV semantics
opaque and granting SAT only when the independent three-valued checker proves
the untouched assertion true.**

The admission collector:

- continues to collect a complete, sorted assignment for every free Boolean;
- permits bound Bool, Int, and BV symbols;
- permits free BV symbols without requiring certificate values for them,
  because the checker must prove the result independent of them;
- continues to reject free Int symbols, functions, arrays, and other sorts; and
- preserves binder uniqueness and the existing node/Boolean-branch caps.

The checker does not add a BV evaluator. BV operations and non-reflexive BV
predicates remain `unknown`; exact same-term equality remains true by
reflexivity. Quantifiers over non-Boolean scalar domains evaluate their body
symbolically, which is sound because only domain-independent `True` can grant
SAT and SMT-LIB BV domains are nonempty. Boolean connectives retain Kleene-style
short-circuit semantics, so a carried true disjunct or false implication
antecedent can discharge an otherwise opaque quantified closure.

If structural evaluation is not `True`, any closure containing BV syntax must
decline before the ADR-0107 LIA fallback. Quantifier erasure and the QF model are
still untrusted candidate search only. Canonical `check_model` independently
replays the same original-IR proof, and `Evidence::Sat` uses that route.

## Acceptance

- `model_6_1_bv` moves from unknown to replayed, evidence-certified SAT with an
  empty trust ledger.
- Free and bound BV syntax of narrow and wide widths is admitted only behind a
  decisive Boolean branch; disabling that branch declines rather than guessing.
- Tampered/incomplete Boolean assignments, negative quantifier polarity,
  functions, arrays, free Int symbols, stale assertions, and unresolved BV
  formulas fail closed.
- A direct-Z3 matrix covers admitted Boolean discharges and satisfiable/unsat
  near misses with zero verdict disagreement.
- The public quantified-BV slice gains exactly the target decision with no
  disagreement, error, replay failure, or existing-row regression.

## Evidence

- `model_6_1_bv` is replayed SAT in a five-run optimized median of 0.064489
  ms. The public cvc5 quantified-BV slice is now 32 SAT / 9 UNSAT / 2 unknown /
  11 unsupported, with 41 expected-status agreements, no disagreement, error,
  or replay failure, and five-run PAR-2 median 6.07677 seconds.
- The dominance audit independently certifies and checks all 41 decisions; 40
  are dominant candidates. The target is classified
  `quantified-bool-model-sat`, has an empty trust ledger, and is dominant. Lean
  reconstructs 8/9 UNSAT rows.
- The direct-Z3 quantified-BV suite covers 1,256 cases and controls with zero
  disagreement. Its 64-case Boolean-discharge matrix admits and replays all 32
  exact cases, agrees on 12 UNSAT controls, and safely declines or replays the
  remaining satisfiable controls.
- Solver 863/863, Boolean-model 10/10, guard 5/5, quantified-certificate 13/13,
  evidence 69/69, and bench 7/7 suites pass. Workspace Clippy, warning-denied
  rustdoc, generated matrices, links, foundational resources, rules-as-code,
  formatting, diff, and all 26 reference-presence checks pass. The independent
  `frontier_bv_reduction` 28-versus-30 ratchet recorded by ADR-0122 remains open
  and its baseline remains unchanged.
- The proof is propositional and independent of BV semantics: `P or true` is
  true for every interpretation of opaque `P`.
- Z3's model checker searches for counterexamples to quantified model
  interpretations (`references/z3/src/smt/smt_model_checker.cpp`), while cvc5's
  nested-QE route invokes dedicated elimination subsolvers
  (`references/cvc5/src/theory/quantifiers/cegqi/nested_qe.cpp`). Axeyum uses a
  strictly smaller complete checker for the measured Boolean-discharge class.
- ADR-0107 already establishes complete free-Boolean assignments, original-IR
  replay, source-bound fallback proofs, and candidate-only quantifier erasure.
  ADR-0123 changes only which opaque scalar syntax may reach that checker.

## Alternatives

- **Add general BV model construction.** Deferred: no BV value participates in
  this proof, and inventing values would enlarge both model and replay surfaces.
- **Evaluate the opaque BV branch with the solver.** Rejected: it is unnecessary
  for a complete Boolean proof and would mix untrusted search into checking.
- **Create another certificate family.** Rejected: this is exactly ADR-0107's
  complete free-Boolean model artifact with a wider opaque body vocabulary.
- **Accept free values of every sort as opaque.** Rejected: only Bool/BV is
  measured, finite BV domains are explicitly nonempty, and broad admission
  would obscure the intended boundary.

## Consequences

- Boolean configurations can certify quantified BV closures when they make all
  BV semantics irrelevant.
- The certificate still carries only free Boolean values; omitted BV values are
  proved irrelevant rather than defaulted.
- General BV models, non-Boolean discharges, QSAT/QE, piecewise Skolems,
  function interpretations, and proof serialization remain open.
