# ADR-0132: Checked zero-product quantified-BV models

Status: accepted
Date: 2026-07-12

## Context

After ADR-0131, `gn-wrong-091018` is the smallest unsupported row in the
public cvc5 quantified-BV slice. Its assertion is a directly negated
existential implication. Exactly one outer antecedent conjunct depends on the
single binder; that conjunct is itself an implication whose conclusion is

```text
(bvsge (bvmul (bvsdiv (_ bv1 32) (_ bv2 32)) P(b)) (_ bv0 32))
```

for a nonlinear binder-bearing polynomial `P`. Under SMT-LIB bit-vector
semantics, signed division truncates toward zero, so the direct binder-free
factor `bvsdiv 1 2` is exactly zero. Multiplication by that zero annihilates the
polynomial without interpreting or linearizing it, and the resulting signed
comparison is reflexively true.

cvc5's quantifier `TermUtil::isSingularArg` identifies zero as a singular
argument of `BITVECTOR_MULT`; its BV CEGQI instantiator separately attempts
guarded addition/multiplication linearization and reports unresolved nonlinear
terms. cvc5 eliminates signed division to sign tests, absolute values, and
unsigned division. Z3 constant-folds concrete signed division with machine BV
semantics, routes multiplication through its polynomial rewriter, and checks a
quantified candidate model by asserting the model-substituted negated body with
fresh skolems in an auxiliary context. These are design references, not
evidence accepted by Axeyum.

## Decision

**Add one independently checked `NegatedExistentialZeroProductImplication`
proof form to `QuantifiedBvModelSatCertificate`; untrusted QF_BV search may
propose the complete free-BV model, but SAT credit requires exact source
annihilation plus canonical model replay.**

The source checker admits exactly one directly negated existential binder and
one outer implication. Its outer antecedent must have exactly one
binder-dependent conjunct. That conjunct must be an implication whose
conclusion is exactly signed nonnegativity of a binary BV product:

```text
(bvsge (bvmul zero_factor binder_factor) literal_zero)
```

The factors may be commuted. `zero_factor` must be a direct, binder-free
`bvsdiv`; `binder_factor` must contain the unique binder; and the right operand
must be a literal zero of the same BV sort. No property of the inner premise or
the nonlinear binder factor is assumed.

Under the certificate's exact, sorted, complete free-symbol assignment, the
checker:

1. evaluator-replays every binder-free outer antecedent leaf to `true`;
2. evaluator-replays the untouched outer conclusion to `false`;
3. evaluator-replays the direct signed-division factor to an exact zero BV;
4. checks the product, comparison, binder occurrence, and literal-zero source
   structure independently from search; and
5. concludes that the product is zero and hence `0 >=s 0` for every binder
   value.

The inner implication is therefore true for every binder value regardless of
its premise. The outer antecedent is true and its conclusion false for every
binder value, so the existential is false and the asserted negation is true.

ADR-0130 source admission remains in force: Bool/BV only, no function
applications, unique binders, exact free-symbol coverage, at most 128 binders,
4,096 complete source DAG nodes, depth 256, and 4,096 total free-BV bits.

Untrusted search extracts only sufficient ground QF_BV obligations: every
binder-free outer antecedent leaf, equality of `zero_factor` with a same-width
zero, and the negated outer conclusion. Missing unconstrained free values are
completed deterministically with zero. The result is discarded unless the
independent source checker and canonical `check_model` both accept it.

## Evidence

Before this change, the 88-DAG-node `gn-wrong-091018` row was expected SAT but
returned unsupported immediately. Its source shape and exact annihilation were
checked against:

- `references/cvc5/src/theory/quantifiers/term_util.cpp`;
- `references/cvc5/src/theory/quantifiers/cegqi/ceg_bv_instantiator.cpp`;
- `references/cvc5/src/theory/bv/theory_bv_rewrite_rules_operator_elimination.h`;
- `references/z3/src/ast/rewriter/bv_rewriter.cpp`; and
- `references/z3/src/smt/smt_model_checker.cpp`.

The row now returns replay-checked SAT. Five release corpus samples are
84.292858, 89.874858, 88.677335, 79.148524, and 91.340195 ms (median
88.677335 ms). Separate evidence-production samples are 70.429, 72.517,
70.981, 72.258, and 70.548 ms (median 70.981 ms).

The 54-row public cvc5 quantified-BV slice is now 35 SAT / 17 UNSAT / 0 unknown
/ 2 unsupported, with 52 expected-status agreements and no disagreement,
error, or replay failure. Five PAR-2 samples are 0.794452, 0.794156, 0.794198,
0.794015, and 0.794377 seconds (median 0.794198 seconds). Exactly
`gn-wrong-091018` changes outcome.

The complete dominance audit certifies and checks all 52 decisions, marks
43/52 dominant candidates, and retains Lean coverage at 8/17 UNSAT. The target
evidence kind is `quantified-bv-model-sat`, with no trust steps or holes.

Thirteen focused tests cover all three public model classes, evidence replay,
free-value/binder/certificate tampering, exact direct-signed-division and
comparison polarity, a commuted nonlinear product at width 129, source caps,
and 128 direct-Z3 cases and controls. The 32 new zero-product cases comprise 16
certified SAT models and 16 nonzero-factor UNSAT controls. Cumulative
quantified-BV direct-Z3 coverage is 1,848 cases and controls with no
disagreement. Strict all-target solver Clippy and adjacent evidence,
free-Boolean model, alternation, and quantified-BV differential suites pass.

The complete workspace `just check` passes, including formatting, strict
Clippy, all tests, warning-denied rustdoc, foundational-resource validation,
generated-document consistency, and link checking.

## Alternatives

- **Extend ADR-0131's interval matcher.** Rejected: interval containment and
  zero-product annihilation are different proof theorems and should fail
  independently.
- **Normalize the whole nonlinear polynomial.** Rejected: no property of the
  polynomial is needed once an independently checked direct factor is zero.
- **Assume mathematical rational division.** Rejected: only the original IR
  evaluator's total SMT-LIB signed-BV semantics may establish the zero factor.
- **Trust a rewritten QF_BV query or solver candidate.** Rejected: search code
  re-extracts a sufficient condition but cannot certify the quantified source.
- **Accept arbitrary ground-zero expressions or arbitrary comparisons.**
  Rejected for this increment: the checker intentionally requires the direct
  signed-division/product/signed-nonnegativity source shape measured here.
- **Use implication vacuity.** Rejected: the checker proves the inner
  conclusion true for every binder and does not inspect premise truth.

## Consequences

Axeyum can now certify this exact class of complete free-BV models without
enumerating the binder or interpreting nonlinear binder arithmetic. The rule
remains deliberately incomplete: it is not general
nonlinear BV simplification, arbitrary zero-factor reasoning, interval
reasoning, nested alternation, function/array support, proof serialization, or
Lean SAT reconstruction.
