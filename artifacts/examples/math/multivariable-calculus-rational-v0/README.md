# Exact Rational Multivariable Calculus Checks

This pack adds a finite, exact bridge from one-variable calculus into the
multivariable material that appears in undergraduate calculus, optimization,
numerical analysis, and graduate analysis.

It intentionally checks only polynomial rows over exact rationals:

- gradient and value replay for a fixed two-variable quadratic;
- directional derivative replay as a gradient dot product;
- Jacobian chain-rule replay for a fixed polynomial map composition;
- Hessian positive-definiteness by exact leading principal minors;
- checked rejection of a false gradient row through source-linked
  QF_LRA/Farkas evidence;
- Lean-horizon metadata for general multivariable analysis.

The pack reinforces Axeyum's boundary: untrusted fast search can find concrete
rational witnesses, while a small trusted checker can replay the derivative
tables and matrix arithmetic. The bad-gradient row also links replay's computed
`gradient_y = 14` against the malformed claim `gradient_y = 13` through
`smt2/bad-gradient-farkas-conflict.smt2`, which Axeyum checks with
`UnsatFarkas` evidence.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
```
