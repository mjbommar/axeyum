# SMT and Theories

**Satisfiability modulo theories** (SMT) keeps SAT's Boolean structure and adds
typed values with defined operations: machine words, integers, reals, arrays,
functions, floating-point values, strings, and more.

Instead of manually encoding every operation as Boolean gates, you can ask a
question in the vocabulary of the problem.

## Sorts give terms meaning

An SMT **sort** is a type. It determines the values a term may have and which
operations are legal.

```smt2
(declare-const flag Bool)
(declare-const byte (_ BitVec 8))
(declare-const count Int)
(declare-const ratio Real)
```

`byte` has exactly 256 possible values and wraps after 255. `count` ranges over
mathematical integers and does not wrap. Treating either one as the other would
change the problem, so Axeyum's typed term builder rejects sort and bit-width
mismatches rather than guessing a coercion.

The mathematical `Int` sort is a semantic contract, not an arbitrary-precision
implementation claim. Axeyum's current concrete `Int` values and rational
reference components use `i128`; out-of-range evaluation reports
`ArithmeticOverflow`, and a dependent solve fails closed instead of wrapping.

## A first theory query

This asks whether an 8-bit value can wrap to zero after adding one:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-model)
```

The result is `sat` with `x = #xff`. The important pieces are:

- `QF` means **quantifier-free**;
- `BV` selects fixed-width **bit-vectors**;
- `declare-const` introduces a typed unknown;
- `assert` adds a condition that must be true;
- `check-sat` asks whether all current assertions have a model.

`get-model` is a command about how to present a prior `sat` result. It does not
change satisfiability.

## Common theories

| Theory | Typical logic name | What it models |
|---|---|---|
| Fixed-width bit-vectors | `QF_BV` | registers, machine arithmetic, bitwise operations |
| Linear integer arithmetic | `QF_LIA` | counters and exact integral constraints |
| Linear real arithmetic | `QF_LRA` | exact rational linear constraints |
| Arrays | `QF_ABV`, `QF_AX` | memory-like read/write maps |
| Uninterpreted functions | `QF_UF` | unknown functions constrained only by equality |
| Floating point | `QF_FP` | IEEE-style formats, rounding, NaNs, infinities |
| Strings and sequences | `QF_S`, `QF_SLIA` | concatenation, length, containment, indexed access |

Logic names describe a language fragment; they do not by themselves prove that
a particular solver implements every command, operator, or proof route in that
fragment. For Axeyum, check the
[capability matrix](../research/08-planning/capability-matrix.md) and
[limitations](../user-guide/limitations.md) before depending on a fragment.

## How SAT and theories cooperate

Take this integer formula:

```text
(x <= 0 or y <= 0) and x > 0 and y > 0
```

SAT can choose Boolean truth values for the three comparisons, but arithmetic
must determine whether those choices can describe actual integers. A theory
procedure reports the contradiction; the Boolean engine learns from it and
continues or concludes `unsat`.

Different fragments use different architectures:

- finite bit-vectors can be completely lowered to Boolean circuits and SAT;
- linear arithmetic can use exact simplex and theory lemmas;
- equality with uninterpreted functions uses congruence closure;
- combined theories exchange equality and model information;
- incomplete or bounded procedures may honestly stop at `unknown`.

The public contract remains the same even when the route changes: a returned
`sat` needs a model that satisfies the original assertions, and a supported
`unsat` route should carry independently checkable evidence.

## Theories define edge cases

SMT operators have mathematical specifications, including cases programming
languages sometimes leave undefined. For example, SMT-LIB bit-vector division
by zero is total: unsigned `bvudiv x 0` returns the all-ones bit-vector. Signed
and floating-point operations likewise have exact specified behavior.

This matters for verification. If an encoder and evaluator disagree on one
edge case, a solver can produce a convincing answer to the wrong problem.
Axeyum therefore keeps semantics, lowering maps, model lifting, and replay
explicit.

## Quantifiers change the problem

Quantifier-free formulas ask about declared constants. Quantifiers express
claims over every or some value:

```smt2
(assert (forall ((x Int)) (>= (* x x) 0)))
```

Finite domains can sometimes be expanded completely. General quantified
reasoning needs instantiation, model finding, or specialized certificates and
is often incomplete. `unknown` is the correct result when the active procedure
has not proved either side.

## Logical outcomes and operational errors

Keep these categories separate:

- `sat`: a model exists and is returned only after the applicable replay/check;
- `unsat`: no model exists, with assurance depending on the route's evidence;
- `unknown`: the procedure or resource budget did not settle the query;
- error: the input was malformed, used unsupported syntax, or the backend
  failed operationally.

An integration must handle all four. In particular, never convert `unknown` or
an error into `unsat`.

## Next

Continue to [Bit-vectors and bit-blasting](04-bit-vectors-and-bit-blasting.md),
then learn how to interpret [sat, unsat, and unknown](05-models-unsat-and-unknown.md).
