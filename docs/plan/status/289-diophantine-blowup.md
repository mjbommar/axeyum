# 289 — the 96 MB Lean module for `14x + 21y = 5`

Lane: `diophantine-blowup`. Status: **in progress**.

## Step 0 — reproduced standalone, before reading any code

    ./target/release/examples/lean_hypothesis_binding_dump \
      artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2

    rc=0, 2.24 s wall, stdout = 96,297,506 bytes (91.8 MiB)
    stderr: BINDING_DUMP|...|fragment=Diophantine|assertions=1|indices=0

Confirms the finding lane's report independently.

## First structural measurement

The module is **234 lines**. One of them is 96,155,365 bytes — **99.85 % of the
whole file**. It is line 232, the body of

    theorem axeyum_refutation : False :=

The next-largest line is 14,183 bytes. So this is not a diffuse blowup across a
prelude; it is a single proof term.

Two candidate mechanisms visible by eye in that line, to be measured next:

- **Unary integer literals.** `7` renders as
  `Int.add (Int.add (Int.add (Int.add (Int.add (Int.add Int.one Int.one) Int.one) …`
  — seven `Int.one`s. The hypothesis axiom `dio.hyp._2` likewise renders
  `14x + 21y` as a 35-term sum of bare `x`/`y` atoms rather than an `Int.mul`.
- **An unshared repeated subterm.** The divided-through witness
  `t = 2x + 3y` renders as `(Int.add (Int.add (Int.add (Int.add x0 x0) x1) x1) x1)`
  and recurs constantly in the proof term. The module banner documents
  scope-aware `let` sharing; whatever the mechanism, it is plainly not
  applying to this term.

Which of these dominates is a measurement, not a guess, and is the next step.
