# Notes: 119-consumer-interface

Detail moved out of [`../status/119-consumer-interface.md`](../status/119-consumer-interface.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

ADR-0541 states the rule as **a command is answered or it says `unsupported`
with a reason**. `solve_smtlib_session` walks the command stream and returns one
response per output command; `solve_smtlib_incremental` is now that same walk
with the output commands switched off (`SessionPolicy::VerdictsOnly`), not a
second implementation, so the two cannot disagree about a verdict.

**Every default was measured against both references, not assumed.** Z3 4.13.3
and cvc5 1.3.4 both answer `(get-model)` in a script that never set
`:produce-models`, so that default is `true`; both error on `(get-unsat-core)`
without `:produce-unsat-cores`, so that one is `false`. An unhonored
`set-option` answers `unsupported` (cvc5's behaviour and SMT-LIB §4.1.7; z3
raises an error instead). `(set-logic NONSENSE_XYZ)` answers `unsupported` and
still decides, which is exactly z3.

**`set-logic` is recognized and deliberately not enforced, and the decision is
priced.** Over the 1,430 tracked `.smt2` files every one declares a logic, and a
minimal five-rule conformance check flags **5** — all `QF_SLIA` scripts using
`(_ BitVec n)` sequence elements. z3 rejects all five at the parser; axeyum
decides one. So enforcement costs one file, which is *not* the reason to
decline: enforcement needs a complete logic → theory table, and a table with a
hole refuses a **correct** file, which is a wrong answer where deciding a
nonconforming script merely answers a superset.

**The recognizer was a hand-written list and the list was wrong on first
contact.** It omitted **`BV`**, which 59 tracked files declare. It is now a shape
rule over the generated grammar, with the corpus's 40 distinct logic names as a
positive control.

**`get-model`/`get-value` decline rather than guess** — and a census said which
refusal to stop making. A value whose sort has no re-parseable SMT-LIB spelling
makes the whole command `unsupported`; over 400 corpus files that was **66
refusals, 58 of them arrays** — more than every other cause combined. So arrays
now render as `(store … ((as const (Array I E)) default) …)`, the spelling z3
4.13.3 prints, and the same census re-run reads **166 models rendered, 9
refused**. The residual is uninterpreted carrier tokens (7), algebraic reals (2)
and datatypes (0 in this population): a `QF_UF`
`(get-model)` is refused because z3's `U!val!0` universe block is a z3 extension
whose element distinctness is conventional, and inventing our own spelling would
hand a consumer something that looks like a model and is not one.

Measuring the refusals rather than reasoning about them is what changed the
order of work: uninterpreted sorts *felt* like the gap and arrays were ten times
the volume.

**`smtcomp_cli` is untouched** and stays single-query with no added output
(SMT-COMP 2026 §7.1.2 treats stray verdict text as a reported result).

**The new answers are cross-validated by z3, not diffed against it** — two
models are both correct, so equality is the wrong test. Every reported value is
pinned as an equation on the original script and z3 must call the result `sat`
(**133/133**); every unsat core is re-run alone and z3 must call it `unsat`
(**122/122**). Both controls fire, and both needed a fix first: z3
**error-recovers**, so a sort-broken pin draws `(error …)` and the following
`(check-sat)` still prints a verdict — the corrupted-value control passed on a
script that never contained the corruption. And the harness's own `(get-value)`
parser read the first parenthesised group as the *term*, which is wrong when the
term is an atom and the value is an array; 89 files read as "z3 rejected our
model" and the models were fine.

**Next.** Render uninterpreted-sort models (7 refusals of 400 files) and
algebraic reals (2); answer `get-info`/`get-option`, which say `unsupported`
where z3 answers; decide
whether `(exit)` should truncate the walk, which needs the parser to stop reading
at it rather than the driver to stop executing; and the logic → theory table if
conformance is ever wanted.
