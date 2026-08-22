# Lane: agent-consumer-interface — a command is answered or refused, never dropped

<!-- plan-section: lane-status -->

**Gap #3 of the 2026-08-21 capability audit is closed at the command level**
(`WIP`, agent-consumer-interface, 2026-08-21). §6.3 ranked the consumer
interface third by measured cost and called it "the difference between a library
and a solver a stranger can run". Four of its six items were one defect wearing
four hats: **the front door accepted a command and did not answer it.**
`get-model`, `get-value`, `get-unsat-core` and `get-proof` were CLI no-ops with
Rust-API-only counterparts; `set-option` was inert; `set-logic` was stored and
never read.

The half landed earlier — `examples/axeyum_cli.rs`, one verdict per `check-sat` —
made the rest sharper rather than softer. A driver that answers `check-sat` and
drops `(get-model)` produces **no output and no complaint**, and that is
indistinguishable from a solver with no model. It is this repository's own
recurring failure: silence read as a negative result.

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

<!-- plan-section: landed-changes -->

| 2026-08-21 | `b3ef9a965` | The refusal census picked the next thing to build, and it was not what the gap felt like. `(get-model)` declined 66 times over 400 corpus files and **58 were arrays**, against 6 uninterpreted-sort tokens; arrays now render as `(store … ((as const (Array I E)) default) …)` and the same census reads **166 rendered, 9 refused**. Also `DecidedQuery::proof_eligible`: a bounded-string `unsat` the gate did not confirm cannot draw an Alethe proof of the *packed* assertions. That one is defence in depth and says so — over 184 QF_S/QF_SLIA benchmarks, deleting it changes no answer, because the QF_BV emitter declines those shapes. |
| 2026-08-21 | `81361cdd1` | Gap #3's items 2–4. `solve_smtlib_session` answers `get-model`, `get-value`, `get-unsat-core`, `get-proof`, `get-assertions` and `echo` at the command where they stand; `set-option` reports `unsupported` for every option it does not honour; `(set-logic NONSENSE_XYZ)` says `unsupported` and still decides, as z3 does. `solve_smtlib_incremental` became the same walk with the output commands off, so no verdict could move — A/B over all 1,430 tracked `.smt2` at a 10 s budget: 2 differences, both on files that finish in 9.7–11.8 s, both binaries agreeing three of three at 60–120 s. 34 tests; 23 guards deleted one at a time, 22 killed a test and 16 killed exactly one. |
