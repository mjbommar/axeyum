# ADR-0541: The SMT-LIB front door answers a command or says `unsupported` — never nothing

Index-summary: A per-command session response stream (`get-model`/`get-value`/`get-unsat-core`/`get-proof`/`echo`), a `set-option` that reports what it does not honor, and a `set-logic` that is recognized rather than enforced.
Status: accepted
Date: 2026-08-21

## Context

[`gap-analysis-smt-solvers-2026-08-21.md`](../../plan/gap-analysis-smt-solvers-2026-08-21.md)
§6.3 calls interfaces "the weakest axis" and ranks the consumer interface as
gap #3: *"Nothing here is research; it is the difference between a library and a
solver a stranger can run."* Four of its six items are one defect wearing four
hats — **a command the front door accepts and does not answer**:

- `get-model`, `get-value`, `get-unsat-core`, `get-proof` were CLI no-ops. A
  library entry point existed for each ([`solve_smtlib_get_model`] and
  siblings), but each decides a *whole script* rather than a command in the
  middle of one, so none could be reached from a driver that walks commands.
- `set-option` was inert. `:produce-models`, `:produce-proofs`,
  `:produce-unsat-cores` and `:timeout` all silently did nothing.
- `set-logic` was stored as an opaque string and never read;
  `(set-logic NONSENSE_XYZ)` and no `set-logic` at all both decided normally.

The half that was closed first — `examples/axeyum_cli.rs`, one verdict per
`check-sat` — made the rest sharper, not softer: a driver that answers
`check-sat` and drops `(get-model)` gives a consumer **no output and no
complaint**, which is indistinguishable from a solver that has no model.

The failure mode is the repository's own: *silence read as a negative result.*
An empty answer and an unasked question look identical, and this codebase has
already paid for that reading twice — once on a corpus gate that ran zero tests
for fifteen days while exiting 0, once on a `prelude_axiom_inventory` grep that
returned nothing because the tool was never pointed at the subject.

## Decision

**Every SMT-LIB command the parser accepts produces a response, and a command
this front door cannot answer says `unsupported` with a reason.**

Concretely:

1. **`ScriptCommand` records output and metadata commands positionally.** New
   variants `SetLogic`, `SetOption`, `GetModel`, `GetValue`, `GetUnsatCore`,
   `GetProof`, `Echo`, `UnansweredOutput`. The parser already had `Script::logic`,
   `Script::options`, `Script::get_model` and `Script::get_value_terms`, but a map
   cannot say *where* an option was set, collapses a key set twice, and cannot
   scope a model query to the `check-sat` it follows.

2. **`solve_smtlib_session` walks that stream and returns one
   `SmtLibResponse` per output command.** `get-model`/`get-value` answer from the
   retained model of the preceding `check-sat`; `get-unsat-core` runs the
   deletion-minimizer over the exact assertion set that query decided;
   `get-proof` runs the same four Alethe emitters as
   `solve_smtlib_get_proof`, each re-checked before it is returned.

3. **`solve_smtlib_incremental` is that same walk with the output commands
   switched off** (`SessionPolicy::VerdictsOnly`), not a second implementation
   of it. The two therefore cannot report different verdicts, and adding the
   session could not move a verdict on any existing corpus file. Options are
   deliberately inert in that mode: honoring `(set-option :timeout …)` there
   would change what a committed benchmark decides.

4. **A closed set of honored options**: `:produce-models`, `:produce-unsat-cores`,
   `:produce-proofs`, `:print-success`, `:timeout`. Everything else draws
   `unsupported`. cvc5 1.3.4 answers `unsupported` here and Z3 4.13.3 raises an
   error; SMT-LIB §4.1.7 prescribes `unsupported`, so that is what is emitted.

5. **The caller's timeout is a ceiling on the script's `:timeout`**, never a
   default the script overrides. A script cannot award itself more budget than
   the operator granted.

6. **`set-logic` is recognized, not enforced.** A name that is not shaped like an
   SMT-LIB logic draws `unsupported` and the script is still decided, which is
   exactly what Z3 4.13.3 does. Conformance checking — rejecting `Int` under
   `QF_BV` — is deliberately not implemented; see the alternatives below.

7. **`get-model` and `get-value` decline rather than guess.** A value whose sort
   has no re-parseable SMT-LIB spelling here (uninterpreted carrier token,
   datatype, array, algebraic real) makes the whole command `unsupported`.

## Consequences

- A stranger can run `axeyum_cli script.smt2` the way they run `z3 script.smt2`
  and get the SMT-LIB responses, or an explicit refusal.
- `SmtLibResponse` is deliberately **not** `#[non_exhaustive]`: a downstream
  `match` would then need a wildcard, and the wildcard is how a new response
  variant gets silently dropped by the driver that is supposed to print it.
  `axeyum_cli` matches it exhaustively.
- `axeyum_cli`'s exit status depends on what the run *found*: an `(error …)`
  response exits 3. A status that cannot fail is worse than none.
- The three `ScriptCommand` walks outside the parser (`smtlib_single_query`,
  `solve_smtlib_get_assertions`, `axeyum-wasm`) list the new variants explicitly
  rather than wildcarding them, so a future command that *does* move the
  assertion stack fails to compile instead of being skipped.
- `smtcomp_cli` is untouched and stays single-query with no added output:
  SMT-COMP 2026 §7.1.2 treats stray `sat`/`unsat` text as a reported result.
  That is why two binaries exist.

## Alternatives considered

**Enforce logic conformance.** Standards-correct, and both references do it.
Measured 2026-08-21 over the 1,430 tracked `.smt2` files: every one declares a
logic, and a minimal five-rule conformance check flags **5** (all `QF_SLIA`
scripts using `(_ BitVec n)` sequence elements, which `QF_SLIA` does not have).
Z3 4.13.3 rejects all five at the parser; axeyum decides one of them. So the cost
is one decided file — which is *not* the reason to decline. The reason is that
enforcement needs a complete logic → theory table, and a table with a hole
refuses a **correct** file: a false refusal is a wrong answer, while deciding a
nonconforming script answers a superset of what was asked. The table is the
work, and it is not started here rather than half-started.
`logic_conformance_would_reject_five_corpus_files` pins the census.

**A hand-written list of logic names.** Tried first, and wrong on first contact
with the corpus: it omitted **`BV`**, which 59 tracked files declare. SMT-LIB
logic names are generated — optional `QF_` plus theory tokens in canonical
order — so a list is a snapshot of someone's memory while a shape rule is the
grammar. `every_logic_the_corpus_declares_is_recognized` is the positive control
that caught it.

**Render an uninterpreted-sort model the way Z3 does.** Z3 emits a universe
block with `U!val!0` tokens and a cardinality constraint — a Z3 extension, not
SMT-LIB, and one whose element distinctness is conventional rather than
asserted. Inventing our own spelling would hand a consumer something that looks
like a model and is not one, so a `QF_UF` `(get-model)` is refused instead. This
is a named gap, not an oversight.

**Honor `(exit)`.** The parser reads the whole script before anything is
decided, so honoring `exit` means *dropping* trailing commands — a verdict-stream
change to every corpus file that ends in one. Recorded as a stated divergence in
`axeyum_cli`'s module docs rather than half-done.

## Evidence

- Differential against `/usr/bin/z3` 4.13.3 and
  `/nas3/data/axeyum/harness/bin/cvc5` 1.3.4, 2026-08-21. Every default in
  `SessionOptions` was measured rather than assumed: both references answer
  `(get-model)` in a script that never set `:produce-models` (so the default is
  `true`) and both error on `(get-unsat-core)` without `:produce-unsat-cores`
  (so that default is `false`).
- `crates/axeyum-solver/tests/smtlib_session.rs`, 29 tests. Each guard was
  deleted and the suite re-run; the two that killed nothing
  (`get-value`'s own `:produce-models` and `sat` guards — the `get-model` tests
  cover a different code path) got the tests they were missing.
