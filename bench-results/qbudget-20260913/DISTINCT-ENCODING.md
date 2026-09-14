# The 0.1 s rows: `distinct` is expanded pairwise at the front door

Lane `QBUDGET`, 2026-09-13. Diagnosis only in this file; whether a fix landed is
recorded in `README.md` beside it.

## What the rows are

Five `UFNIA` rows of the pinned 200 (four of them winnable) refuse at the front
door in ~0.107 s:

    UFNIA/lahiri-cav09-storm-queries/serial_write_example_cegar_2_2_2.smt2
      `distinct` with 1491 arguments requires 1110795 pairwise expansions
    UFNIA/lahiri-cav09-storm-queries/usbsamp_bug_example_2_3_8_1.smt2
      `distinct` with 1571 arguments requires 1233235 pairwise expansions
    UFNIA/lahiri-cav09-storm-queries/usbsamp_example_2_3_4_0.smt2
      `distinct` with 1571 arguments requires 1233235 pairwise expansions
    UFNIA/spec_sharp/test14-CommandLineOptions...get_ProverNeedsTypes.smt2
      `distinct` with 422 arguments requires 88831 pairwise expansions
    UFNIA/spec_sharp/test14-Xml.ssc...WriteFileFragment_System.String_notnull.smt2
      `distinct` with 380 arguments requires 72010 pairwise expansions

The cap is `MAX_DISTINCT_EXPANSION_PAIRS = 65536` at
`crates/axeyum-smtlib/src/parse.rs:19680`. The parser expands `(distinct t1 …
tN)` into `N(N-1)/2` pairwise disequalities, so cost is quadratic in `N` and the
cap is a deterministic ingest limit, not a clock.

The arguments are what Boogie always emits here: **nullary uninterpreted
constants of an uninterpreted sort**. From
`usbsamp_bug_example_2_3_8_1.smt2` (largest application, arity 1607):

    (distinct UNALLOCATED ALLOCATED FREED BYTE T.unused_WDFCOLLECTION__ …)

## Why this is not a one-line cap raise

Raising the cap to admit 1.2 M binary disequalities moves the failure from the
parser to whatever consumes the term. The quadratic blow-up is the defect; the
cap is only where it surfaces.

## The linear encoding, and the soundness constraint that scopes it

For a fresh uninterpreted `f : S -> Int` appearing nowhere else,

    (distinct t1 … tN)   ~>   (and (= (f t1) 0) (= (f t2) 1) … (= (f tN) N-1))

is `N` conjuncts instead of `N(N-1)/2`, and it is exact in both directions: if
`ti = tj` the right-hand side forces `i = j`; and any model making the `ti`
pairwise distinct extends to one interpreting `f` as required. It needs no
side-assertion channel — the result is a single term, so the parser's expression
path can build it — and `TermArena` already allows interning a fresh symbol
there.

**The constraint, which is the whole reason this is not a trivial patch:** the
rewrite introduces a fresh symbol, so it is equisatisfiable only in **positive
polarity**. Under a negation, `¬(distinct …)` is *not* `¬(and (= (f t1) 0) …)` —
the latter is satisfiable by any `f` that disagrees, for *any* `ti`, and the
result would be a wrong `sat`. `parse.rs` builds terms bottom-up with no polarity
context, so a naive substitution at the `distinct` site is unsound.

Two sound scopings, in increasing order of work:

1. **Top-level assert only.** Apply the rewrite only when the `distinct`
   application is the entire body of an `(assert …)` command — a context the
   command loop knows and the expression path does not. Covers all five rows
   above (Boogie emits the axiom exactly this way). Needs the check to be on the
   `assert` handler, not inside the `distinct` case.
2. **Polarity-tracked rewrite.** A rewrite pass over the assertion set that knows
   its polarity, applying the encoding at positive occurrences and the pairwise
   expansion (or a `Distinct` op, if one is ever added to the IR) elsewhere.

A soundness-negative test for either one must include a **negated** large
`distinct` and require the old path, and must assert on the *verdict* of a
satisfiable query, not merely that parsing succeeded: a `sat` is exactly the
failure mode the polarity trap produces, so a test that only checks "it parsed"
cannot fail on the bug it exists to catch.

## Sizing

4 winnable `UFNIA` rows, deterministic, ~0.1 s each. No A/B envelope is needed:
each file either parses and gets a verdict or it does not, and ambient load
cannot reach a 0.1 s front-door refusal. The verdict each file then reaches is
*not* predicted here — clearing the front door hands the query to the quantified
ladder, which may well spend its 24 s and return `unknown`. That is the second
half of the measurement and must be run, not assumed.

## Addendum (same lane, after reading the IR): the pieces all exist

Three things I did not know when the section above was written, each of which
shortens the work:

1. **The polarity problem has a structural answer already in the parser.**
   `parse.rs`'s command loop has an `"assert"` arm (`parse.rs:6251`) that holds
   the assertion's `SExpr` *body* before it is parsed. A `distinct` application
   that is the whole body of an `(assert …)` is in positive polarity **by
   construction**, including under `push`/`pop`. So scoping 1 is a test on that
   `SExpr`, not a polarity analysis — and the five rows above are all exactly
   this shape, because that is how Boogie emits the axiom.

2. **The fresh symbol has a purpose-built constructor.**
   `TermArena::declare_internal_fun` (`crates/axeyum-ir/src/arena.rs:1800`)
   declares an uninterpreted function *in a namespace disjoint from user
   declarations*, sharing one `FuncId` across repeated identical declarations so
   congruence is preserved. That is exactly the `f` the encoding needs, and it
   removes the "what if the user declared `f`" objection entirely. Note that
   name-sharing means two different `distinct` applications must be given
   **different** internal names, or they would be forced onto one injection.

3. **Model replay is unaffected, for a reason worth stating.** `check_model`
   evaluates the assertions the front door produced, which under this rewrite
   are the rewritten ones — so `f` is in the model and the conjunction evaluates.
   Nothing has to hide `f` from the replay; it only has to stay out of the user's
   `get-model` surface, which the internal namespace is what it is for.

**What is still genuinely unfinished:** the soundness-negative test. It must be a
**negated** large `distinct` over a **satisfiable** query, asserting the VERDICT
— because `sat` is precisely what the polarity bug produces, and a test that only
checks "the file parsed" cannot fail on the bug it exists to catch. Alongside it,
an `unsat` twin differing in one small term, so the pair cannot be passed by a
solver that answers `unknown` to both.

**This lane did not implement it.** The budget measurement is the lane's primary
deliverable and it took the compute window. The above is a handoff, and its
sizing — 4 winnable `UFNIA` rows, deterministic, 0.1 s each — is unchanged.

## The sizing, MEASURED rather than inherited (`distinct/references.tsv`)

The "4 winnable" above came from another lane's winnable set. Re-derived here by
running both references on all five files at the board envelope:

| file | `:status` | z3 | cvc5 |
|---|---|---|---|
| `lahiri…/serial_write_example_cegar_2_2_2` | unknown | **no verdict** at 24 s | **no verdict** at 24 s |
| `lahiri…/usbsamp_bug_example_2_3_8_1` | unsat | unsat in **508 ms** | unsat in **211 ms** |
| `lahiri…/usbsamp_example_2_3_4_0` | unsat | unsat in **309 ms** | unsat in **310 ms** |
| `spec_sharp/test14-CommandLineOptions…` | unsat | unsat in **111 ms** | unsat in **109 ms** |
| `spec_sharp/test14-Xml.ssc…` | unsat | unsat in **309 ms** | no verdict at 24 s |

**Four of the five are refuted by z3 in 111–508 ms**, three of them by cvc5 as
well, and all four declare `:status unsat`. These are not hard queries. We refuse
them at the front door in 107 ms and never reach a solver at all, on a
deterministic ingest cap whose only cause is that the encoding is quadratic.

That makes this handoff **4 rows that two independent solvers decide in under
600 ms**, not 4 rows of unknown difficulty — and it is the strongest sizing on
anything this lane looked at.

The fifth (`serial_write_example_cegar_2_2_2`, `:status unknown`) is out of reach
of both references at this budget and is **not** counted in the 4.
