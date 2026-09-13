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
