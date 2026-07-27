# ADR-0372: Preregister one bounded negated-conjunction branch split

Status: rejected

Date: 2026-07-27

## Context

After ADR-0370, the frozen 108-family QF_BVFP sample has 20 two-second process
non-decisions. Route explanation shows that all 20 reach the scalar BV backend;
the representative `prefix_sum_klee_bug_double/query.17.smt2` is SAT-search
dominant at about 130 ms lowering versus 2.8 s BatSat search on 135,109 variables
and 501,660 clauses. Existing paired inprocessing/vivification takes 7.81 s, the
native core 6.42 s, and Z3 times out at 10.65 s on the same row.

The source query is not one opaque obligation. Ten global assertions are
conjoined with exactly one final `not(and(A, B, C))`, so the query is equivalent
to the disjunction of three branches sharing all ten globals:

```text
globals and not A
or globals and not B
or globals and not C
```

ADR-0065 rejects broad top-level disjunction splitting because it multiplied
hard sub-solves. ADR-0367 later accepted a different exact shape: one large
shared-antecedent disjunction. This candidate likewise needs a structural gate,
one shared deadline, disabled recursion, and original-query SAT replay.

## Proposed decision

**Before word-level preprocessing and the monolithic scalar-BV fallback, split
only one large conjunction of global assertions containing exactly one
three-leaf top-level negated conjunction.** Admission requires:

1. a configured timeout, scalar Bool/BV/FP only, and at least 3,000 reachable DAG
   nodes;
2. at least two global assertions plus exactly one assertion whose root is
   `not(and(...))` with exactly three leaves after flattening a binary
   `BoolAnd` tree;
3. three unique, nonconstant conjunction leaves; and
4. no second three-leaf top-level negated conjunction candidate.

The placement and exact arity are evidence-driven corrections made before the
candidate was judged. The parsed FP IR has 3,856 source DAG nodes, but FP
predicates are already expanded into Boolean terms: all eleven top-level
assertions appear as `not(and(...))`. Ten flatten to two or four leaves; only the
intended source counterexample assertion flattens to three. Word-level
preprocessing then erases that assertion boundary. Consequently the recognizer
runs on the original parsed assertion sequence and admits exactly one
three-leaf candidate; it does not try to infer source syntax after reduction.

The auto dispatcher constructs `not leaf_i` terms in the existing arena and
solves `globals + not leaf_i` serially under one fair shared deadline. Branches
use the ordinary preprocessing plus SAT-BV pipeline; removing the sole
three-leaf assertion structurally disables split recursion.

Verdict transfer is exact: every branch UNSAT proves the original query UNSAT;
one SAT branch can prove SAT only after completing missing symbol values and
replaying every original assertion. Any unknown, missing default, failed replay,
or operational error remains unknown/error. No proof claim or trusted rule is
added.

## Acceptance gate

- Focused recognizer tests cover exact admission, DAG floor, two-/four-leaf
  rejection, multiple-candidate rejection, constant/duplicate rejection, and
  near misses.
- Focused transfer tests cover all-UNSAT and replayed SAT; recursion stays off.
- The exact `prefix_sum` row changes from its frozen-process two-second unknown
  to declared/Z3-matching UNSAT and materially outperforms an immutable current
  baseline when that baseline decides, or the candidate is rejected.
- The frozen 108-family sample has zero wrong verdict and no retained decision
  loss; the eight binary79 rows and 34 ESBMC rows retain every decision.
- Warning-denied solver Clippy, fmt, and links pass. Any wrong verdict, replay
  failure, material PAR-2 regression, or broad shape admission rejects the
  candidate.

## Measured outcome

Rejected. A release prototype implemented the exact recognizer, shared deadline,
preprocessed branch solves, model completion, original-query SAT replay, route
telemetry, and focused admission/transfer tests. The code and tests were removed
after the selected-row gate failed.

The parser-shape audit corrected two assumptions before measurement. The selected
row has 3,856 reachable source-IR DAG nodes (and a saturated unfolded tree), so
the 3,000-node floor was valid. However, FP predicates are already Boolean-
expanded by this boundary: the eleven top-level negated-conjunction arities are
`2,4,2,4,2,4,2,4,2,4,3`. The prototype therefore admitted only the unique
three-leaf assertion before preprocessing; the initial post-preprocessing
placement correctly declined and was not counted as a candidate result.

On a quiet host, the immutable baseline binary decided the exact selected row
UNSAT in five of five two-second runs, at 1.70--1.80 s. The corrected split
prototype reached its route but returned timeout/unknown at two seconds. Giving
each branch an independent five-second ceiling showed why: all three were UNSAT,
but took approximately 0.205 s, 0.096 s, and 2.893 s. Their 3.194 s serial sum is
materially worse than the monolithic solve, and the hard third branch alone
exceeds the product deadline. This fails the required headroom and PAR-2 gates;
there is no justification for population or retained-suite runs after the
selection gate fails.

## Alternatives

### Split every top-level disjunction

Rejected by ADR-0065. This candidate recognizes one bounded counterexample
shape only and does not reopen generic OR splitting.

### Tune BatSat options

Rejected by prior A/B measurement: exposed option sweeps were net-neutral, and
the pinned RustSAT wrapper does not expose mutable options. Repeating that sweep
on one row would overfit stale negative work.

### Enable preprocessing, inprocessing, or the native core

Rejected by the exact row: the product preprocessing route is already active;
paired inprocessing/vivification and the native core are both materially slower.

## Consequences

No production behavior changes. The negative result closes serial branch
splitting for this prefix-sum witness shape: two branches are easy, but the
remaining ordering obligation is harder than the monolithic query. A future
candidate must reduce that hard branch itself (for example through an exact
word-/FP-level implication) or improve the underlying SAT search; wider leaf
syntax/count or multi-candidate splitting would repeat the rejected cost model
and requires a fresh preregistration.
