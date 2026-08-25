# 262 — Choosing autogenesis targets from the curriculum DAG

Date: 2026-08-24

## Result

Target selection in this programme is currently by **proof-graph locality**: a
fact is a candidate when every `depends_on` is settled. Measured today, that
selection principle yields

```
scripts/fact-frontier.py --json
  ready total: 141   admissible: 0   selected: None
  outcome: refused-no-admissible-candidate
```

— **141 dependency-ready facts, zero dispatchable**, every one rejected
`no-registered-operation`. The registry covers 30 facts, all of them already
settled: **30-of-30 on proved work, 0-of-138 on anything open.**

Locality also has a recorded failure mode. Doc
[`228`](228-capsule-lane-retrospective.md): *"Nine of the ten most recent
operations are Fibonacci/gcd. Picking the adjacent theorem is how a lane ends up
with nine capsules and zero generality."*

`docs/curriculum/curriculum.toml` is a **non-local** selection principle that
already exists: 23 nodes, 37 prerequisite edges, four layers, derived backward
from three destinations, gated for acyclicity by `axeyum-scenarios::mathtour`
and for exercise coverage by `scripts/check-curriculum-coverage.py`. It says
what a destination *requires*, independent of what happens to sit next to what
in an imported corpus.

This document is the crosswalk between the two, and it is mostly a record of
how far apart they are.

## The measurement

Nursery families mapped onto curriculum nodes. The mapping is **arguable and
deliberately stated in the open** — it is a judgement, not a derivation, and
disagreeing with a row is the point of writing it down.

| Curriculum node | Layer | Status | Nursery rows |
|---|---:|---|---:|
| `modular-arithmetic` | 2 | covered | 40 |
| `counting` | 2 | covered | 35 |
| `divisibility-and-euclid` | 2 | covered | 30 |
| `number-theory` | 3 | covered | 21 |
| `naturals` | 1 | covered | 18 |

**Five of 23 nodes carry all the pressure**, and every one is in the ℕ/ℤ
arithmetic corner.

### Gap 1 — nursery rows with no curriculum home: 72 of 216 (33%)

| Orphan family | Rows |
|---|---:|
| `natural-logarithm` | 21 |
| `natural-bitwise` | 19 |
| `natural-fibonacci` | 16 |
| `integer-fibonacci` | 16 |

A third of the evaluation population is aimed at subjects the curriculum does
not name. Two readings, and they are not equivalent:

- the curriculum is **missing nodes** — logarithms, binary representation and
  linear recurrences are real topics, and this repository has landed
  `Nat.testBit`/`Nat.size`/`sum_testBit_eq`, `Nat.fib`/`fib_add`/`fib_cassini`
  and `Nat.catalan` in the last day; or
- those rows are **not worth pursuing**, and the nursery inherited Mathlib's
  shape rather than a chosen one.

**Neither reading is free.** Adding a node obliges an exercise family and a
negative control (`check-curriculum-coverage.py` reports
`covered=19|running=19|with_negative_control=19`). Declining the rows shrinks a
preregistered blind population, which is an amendment, not an edit —
`ADR-0542` and the held-out isolation gate exist for exactly that.

### Gap 2 — curriculum nodes with zero nursery pressure: 18 of 23

```
L0  propositional-logic  predicate-logic  proof-methods  induction
    sets  relations-and-functions  cardinality
L1  integers  rationals  reals  complex
L2  groups  rings  fields  polynomials  sequences-and-limits
L3  linear-algebra  calculus
```

**Both remaining destinations are here.** `linear-algebra` is marked `covered`
with `computable` decidability and has **zero** rows in the evaluation
population; `calculus` is `lean-horizon` and likewise zero. The curriculum names
them as the point of the whole tour and autogenesis has no path to either.

This is the sharper of the two gaps, because it is not a labelling question. A
producer cannot be evaluated against a population that contains nothing from the
subject it is meant to advance.

## How to use this to choose

The two selection principles answer different questions and should be composed,
not swapped:

| Question | Answered by |
|---|---|
| *Which subject should the next capability serve?* | the curriculum DAG — a node on a path to a destination |
| *Which specific row inside that subject?* | `fact-frontier.py` — dependency-ready, partition-legal |
| *Is the capability general?* | `gen-production-provenance-ledger.py` — `facts_via_multi_target` |

Concretely, the decision procedure this document proposes:

1. **Pick a curriculum node on an unfinished path to a destination.** Prefer one
   whose `decidability` is `computable` or `decidable`; `bounded` nodes cap what
   a self-checking exercise can establish, and `DEPTH.md` explains why.
2. **Read its nursery pressure from the table above.** Zero pressure means the
   next action is population work, not producer work — and that is a finding,
   not a blocker.
3. **Ask what the next three targets in that node share.** Doc 228, item 2:
   if the answer is "nothing — each needs its own route," that belongs in a
   decline record rather than in three more capsules.
4. **Register the operation against all of them.** `applicability.fact_ids`
   takes a list and nothing ever required length one.
5. **Check the generality counter moved.** If `facts_via_multi_target` is
   unchanged, the work did not produce; that is the one number doc 228
   installed and the one it says to watch.

## Boundary

This document **selects nothing and authorizes nothing.** It adds no operation
applicability, no fact status, no admission authority, and no partition change.
It does not measure expected proof yield, cost, or downstream mathematical
value, and it does not assert that any curriculum node is reachable.

The family→node mapping is a **stated judgement**, not a derivation. It is not
gated, and it should not be gated until someone is prepared to defend each row;
a crosswalk that cannot be argued with is the checker-that-cannot-fail defect in
a different costume.

The counts are reproducible from `docs/curriculum/curriculum.toml` and
`artifacts/autogenesis/nursery-v1.json` at this commit. If either moves, the
tables here go stale and say nothing about it — which is why they carry no gate
and must be re-measured before being quoted.

## What this does not resolve

The frontier is empty for a reason this document does not touch: **no registered
operation covers any open fact.** Choosing a better subject does not create a
producer. The loop demonstrably closes end to end — two facts proved by a
model-chosen plan and checked by an independent second kernel — and wrote
nothing, because a transaction requires a registered operation and none covers
the `Nat.ModEq` family. That registration is a human decision and remains the
binding constraint.

What the curriculum DAG changes is **which** registration to make next, and
whether it is chosen from the neighbourhood or from a path to somewhere.
