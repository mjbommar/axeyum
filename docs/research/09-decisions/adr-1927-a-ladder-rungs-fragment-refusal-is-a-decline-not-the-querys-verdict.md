# ADR-1927: A quantified-ladder rung's fragment refusal is a decline, not the query's verdict

Status: accepted
Index-summary: `solve`'s quantified ladder has twenty rungs, and three of them propagated a *speculative sub-solve's* `SolverError::Unsupported` with a bare `?`. A rung that rewrites the query — a validity check's `not body[x := c]`, the e-graph refuter, an MBQI ground round — and hands the rewrite to a backend that refuses ITS fragment was therefore ending the whole dispatch: `solve` returned `Err(Unsupported)` and every rung below never ran. Measured 2026-09-12: the `AUFDTLIRA` division (11,043 files) stopped at `attempts=2` after **1 ms** on `eager Ackermann elimination does not admit array-valued function results` — a sentence about a quantifier-ERASED SKELETON — and scored **0 of 200** on its first parity board while z3 and cvc5 each scored 176. Decision: **a rung's fragment refusal is recorded on the route trail and the ladder continues.** Three guards, at valid-universal elimination, the e-graph refuter and the MBQI pass; declining is sound by construction (a skipped route can only lose completeness) and every remaining route still surfaces its own `Unsupported` if nothing decides. Result on a 200-file stride sample at 10 s, per file against the same binary without the guards: **AUFDTLIRA 0 → 62 decided, UFDTLIRA 70 → 75, UFDT 23 → 26, UFDTNIRA unchanged, 0 decided→undecided, 0 `sat`↔`unsat` flips, and 0 movement in either direction on a `UF` control**; all 70 new verdicts are `unsat` with **0 disagreements** against the declared `:status`, z3 4.13.3 and cvc5 1.3.4 — 70 of 70 comparable on all three. The second result is the one to carry forward: **the division's published blocker census was an artifact of this bug.** Before, 147 of 158 undecided `AUFDTLIRA` files named "eager Ackermann … array-valued function results"; after, that message is **3 of 200** and the real top blocker is `datatype_native` refusing array/UF-sorted datatype FIELDS (70) followed by UF applied to a datatype argument (32) — which is exactly the capability ADR-1920 already named as BUILD NEXT. A census taken through a ladder that stops at its first refusal measures the ORDER OF THE LADDER, not the missing capability.
Index-status: accepted
Date: 2026-09-12

## Context

Four SMT-LIB 2024 divisions — `UFDT` (4,569), `UFDTLIRA` (7,749),
`AUFDTLIRA` (11,043), `UFDTNIRA` (4,424), **27,785 files** — had no parity row.
ADR-1920 made them parse; this lane was sent to measure them and then fix the
largest blocker the measurement named.

The measurement is in
[`dt-divisions-headtohead-20260912`](../../../bench-results/dt-divisions-headtohead-20260912/README.md).
The first board row for `AUFDTLIRA` is the one that forced this ADR:

| division | files | axeyum | z3 | cvc5 |
|---|---:|---:|---:|---:|
| UFDTLIRA | 200 | 66 | 181 | 158 |
| UFDT | 200 | 22 | 66 | 78 |
| UFDTNIRA | 200 | 5 | 173 | 183 |
| AUFDTLIRA | 200 | **0** | 176 | 176 |

Zero, against two references that each decide 88 % of the same files in
**under a tenth of a second** on most of them. A capability gap does not look
like that. A routing bug does.

`--trace` said so immediately:

```
; give-up kind=Error detail=unsupported by backend: eager Ackermann elimination
  does not admit array-valued function results; use canonical AUFBV combination
; route decided_by=none bound_by=fd:parse last=q:ground-subset
  bound_ms=1 total_ms=1 attempts=2
```

**`attempts=2`.** The ladder has twenty rungs and the file touched two of them,
in one millisecond. And the message is about *eager Ackermann on bit-vectors* —
a `QF_UFBV` reduction — for a quantified `AUFDTLIRA` benchmark that contains no
bit-vector at all. It is a sentence about a query the solver *built*, not about
the query it was given.

## What was actually happening

`solve`'s quantified ladder runs rungs in order, and several of them are
**speculative**: they rewrite the query and hand the rewrite to an inner
`check_auto`.

* `quant_valid_universal::eliminate_valid_universals` proves `∀x. body` valid by
  sub-solving `¬body[x := c]`.
* `qinst_egraph::prove_quantified_unsat_via_egraph` runs an instantiation loop.
* `prove_unsat_by_mbqi` runs ground rounds over a model candidate.
* `checked_quantified_fast_path`'s rungs solve a canonicalized form and a
  quantifier-erased skeleton.

Each called its sub-solve with a bare `?`. So when the *rewritten* query landed
on a backend that refuses its fragment, the `SolverError::Unsupported` travelled
all the way out of `solve`, and the front door reported it as the file's answer.

The rung **directly above these** already had the rule, in its own words:

```rust
// This is an optional accelerator. It must never turn a query the
// established portfolio can handle into an operational error.
Err(_) => Ok(false),
```

`ground_subset_refutes_quantified_query` converts *every* error to a decline and
says why. The rungs below it had the same contract and not the guard — which is
why this is one ADR and not one comment.

**This also makes the repository's own `unknown` rule concrete.** "`unknown` is
a first-class solver result, never an error" (`CLAUDE.md`, Hard Rules) is
usually read as being about what a *backend* returns. The failure here is one
level up: a backend's honest refusal of a sub-query became the *dispatcher's*
error, and an error is not a verdict.

## Decision

**A quantified-ladder rung that refuses the query's FRAGMENT records a decline
on the route trail and the ladder continues.** `Err(SolverError::Unsupported)`
from a rung's sub-solve is not that rung's verdict on the query, and therefore
cannot be the query's verdict.

Three guards, one per rung that measurably propagated:

1. `eliminate_valid_universals` → treat as "nothing eliminated" and go on.
2. `run_egraph_quantified_fallback`'s terminal arm → `Ok(None)` rather than
   re-raising. The e-graph refuter is **refutation-only**; its declining says
   nothing about whether a later rung can decide the query.
3. `prove_unsat_by_mbqi` → carry the message as a first-class
   `UnknownKind::Incomplete` so the full finite-model rung below still runs.

Every one keeps the refusing call's own sentence on the trail
(`unsupported_decline`), so the reason is not lost — it moves from being the
verdict to being telemetry, which is what it always was.

**Soundness is structural, not argued.** Declining a route can only lose
completeness: the ladder continues with the ORIGINAL assertions; the arena is
append-only during solving (`TermArena` has no remove/clear/truncate, and its
one mutator `set_quantifier_patterns` is called by the PARSER, checked rather
than assumed), so the speculative terms a refused probe interned are
unreachable from the original roots; and every rung the ladder reaches applies its own soundness
discipline (an MBQI `sat` is still re-checked against the original assertions by
`check_model`; an `unsat` still comes from an equisatisfiable reduction). The
risk this ADR has to exclude is the other direction — that letting more rungs
run manufactures a **wrong `unsat`** — and that is what the negative test and
the three-way cross-check below are for.

## What it measured

Everything is a **per-file A/B against the same binary without the guards**, run
back to back on the same pinned core pair of the same idle homogeneous box with
the arms alternating per file, 10 s and 8 GiB per run, over 200-file stride
samples.

| division | base | guarded | newly decided | decided → undecided | `sat`↔`unsat` flips |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 0 / 200 | **62 / 200** | 62 | **0** | **0** |
| UFDTLIRA | 70 / 200 | **75 / 200** | 5 | **0** | **0** |
| UFDT | 23 / 200 | **26 / 200** | 3 | **0** | **0** |
| UFDTNIRA | 10 / 200 | 10 / 200 | 0 | **0** | **0** |
| **UF (control)** | 83 / 189 | 83 / 189 | 0 | **0** | **0** |

`UF` is the control and it is not decoration: it is an established quantified
division already on the parity board, where letting more rungs run could only
cost time. It costs nothing — no verdict moved in either direction.

**Soundness — 70 new verdicts, all `unsat`, three independent checks, 0
disagreements**, and every one of the three was *comparable* on every file (no
check was silently vacuous):

| check | comparable | disagreements |
|---|---:|---:|
| the file's declared `:status` | 70 of 70 | **0** |
| z3 4.13.3, 24 s, same box | 70 of 70 | **0** |
| cvc5 1.3.4, 24 s, same box | 70 of 70 | **0** |

### Mutation control, and what it can and cannot show

Deleting **one** guard at a time, in the lane's own worktree, and running
`quant_ladder_rung_refusal_declines` (3 tests):

| guard deleted | tests that die |
|---|---|
| valid-universal | `a_refused_rung_does_not_answer_a_query_a_later_rung_decides`, `a_refused_rung_yields_a_first_class_unknown_not_an_error` |
| e-graph | `a_refused_rung_yields_a_first_class_unknown_not_an_error` |
| MBQI | `a_refused_rung_yields_a_first_class_unknown_not_an_error` |

Every guard is individually load-bearing: delete any one alone and a green suite
goes red. **The e-graph and MBQI guards are not separable by a verdict-level
test, and that is structural rather than a gap in the suite** — they are
consecutive rungs on one path, so deleting the earlier one stops the dispatch
before the later one is reachable. An earlier guard strictly dominates a later
one on any query that reaches both. Separating them would take a route-trail
assertion rather than a verdict assertion, and the property that matters — no
guard here is dead weight — is already decided by the table.

### A fourth guard was written, measured, and REMOVED

`checked_quantified_fast_path` has the same defect by construction, and a guard
for it was written while the cause was being bisected. It was then run over
**800 corpus files** across all four divisions with the route trail inspected for
its own decline entry (`q:checked-fast-path` recorded as `declined`, a label
nothing else writes): it **fired 0 times**. A guard with no reachable trigger is
the un-failable checker this repository keeps deleting, so it was deleted rather
than shipped as a safety margin. Re-deriving that is one command — scan for that
trail entry — and the guard is three lines if a corpus ever produces one.

## The finding worth more than the 70 files

The blocker census of these divisions — the table this lane was dispatched to
act on — **was measuring the ladder, not the solver.**

`AUFDTLIRA`, undecided files, before and after the guards:

| refusal | before | after |
|---|---:|---:|
| eager Ackermann, array-valued function results | **147** | **3** |
| `datatype_native`: array/UF-sorted datatype FIELDS (ADR-0022) | 0 | **70** |
| UF applied to a datatype argument (ADR-1920) | 7 | **32** |
| `is`/`select` over a non-variable datatype term | 0 | **13** |
| quantified / e-matching budget | 0 | **12** |
| parse: nested array element sort | 4 | **5** |

The number one blocker of the largest unmeasured division was reported as a
`QF_UFBV` Ackermann restriction. It is **1.5 %** of the division. The real
number one is a datatype-theory restriction that ADR-0022 names and ADR-1920
already flagged as the next thing to build, and it is 35 %.

**Generalisable rule, which is why this is an ADR and not a bug fix:** *a
blocker census taken through a ladder that stops at its first refusal measures
the ORDER OF THE LADDER.* Every file reports whichever rung happens to run
first and refuse, so the census is a fixed point of the dispatch order rather
than a map of missing capability — and it is stable, reproducible and
confidently wrong, which is exactly the shape this repository keeps finding.
Before quoting a refusal census, check that the ladder ran to the end: the
`attempts=` field of `--trace` is the check, and `attempts=2` on a
twenty-rung ladder is the tell.

## Consequences

### What this buys

- `AUFDTLIRA` goes from a division we decide **nothing** in to one we decide
  roughly a third of, with no new theory code.
- The four divisions' blocker census is now a capability map. The next build is
  named by it and by ADR-1920 independently, which is a rare agreement:
  **datatype-sorted UF arguments and array/UF-sorted datatype fields**, 102 of
  400 sampled files across the two `*DTLIRA` divisions.

### What it costs, and this is not free

A query the ladder used to refuse in **1 ms** now runs all twenty rungs and can
spend its whole budget. On an undecided `AUFDTLIRA` file at 24 s that is 24 s
instead of a millisecond. The A/B measured **0 verdicts lost** to that at 10 s,
so no file traded a verdict for the extra work — but a *sweep* over these
divisions is now far slower in wall clock, and any harness with a per-file
budget tighter than the ladder's needs should know that. The refusal was fast
because it was wrong.

### What this ADR does not claim

- It does not claim any new theory capability. Nothing in the datatype, array or
  UF backends changed; the same routes decide the same fragments. What changed
  is which routes get to run.
- It does not help `UFDTNIRA`: 10 of 200 before, 10 of 200 after. That division's
  blockers sit elsewhere and this ADR is not evidence about them.
- The `AUFDTLIRA` A/B was taken at 10 s; the 24 s board row for the guarded
  binary is a separate run against the same pinned list.

## Evidence

- `crates/axeyum-solver/tests/quant_ladder_rung_refusal_declines.rs` — three
  tests. The positive control's contradiction is `x > 0 ∧ x < 0`, so its `unsat`
  is not in doubt; the soundness-negative one is the same shape, satisfiable,
  and fails on any change that trades the refusal for a wrong refutation.
- `bench-results/dt-divisions-headtohead-20260912/` — the parity boards, the
  A/B, the three-way verification of every new verdict, and the before/after
  blocker census.
- `docs/research/03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md`
  — the protocol and the full tables.
