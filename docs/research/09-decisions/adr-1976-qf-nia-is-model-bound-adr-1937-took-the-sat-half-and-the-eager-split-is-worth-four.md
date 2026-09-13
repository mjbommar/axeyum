# ADR-1976: QF_NIA is model-bound, ADR-1937 took the sat half, and the eager split is worth four

Status: accepted
Index-summary: The QF_NIA sat half is 40 files, not 64 — ADR-1937's 32 gains were ALL `sat`. The replay-failure class is now empty; every remaining loss is "no model produced". Sizes the one unrefuted hypothesis (eager small-domain split) at 3–5 of 29 against a noise floor of ±1, and declines to build it. Records that the natural sat-side control is vacuous.
Index-status: accepted
Date: 2026-09-13

## Status

Accepted, 2026-09-13. Lane `qf-nia-sat`. No solver code changed.

## Context

QF_NIA is Tier-1 #5. Three lanes had worked it and all three chased refutation
paths; two returned zero ([ADR-1921](adr-1921-the-int-blast-width-escalation-is-measured-and-not-shipped.md),
the CNF clause budget). The one that worked,
[ADR-1937](adr-1937-the-blaster-pins-products-and-nothing-else-and-the-wraparound-is-additive.md),
was a model-construction fix. `bench-results/winnable-polarity-20260913/` then
showed QF_NIA at 65 % satisfiable — the highest of any Tier-1 division and the
opposite of its four neighbours — and the hypothesis was framed: **QF_NIA is
held by model production, not refutation power.**

This lane tested it. The hypothesis is right; its sizing was not.

## Decision

1. **Record that the sat half is 40 files, not 64.** The 65 %-of-110 figure is
   read from a board snapshot that predates ADR-1937, and ADR-1937 harvested
   precisely the sat files. Remaining winnable is **78 = 40 `sat` + 38 `unsat`**.
2. **Record that the "model produced, replay failed" class is empty.** It was 25
   files; ADR-1937 closed it completely. Every one of the 78 remaining losses is
   "no model produced".
3. **Do not build the eager small-domain split route.** Sized at **3–5 of 29**
   against a measurement noise floor of ±1 at fixed code.
4. **Reserve the sat-side vacuity finding** (below) as the reusable part.

## Evidence

Full measurement, population, and raw rows:
[`bench-results/qf-nia-sat-20260913/`](../../../bench-results/qf-nia-sat-20260913/README.md).

### The polarity thesis is confirmed on a natural experiment

Cross-referencing ADR-1937's committed A/B against per-file ground truth:

| ADR-1937 armed verdict | ground truth | files |
|---|---|---:|
| `sat` | `sat` | **32** |
| `unknown` | `sat` | 40 |
| `unknown` | `unsat` | 38 |

Every one of its 32 gains on the winnable population was `sat`; zero were
`unsat`. A model-construction fix on a 65 %-satisfiable division harvested
only satisfiable files. That is the strongest available confirmation of the
polarity framing — and simultaneously the reason the remaining target is
38 % smaller than the brief that cited it.

### The asymmetry is in the clock

| | spends ≥98 % of the 24 s budget | median budget used |
|---|---:|---:|
| `sat` half (40) | 8 of 40 (20 %) | **45 %** |
| `unsat` half (37) | 33 of 37 (89 %) | **100 %** |

The unsat half is clock-bound. The sat half is not: 29 of 40 refuse at the
pre-lowering CNF clause estimate at a median of 11.8 s, leaving a median
**13,172 ms — 55 % of the budget — used by nothing** (ADR-1950 split; ADR-1971
decline times; `bound_by` per ADR-1941 is `nia-linearize` on all 29).

Raising that budget is already a closed question: `docs/plan/notes/118-nia-diagnosis.md`
measured the estimator's own 9.4x slack lifted at **0 of 49 decided, 0 memory
aborts** — *"the refusal was in front of a search that does not finish either."*
Confirmed applicable here: 0 of 30 estimates exceed the ceiling by more than
9.4x (range 1.16x–4.49x, median 2.00x).

### The sizing, and why the two numbers differ

The one hypothesis that note left standing was an **eager** small-domain split.
`nia_linearize::small_domain_lemmas` already implements the split but only
inside the relaxation, which its own docs confine to `unsat` transfer — it
structurally cannot produce a `sat`. The eager form was therefore built as a
**sound one-way surrogate outside the solver** and the shipped CLI run on the
result, rather than as a route.

| condition | decided |
|---|---:|
| surrogate, whole 24 s budget for the transformed file | 6 of 29 |
| **in-solver, rung at its natural position** | **4 of 29** |

The in-solver figure is the one that governs, and it is measured on both halves
rather than modelled: the split changes only the query handed to
`int-blast-ladder`, so the condition is `ladder_elapsed(transformed) ≤ 24 s −
total_ms(original)`. Pre-ladder cost is ~10.8 s; ladder times on transformed
queries run 3.9–19.4 s.

**Noise floor, three repeats at one commit on one binary: 4 / 3 / 5.** Spread 2
on a mean of 4 — the noise is half the effect, which is the
[ADR-1970](adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md)
situation and the reason the bracket is quoted as a range.

Against the running blocker→reachable tally (143→6, 51→2, 173→10, 84→49,
27,150→1,135, 19,620→0, 177→0, 934→0, 46→2), this is **29→3–5**: four files of a
78-file gap, for an equisatisfiable rewrite inside the blaster with real
soundness obligations. The upper end additionally requires moving the split
ahead of `int-real-relax` and `nia-linearize`, taxing every integer-bearing
query in every division.

## The generalizable finding — a sat-side reference control is vacuous

This is the part worth carrying to the next lane, and it was nearly missed.

The surrogate's natural control re-checked each transformed file against z3 and
cvc5 and compared to the original's declared `:status`: **0 disagreements on
29 of 29, 0 files with no reference opinion.** That number is worthless alone.
Deliberately mutating the case-split scaling so `a = k` implies `r = (k+1)·b` —
a plainly wrong linearization — produced **0 disagreements as well**, on 5 of 5.

The reason is structural, not a checker bug: **a satisfiable, underconstrained
query stays satisfiable under a wrong transformation.** It just has a different
model. So on the sat half — exactly the polarity this whole lane targets — a
reference verdict cannot distinguish a correct transform from a broken one.

Two consequences, both already in the repository's rules and both easy to skip:

- **For a `sat`, the model is the evidence and a reference verdict is not.** The
  brief said so; the measurement shows what it costs to ignore it.
- **A transformation aimed at the sat half must be controlled on the unsat
  half**, where a wrong rewrite has somewhere to go. Measured:

  | arm | unsat winnable files z3 turned `sat` | requirement |
  |---|---:|---|
  | correct transform | **0** | must be 0 |
  | mutant (off-by-one scaling) | **6 of 10** | must be ≥ 1 |

  `scripts/qf-nia-sat-transform-control.py` fails on **either** violation — a
  flip on the correct arm, or *no* flip on the mutant arm — so its zero cannot
  be read without its six.

## Consequences

- QF_NIA's remaining gap is **38 `unsat` vs 40 `sat`**, near balanced. The
  polarity argument that should now be quoted is the post-ADR-1937 one; the
  65 %-of-110 figure describes a population that no longer exists.
- The eager small-domain split is **sized and closed**. The 2026-09-12 note's
  last standing hypothesis has been tested; a future lane should not re-derive it.
- Thirteen seconds per sat file remain unused after the ladder's instantaneous
  refusal. Any route producing a candidate model without blasting the whole query
  runs in a free budget. A direct small-witness enumerator over the declared
  `[-2,2]` boxes is unsized and is the obvious next candidate.
- `estimate_blast_clauses` charges `Op::BvMul` a flat `8w²` with no numeral-operand
  case. Worth 6 % on the original files (measured and correctly dropped
  previously) but **19 % here** (82,057,350 → 66,466,002 on one file) once a
  rewrite introduces constant multiples. It matters for the next rewrite, not
  this one.

## Alternatives considered

- **Build the route anyway.** Rejected: 4 files against a ±1 noise floor, for a
  soundness-bearing rewrite in the blaster.
- **Move the split ahead of the budget-consuming routes** to capture the upper
  bound of 6. Rejected: taxes every integer query in every division to convert
  four files in one, and was not measured across divisions.
- **Raise the CNF clause ceiling.** Already measured at 0 of 49 by a previous
  lane, and confirmed applicable to this population (all 30 estimates within
  the lifted factor).
- **Report the surrogate's 6, or its 7.** Rejected: 7 includes a file that
  decided at 24.3 s against a 24 s budget, and 6 charges the split for routes it
  does not remove.
