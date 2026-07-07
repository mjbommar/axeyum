# ADR-0059: Enable CNF inprocessing + vivification by default (paired), gated on a broader measure

Status: proposed
Date: 2026-07-07

## Context

Gap 1 / leverage step 1 of the
[2026-07-07 Z3/cvc5 gap analysis](../../plan/gap-analysis-z3-cvc5-2026-07-07.md)
asked whether the **built-but-default-off** SAT-inprocessing levers help, measured
on the committed public QF_BV `p4dfa` slice. The measurement landed
([findings](../05-algorithms/inprocessing-reduction-levers-p4dfa-findings.md),
task #56, `64f51dcf`): the levers — `cnf_inprocessing` (subsumption + self-subsumption
+ BVE, `axeyum-cnf/src/{simplify,bve}.rs`) and `cnf_vivify` (`vivify.rs`), both
`false` by default in `backend.rs` — are a **sound, net-positive** increment.

The question this ADR closes: **should they be enabled by default?**

## Decision

**Propose enabling `cnf_inprocessing` and `cnf_vivify` TOGETHER by default — as a
paired unit — with the actual `SolverConfig` default flip gated on a broader QF_BV
re-measure (beyond the arithmetic-free `p4dfa` slice).** They must be paired:
inprocessing *without* vivification regresses at a tight budget; vivification
recovers and exceeds. This ADR records the decision + the pairing constraint; the
code flip + the confirming measure are the follow-up (task queued).

`preprocess` (word-level reduction, ADR-0034/0037) already defaults **on** and is
unaffected.

## Evidence

Measured on `p4dfa` (113 files, Z3 4.13.3 oracle, `DISAGREE=0` and 0 replay
failures in **every** config):

| config | 3s budget | 20s budget |
|---|---:|---:|
| OFF (eager) | 3 | 4 |
| +preprocess | 4 | — |
| +preprocess +inprocess (no vivify) | **3** ↓ | — |
| ALL-ON (+vivify) | **5** | **7** |

- The **full stack is net-positive at BOTH budgets** (3→5 @3s, 4→7 @20s) — a
  strict superset of OFF's decided set, every decision `sat` and replay-checked.
- The **pairing constraint is the load-bearing subtlety**: `+inprocess` alone
  *costs* one decide at the tight 3s budget (subsumption/BVE overhead eats the
  wall clock); `+vivify` on top recovers (3→5). So the two ship together or not
  at all — never inprocessing alone.
- `DISAGREE=0`, `0` replay failures across all six configs — no lever introduced
  a wrong verdict.
- PAR-2 narrows marginally (38.64→37.84s @20s, −2.1%).

Caveat on scope: `p4dfa` is **arithmetic-free** DFA/protocol bit-logic (ADR-0037);
the +3 is real but the corpus is narrow. A broader QF_BV re-measure (arithmetic-
heavy + mixed slices) must confirm no regression before the default flip — hence
`proposed`, not `accepted`.

## Alternatives

- **Unconditional default-on immediately.** Rejected as premature: measured only
  on one arithmetic-free slice; the tight-budget inprocessing-alone regression
  shows the levers are budget-sensitive, so a broader measure is warranted.
- **Budget-gated default-on** (enable only when `config.timeout ≥ T`). Considered;
  deferred. The full *paired* stack is net-positive at both measured budgets
  (3s and 20s), so a budget gate is not required by the data — but if a broader
  measure surfaces a tight-budget regression for the paired stack, a
  `config.timeout`-keyed gate is the fallback design.
- **Keep opt-in.** Rejected: a sound, measured net-positive increment that stays
  off-by-default is a decide-rate row left on the table.

## Consequences

- **Easier:** ~+3 QF_BV decide-rate on the p4dfa class once flipped; the built
  inprocessing machinery earns its keep in the default path.
- **The bigger picture (why this is a small win):** the p4dfa residue is
  **decisively search-bound** — 99/106 unknowns are SAT-search timeouts on CNFs
  that are already *smaller than Z3's* (0.71× vars, 0.34× clauses median). The
  reduction lever has harvested the cheap encoding wins (`EncodingBudget` 10→6);
  further encoding effort caps at ~6 more instances. **The real perf lever is
  SAT-core modernization (P1.3)** — a default-capable CDCL with *in-solver*
  inprocessing/vivification interleaved with search — the funded arc where Z3
  wins these instances. This ADR banks the cheap pre-pass win; P1.3 is the
  chasm.
- **Also corrected:** the gap-doc headline "Z3 decides all 113 p4dfa in ≤1s" is
  stale for this slice — measured Z3 is 8–9/113 at 20s (both solvers find p4dfa
  hard). The findings doc records this.
- **Revisited when:** the broader QF_BV re-measure lands. Flip the default (paired)
  if net-positive with `DISAGREE=0`; otherwise apply the `config.timeout` budget
  gate. Determinism/soundness are unaffected either way (the levers are
  denotation-preserving CNF simplifications, verified `DISAGREE=0`).

## Backlinks

- Measurement: [inprocessing-reduction-levers-p4dfa-findings.md](../05-algorithms/inprocessing-reduction-levers-p4dfa-findings.md) (`64f51dcf`, task #56)
- Priority map: [gap-analysis-z3-cvc5-2026-07-07.md](../../plan/gap-analysis-z3-cvc5-2026-07-07.md) Gap 1
- The real perf arc: P1.3 SAT-core modernization; word-level reduction ADR-0034/0037
