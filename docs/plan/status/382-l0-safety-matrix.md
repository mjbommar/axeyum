# 382 — L0/S0: the safety matrix census

<!-- plan-section: lane-status -->

Lane: `l0-safety-matrix`
Phase: ADR-0717 L0, roadmap phase **S0** — complete.
Decision: [ADR-0746](../../research/09-decisions/adr-0746-the-safety-matrix-is-generated-and-gated.md)

## Status

S0's exit criterion is met and gated. `scripts/gen-safety-matrix.py` generates
`artifacts/safety-matrix/safety-matrix.tsv` (one row per proved fact, exactly
once) and `safety-matrix-summary.md`; `--check` runs in both `scripts/check.sh`
and the justfile, and `check-aggregate-scope.sh` still reports its recorded 64
divergences, so the registration is two-sided.

Six mutations, three distinct guards, each firing through the right one —
deleting a controlled fact, dropping its checker, unsettling it, deleting an
**uncontrolled** fact, downgrading an own-subject checker to the shared prelude
sweep, and breaking a classifier so it matches nothing. Full table in ADR-0746.

**No fact was edited.** This lane is measurement only.

## The numbers a later phase should start from

2,270 facts, 2,117 `proved`. Median protections per fact: 3.

| protection | facts / 2117 |
|---|---:|
| `env_footprint` (prelude-wide sweep) | 1859 |
| `kernel_theorem` (explicit binding) | 1466 |
| `coverage_bearing_checker` (own subject) | 1442 |
| `exact_statement` (drift pin) | 142 |
| `semantic_falsification` | 91 |
| `per_theorem_footprint` | 59 |
| `circularity` | 38 |
| `mutation_control` | 14 |
| `independent_replay` | 8 |

53 facts hold none of the nine. 523 hold one, and for 400 of those the one is
the prelude sweep.

Checker fan-out: 2,284 distinct commands, **largest 463**
(`--require-axiom-free creal`), then 318 and 280. 2,221 commands serve exactly
one fact; only 48 proved facts have no checker of their own and 17 cite none.

## Three findings that should change how a later phase is scoped

1. **The evidence `kind` enum no longer discriminates.** 1,901 rows declare
   `exhaustive-enumeration` or `instance-pin` while their `supports` records an
   axiom footprint. Reading `kind` at face value turns a true semantic-
   falsification count of 91 into 1,992. S3 must not size itself off `kind`.

2. **The statement-drift gate covers 6.8% of settled facts and exits 0.**
   `check-settled-fact-statements.py` reports `settled=2119|pinned=144`; a fact
   absent from the manifest is treated as newly settled, never as a gap. S1's
   first move is a coverage assertion on that manifest, not new machinery.

3. **`generated-unreviewed` is the best-protected population, not the worst.**
   All 1,038 carry a discriminating own-subject checker against 392 of 1,067
   hand-authored rows. What none of them has is any check on
   `formal.statement` — the field their own prose calls authoritative. The
   unreviewed part is the prose; the unprotected part is the formal statement.

## Handoff — what I did NOT do, and what is a hypothesis

Per the standing rule that a handoff's "blocked on X" is a claim about one
route: everything below is what my route did not reach, not a claim that it is
hard.

- **`just check-theorem` was out of scope by instruction** and remains so until
  the receipt schema exists. When it is built, its table must distinguish
  "cites a discriminating command" from "cites a command naming THIS fact's
  subject" — the ledger's own regex fallback would claim 82.4% coverage where
  the explicit bindings support 68.1%, guessing for 302 rows.
- **I did not run `scripts/check-fact-evidence-replay.sh`,** so I have not
  measured whether the cited commands actually pass today. The census reads
  what facts CLAIM; it does not execute their checkers. That is a real gap in
  S0 and the honest place for S6 to start.
- **`per_theorem_footprint` at 59 may be an undercount** for routes I classified
  by command shape rather than by running anything. I did not verify that a
  prelude-wide `--require-axiom-free` fails to bound an individual theorem; I
  only recorded that it is not a per-theorem check.
- `scripts/check-fact-depends-derived.py` was run and exits 0, reporting
  `kernel_facts=2037|named=1868|graph=2021|missing_edges=0` with **169**
  kernel-route facts whose checker command names no theorem, explicitly "not
  enforced". That corroborates the subject-binding gap from a second tool.

## Paths owned by this lane

`scripts/gen-safety-matrix.py`, `artifacts/safety-matrix/`,
`docs/research/09-decisions/adr-0746-*.md`, this file. Registration lines only
in `scripts/check.sh` and `justfile`.
