# CORE-SELECT preregistration

Lane `core-select`, 2026-09-15. Branch base: `git merge-base main HEAD` is
`b78b887b3064b1075783ba6f4528519d07b1bbb6`, which **is** local `main`'s HEAD.

## The question

[ADR-2050] §3 measured, over its 13 quantifier-free rows, that **every one's
minimal unsat subset is ONE conjunct** (one is 3) — median 1 against a
pre-registered ≤ 5 — and its bucket (B) named two rows where we refute a
**3-of-268** and a **1-of-633** subset in 24 s and fail on the whole.

Two rows is a footnote. This lane asks whether the shape is the population:

> Across the **undecided** rows of the seven Tier 1 divisions, how large is the
> minimal refutable subset?

**Which sense of "selection".** [ADR-2005] closed a different one — *which
representative TERM to substitute* — and measured it at zero. This lane
measures **which ASSERTIONS to look at**, [ADR-2020]'s open axis. The two are
not the same question and no number from one transfers to the other.

## The population

The seven pinned 200-file lists `bench-results/parity-lists/<D>.txt` for
`UFNIA QF_NIA UFLIA AUFDTLIRA UFDTLIRA AUFLIRA UF` — 1,400 files. The pinned
lists are the authority for *which files*; the tier-1 board TSVs supply only an
inherited verdict, which is printed beside the re-derived one and never counted.

Derived by `derive-population.sh`, which also checks corpus presence and
non-emptiness (a census over files still being written reports a false absence,
[ADR-2080]) and prints any membership drift between board and pinned list.

## The unit of selection

A **conjunct**: a top-level `assert` body, with every top-level `(assert (and
a b c))` split into separate asserts. That split is an **equivalence**, not a
weakening, and is re-checked before anything else runs. It is the right unit
because [ADR-2050]'s haystacks (268, 633, 682) are *inside one `and`*, not
spread over 268 `assert` forms.

Dropping conjuncts **weakens** the formula, so `subset unsat ⟹ whole unsat`.
That direction is the one this lane needs and it is the sound one; the converse
is never claimed.

## R — the rules

**R1 — the inherited list is a claim, not the population.** Every row's verdict
is re-derived on this branch, at the board's envelope (24 s wall, shipped
defaults, one pinned physical core), before it is counted. [ADR-2035] found
**8 of 22** censused "declining" rows were decided anyway; [ADR-2065] moved
AUFLIRA by 14 after the board TSV was written. The re-derivation is reported
with its denominator whether it confirms or not.

**R2 — three reference buckets, never merged.** For each re-derived-undecided
row the reference is asked for a verdict, and the row lands in exactly one of:

| bucket | meaning | in scope for selection? |
|---|---|---|
| `REF-UNSAT` | the reference refutes the whole query | **yes** — a core exists |
| `REF-SAT` | the reference satisfies it | no — there is no refutable subset |
| `REF-NONE` | the reference is `unknown` / times out | **unknown**, and reported as its own bucket |

`REF-NONE` is never folded into either side. Every proportion below names which
of these is its denominator, and the comparable denominator is printed beside
any zero.

**R3 — three size measures, never conflated.** Each reported row carries:

| column | what it is | what it is NOT |
|---|---|---|
| `conjuncts` | the haystack: top-level asserts after `and`-splitting | — |
| `z3_core` | what `(get-unsat-core)` returned | **not** minimal — *a* core |
| `minimal` | 1-minimal under greedy single deletion | **not** minimum cardinality |

Any headline size states which of the three it is. Minimisation is capped
(§ cost, below) and a capped row reports `z3_core` with `minimal=CAPPED`, never
a guess.

**R4 — every core is re-checked by a second, independent authority.** A core
this lane reports is `unsat` under z3 **and** under cvc5, from its written file,
by a fresh process. A disagreement is reported as `AUTHORITY-SPLIT` and excluded
from every size distribution, with its count printed.

**R5 — the generalisation test, fixed before the data.** [ADR-2050]'s
median-of-1 **generalises** iff BOTH:

- (a) the median `minimal` over `REF-UNSAT` rows is **≤ 5** — ADR-2050's own
  pre-registered bound, reused so the comparison is not rewritten after seeing
  the data; **and**
- (b) `REF-UNSAT` is **≥ 20 %** of the re-derived-undecided rows.

Both halves are required. A median of 1 over three rows is a footnote, which is
what (b) exists to catch; a large `REF-UNSAT` bucket whose cores are hundreds of
conjuncts is a capability finding, which is what (a) catches.

**R6 — `WOULD-DECIDE` is a CEILING, not a gain.** Handing our solver the
reference's core and seeing `unsat` measures what selection could buy *if
selection were free and perfect*. It is reported as an upper bound and never as
a conversion, a delta, or a parity number. "We would decide it if we already
knew the answer" is not a result.

**R7 — a strategy claim requires a REFERENCE-FREE selection rule.** Sizing a
strategy means: a rule computable from the query text alone, run offline, whose
output subset is then decided. The reference may decide the subset; it may not
choose it. Each sized strategy is reported with the subset size it needs and the
fraction of the ceiling it reaches.

**R8 — the negative closes the lane.** If R5 fails, this axis is small. That is
a complete outcome and the lane says so plainly rather than manufacturing a
lever ([ADR-2050] R10, [ADR-1976]'s declined eager split).

**R9 — the build gate.** No solver change is made unless R5 passes **and** some
reference-free strategy from R7 reaches the R6 ceiling on **≥ 50 %** of the
`REF-UNSAT ∩ WOULD-DECIDE` rows at a subset our solver actually decides within
the same 24 s. Below that, nothing is built and the lane reports the sizing.
Chosen before any strategy exists: below half, the strategy is not the mechanism
doing the work.

**R10 — Wilson 95 % on every proportion**, quoted rather than a point estimate.
`REF-UNSAT ∩ WOULD-DECIDE` will be small and the interval is the honest form.

**R11 — if a lever is built and A/B'd**: interleaved per file, ONE binary and
two env values, arms back to back on the same pinned core with the order
alternating, polarity in the runner header, 3 passes per arm on every moved row,
a published noise floor on one whole division, a control shown NON-VACUOUS by
measuring that the lever's site EXISTS in the control population, and an
**EXIT-STATUS channel** — [ADR-2045]'s arm was `losses=0` by verdict while
creating five new aborts. An A/B over corpus rows is **not** a superset of the
fixture suites ([ADR-2065] measured 14/0/0 and still broke a fixture
obligation): the 19 dispatch/reason suites are run.

**R12 — every list and every count is derived by script from committed
artifacts.** A typed list measures the maintainer's memory.

## Cost control, fixed in advance

- Reference verdict on the whole query: `z3 -T:60`, one pinned core, idle host.
  60 s rather than 24 s deliberately — the question is what a core *is*, not
  what a reference scores in our envelope.
- Unsat core: `(set-option :produce-unsat-cores true)` over named conjuncts,
  same budget.
- Minimisation: greedy single deletion, `z3 -T:15` per probe, and **only where
  `z3_core ≤ 64`**. Above that the row is `MIN-CAPPED`. The cap is stated here
  because a cap chosen after seeing the sizes is a filter on the answer.
- Our solver on a core: the same 24 s, same shipped defaults, same pinned core
  class as the re-derivation, so the two are comparable.

## Hosts and cores

At most **6 pinned physical cores**, named here and held fixed:

- **s7** (idle, load 0.08 at 04:58): cores `0,1,2,3` — all reference
  measurement, because a lane read z3 at 155 against a true 166 by running six
  concurrent shards.
- **s5** core `1`, **s6** core `3` — the free pairs named in the brief.

Every analysis script runs under `MEM_LIMIT_GB=16 scripts/mem-run.sh`; a lane's
`let`-expander reached 63.4 GB under a `timeout`, which bounds wall clock and
says nothing about memory.
