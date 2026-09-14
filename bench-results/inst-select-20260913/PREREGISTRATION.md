# Lane `INST-SELECT` — pre-registration

**Written before any at-scale measurement.** Committed in its own commit, ahead
of the census and ahead of any A/B, so that the sizing below can be compared
against what was realised rather than reconstructed after the fact.

Branch base: `2611e14b0`. `git merge-base main HEAD` is `2611e14b0`, which **is**
`main`'s HEAD at the time of writing.

## What was already measured before this file was written

Disclosed rather than hidden, because "pre-registered" must mean something:

1. `cvc5 --dump-instantiations` was re-run on the single file the brief names
   (`UFNIA/2019-Preiner/combined/f2_rw160.smt2`) to confirm the instrument
   reproduces. It does.
2. On that **one** file, three cvc5 arms were run (`default`,
   `--no-enum-inst --no-cegqi`, `--no-e-matching`) and the numerals occurring in
   the source were counted.

Both are exploratory, on one file, and neither is counted as a result. They are
what motivated the design below. Nothing in this lane's population has been
measured.

## The question

ADR-1995 closed the budget question: the target family is **0 of 87** at a
genuine one-way clock ceiling. Its closing claim is *"the vein is instance
selection, not clock."* This lane tests **whether that is true**, and
specifically whether the instances a refutation needs are reachable by
e-matching at all.

The brief's stated hypothesis, which this lane treats as a hypothesis and not a
finding:

> the winning instantiations use small integer numerals and Skolem constants, and
> if a refutation needs `pow2 2` where the numeral `2` occurs nowhere in the
> query, then pure e-matching structurally cannot generate it at any budget.

## Population

`bench-results/ufnia-uflia-census-20260913/winnable/{UFNIA,UFLIA}.txt` — 61 + 68
= **129 rows**: files a reference decides and we return `unknown` on.

**That list is a snapshot and is re-derived, not inherited.** It was produced at
`c281a4b22`; this lane's base is `2611e14b0`, which is 28 commits later and
includes the `qbudget` and `dt-exactness` merges. Step M3 below re-runs our own
binary over all 129 and the census reports only rows we still fail on **at this
lane's base**. Rows that main now decides are reported as such and dropped from
the denominator, with the count published.

## Measurements, in order

### M1 — reference ablation (the capability question, on an independent solver)

For each of the 129 files, `cvc5` at a 24 s `--tlimit`, 8 GiB `ulimit -v`,
pinned core, in four arms:

| arm | flags | what a refutation in this arm means |
|---|---|---|
| `default` | *(none)* | the reference verdict, reproduced |
| `ematch-only` | `--no-enum-inst --no-cegqi` | the instances are reachable **by e-matching** |
| `no-ematch` | `--no-e-matching` | e-matching is **not necessary** |
| `neither` | `--no-e-matching --no-enum-inst --no-cegqi` | neither route is necessary |

This is the sharpest available test of the brief's question and it does not
depend on our own instrumentation at all. It is a statement about *cvc5's*
e-matching, not ours — stated that way in the report, and it bounds the question
from one side only: **a refutation in `ematch-only` proves the instances are
e-matchable; a failure there does not prove they are not**, because cvc5's
e-matching is one implementation with its own trigger inference.

`ematch-only` is the load-bearing arm. `no-ematch` and `neither` are reported to
keep the arms from being read as a partition when they are not: a file may be
refutable every way, which is itself informative and is the outcome the single
exploratory file showed.

### M2 — the instantiation census (buckets)

For every file cvc5 refutes, collect `--dump-instantiations` and classify each
instantiating ground term:

- **Q** — occurs as a subterm of the original query (after `let`-expansion).
- **G** — occurs in **our** accumulated ground set at give-up, but not in Q.
- **N** — neither.
- **S** — a cvc5-invented Skolem constant (`@quantifiers_skolemize_*`).
  **Reported as its own class, not forced into Q/G/N**, because it has no
  counterpart in the query by construction and matching it to one of our Skolems
  modulo renaming would be a judgement, not a measurement.

Bucket **G** requires our ground set. `AXEYUM_QGROUNDDUMP=<path>` already exists
(`qinst_egraph.rs:3415`, added by lane Q2 in `f87d0f649`) and writes the
accumulated ground set at every give-up point. **No new instrumentation is
planned.** If it proves not to cover the rungs this population stops on, the
census reports a **two-way Q / not-Q split and says so**, rather than inventing
a three-way one.

**Stated caveat, up front:** `--dump-instantiations` prints the instantiations
cvc5 **produced** on the run that ended `unsat`, not a minimised set that the
refutation **needs**. So the census measures a **superset**. A term in bucket N
is therefore *not* proof that a refutation requires an unreachable term; the
honest reading of a large N is "cvc5's successful run used terms we never
build", and of a small N is the stronger "everything cvc5 used, we had". The
asymmetry is in the report, not just here.

### M3 — our baseline on this lane's base

All 129 through `smtcomp_cli-base` at 24 s / 8 GiB / pinned core, `--trace` with
`AXEYUM_QTRACE=1`, recording verdict, `attempts=`, the `route-open` segment, and
`bound_by` — so rows are classified by **ADR-1941**'s rule (the open segment is
the discriminator) and not by `attempts=` alone.

## Sizing — pre-registered, to be compared against realised

**I am declining to pre-register a conversion rate**, and the reason is the
failure mode the brief names: *a conversion rate measured on a MIXED blocker
population does not transfer to a subset of it.* ADR-1995's +2/87 and
ADR-1980's +79 were drawn from different blocker families and neither is a prior
for this one. Instead I pre-register **decision rules**, which are falsifiable
without a rate:

| M1 `ematch-only` refutations, of the files cvc5 refutes | reading | what this lane does |
|---|---|---|
| **≥ 70 %** | the instances are mostly e-matchable; our loop's failure is **selection or trigger inference**, not reach | proceed to Deliverable 2; the prototype targets selection |
| **30–70 %** | mixed population; no single mechanism | **report the split and stop.** Sizing a fix against a mixed population is the pre-registered failure mode above |
| **≤ 30 %** | the instances are largely out of e-matching's reach | **report that plainly and size what would reach them.** No prototype |

**Pre-registered expectation, recorded so it can be wrong:** on the strength of
the single exploratory file — where every instantiating numeral occurred
literally in the query and `ematch-only` refuted — I expect `ematch-only` to land
**above 70 %**, and I expect bucket **N to be small**. That is the **opposite**
of the brief's hypothesis. If M1 lands ≤ 30 % the brief is right and I am wrong,
and the report says so in those words.

**Pre-registered secondary expectation:** the brief asks whether the explicit
`:pattern ((instantiate_me a))` shape generalises beyond `2019-Preiner`. I expect
it does **not** — `instantiate_me` is a Preiner-family idiom. Counted over the
whole population, not asserted.

## If Deliverable 2 happens

Binding on this lane, so that a prototype cannot be graded after the fact:

- **One binary, two arms behind an env lever.** The lever **ships OFF**; `off` /
  `0` / empty / unparseable / absent all resolve to the shipped behaviour, and
  the runner header states that polarity in words. The arm under test is the
  non-default value.
- Interleaved per-file A/B, both arms back to back on the same file on the same
  pinned physical core, **order alternating**, 24 s wall, 8 GiB `ulimit -v`.
- **Control division that must not move**, reported even at zero, together with
  the count of undecided rows the affected route actually binds — so the control
  is shown non-vacuous rather than asserted to be (ADR-1995's method).
- Every moved row re-run **3x per arm**: STABLE-GAIN / STABLE-LOSS / UNSTABLE /
  FLIP, against a noise floor measured on one whole division, same arm, repeated.
- New verdicts verified with
  `bench-results/dt-exactness-20260913/verify-new-verdicts.sh` — **not** the
  `dispatch-decline-audit-20260913/` copy, whose `:status` stage matches nothing.
  No-opinion counts published separately from agreements (ADR-1957).
- **Wilson** intervals, never normal.
- The A/B measures **this branch**. The post-merge value is predicted with its
  reason before merging.

## Compute

s5 core pairs `1,9` `3,11` `5,13` and s6 core pairs `1,9` `3,11` `5,13` — **6
pairs**, the brief's cap. s7 and both `6,14` pairs are left for the concurrent
lane.
