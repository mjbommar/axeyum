# UF residual census — what actually limits the quantifier route

Date: 2026-07-30. Corpus: 300-file stratified UF slice (SMT-LIB 2024
non-incremental), `smtcomp_cli`, 6 GiB cap.

This note exists to stop a specific wrong move: spending the next increment on
**budgets** (more time, more rounds, bigger caps). Four measurements say that
would buy nothing. The lever is instance *selection*, not instance *volume*.

## The baseline

Of 300 files, 159 carry a declared `sat`/`unsat` `:status`.

| | count |
|---|---|
| correct | 8 |
| unknown | 151 |
| **wrong** | **0** |

That is **5.0%** on ground-truth files — the weakest measured division we have
(UFLIA is 22.3%; cvc5 took 40.5% of UF and 58.1% of UFLIA at SMT-COMP 2025).

The 151 unknowns with known ground truth are the subject of this census. Raw
results: `uf-baseline.tsv` (name / declared / axeyum).

Prerequisite: this run was impossible before `2b4b6934`. Six files consumed all
available address space in e-matching and aborted the whole sweep at 32 GiB.

## Four measurements

**1. Quantifier count is not the discriminator.** The residual averages 317
`forall` (median 393), which invites the theory that we simply drown in
quantifiers. But the files we *do* solve include ones with 456, 458, and 521
`forall`. Size is not what separates a solve from a miss.

**2. The residual is not budget-limited.** 60 residual files at a **15×** budget
(2 s → 30 s): **0 newly decided**.

**3. It is not round-limited either.** `MAX_INSTANTIATION_ROUNDS` 8 → 64, at
30 s: **0 newly decided** across the same 60.

**4. The decline is round exhaustion, and instantiation is productive when it
happens.** Probing the exit path over 30 residual files at 5 s: **29
`rounds_exhausted`, 1 timeout**, zero ground-limit. And the loop is *not* at a
fixpoint when it stops — ground grows every round right up to the cap:

```
ground=35  admitted=8     ground=40   admitted=21
ground=63  admitted=9     ground=301  admitted=147
ground=118 admitted=22    ground=1100 admitted=608   <- exits here, cap is 8192
```

## What that combination means

Points 2–4 look contradictory: the loop stops early *while still producing
instances*, yet giving it more rounds decides nothing. Raising the cap to 64
resolves it — the run then saturates:

```
ground=5560 admitted=1160
ground=8009 admitted=2449
ground=8104 admitted=95
ground=8192 admitted=32
ground=8192 admitted=0     <- 9 of 10 files land exactly here
```

So the route can generate **8192 ground terms**, run itself to a standstill, and
*still* not refute. The instances it produces are not the ones the proof needs.
More rounds produce more of the same irrelevant instances.

This is the classic e-matching relevance problem, and for the files that reach
instantiation it names the mechanism: **instance selection** — trigger quality,
relevance filtering, and a model-guided route (MBQI). Not bigger budgets.

> **Amended the same day — instance selection is the *second* lever, not the
> first.** Everything above is measured and stands, but it was derived by
> probing the route's *internal* decline path, on files sampled from the head of
> the residual. Re-running the whole slice through `axeyum-bench --backend solver`
> (which reproduces this harness exactly: 9 unsat, 291 unknown, agree = 8,
> DISAGREE = 0) surfaces the *reported* decline reason for every file, and the
> population tells a different story about where the mass is.

## Where the residual mass actually is

`axeyum-bench --backend solver`, 2 s, over the same 300 files. Counting only the
**159 files with a declared `sat`/`unsat`**, since those are the parity-relevant
ones:

| n | decline reason |
|---|---|
| **126** | **quantifiers instantiation never reaches — nested, existential, or non-top-level** |
| 14 | quantified time budget exhausted |
| 8 | *(decided)* |
| 6 | uninterpreted sort the BV backend cannot bit-blast |
| 3 | instantiation saturated, universal still unproven |
| 1 | Ackermann admission bound (496 congruences vs a bound of 64) |
| 1 | preprocessed dispatch timeout |

Also note **`unsupported` is 0**. Unlike UFLIA — where 141 of 300 were a
feature/parse gap — every UF file parses and is supported. UF is a pure search
gap.

**83 % of the residual is structural, not a search-quality problem.** Those 126
files are declined because their quantifiers sit outside the fragment
instantiation operates on at all; the route never gets to be bad at choosing
instances, because it never chooses any. A sample of 60 confirms it: **60/60
contain `exists`, and 60/60 have a second quantifier in scope.** That matches the
shape census above, which found `exists` in 122 of 151.

Only **3** files are in the state the e-matching analysis describes —
instantiation saturated and the universal still unproven. That is the population
MBQI and trigger work would serve today.

Reconciling the two readings: both are real and they compose. On a bucket-A file
the e-graph route still runs, still exhausts its rounds, and still shows the
productive-but-unfocused growth traced above — but that instantiation is over the
*reachable* part of a query whose actual content is nested under quantifiers it
never entered. Round exhaustion is the symptom; unreachable structure is the
cause.

**So the ordering is: make the quantifiers reachable first** — Skolemization,
prenexing/miniscoping, and non-top-level universal handling — *then* invest in
instance selection, which at that point will have 126 more files to be good at.
Building MBQI first would be tuning the search on 3 files while 126 sit
untouched.

### Method note, second order

The first conclusion came from probing the internal decline path on a sample from
the head of the list. It was measured, reproducible, and pointed at the wrong
lever, because the internal reason a route gives up is not the same question as
what stopped the *population*. Read the reported reason across the whole corpus
before choosing a mechanism.

## Secondary findings

- The ground-limit check is `ground.len() > MAX_GROUND_TERMS`, and ground
  plateaus at *exactly* 8192, so the limit never trips — the run reports
  `rounds_exhausted` instead. Cosmetic today (both yield `unknown`), but it
  makes the decline reason misleading in exactly the place we now care about.
- The `admitted → 0` plateau is reported as observed, not as a proven fixpoint:
  at 8192 ground terms the e-matching frontier caps from `2b4b6934`
  (`MAX_MATCH_FRONTIER`) could also be binding. Distinguishing "saturated" from
  "truncated" needs an instrumented count, and matters if anyone later argues
  the caps are costing refutations.
- Three `sledgehammer` files overrun a 2 s budget by 20–30× with bounded memory
  (task #26). Separate defect from the memory blowup; that one is fixed.

## Method note

The `2b4b6934` root cause took four failed attempts by deduction and three
`eprintln` phase probes by measurement. Every conclusion above is a measured
verdict count, not an inference from reading the code. When the next increment
touches this route, probe first.
