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

## Outcome — the reachability lever, landed

`fdfb910b` implements the ordering this census argued for: NNF + Skolemization
(Skolem **functions** over the enclosing universals) + prenexing, wired into the
residual-quantifier decline path.

| | before | after |
|---|---|---|
| UF correct (of 159 declared-status) | 8 | **23** |
| UF percentage | 5.0 % | **14.5 %** |
| wrong verdicts | 0 | **0** |
| errors | 0 | 0 |
| UFLIA decided | 67 | 67 *(unchanged, DISAGREE = 0)* |

All three steps turned out to be necessary, and each intermediate state was
measured rather than assumed:

1. **Skolemization alone** — fired (`changed = true`) and instantiation *still*
   reported a residual quantifier, because discharging the existentials leaves
   the universals exactly where they were.
2. **Adding NNF + prenexing** — still residual: 7 assertions out of 379 hit the
   polarity-mixing bail-out, and **one** abandoned assertion is enough to make
   the whole query undecidable by instantiation.
3. **Expanding Bool-sorted `xor`/`=`/`ite`** into polarity-pure equivalents
   instead of bailing — `residual = false`, and the verdicts move.

A latent bug surfaced on the way: `skolemize_top_existentials` numbered its
symbols with a per-call counter against an arena-lifetime namespace, so a second
call reused `!sk_3`. It hard-errored once the new pass began declaring symbols
first — and would otherwise have silently made two unrelated existentials share
one witness. Both skolemizers now probe for an unused name.

### Method note, third order

Three consecutive runs measured "no change" against a **stale binary**:
`cargo build --release -p axeyum-bench --example smtcomp_cli` builds only the
example, not the `axeyum-bench` binary the sweep actually runs. The fix that was
already working looked inert for three iterations. Rebuild `-p axeyum-bench`
without `--example` before benching, and be suspicious of a byte-identical
result table.

The 3 saturated-but-unproven files remain the MBQI/trigger population, and it is
now worth re-running this census: with 126 files newly reaching instantiation,
the residual has a different shape than it did this morning.

## Re-census after the reachability fix — the lever moved again

Same command, same slice, after `fdfb910b`. Counting the 159 declared-status
files:

| bucket | before | after |
|---|---|---|
| **uninterpreted sort the BV backend cannot bit-blast** | 6 | **51** |
| quantifiers instantiation never reaches | 126 | 38 |
| **decided** | 8 | **23** |
| instantiation saturated, universal unproven (the MBQI population) | 3 | **21** |
| quantified time budget exhausted | 14 | 14 |
| dispatch timeout | 1 | 11 |
| Ackermann admission bound | 1 | 1 |

Two things this says that could not have been predicted from the earlier table:

**The new top bucket is a backend gap, not a search gap.** Making quantifiers
reachable pushed 51 files *past* instantiation and straight into the pure-Rust BV
backend, which declines them: `term #N has sort (Uninterpreted k) that the
pure-Rust BV backend cannot bit-blast`. These are UF files — uninterpreted
functions over uninterpreted sorts, no bit-vectors anywhere — so bit-blasting is
simply being handed a sort it has no encoding for. At 51 of 159 that is **32 % of
the parity-relevant set**, and it is a bounded feature gap rather than a
search-quality problem.

The machinery to build on already exists: `euf.rs` eliminates uninterpreted
*functions* by eager Ackermann reduction (ADR-0013), and `euf_egraph.rs` does
congruence closure. What is missing is an encoding for uninterpreted **sorts**.
The standard route is the finite model property: an EUF formula containing `n`
terms of an uninterpreted sort is satisfiable iff it is satisfiable over a domain
of size ≤ `n`, so each such sort can be encoded as a bit-vector of width
`ceil(log2(n))` and handed to the existing pipeline. `ufbv_finite.rs` already has
`finite_sort_cardinality`, and it returns `None` for `Sort::Uninterpreted(_)` —
that is the precise hole.

**The MBQI population grew 7×, from 3 to 21.** Instance selection was correctly
*not* the first lever, and it is now a real one rather than a rounding error. It
is still second: 51 > 21, and the backend gap is the more mechanical of the two.

Third-order method note: this is the second time the top bucket changed identity
after an increment landed (search-quality → structural → backend). Re-census
before choosing a mechanism, every time; a distribution measured before a fix is
evidence about a solver that no longer exists.

## Re-census #3, after the uninterpreted-sort encoding (`142ab435`)

The bit-blast bucket is **gone**, and UF roughly doubled again.

| bucket | census 1 | census 2 | census 3 |
|---|---|---|---|
| **decided** | 8 | 23 | **48–49** |
| uninterpreted sort not bit-blastable | 6 | **51** | **0** |
| quantifiers instantiation never reaches | 126 | 38 | 31 |
| lazy function-consistency CEGAR declined | — | — | **29** |
| instantiation saturated, universal unproven (MBQI) | 3 | 21 | 21 |
| quantified time budget exhausted | 14 | 14 | 19 |
| dispatch timeout | 1 | 11 | 9 |

**UF is now ~30 % (48–49 of 159), from 5.0 % this morning**, with `DISAGREE = 0`
and `errors = 0` at every step. cvc5 took 40.5 % of the SMT-COMP UF selection.

Two runs returned 49 and 48; at a 2 s budget the last file or two is
timing-sensitive, so the honest figure is a range, not a point.

The residual has no dominant bucket any more — 31 / 29 / 21 / 19 is flat, where
the first census had a single bucket holding 126. That is a different kind of
problem than the one this note opened with, and it means the next increment
should expect a smaller, more incremental payoff than the last two.

### The bug this increment surfaced

Freshness probes used `TermArena::find_symbol`, which searches only the
**user-declared** namespace. `declare_internal` mints into a deliberately
disjoint internal namespace — the crate documents it as a soundness firewall —
so every probe reported "free" and the check did nothing.

Here it failed loudly: 228 `symbol ... already declared with sort (_ BitVec 1),
requested (_ BitVec 2)` errors across the slice. In the two skolemizers shipped
in `fdfb910b` it failed **silently**, because a reuse whose sorts happen to agree
just makes two unrelated existentials share one witness — precisely the hazard
that commit's own message described while introducing it. Anything checking
freshness against `declare_internal` / `declare_internal_fun` must use
`find_internal_symbol` / `find_internal_function`.

Fourth-order method note: the top bucket has now changed identity **three**
times — search-quality → structural → backend → flat. Each change was visible
only after the previous increment landed.
