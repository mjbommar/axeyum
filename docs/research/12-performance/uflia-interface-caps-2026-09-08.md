# QF_UFLIA after the reachability fix: the route runs, and declines in 0.2 ms

Lane `uflia-after-reachability`, 2026-09-08. Running diary; numbers are filled
in as each sweep lands and every one names the artifact it was read from.

## The question

On 2026-09-08 the `euf-driver-mbtc` lane made the online model-based EUF + LIA
combination **reachable** on the losing `QF_UFLIA` population for the first time
([`uf-arith-overbound-2026-09-08.md`](uf-arith-overbound-2026-09-08.md)): a
guard above 64 eager-Ackermann congruence pairs had made four routes dead code
and the lazy CEGAR's own `Unknown` the dispatcher's final answer. That bought +9
files. The division then stood at **129 of 200, reference `cvc5 1.3.4` 180,
both/ours-only/theirs-only 129 / 0 / 51**.

Nobody had profiled the remaining losses since the routes started running. This
lane's step 1 was to classify them, and everything below step 1 is a consequence
of what the classification said.

## 1. The measurement

Instrument: `smtcomp_cli --trace`, front door (`solve_smtlib`), the full `;`
output kept per file rather than only the route line — the sweep script is
`.lane-uflia/scripts/sweep.sh` in this lane's scratch, committed as
`bench-results/uflia-interface-20260908/scripts/sweep.sh`.

Protocol: the parity protocol verbatim — 24 s wall, 8 GiB `ulimit -v`, **one
file at a time**. Population: the committed 200-file division list
`bench-results/parity-lists/QF_UFLIA.txt` (sha256 `f88e67890fae`), not a loss
list, so the denominator is the board's.

Hosts: s5, s6, s7 — three idle 16-core boxes, one third of the list each,
interleaved (`NR%3`) so a family cannot land entirely on one host. s4 was
excluded: it carries the lane traffic and its load average sat between 5 and 7
throughout.

Reference verdicts are read from the committed per-file detail of the
2026-09-06 board run (`bench-results/parity-details/QF_UFLIA.tsv`, 180 solved),
because a reference verdict does not move between runs and re-running `cvc5`
would only add noise to the comparison.

### Result

| | |
|---|---:|
| files | 200 |
| reference solved | 180 |
| we decided | **130** |
| losses (reference solved, we did not) | **50** |
| disagreements | **0** |

130/50 against the board's 129/51 — a one-file difference, which is run-to-run
variance on the timeout boundary and not a change.

### The split

| bucket | files |
|---|---:|
| (a) declines before trying | **6** |
| (b) tries and times out | **44** |
| (c) hits a memory / size bound | 0 |
| (d) `unknown` for another reason | 0 |

The six in (a) are the wide-integer-literal ingest rejects
(`fd:bounded-completeness-unsat`, ADR-1702 slice 2). They are already
understood: ADR-0376's ablation, re-measured 2026-09-06, is 6/6 still `unknown`
with every wide literal **removed**, so the binding constraint on them is the
decision procedure and not the literal type. They are not this lane's subject
and no work here touches them.

**So on the current board the whole actionable gap is bucket (b): 44 files, all
of them watchdog timeouts.** And that is where the classification stops being a
summary and starts being a finding.

### What bucket (b) is actually made of

`bound_by` on a timed-out file names the route that consumed the budget. On all
44 that is `uf-arith-lazy-overbound` — the lazy CEGAR, which under the shipped
`probe` policy holds 18 s of the 24 s budget. That is a fact about the **budget
split**, and it is the answer the previous lane already recorded.

The question this lane was sent to ask is what the routes underneath did with
the 6 s reserve, and that is a different field: the **last** recorded attempt.
On all 44 it is `uf-arith-online` — the online combination, the route whose
architecture matches Z3's `setup_QF_UFLIA` and cvc5's default. It ran on every
single one of them, and this is what it said:

| what `uf-arith-online` reported | files |
|---|---:|
| `too many theory atoms for the online combination boolean layer: N > 512` | **27** |
| `opaque-app online UFLIA incremental combined state could not be built safely` | **8** |
| `theory combination inconclusive …: too many interface pairs for the online combination split` | **5** |
| `combined CDCL(T) leaf did not rebuild a replaying model` | **4** |

The `N` in the first row ranges from **595 to 2,972** against a ceiling of
**512**.

**40 of the 44 are an admission decline of the online combination**, and each
one costs between 0.1 and 0.3 ms. The route that matches what both reference
solvers do for this logic is reached, looks at the query, and refuses it in less
than a millisecond; the twenty-four seconds are then spent in the two routes
that cannot decide it.

That is the answer to step 1, and it is not the answer the candidate list in the
brief anticipated. The model-based-combination filter, the quadratic EUF driver
and the DFS depth cap are all downstream of code that does not execute on this
population: `split_nodes = 0` on every one of these files, because the search
never starts.

<!-- RESULTS-STEP1 -->

## 2. Two of those four strings did not name their own cause

Twice on 2026-09-08 a printed decline reason turned out not to be the operative
one, so each of the four rows above was traced to the guard that produced it.

- **Row 1 is honest.** `uflia_online.rs`'s atom-cap decline prints the count and
  the *effective* limit (`max_boolean_atoms()`, which the env var can raise), so
  a reader can act on it. It is the only one of the four that can be.
- **Row 2 is not.** "opaque-app online UFLIA incremental combined state could
  not be built safely" is the caller's rendering of a bare `None` from
  `CombinedIncrementalLia::new_with_deadline`, and that `None` has **four**
  causes: a mid-construction deadline, a partition failure, an arena build
  error, and `raw_pairs.len() > MAX_SPLIT_PAIRS` — a hard ceiling of 64 on the
  proposed interface pairs. One string, four causes, three of them different
  kinds, and the string reads as a safety property. Confirmed by direct run:
  on `hard12.smt2` the new counters report `atoms_max=243`,
  `pairs_proposed=221`, `pair_cap_declines=1` — the 64-pair ceiling, on a file
  whose atom count is comfortably inside the atom ceiling.
- **Row 4 is not either.** "combined CDCL(T) leaf did not rebuild a replaying
  model" is returned for *every* `Unknown` the conjunctive core produces — its
  deadline, its `MAX_SPLIT_DEPTH` ceiling, an out-of-fragment atom, an
  unavailable LIA model — with the inner `UnknownReason.detail` in scope and
  discarded.
- Row 3 is the same 64-pair ceiling as row 2, surfaced through the enumerative
  fallback, where the inner detail *is* forwarded.

So the four rows are really **three** conditions: the 512-atom Boolean-layer
ceiling (27), the 64-pair interface ceiling (13), and a genuine leaf failure
whose cause was unrecoverable from the trace (4).

Both mislabels are fixed in this lane: `CombinedBuildFailure` gives the
construction failure one variant per cause and a `detail()` that names the
ceiling and the size that crossed it, and the leaf arm forwards the inner
detail.

## 3. Why the interface pair set is the shape it is

`interface_pairs` proposes **every** unordered pair of atomic integer terms with
at least one EUF endpoint. That is quadratic in the interface-term count, so a
ceiling of 64 pairs is roughly **twelve** shared integer terms, and the DFS
descends one level per pair — the depth cap and the admission cap are the same
number and, because `run` recurses over every pair whether or not it branches,
the same condition.

Neither reference solver enumerates that set:

- **cvc5** builds a *care graph* and proposes an equality only for a pair that
  could fire a congruence — corresponding arguments of two applications of the
  same function.
- **Z3** randomises each coinciding shared variable inside its slack before
  proposing an equality, so only forced coincidences survive.

The care graph is implementable here and is implemented (see §4). **Z3's
randomisation filter is not available at this point in our architecture, and
that is a finding rather than an omission**: we materialise the `eq`/`lt`/`gt`
interface atoms up front, at combined-state construction, before any literal is
asserted and therefore before any model exists to randomise. Z3 filters at final
check, where it has one. Adopting it means moving interface atoms to dynamic
registration at final check — a different slice, and one worth naming so the
next lane does not price it as a filter.

## 4. What changed

Everything below is off by default or behaviour-preserving under the default
arm; the measured arms are named.

### 4.1 `crate::uflia_interface` — the interface layer as a policy plus counters

- `UfliaInterfacePolicy` — `all` (the shipped behaviour: all pairs, decline over
  the ceiling), `care` (cvc5's care graph, still declines), `care-truncate` (the
  care graph, and a deterministic truncation to the ceiling instead of a
  decline). Selected by `AXEYUM_UFLIA_INTERFACE_PAIRS` or, in-process, by
  `UfliaInterfacePolicyGuard`, so the arms A/B on **one** binary.
- **Dropping a pair is sound in both directions.** `sat` is replay-gated
  (`replays_literals` / `replays_assertions`), so a model assembled under a
  coarser arrangement either replays or is declined. `unsat` is a relaxation
  refutation: each dropped pair removes a forced `s = t` / `s < t` / `s > t`
  from the LIA side and the matching arrangement fact from the EUF side, so
  every explored branch stands for a superset of the branches it replaced. What
  a filter costs is **completeness** — and against a ceiling that declines the
  whole query at 65 pairs, that is not the relevant comparison.
- `MAX_INTERFACE_PAIRS = 64`, and `uflia_online::MAX_SPLIT_DEPTH` and
  `combined_theory_lia::MAX_SPLIT_PAIRS` now **read it** rather than repeating
  its value. The config registry had recorded those two plus the `QF_UFLRA` pair
  as "four unlinked copies of one bound … one intended meaning, no code-level
  link"; two of the four are now one definition. The `QF_UFLRA` pair is left
  alone deliberately — this lane did not measure that division and a silent
  re-link would claim it had.
- The **value is unchanged**. Pairs are quadratic in the interface-term count,
  so a raise big enough to admit this population is not a raise, it is the
  removal of a termination bound. The filter is the lever.
- `UfliaInterfaceCounters` — opt-in, clock-free, printed as
  `; uflia-interface …` under `--trace` and recovered from a watchdog kill.
  `entries` is the entry counter and it is deliberately the **outermost** site:
  a counter whose entry site were the pair proposal would print nothing at all
  on 40 of the 44 files it exists to explain. The admission sites publish to the
  live board on every call (they are reached a handful of times per query); the
  DFS sites publish on a 1,024-record cadence.

### 4.2 Decline attribution

- `CombinedIncrementalLia::new_explained` returns `CombinedBuildFailure` — one
  variant per `None` site — and the caller reports its `detail()`, which names
  the ceiling and the proposal size that crossed it, and a deadline as
  `UnknownKind::Timeout` rather than as an incompleteness.
- The conjunctive core's over-ceiling decline names the size and the constant.
- The Boolean CDCL(T) leaf arm forwards the inner `UnknownReason.detail`
  instead of relabelling every cause as a replay failure.
- The leaf model-build failure says its reason is a **union** — overflow,
  coverage, a LIA deadline, or an integer-search cap — rather than asserting the
  modelling half of it.

## 5. The measured effect

All arms run on the 50-file loss population derived from the §1 sweep, with the
**same** pinned binary per column, one file at a time under the parity protocol,
on idle 16-core hosts. `AXEYUM_UFLIA_MAX_BOOLEAN_ATOMS` and
`AXEYUM_UFLIA_MAX_OPAQUE_BOOLEAN_ATOMS` can only RAISE the compiled ceiling (the
override is `v.max(default)`), which is exactly what makes an atom-cap arm
possible without a second build; `AXEYUM_UFLIA_INTERFACE_PAIRS` and
`AXEYUM_UF_ARITH_OVERBOUND` select the two policies. **Baseline is the §1 sweep,
where all 50 are `unknown` by construction.**

| arm | atom ceiling | interface policy | over-bound policy | decided | lost | disagreements |
|---|---|---|---|---:|---:|---:|
| base (§1) | 512 / 128 | `all` | `probe` (shipped) | 0 | — | 0 |
| care only | 512 / 128 | `care-truncate` | `probe` | **1** | 0 | 0 |
| atoms | 8192 / 8192 | `all` | `probe` | **10** | 0 | 0 |
| atoms + skip | 8192 / 8192 | `all` | `skip` | **14** | 0 | 0 |
| atoms + care + skip | 8192 / 8192 | `care-truncate` | `skip` | **31** | 0 | 0 |

<!-- RESULTS-ARMS -->

Four things this table says, in the order they matter:

**The two ceilings together account for 31 of the 50 remaining losses.** Not
"could account for" — decided, with every verdict agreeing with `cvc5`'s
committed verdict on the same file and no disagreement in any arm. The
comparison script's exit status is 1 on a disagreement, so this is a check that
can fail rather than a sentence.

**Neither ceiling alone gets there, and the order is not symmetric.** The
care-graph filter ON ITS OWN decides **one** file: on 27 of the 50 the atom
ceiling fires first, so the interface layer is never reached and the filter has
nothing to filter. It is not inert — on 12 files the last reported reason moves
from the pair-ceiling decline to `interface distinct branch inconclusive`, i.e.
the DFS now runs and reaches leaves — but the route cannot finish while the atom
ceiling is still refusing the queries around it. Raising the atom ceiling alone
gets 14; adding the filter on top more than doubles that to 31. A lane that
measured the pair ceiling without first lifting the atom ceiling would have
concluded the care graph was worth one file.

**Most of the wins are fast, and that is a fact about dispatch order.** Of the
31, twenty-three decide in **0.4–2.0 s** and four more in 6.6–10.7 s. They are
currently reached only after the lazy CEGAR has spent 18 s of a 24 s budget, and
the `probe` arm's 6 s reserve is why the shipped policy captures fewer of them
than `skip` does. `skip` is not a shippable arm — the previous lane measured
four files the CEGAR needs 12.7–23.7 s for — so the honest reading is that the
reserve, set on 2026-09-08 against a ladder that decided in 307–625 ms, is now
sized against a ladder that is much more capable. Re-deriving it, or reordering
so the combination runs first as Z3 and cvc5 do, is the next measurement and is
NOT claimed here.

**Soundness of the filter is checked against an independent solver, not
argued.** The three z3 differential suites run with `care-truncate` forced:
`qf_uflra_differential_fuzz` (1 test), `uf_arith_dispatch_differential`
(2 tests), `uflia_differential_fuzz` (1 test, 328 s) — **4 tests, a nonzero
count confirmed on each, all passing**. The fuzz panics on a wrong `sat` or a
wrong `unsat` and independently replays every `sat` model through the ground
evaluator. It cannot see a completeness loss (an extra `Unknown` is allowed by
design), so it is evidence about the direction that matters and silent on the
one the counters are for.

### Which of the two atom ceilings, separated

The winning arm raised **both** `MAX_BOOLEAN_ATOMS` (512) and
`MAX_OPAQUE_BOOLEAN_ATOMS` (128), so it cannot say which mattered. A separating
arm — general ceiling raised to 8192, the opaque one left at 128 — decides
**the same ten files, by name**. And the new counters answer it directly:
`opaque_atom_cap_declines` is **0 on every file in every arm**, including the
33 files of the 200-file candidate run where the route was entered at all. On
this population the opaque ceiling never fires.

So it is **not** raised. Its own doc comment says the opaque path is the one
place on this route where combined-state construction is *not* deadline-aware;
raising a bound that buys nothing measured and guards the least deadline-aware
code is a cost with no benefit. Only `MAX_BOOLEAN_ATOMS` moves.

## 6. The shipped default, over the whole division list

The shipped configuration is the measured one: `MAX_BOOLEAN_ATOMS = 8192`,
interface policy `care-truncate`, over-bound policy unchanged at `probe`. Run as
two 100-file halves of the committed 200-file list against the same base sweep
from §1, one file at a time, pinned binary digest `e696107665d8`.

| | base (§1) | shipped default |
|---|---:|---:|
| files | 200 | 200 |
| decided | 130 | **151** |
| gained | — | **23** |
| lost | — | **2** |
| disagreements | — | **0** |
| against the reference's 180 | 72.2% | **83.9%** |

**Both losses are base-side outliers at the watchdog wire, and that is
checked rather than assumed.** Each was decided by the base run at 25.0–25.1 s —
past the 24 s internal budget, i.e. right at the harness watchdog — and neither
reproduces:

| file | base, in the §1 sweep | base, re-run | candidate, re-run |
|---|---|---|---|
| `xs_16_26` | `sat` 25,032 ms | `unknown` ×4 | `unknown` ×4 |
| `hash_uns_05_20` | `unsat` 25,131 ms | `unknown` ×4 | `unknown` ×1+ |

`hash_uns_05_20` is the same file the previous lane named as the one its reserve
could not recover ("a route that needs 99% of the clock cannot share it"). The
honest statement is **+23 / −2**, with the note that a re-measured baseline
would likely not have had those two to lose; it is not **+23 / −0**, because
this lane did not re-run the whole baseline.

### What is still lost, and what it needs

Twenty-nine remain on the same denominator §1 used — reference-solved, we did
not — and every one of them is a route that RAN:

| last route and reason | files |
|---|---:|
| `uf-arith-online` — `combined CDCL(T) leaf did not rebuild a replaying model: interface distinct branch inconclusive` | **14** |
| `uf-arith-online` — `timeout in the online combination boolean layer` | **9** |
| `fd:bounded-completeness-unsat` — wide integer literal (ADR-1702) | 6 |

**The shape has changed completely, and that is the result underneath the file
count.** Before this lane, 40 of the 44 solver-side losses were **admission
declines** costing 0.1–0.3 ms; now **zero** are. The largest class is a leaf
failure inside a search that ran to a leaf and could not separate the distinct
branch — a capability gap in the interface search and the LIA sub-solve under
it, not a bound, and the next thing to measure. The 6 wide-integer files are
unchanged and untouched.

The `combined CDCL(T) leaf …: interface distinct branch inconclusive` string is
also a demonstration that §2's attribution fix earns its place: under the code
this lane replaced, all 14 would have printed `combined CDCL(T) leaf did not
rebuild a replaying model` with nothing after the colon, and the next lane would
have gone looking at model reconstruction.

## 7. What this lane did not do

- **Dispatch order.** Twenty-three of the wins arrive at 18.3–20.2 s wall,
  because the online combination runs on the ladder's 6 s reserve after the lazy
  CEGAR has spent 18 s. With the CEGAR skipped entirely the same configuration
  decides **31** of the 50 and most of them in **0.4–2.0 s**. Z3 and cvc5 run the
  combination first. Re-deriving `UF_ARITH_LADDER_RESERVE_SHARE` — set on
  2026-09-08 against a ladder that then decided in 307–625 ms — or reordering
  outright is the obvious next lever and needs its own measurement against the
  files the CEGAR decides.
- **The EUF driver's quadratic `propagate` / `first_conflict`.** Still real,
  still unmeasured on this population, and still not what loses these files.
- **Z3's randomisation filter**, for the architectural reason in §3.
- **`QF_UFLRA`.** Its copies of both constants are untouched; this lane did not
  measure that division.

<!-- RESULTS-AB -->
