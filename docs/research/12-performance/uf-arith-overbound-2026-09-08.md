# QF_UFLIA: the route that matches Z3 and cvc5 could not run

Lane `euf-driver-mbtc`, 2026-09-08. Running diary; numbers are filled in as
each sweep lands, and every one names the artifact it was read from.

## What this lane was sent to do, and why it did something else

The brief was the EUF driver: `EufTheory::propagate` rescans every registered
atom and `first_conflict` rescans every asserted disequality plus an all-pairs
constant loop, **on each assert** (`crates/axeyum-solver/src/euf_egraph.rs`),
where Z3 detects both at merge time off the parent lists. That finding is real
and is restated in §4 below, unchanged.

It is aimed at code that does not run on the population we lose.

## 1. The reachability fact, verified in this tree

`dispatch_uf_fast_paths` (`crates/axeyum-solver/src/auto.rs`) opened with:

```rust
if features.has_function
    && has_arithmetic_function(arena)
    && let Some(result) =
        crate::euf::try_lazy_arith_for_overbound(arena, assertions, config, "UF+arithmetic")?
{
    let array_unknown = features.has_array && matches!(result, CheckResult::Unknown(_));
    ...
    if !array_unknown {
        return Ok(Some(result));
    }
}
```

and `try_lazy_arith_for_overbound` (`crates/axeyum-solver/src/euf.rs`) returns
`Ok(None)` **only** when the eager Ackermann bound did not fire:

```rust
if refuse_oversized_ackermann(arena, assertions, context).is_none() {
    return Ok(None);
}
```

with `MAX_ACKERMANN_CONGRUENCE_PAIRS = 64`. The dispatcher's caller
(`check_auto_dispatch`) does `return Ok(result)` on `Some`, so nothing recovers
from it.

**Consequence, confirmed by reading the whole call chain:** on a non-array
UF+arithmetic query with more than 64 congruence pairs, the lazy CEGAR's
result — *including its `Unknown`* — was the solver's final answer, and every
route after it in the ladder was dead code:

- `euf-online` (`check_qf_uf_online_cdclt`),
- `dispatch_ufbv_online`,
- `euf-offline` (`check_qf_uf_with_config`),
- **`dispatch_uf_arith_online`** — the online model-based EUF + linear-arithmetic
  combination, whose own doc comment says it is "tried *before* the eager
  Ackermann route",
- the eager `check_with_uf_arithmetic`.

This confirms, independently, the claim in
`docs/research/02-ecosystems/pipeline-survey-2026-09/arithmetic-division-gap.md`
finding #1. That document marks the identification of "census class = CEGAR"
with "pairs > 64" as `[I]` — inference, not measured. §2 measures it.

**Neither reference solver Ackermannizes this logic at all.** Z3's
`setup_QF_UFLIA` registers `theory_lra` over native congruence closure; cvc5's
`--ackermann` is expert-only, default false, and force-disabled when UF is
present. So the architecture the guard was protecting is not the architecture
either reference uses here.

## 2. The measurement

Instrument: `smtcomp_cli --trace`, which since ADR-1760 prints the route
attribution (`decided_by=` / `bound_by=` / `last=`) and the full ordered trail
as JSON. This is the front door (`solve_smtlib`), not `explain_corpus` — the
2026-09-05 census's classification through that diagnostic tool was refuted on
67 of 70 files in two divisions.

Population: the committed 58-file loss list
`bench-results/parity-losses-20260905/QF_UFLIA.txt`, unchanged. Protocol
matches `scripts/parity-run.sh`: 24 s wall, 8 GiB `ulimit -v`, one file at a
time.

### The first baseline was contaminated, and the contamination is the control

The first 58-file sweep read `target/release/examples/smtcomp_cli` while a
build was writing it. Rows 1–30 ran the pre-change binary; rows 31–58 ran the
post-change one. Nothing in the TSV said so.

It was caught because the two halves disagree in exactly the way the change
predicts, on files of the same family and size: on every one of rows 7–30 that
reached the over-bound decision point, **no solver route ran after it**; on
every one of rows 33–52, `euf-online`, `euf-offline`, `uf-arith-online` and
`uf-arithmetic` all ran after it. A clean split at the row where the binary was
replaced, in the one field the change touches.

That is an accidental A/B, not a designed one, so it is reported as
corroboration and not as the measurement. The sweep script now writes the
binary's `sha256`, the policy and the load average as `#` header lines into
every TSV, and the runner uses **pinned copies** of both binaries rather than
whatever is in `target/` at the time.

Raw per-file results: `bench-results/uf-arith-overbound-20260908/`.

### Result, all 58 files, base solver

| | |
|---|---:|
| reached the over-bound decision point | **52 of 58** |
| ...and no solver route ran after it | **52 of 52** |
| the CEGAR was the single most expensive segment (`bound_by`) | 37 |
| its share of that file's wall clock, median | **98.6%** (min 17.3%, max 98.8%) |
| decided | 0 |

The other six are the wide-integer-literal ingest rejects (`bound_by=fd:parse`),
already understood and not this lane's subject.

So the `[I]` in the survey's finding #1 is now measured, and the number it
guessed — 52 of 58 — is the number: **52 of the 58 files we lose in QF_UFLIA
reach a decision point where one route answers for the whole dispatcher, and on
every one of them nothing else was allowed to try.** On 37 of them that route
also spent essentially the entire budget.

<!-- RESULTS-BASELINE -->

## 3. What was changed

`UfArithOverboundPolicy` (`crates/axeyum-solver/src/auto.rs`), three arms
selected by `AXEYUM_UF_ARITH_OVERBOUND` or, in-process, by
`UfArithOverboundPolicyGuard`:

| arm | what it does |
|---|---|
| `terminal` | the historical behaviour: the CEGAR gets the whole budget and its `Unknown` is the final answer |
| `probe` (default) | the CEGAR gets the *remaining* budget less the ladder's reserve (a quarter); its `Unknown` declines the route and the ladder below runs on the reserve |
| `skip` | the CEGAR does not run; a measurement arm for what the routes underneath decide alone |

Three properties the change keeps:

1. **The pathological refusal stays terminal under every arm.** A query above
   `MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS` (two million pairs), above
   `MAX_LAZY_DAG_NODES`, or deeper than `MAX_LAZY_DEPTH` is refused *before*
   the CEGAR and does not fall through: those are the inputs the ladder below
   would blow up on, which is what the bound exists for. Counted separately as
   `pathological_refusals` so "we refused" is never read as "the CEGAR tried".
2. **One clock.** The dispatcher takes its deadline at entry; the probe budget
   and the ladder's remaining budget both come out of it, so a probe that
   spends its share leaves the ladder the reserve instead of restarting the
   clock. `dispatch_uf_arith_online`'s own half-budget probe is taken from the
   remaining budget for the same reason.
3. **The probe runs on a cloned arena**, for the same reason
   `dispatch_uf_arith_online` does: the CEGAR appends abstraction symbols and
   congruence lemmas, and leaving them behind would enlarge every route the
   fall-through then runs.

Instrumentation (`UfArithOverboundStats`, opt-in via
`UfArithOverboundStatsGuard`, printed by `smtcomp_cli --trace` as
`; uf-overbound …` and only when the bound actually fired): `engaged`,
`cegar_skipped`, `cegar_decided`, `cegar_unknown`, `terminal_unknown`,
`fell_through`, `pathological_refusals`. Every field is a count; timing for
this decision point already lives in the route trail's `bound_ms`, and a second
clock would only give a reader two numbers to reconcile.

`terminal_unknown` is the field this lane exists for: it is the count of files
where a route declined and **nothing else was allowed to try**.

### The guard was checked against its own removal

`cargo test -p axeyum-solver --lib --features full -- overbound` — **12 tests,
a nonzero count confirmed**, all passing.

Then the mutation that matters, applied in this isolated worktree with a
restoring trap (`scripts/…/mutate.sh` in this lane's scratch, recorded here
rather than committed): make `OverboundOutcome::FallThrough` answer for the
dispatcher, i.e. put back the behaviour this change removes. The script asserts
its own anchor is present first, so a green run cannot come from a mutation
that never applied.

**Exactly two tests died**, and they are the two that assert the ladder runs:

```
overbound_ladder_is_reachable_when_the_cegar_is_skipped ... FAILED
every_policy_gives_the_same_verdict_on_an_overbound_query ... FAILED
test result: FAILED. 10 passed; 2 failed
```

The other ten survived, including `overbound_terminal_policy_still_answers_for_the_whole_dispatcher`
— which *should* survive, because the mutation is that arm's own behaviour.

Two earlier honest failures are worth recording, because both were the test
being wrong rather than the code: the first version of the fixture used 20
padding applications and reported `engaged == 0` on a query unambiguously over
the eager bound — the pre-LIA probe
(`dispatch_arith_uf_overbound_probe_before_lia`) decides such a query on its
own clone and `dispatch_uf_fast_paths` is never reached at all. The fixture now
exceeds `MAX_PRE_LIA_UF_PROBE_ASSERTIONS` (256) so dispatch actually reaches the
decision point under test.

## The measured effect

Three arms over the same committed 58-file loss list, two pinned binaries, run
**concurrently** on one host so the contention is common-mode (this box carried
other lanes throughout, `loadavg` 31.5 at start; read the decided set, not the
milliseconds).

| arm | decided | reached the decision point | nothing ran after it | disagreements |
|---|---:|---:|---:|---:|
| base (pre-change) | 0 | 52 | **52** | — |
| `probe` (new default) | **9 `sat`** | 26 | **0** | 0 |
| `skip` | **9 `sat`** | 47 | **0** | 0 |

**+9 files on the QF_UFLIA loss population, 0 lost, 0 disagreements.** The gap
on this list goes 58 → 49.

Every one of the nine is decided by **`uf-arith-online`** — the online
model-based EUF + linear-arithmetic combination, the route that was previously
unreachable. All nine are `sat`, and all nine match the reference's verdict in
the committed census (`reference_verdict=sat` for each), so the agreement is
against an independent solver and not just against ourselves.

The nine:
`hash_sat_04_11`, `hash_sat_04_14`, `hash_sat_04_17`, `hash_sat_05_05`,
`hash_sat_05_08`, `hash_sat_05_11`, `hash_sat_06_05`, `hash_sat_06_08`,
`hash_sat_07_05` (all `mathsat/Hash`).

**`probe` and `skip` decide the same nine.** That is the load-bearing detail:
the gain is the *reachability*, not the budget split. Halving the CEGAR's budget
neither bought nor cost a file here — what bought them was letting its `Unknown`
fall through. It also means `UF_ARITH_CEGAR_PROBE_SHARE` is not yet a tuned
number; it is a safety margin whose value this population does not constrain.

### What did not move, and the honest limit of the claim

**Twenty-six of the fifty-two still lose.** On those the probe arm ends at the
24 s watchdog with `route unavailable` (the ladder was still running when the
budget expired) and the skip arm ends at `uf-arithmetic`. Those are genuine
search timeouts and the reachability fix does not touch them; they need the
arithmetic work (`LiaTheory` re-solving from scratch per theory check, the
tableau shape) that the companion survey ranks as findings #2 and #3.

`probe` runs slightly past the internal budget on the timeout population
(25.05 s wall against base's 24.31 s, so the harness watchdog is what stops it,
not our own deadline). Not a correctness problem under the parity protocol, and
not investigated further here.

### The regression check on the files we already win

Also run: the full committed 200-file division list, base against `probe`, both
arms concurrent, artifacts `base-QF_UFLIA200.tsv` / `probe-QF_UFLIA200.tsv`.
The budget split can only cost files here — a query the CEGAR used to decide in
more than half the budget now has half of it — so this is the check that decides
whether the default is safe.

### What it measured, and why the constant changed

| arm | list | decided | gained | lost | disagreements |
|---|---|---:|---:|---:|---:|
| base | 200 | 116 | — | — | — |
| `probe`, CEGAR gets **half** | 200 | 121 | +9 | **−4** | 0 |
| base | 58 losses | 0 | — | — | — |
| `probe`, CEGAR gets **3/4** | 58 losses | 9 | **+9** | **0** | 0 |

The half-budget version lost four files, and all four are files the CEGAR
decides *given more than half the clock*: `hash_sat_05_14` (12.7 s),
`xs_23_33` (13.3 s), `hash_uns_05_17` (15.5 s), `hash_uns_05_20` (23.7 s).

It bought nothing for that cost. On the nine files the change wins, the ladder
decides in **307–625 ms** — read off the `skip` arm, where no CEGAR runs at
all. A half-budget split spent twelve seconds to buy four hundred milliseconds
of work, which is the wrong shape: the routes it unblocks need a **reserve**,
not a share.

`UF_ARITH_CEGAR_PROBE_SHARE` therefore became
`UF_ARITH_LADDER_RESERVE_SHARE = 4`. The CEGAR keeps everything except a
quarter: 18 s of a 24 s budget, above three of the four regressing files'
requirements, and the ladder gets 6 s, about ten times the largest ladder time
observed. The fourth, at 23.7 s of 24 s, cannot be recovered by any reserve —
a route needing 99% of the clock cannot share it — and is the named cost of
making the ladder reachable.

A 1/8 reserve was written and rejected before it shipped: it leaves the
ladder's 0.4 s of work behind 21 s of CEGAR on a 24 s budget, where contention
alone can eat the difference.

**Re-measured at the shipped value on the 58-file loss list: +9, 0 lost, 0
disagreements** (`reserve-QF_UFLIA58.tsv`, binary digest `f18559b05bd8`).

### The shipped default, over the whole division list

`base-QF_UFLIA200.tsv` against `reserve-QF_UFLIA200.tsv`, 200 files, pinned
binaries, both arms concurrent:

| | base | reserve (shipped) |
|---|---:|---:|
| decided | 116 | **125** |
| gained | — | 10 |
| lost | — | **1** |
| disagreements | — | **0** |

**Net +9 on the full division list, which is the same number the 58-file loss
population gives — as it should be, since the files it wins are exactly those
losses.**

Two entries in that table need their own sentence rather than a footnote:

- The one loss is **`hash_uns_05_20`**, `unsat` at 23.7 s of a 24 s budget under
  base. It is the file the constant's own doc names as unrecoverable: a route
  that needs 99% of the clock cannot share it with anything. The three other
  files the half-budget split lost — `hash_sat_05_14` (12.7 s), `xs_23_33`
  (13.3 s), `hash_uns_05_17` (15.5 s) — are all **recovered** by the reserve,
  which is what choosing the constant against that bound was for.
- One of the ten gains, **`medium6`**, is *not* a policy effect and should not
  be counted as one. Base timed out on it at 24.4 s; the reserve arm decided it
  `unsat` in 14.7 s **at `uf-arith-lazy-overbound`** — the same route, with
  *less* budget. A policy that gives a route less time cannot make it finish
  sooner, so this is run-to-run variance on a contended host. The defensible
  claim is **+9 / −1**, not +10 / −1.



<!-- RESULTS-AB -->

## 4. The EUF-driver and MBTC findings, recorded but not acted on

Kept here because they are real, and because the next lane to read the survey
will otherwise re-derive them:

- **`EufTheory::propagate` and `first_conflict` are quadratic in the whole
  problem, not in the delta** (`crates/axeyum-solver/src/euf_egraph.rs`):
  `propagate` iterates every registered atom asking `egraph.equal(a, b)`;
  `first_conflict`, called from every `assert`, iterates every asserted
  disequality and then does an all-pairs scan over distinct constants. Z3
  attaches disequalities to the class (`add_th_diseqs`) and rediscovers
  congruence only over the parents of the smaller class
  (`remove_parents`/`reinsert_parents`).
- **Disequality propagation (an atom entailed `false`) is explicitly deferred**
  in our source.
- **Model-based theory combination is missing its filter.** Z3 randomises each
  coinciding shared variable inside its slack before proposing an interface
  equality, so only forced coincidences survive; Yices optimistically merges
  and rolls back; cvc5 uses a structural care graph. We group by model value
  and hand every group to a depth-capped DFS.

The measured reason not to act on them in this lane is in §2: on the QF_UFLIA
losses the budget is consumed before any of that code is reached.

**A separate quadratic, which IS on the hot path**, and which this lane
observed rather than fixed: the lazy CEGAR itself rescans every application
pair every round. On `hard12.smt2` its own summary reports
`potential_pairs=14916`, `solve_rounds=79`, `pair_checks=1154629` — the
all-pairs loop over `groups` in `check_with_function_consistency`, re-run per
round. That is the same "work proportional to the state, not the delta" shape
the survey names in the EUF driver, in the code that actually runs here.
