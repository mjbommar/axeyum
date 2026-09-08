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

<!-- RESULTS-BASELINE -->

## 3. What was changed

`UfArithOverboundPolicy` (`crates/axeyum-solver/src/auto.rs`), three arms
selected by `AXEYUM_UF_ARITH_OVERBOUND` or, in-process, by
`UfArithOverboundPolicyGuard`:

| arm | what it does |
|---|---|
| `terminal` | the historical behaviour: the CEGAR gets the whole budget and its `Unknown` is the final answer |
| `probe` (default) | the CEGAR gets half the *remaining* budget; its `Unknown` declines the route and the ladder below runs on what is left |
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
   spends half the budget leaves the ladder the other half instead of
   restarting the clock.
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
