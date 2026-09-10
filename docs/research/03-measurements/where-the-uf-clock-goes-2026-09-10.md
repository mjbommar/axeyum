# Where the UF clock goes, and why the probe divisor is not the lever

Measured 2026-09-10 on `s4` at `8c8671d7f` (+ a measurement-only patch, §Reproducing),
`taskset -c 0-7`, 4-wide, load 19.5 before / 12.5 after. Population: the 32 files in
[`bench-results/parity-losses-20260908/UF.txt`](../../../bench-results/parity-losses-20260908/UF.txt)
(30 declared `unsat`, 2 declared `unknown`), budget 24 000 ms. The NAS mount was
live; nothing here reproduces without it.

**In one line: the 56.2% does not reproduce as stated — it charges an
unsat-capable rung's clock to an unsat-incapable one — and the constant the item
names, `UFBV_ONLINE_PROBE_SHARE`, is neither the thing that bounds the probe nor
a constant that can be retuned for UF reasons alone.**

## Summary of findings

| # | finding |
|---|---|
| 1 | The **56.2%** is not reproducible as a statement about unsat-incapable rungs. It is instrument A's `q:uf-fmf-probe + q:uf-fmf-full`, and `q:uf-fmf-full`'s segment **contains the whole full-MBQI pass** — a defect the source document records 120 lines above the number. Corrected: **52.4%**, of which only the probe's **42.4%** is time a refuter could have used. |
| 2 | The two finite-model rungs are **structurally** incapable of `unsat`: the producer returns `Result<Option<Model>>`, and its internal `CheckResult::Unsat` arm is `{}` — it *discards* every refutation it finds. Every other rung on this population is capable, with a live `Unsat` return. |
| 3 | `q:uf-fmf-full`'s share is **terminal** — nothing runs after it — so reallocating it buys nothing by construction. Only `q:uf-fmf-probe` is upstream of a refuter. |
| 4 | **The divisor does not bound the probe.** It grants ~12 000 ms of a 24 000 ms budget; on **13 of 32 files the probe spends more**, up to **19 478 ms (162% of its grant)**. Retuning the fraction treats a rung that is already overrunning it by up to 7.5 s. |
| 5 | `UFBV_ONLINE_PROBE_SHARE` governs **no QF_UFBV route at all**. Its two consumers are the pure-UF FMF probe and `dispatch_uf_arith_online` — the QF_UFLIA/QF_UFLRA route that a *dated* measurement's +9 files rest on. Retuning it for UF reasons silently retunes QF_UFLIA dispatch. |
| 6 | Budget utilisation at the rung that *can* refute is **not** evidence for reallocation: 39 of 55 invocations use ≥90% of their slice, but the e-graph loop **saturates by design**, so that is its behaviour at any budget. |

## Step 1 — reproducing the attribution

The item cites **56.2%** from
[`instantiation-strategy-gap-2026-09-10.md`](instantiation-strategy-gap-2026-09-10.md)
Finding 5. It does not reproduce as a statement about rungs that cannot emit
`unsat`, and the reason is in that document's own Finding 1:

> **`q:mbqi`'s wall clock is attributed to `q:uf-fmf-full`.** … the segment
> between the previous record and `q:uf-fmf-full` covers **both** runs and
> `q:mbqi` always shows ~0 ms. `bound_by=q:uf-fmf-full` therefore means "MBQI
> plus the full finite-model finder", never the finder alone.

The 56.2% is `q:uf-fmf-probe` + `q:uf-fmf-full` read off the route trail. By that
document's own account the second term is not the finder. MBQI **is** unsat-capable,
so its seconds do not belong in a total labelled "cannot produce `unsat`".

Two instruments were run, deliberately, so the prior number is reproducible *as
computed* and also correctable.

**Instrument A — the route trail's `elapsed_ns`** (what produced the 56.2%).
Coverage 100.0% of the route summary's own total.

```
     239053 ms   40.1%  q:uf-fmf-probe             (>=100ms on 27 files)
     186961 ms   31.4%  q:egraph                   (>=100ms on 26 files)
     138103 ms   23.2%  q:uf-fmf-full              (>=100ms on 21 files)
      28277 ms    4.7%  q:mbqi-quick               (>=100ms on 27 files)
       2914 ms    0.5%  q:forall-exists-witness    (>=100ms on 12 files)
          0 ms    0.0%  q:mbqi
     596100 ms  total
```

`q:mbqi` reads **0 ms**, which is the defect visible in the output rather than
inferred: the full MBQI pass demonstrably runs on this population and its clock
is inside the 23.2%.

**Instrument B — `AXEYUM_QTRACE` consecutive differences**, which separate them.
Coverage 112.4% of the route summary's total (the ladder's `t0` starts before
the summary's clock; the excess is that offset, not unattributed work).

```
     283934 ms   42.4%  uf-fmf-probe               (>=100ms on 31 files)
     202177 ms   30.2%  egraph                     (>=100ms on 30 files)
      81577 ms   12.2%  mbqi                       (>=100ms on 24 files)
      67343 ms   10.0%  uf-fmf-full                (>=100ms on 22 files)
      35178 ms    5.2%  mbqi-quick                 (>=100ms on 32 files)
          0 ms    0.0%  forall-exists-witness / finite-expansion / nat-induction
     670231 ms  total
```

**So the number is 52.4%, not 56.2%** — and the 11-point gap between the two
instruments is exactly the MBQI conflation. Instrument A on today's tree would
have said **63.3%**; quoting either without the correction overstates the
reallocatable share.

Getting instrument B right needed three clock conventions kept apart, and a
first version of this script that mixed them reported **247% coverage**:

- top-level rungs stamp **cumulative** seconds from one `t0`;
- `mbqi-quick` / `nat-induction` stamp their **own** `Instant`, and their
  seconds are *also* inside the next cumulative difference, so they are charged
  twice unless subtracted;
- `egraph-seg` / `match-seg` / `nested-quant` are **sub-stages inside** a
  top-level window and double-count the same seconds if summed alongside it.

The coverage figure is what caught it. An attribution that does not print its
own coverage cannot distinguish "these are the shares" from "these are the
shares of the part I explained".

### Only part of that share is reallocatable

`q:uf-fmf-full` runs **after every refuter has declined** and nothing runs after
it (`finish_quantified_solve`, the `other =>` arm). Its 10.0% is budget the
ladder would otherwise discard: reallocating it is a no-op by construction, not
an empirical question. The 2026-09-06 census
([`2026-09-06-uf-front-door-census.md`](../11-design-review/2026-09-06-uf-front-door-census.md))
already recorded this and it still holds.

**The reallocatable share is the probe's 42.4%**, and it is the number this item
is actually about.

## Step 2 — which rungs can emit `unsat`, argued from the code

Asked as a property of the rung, not as "we never saw it".

**Structurally incapable — the two finite-model rungs.** Two independent
arguments, either of which is sufficient:

1. **The return type has no `unsat` inhabitant.** `find_uf_finite_model`
   (`crates/axeyum-solver/src/uf_fmf.rs:106`) is
   `-> Result<Option<Model>, SolverError>`. Both call sites wrap the `Some` case
   as `CheckResult::Sat(model)` and record only that
   (`auto.rs:394-401`, `auto.rs:498-505`); the `None` case records a decline. No
   value of the producer's type can become an `unsat` verdict.
2. **The rung throws refutations away.** Inside the deepening loop
   (`uf_fmf.rs:276`) the ground engine's own verdict is matched, and the `unsat`
   arm is empty:

   ```rust
   // UNSAT AT SIZE k TRANSFERS NOTHING about the original: deepen.
   CheckResult::Unsat => {}
   ```

   On a declared-`unsat` file this is the arm that fires at every cardinality it
   tries. The rung spends its budget manufacturing refutations it is obliged to
   discard, because a refutation at a bounded carrier size says nothing about
   the unbounded original. That is a stronger statement than "it did not return
   `unsat` on 30 files": it *cannot*, and it is not idle while failing to.

The doc comment on `UF_FMF_PROBE_SOLVE_ASSERTIONS` (`uf_fmf.rs:97`) calls the
probe "cheap, cannot starve the refutation family". That is an inference from a
**round-size** cap (2 000 assertions) to a **wall-clock** property, and finding 4
below measures it false.

**Capable — every other rung on this population.** Each has a live `Unsat` path:

| rung | site | how `unsat` reaches the verdict |
|---|---|---|
| `q:mbqi-quick` | `auto.rs:4201-4209` | `Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat))` |
| `q:egraph` | `auto.rs:277-284` | `Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat))` |
| `q:mbqi` | `auto.rs:445`, `other =>` arm | `prove_unsat_by_mbqi`'s `Unsat` falls into `other` and is returned |
| `q:finite-expansion` | `auto.rs:517-527` | `check_with_quantifiers`'s non-`Unknown` result is returned unchanged |
| `q:forall-exists-witness` | `auto.rs:330-341` | returns the pass's own `CheckResult` |
| `q:nat-induction` | `auto.rs:925` | `qtrace("nat-induction", t0, "unsat")` on a refutation |

And the empirical control agrees with the code in the one place it can: `q:mbqi-quick`
is the rung that decides the one file this slice decides.

## Step 3 — the constant, and two reasons it is the wrong lever

### 3a. The divisor does not bound the probe

`probe_budget` grants the probe `remaining/UFBV_ONLINE_PROBE_SHARE`. On this
population `forall-exists-witness` and `finite-expansion` cost ~0 ms, so
remaining at the probe's entry is ~24 000 ms and the grant is ~**12 000 ms**.

Measured spend against that grant:

| file | probe spend | % of grant |
|---|---:|---:|
| f18 | 19 478 ms | **162.3%** |
| f32 | 19 301 ms | 160.8% |
| f11 | 17 798 ms | 148.3% |
| f07 | 17 717 ms | 147.6% |
| f02 | 17 630 ms | 146.9% |
| f05 | 15 853 ms | 132.1% |
| f20 | 14 906 ms | 124.2% |
| f10 | 14 871 ms | 123.9% |
| f15 / f31 / f21 / f29 / f27 | 12 025 – 12 479 ms | 100.2 – 104.0% |

**13 of 32 files overrun the grant, 8 of them by more than 20%.** The five files
sitting at 100.2–104.0% are the slice firing as documented; the eight above
124% are the rung not honouring it. A non-preemptible round inside
`find_uf_finite_model` runs past the shared deadline — the same shape the
2026-09-06 census recorded for the whole ladder (6 of 32 files overshoot their
budget; one ran 62 866 ms of a 24 000 ms budget).

So halving the fraction does not halve the spend on the files where the spend is
worst. **A constant that is already being exceeded by up to 7.5 s is not the
thing bounding this rung**, and tuning it is treating the wrong cause.

### 3b. The constant is shared, and its name and doc comment are wrong

`UFBV_ONLINE_PROBE_SHARE` (`auto.rs:4138`) is reached through `probe_budget`,
which has exactly **two** call sites:

| call site | route it budgets |
|---|---|
| `auto.rs:390` | the pure-UF finite-model **probe** in `finish_quantified_solve` |
| `auto.rs:4295` | `dispatch_uf_arith_online` — the **QF_UFLIA / QF_UFLRA** online probe |

**Neither is a QF_UFBV route.** `dispatch_ufbv_online` (`auto.rs:3998`), the
route the constant is named for, passes `config` through unsliced and never
calls `probe_budget`. The name and the doc comment describe a consumer that does
not exist.

This is drift with a date: the FMF probe borrowed `probe_budget` in `c36e3ee33`
(2026-07-31); the helper was given this name and doc comment in `aaa5c2862`
(2026-09-08), six weeks later, when it already had two unrelated consumers.

The second consumer matters. `dispatch_uf_arith_online` is the route named in
`UF_ARITH_LADDER_RESERVE_SHARE`'s **dated** justification
(`config_registry.rs`, `docs/research/12-performance/uf-arith-overbound-2026-09-08.md`)
as the one its +9 QF_UFLIA files are decided by. Changing
`UFBV_ONLINE_PROBE_SHARE` for a UF reason changes that route's probe budget too,
silently, and the +9 measurement does not cover the new value.

**So even if a retune were warranted, it could not be done on this constant.**
The helper has to be split into one constant per consumer first — a mechanical
change, but a prerequisite, not an afterthought.

### The sibling constants with the same defect

The item asked for other constants whose doc comments admit they are unmeasured.
`config_registry.rs` makes this checkable rather than a grep: every entry carries
`justification: dated(...)` or `undated("doc comment")`. The quantified ladder's
three budget splitters are **all** `undated`, and they compose multiplicatively
above the rung that decides:

| constant | value | what it divides |
|---|---:|---|
| `UFBV_ONLINE_PROBE_SHARE` | 2 | the probe takes half before any refuter |
| `MBQI_FIRST_REFUSAL_SHARE` | 8 | `mbqi-quick` gets 1/8 of what is left |
| `QINST_EGRAPH_RETRY_SHARE` | 2 | the skolemized e-graph retry gets half of *that* |

On a 24 000 ms budget that chain is 2 × 8 × 2 = **32x**: the rung that produced
this slice's only `unsat` was handed **746.8 ms**. The arithmetic is confirmed
exactly by `AXEYUM_QPROBE` on `f27`:
`QPROBE skolemized-egraph(exhausted) budget=Some(746.8ms) elapsed=107.8ms result=unsat`.

## Step 4 — the outcome, measured on verdicts

*(Populations, arms and results: filled in below once the A/B completed.)*

## Reproducing

```sh
scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli \
  --features axeyum-solver/full
AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 taskset -c 0-7 \
  ./target/release/examples/smtcomp_cli <file> --timeout-ms 24000 --trace
```

Instrument A is the `; route-trail` JSON line's per-attempt `elapsed_ns`;
instrument B is the `[qtrace]` stderr lines, differenced under the three clock
conventions above. The scripts live in this session's scratchpad and are not
committed; they are ~80 lines of parsing over those two outputs and the
conventions they must respect are written out in §Step 1 so they can be
re-derived rather than trusted.

The A/B arms need one measurement-only patch, which makes the divisor settable
without changing the shipped default:

```rust
// crates/axeyum-solver/src/auto.rs, fn probe_budget
let divisor: u32 = std::env::var("AXEYUM_UF_FMF_PROBE_DIVISOR")
    .ok().and_then(|v| v.parse().ok()).filter(|d| *d > 0)
    .unwrap_or(UFBV_ONLINE_PROBE_SHARE);
LadderSlice::fraction("ufbv-online-probe", divisor).apply(config, config.timeout)
```

This is the same knob, and the same environment-variable name, as
`bench-results/parity-losses-20260906/measurement-patch-probe-divisor.py`. That
committed script's anchor is **stale** — `probe_budget` was refactored onto
`LadderSlice` in `aaa5c2862` — so it asserts and stops rather than mis-patching.

## What was not measured

- **Where inside `find_uf_finite_model` the probe's time goes.** There is no
  qtrace inside `uf_fmf`, so the 42.4% is attributed at the rung boundary only.
  Unchanged from the 2026-09-06 census, which recorded the same gap.
- **The source of the deadline overrun in finding 4.** Established that the rung
  exceeds its grant by up to 62%; *not* established which non-preemptible call
  inside it does so.
- **Whether contention moved the shares.** Runs were 4-wide at load 19.5 → 12.5,
  not idle. Shares are ratios and the two instruments agree on the ordering, but
  the absolute milliseconds are not comparable to an idle-host measurement.
