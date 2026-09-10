# Where the UF clock goes, and why the probe divisor is not the lever

> **UPDATE 2026-09-10 — the instrument this note audits is now fixed
> (ADR-1906, commit `72a5adf6f`).** Instrument A no longer conflates MBQI with
> the full finite-model finder, so the `23.2% q:uf-fmf-full` / `0.0% q:mbqi` /
> `63.3%` figures below are historical readings of the defective instrument,
> which is exactly how this note already presents them. **Nothing here is
> withdrawn.** The 52.4% and 42.4% are instrument-B (`AXEYUM_QTRACE`) numbers
> and were never contaminated by this defect.
>
> One caution for anyone quoting across the two: a re-derivation on the repaired
> instrument A reads **38.4%** for `probe + full`, against this note's
> instrument-B **52.4%**. The gap is almost entirely the **probe** term — a rung
> the fix does not touch — so it is between-run and between-denominator
> variation, not a further correction. 56.2 / 52.4 / 38.4 are three measurements
> of three slightly different quantities, not a chain of corrections of one.
> [`route-trail-mbqi-attribution-fixed-2026-09-10.md`](route-trail-mbqi-attribution-fixed-2026-09-10.md).

Measured 2026-09-10 on `s4` at `8c8671d7f` (+ a measurement-only patch, §Reproducing),
`taskset -c 0-7`, 4-wide. Load 19.5 → 12.5 for the attribution sweep and 4.7 →
10.3 across the six A/B arms — a shared box, not an idle one, so the wall-clock
absolutes here are not comparable to an idle-host run and are read only against
each other. Population: the 32 files in
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
| 6 | Budget utilisation at the rung that *can* refute is **not** evidence for reallocation: 39 of 55 invocations use ≥90% of their slice, but the e-graph loop **saturates by design**, so that is its behaviour at any budget. The A/B confirms it — doubling the pool decides nothing more. |
| 7 | **The retune is refuted at its own ceiling.** With the probe effectively off the 32 losses decide the same single file, while the 24 files only we solve lose one and go from 19.8 s to 241.6 s PAR-2. **DO NOT BUILD.** |

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
Its coverage against the route summary reads 100.0%, and that number is
**vacuous**: the summary's `total_ms` *is* `RouteTrace::total_elapsed()`, the sum
of the very per-attempt durations being checked. A coverage figure computed from
the instrument it is checking cannot fail, so it validates nothing here — it is
instrument B's coverage, against a denominator A produced, that is the real
check.

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
This is a genuinely separate instrument — stderr stamps from `qtrace`, not the
`RouteTrace` — so its coverage against the summary's total can fail, and did:
the first version of the parser read **247%** before the three clock conventions
below were kept apart. It now reads **112.4%**; the residual 12 points are the
ladder's `t0` starting before the summary's clock, not unattributed work.

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

The coverage figure is what caught it — but only because it was computed across
two instruments. An attribution that does not print its own coverage cannot
distinguish "these are the shares" from "these are the shares of the part I
explained"; one that prints a coverage derived from itself, as A's is, prints a
number that is guaranteed to look right.

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
| `q:mbqi-quick` | `auto.rs:4251-4259` | `Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat))` |
| `q:egraph` | `auto.rs:277-284` | `Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat))` |
| `q:mbqi` | `auto.rs:445`, `other =>` arm | `prove_unsat_by_mbqi`'s `Unsat` falls into `other` and is returned |
| `q:finite-expansion` | `auto.rs:517-527` | `check_with_quantifiers`'s non-`Unknown` result is returned unchanged |
| `q:forall-exists-witness` | `auto.rs:330-341` | returns the pass's own `CheckResult` |
| `q:nat-induction` | `auto.rs:925` | `qtrace("nat-induction", t0, "unsat")` on a refutation |

And the empirical control agrees with the code in the one place it can: `q:mbqi-quick`
is the rung that decides the one file this slice decides.

## Step 3 — the constant, and two reasons it is the wrong lever

### 3a. The divisor does not bound the probe

`probe_budget` grants the probe `remaining/UFBV_ONLINE_PROBE_SHARE`. The grant
is therefore ~**12 000 ms** of a 24 000 ms budget — not by assumption: the two
rungs above the probe both stamp `+0.000s` on every file, so remaining at the
probe's entry is the full budget. (`forall-exists-witness +0.000s`,
`finite-expansion +0.000s`, then `uf-fmf-probe +19.478s` on `f18`.)

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
123% are the rung not honouring it. A non-preemptible round inside
`find_uf_finite_model` runs past the shared deadline — the same shape the
2026-09-06 census recorded for the whole ladder (6 of 32 files overshoot their
budget; one ran 62 866 ms of a 24 000 ms budget).

So halving the fraction does not halve the spend on the files where the spend is
worst. **A constant that is already being exceeded by up to 7.5 s is not the
thing bounding this rung**, and tuning it is treating the wrong cause.

### 3b. The constant is shared, and its name and doc comment are wrong

*Line numbers and names in this subsection are the tree **as measured**, before
the split this note ships (§What was shipped). `UFBV_ONLINE_PROBE_SHARE`,
`UFBV_ONLINE_PROBE_SLICE` and `fn probe_budget` no longer exist at `8c8671d7f`+.*

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

Two populations, because a reallocation is a transfer and only one of them can
show what it costs:

- **gain side** — the 32 `UF` parity losses, all but two declared `unsat`;
- **cost side** — the 24 files in
  [`bench-results/parity-losses-20260906/UF.axeyum-only24.txt`](../../../bench-results/parity-losses-20260906/UF.axeyum-only24.txt),
  the UF files **only we** solve. 22 of them are `sat` and the finite-model
  finder is what decides them, so they are the population that pays for any
  clock taken off it.

Both are the populations the 2026-09-06 lever test used, so these numbers are
comparable to that one rather than to a fresh construction.

### Arms, and the two controls

One binary, the divisor read from `AXEYUM_UF_FMF_PROBE_DIVISOR`.

- **Inert at the shipped value.** The patched binary with the variable unset
  reproduces the unpatched binary on `f27` — `unsat`, `decided_by=q:mbqi-quick`,
  probe 12 036 ms against 12 028 ms — and on the whole 32-file population:
  1/32 decided, PAR-2 1500.1 s in both.
- **The knob fires.** At divisor 1 000 000 the probe goes 12 036 ms → 1.2 ms.

`probe-off` (divisor 1 000 000, the probe clamped to `MIN_LADDER_SLICE` = 1 ms)
is not simply a third sample. **It is the ceiling.** Every divisor larger than 2
hands the refutation family strictly *less* extra clock than turning the probe
off does. So whatever `probe-off` fails to gain, no value of this constant can
gain.

### Results

| population | arm | decided | PAR-2 (s) | wall (s) |
|---|---|---:|---:|---:|
| **32 losses** | `d2` (shipped) | **1/32** | 1500.1 | 695.8 |
| | `d16` | **1/32** | 1489.7 | 679.5 |
| | `probe-off` (ceiling) | **1/32** | 1488.1 | 686.9 |
| **24 wins** | `d2` (shipped) | **24/24** | 19.8 | 19.8 |
| | `d16` | **24/24** | 36.1 | 36.1 |
| | `probe-off` (ceiling) | **23/24** | 241.6 | 218.6 |

Verdict-set diffs against the shipped arm, rather than a count that could hide
an offsetting swap: on the losses both arms gained `[]` and lost `[]`; on the
wins `d16` gained `[]` / lost `[]` and `probe-off` lost `f03`.

Summed over both populations, PAR-2 is **1519.9 s** (`d2`) → **1525.8 s**
(`d16`) → **1729.7 s** (`probe-off`): monotonically worse the more clock is
moved. No arm on either population produced a verdict contradicting a declared
`:status`.

### What the numbers say

**The gain side is empty, and the freed clock is absorbed rather than saved.**
`d16` hands the refutation family back ~10.5 s of a 24 s budget on most files
and decides the same single file; the ceiling arm hands back ~12 s and also
decides the same single file. Total wall moves 695.8 s → 679.5 s → 686.9 s —
under 3%, and not monotonically.
The e-graph instantiation loop expands to fill whatever it is given — the
2026-09-06 census's "reliably consumes every second it is given" — so taking
time off the probe does not shorten an undecided file, it just moves which rung
spends it.

**The one measurable gain is latency on a file that already decides.** `f27`
goes 12 127 ms → 1 713 ms (`d16`) → 116 ms (`probe-off`). Its refutation is
~110 ms of work sitting behind a rung that spends 12 s and cannot refute. Under
the 24 s scoring protocol this is worth **zero** — the file is decided in every
arm.

**The cost side is real, and it is paid in the currency the gain is not.**
Turning the probe down does not turn finite model finding *off*; it **defers**
it, because `q:uf-fmf-full` is the same producer at a terminal placement. The
`decided_by` census shows the deferral directly:

| arm | how the 24 wins were decided |
|---|---|
| `d2` | 22 `sat` by `q:uf-fmf-probe`, 2 `unsat` by `q:mbqi-quick` |
| `d16` | 20 by `q:uf-fmf-probe`, **2 by `q:uf-fmf-full`**, 2 by `q:mbqi-quick` |
| `probe-off` | **21 by `q:uf-fmf-full`**, 2 by `q:mbqi-quick`, **1 undecided** |

So the code comment's rationale for the early placement — that a post-only
finder would be starved by refutation loops that consume their whole budget — is
**confirmed, not refuted**: at the ceiling, 21 of 22 `sat` verdicts survive the
deferral at 11x the wall clock, and one does not survive at all.

### Scope of the ceiling argument

`probe-off` bounds **this constant**. It does not bound
`MBQI_FIRST_REFUSAL_SHARE` or `QINST_EGRAPH_RETRY_SHARE`: doubling the pool the
whole family draws from changed nothing, which is a strong prior that the family
is not clock-limited, but those two constants change the *split within* the
family, and a split can matter when the pool size does not. They are identified
here as sharing the undated defect and are **not** retuned — retuning an
unmeasured constant on the strength of a measurement of a different one is the
error this note is about.

## Recommendation

**DO NOT BUILD the reallocation.** Four reasons, in the order that settles them
most cheaply:

1. **The gain side is empty at its own ceiling.** With the probe effectively
   off — strictly more clock than any larger divisor can give the refuters — the
   32 losses decide the same single file. This is a bound, not a sample.
2. **The cost side is measured on the population that pays.** `d16` doubles
   PAR-2 on the 24 wins (19.8 → 36.1 s); the ceiling arm costs a file outright
   and takes PAR-2 to 241.6 s.
3. **The divisor is not what bounds the rung.** It grants ~12 000 ms and the
   probe spends up to 19 478 ms — 162% of its grant — on 13 of 32 files.
4. **The constant could not be retuned alone even if it should be.** It was
   shared with `dispatch_uf_arith_online`, the route a *dated* +9-file QF_UFLIA
   measurement rests on.

This reproduces the 2026-09-06 lever test's conclusion on a tree that has since
gained `318930806` — the e-matching routing fix that took this slice from 0 to
1 decided. That fix is the reason the question was worth re-asking: it made a
refutation route reachable that the earlier arms never exercised. Re-run, the
answer is the same, and it is now the same on a ladder that can actually refute
one of these files.

### What this measurement does support

**Only one thing, and it is not a policy change: the probe overruns its own
deadline by up to 7.5 s (finding 4).** That is clock recoverable without
changing any share, on the files where the waste is worst, and it does not touch
the sat-side capability the arms above show is load-bearing. Establishing which
non-preemptible call inside `find_uf_finite_model` runs past the shared deadline
is the follow-up this note supports. It was not built here.

### What was shipped

Only the hygiene finding 5 forces: `UFBV_ONLINE_PROBE_SHARE` is split into
`UF_FMF_PROBE_SHARE` and `UF_ARITH_ONLINE_PROBE_SHARE`, **both keeping the value
2**, so no verdict moves. The `LadderSlice` route labels go with them
(`ufbv-online-probe` → `uf-fmf-probe` / `uf-arith-online-probe`); those labels
are documentation-only and appear in no `record_*` call, which this measurement
confirms empirically — `ufbv-online-probe` appears in none of the 20 route names
across 32 traced files. (That settles, for this label, open question 2 of
`docs/solver-inventory-2026-09/03-dispatch-routing-and-backends.md`, which had
it as `[unverified]`.) The registry gains a `dated` row for the FMF probe
carrying this measurement, and the arith row stays **undated** — its route was
never measured here.

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
// crates/axeyum-solver/src/auto.rs, fn uf_fmf_probe_budget
// (`fn probe_budget` at the time these arms were run -- see §What was shipped)
let divisor: u32 = std::env::var("AXEYUM_UF_FMF_PROBE_DIVISOR")
    .ok().and_then(|v| v.parse().ok()).filter(|d| *d > 0)
    .unwrap_or(UF_FMF_PROBE_SHARE);
LadderSlice::fraction("uf-fmf-probe", divisor).apply(config, config.timeout)
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
- **Whether contention moved the shares.** Runs were 4-wide on a shared box, not
  idle. Shares are ratios and the two instruments agree on the ordering, but the
  absolute milliseconds are not comparable to an idle-host measurement. The
  verdict counts, which are what the recommendation rests on, are robust to it.
- **Arm interleaving.** The six arms ran back to back, not interleaved per file
  the way the 2026-09-06 lever test ran its arms, so each arm saw a slightly
  different load (4.7–10.3). This is why the wall column is read as "did the
  freed clock get saved" and not as a precise per-arm cost.
- **Any budget other than 24 000 ms.** `f27`'s refutation is ~110 ms sitting
  behind a rung that spends 12 s, so there is presumably a budget band below
  which the probe costs that verdict rather than only its latency. The band was
  **not** measured; every arm here is at 24 s, the budget the loss list was cut
  at. Nothing in this note says what happens at a tighter one.
- **`MBQI_FIRST_REFUSAL_SHARE` and `QINST_EGRAPH_RETRY_SHARE`.** Identified as
  sharing the undated defect and left alone; see §Scope of the ceiling argument
  for why the ceiling arm does not bound them.
- **Population B and the other 7 558 UF files.** Everything here is the 32
  losses and the 24 axeyum-only wins.
