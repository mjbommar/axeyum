# ADR-2045: the bound is not the wall — `QF_LRA` is one offline dense engine, and the knob that reaches it hands one construction the whole process

Status: accepted
Index-summary: `QF_LRA` is fully decidable and we ship a simplex, so a 59-file board gap was a signal, not a research problem. Population **re-derived** (200 files, 107/93, reproducing the board's 107 exactly; `--trace` perturbs **0 rows**). **Two give-up labels had to be split and BOTH were wrong as written**: `kind=Timeout` is a relabel whose detail *contains* `;` ([ADR-2020]'s trap), and `lra.rs:159`'s `"Fourier–Motzkin … exceeded the … budget"` is ONE string for every `Decision::TimedOut` out of `decide_within` (overflow, deadline, simplex, elimination) — **34 of 34 rows carrying it have `cube_matrices=0` and `cube_simplex_calls>0`; Fourier–Motzkin never ran**. The 40 remaining rows **abort with no give-up line at all** (stderr only), so a census on the give-up string alone loses the largest bucket; the runner captures four channels. Result: **74 of 93 undecided rows are ONE route**, the offline dense-matrix LRA engine — 40 aborting on its allocation, 34 exhausting the clock — at a **5.07 GiB median peak RSS, 51 of 93 over 4 GiB**. Cause: the harness bounds memory with `ulimit -v 8G` and the solver cannot see it, so `fm_admission`/`simplex_admission` open with `current_limit_bytes()?` and **do not screen at all**; a which-matrix probe (`cube_simplex_ms=46356`, `cube_matrices=0`, 11.50 GiB) shows the **dense simplex tableau** is the allocator, **correcting `lra_online.rs`'s own doc**, which still attributes that exact file's bytes to FM's Farkas matrix from a stack sample taken the day `simplex_first` shipped. z3 decides one such file (25,273 asserts) at `:arith-max-rows 334`, `:max-memory 52.92` MB, re-solving incrementally 77,779 times: **it never materialises the system**. The lever — telling the solver the limit the harness already enforces, ONE BINARY under TWO ENV VALUES, proved live **by mechanism** (the refusal is formatted from the value: `memory_limit_mb 8192` vs `2048`) — is **net +0, 0 gains, 0 losses, 0 flips** at a **row-level noise floor of 0 of 200** over two identical passes, with soundness 0 disagreements at a **194** denominator; **0 movers, so the mover recheck and authority check have a comparable denominator of 0**, printed. An ordered probe ([ADR-2030]'s distinction) on the 24 admission-screen rows: **0 still refused, 21 REACH the engine, 0 newly decided** — **the bound is not the wall**; 19 die at `"model did not replay (arithmetic outside the incremental engine)"`. **The arm CAUSES five new aborts**: one knob drives two screens wanting opposite settings, so the online construction's budget jumps 640 MiB → 8 GiB and it peaks at **8.02-8.05 GiB against an 8.00 GiB ceiling** — 640 MiB was a *fraction* of a process budget and 8 GiB is the *whole* one. Pre-registered R8 was ≥ +5, so **the lever ships `Off`**, and R10's second falsifier is what fired — half of it: the 20 abort rows that ARE addressable get converted from core dump to first-class `unknown`, the ladder below runs, and **not one is decided**. Re-sizing: **the first reference pass was wrong in exactly the direction its own caveat predicted** — six concurrent shards on s4 read z3 = 155 against the board's 166, and re-taking the 43 "decided by nobody" rows on IDLE hosts decides **11**, giving **z3 = 166 and gap = 59 to the file**, so the published figures are **61 addressable / 32 nobody** and not the 50/43 the loaded pass would have printed (a **"decided by nobody" claim measured under load is not evidence**). **50 of the 61 addressable rows — 82 % — are that one offline dense engine.** Control and exposure divisions **NOT RUN** and reported as such: they gated shipping `On`. Two unpriced allocations are left named for the next lane, neither needing a config change: `simplex::MAX_TABLEAU_CELLS` is not consulted by `feasible_within`, and `lra.rs:944` builds an `n × nvars` dense matrix that `Tableau::new` immediately re-sparsifies.
Index-status: accepted
Date: 2026-09-14

## Context

`QF_LRA` on the canonical 200-file board reads ours 107 against z3 166 and cvc5
145. Linear real arithmetic is **fully decidable** and we ship a simplex, so a
gap that size is not a research problem — it is a signal that something
structural is wrong. Nobody had worked this division in this session.

Branch base: `git merge-base main HEAD` is
`cfcae7fa78bbc8297ccb62d8517895edb87d8c33`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/qflra-gap-20260914/PREREGISTRATION.md)
in their own commit (`9467f0780`) before the census aggregated and before any
lever existed.

Compute: **6 pinned pairs** — s5 `(0,8)`/`(1,9)`, s6 `(0,8)`/`(1,9)`,
s7 `(0,8)`/`(1,9)`. Two shards per host and not three, because this division's
undecided rows reach ~7.8 GiB each against 27 GiB hosts.

## 1. The census, and the two labels that had to be split first

Population **re-derived on the current tree** (R0 — [ADR-2035] found 8 of 22
inherited "declining" files were decided anyway): **200 files, 107 decided, 93
undecided**, reproducing the board's 107 exactly.

The census instrument is `--trace`, so its own effect was measured rather than
assumed: the trace arm and the plain arm ran back to back on the same file on
the same pinned core and both read **107, with 0 rows differing**.

**Only one of the four cause channels is a give-up string**, and building the
census on it alone would have lost the largest bucket outright:

| channel | what it carries |
|---|---|
| `; give-up kind=… detail=…` | the solver's own classified give-up |
| the verdict line | `sat` / `unsat` / `unknown` |
| the process exit status | `134` = abort, `124` = wall kill |
| **stderr** | an allocation failure prints **only** here, and emits **no give-up line at all** |

Two labels covered more than one site and were split before anything was
counted.

**`kind=Timeout` is a relabel.** `auto.rs` wraps a reduced solve's own reason as
`preprocessed dispatch timeout after reduced solve; the reduced solve's own
reason was [{kind}] {detail}` — and that detail **contains `;`**, the exact
[ADR-2020] separator trap. Counted as written, 43 rows would have read "ran out
of time". Split on the bracketed inner reason, the clock is almost never the
binding cause.

**`"lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget"` is
one string at `lra.rs:159` standing for every `Decision::TimedOut` reaching it
out of `decide_within`.** There are **six** such producers, and only one of them
is the elimination:

| site | what actually happened |
|---|---|
| `lra.rs:574` | deadline on **entry**, before collection — nothing ran at all |
| `lra.rs:588` | collection declined **and** the clock had expired |
| `lra.rs:608` | **`ctx.overflow` — an `i128` overflow, not a timeout of any kind** |
| `lra.rs:697` | deadline inside the `unit_vec` multiplier loop — **the only genuine Fourier–Motzkin site** |
| `lra.rs:840` | `simplex_after_elim` re-entered with `stages.simplex` already set |
| `lra.rs:853` | the **simplex** fallback declined |

So the sentence a reader gets names the wrong engine for four of the six, and
for `608` it names the wrong *kind of event* — the same shape as this
repository's own recorded gotcha, *"an error naming a node cap when the cause
was an `i128` overflow."*

Split on the engines' own counters (they are incremented by the engines, so they
cannot agree with a wrong guess): **34 of 34 rows wearing this label have
`cube_matrices=0` and `cube_simplex_calls>0`. Fourier–Motzkin never ran on any
of them.**

**The misattribution is not in the string. It is in the variant's own doc
comment**, which the string faithfully renders:

```rust
/// The Fourier–Motzkin elimination did not finish within the wall-clock /
/// size budget; the query is left undecided (a timely, sound `unknown`).
TimedOut,
```

`Decision::TimedOut` is named and documented as if it were the elimination's
verdict, and five of its six producers are not.

**Nothing in the workspace pins the rendered string** — no test, no gate, no
golden file (`grep -rn` over `crates/` and `tests/` returns only the
definition). So it was free to be wrong, and it is free to correct.

**And `Decision` already contains the pattern for the fix, applied twice.**
`Incomplete(String)` carries a detail; `OutOfMemory` was split off from
`TimedOut` with the explicit reason that *"the two demand opposite fixes and a
consumer must not have to guess."* The overflow at `lra.rs:608` is a third
instance of that same principle that nobody applied: it is not a clock at all.
So the fix is idiomatic here rather than novel — give `TimedOut` a detail in
`Incomplete`'s style, and stop routing `ctx.overflow` through it. **It is NOT
corrected in this lane** — see the Decision section for why.

The census after both splits:

| n | median ms | at ≥90% of budget | binding cause |
|---:|---:|---:|---|
| **40** | 7 143 | 1 | **process ABORT** — no verdict, no reason, core dump |
| **34** | 24 140 | 34 | **dense simplex spent the budget** (label says FM; FM never ran) |
| 7 | 24 038 | 7 | online CDCL(T) LRA model did not replay |
| 6 | 25 136 | 6 | watchdog fired before the worker returned |
| 3 | 4 918 | 0 | int↔real coercion relaxation |
| 1 | 25 437 | 1 | silent `unknown`, no give-up line |
| 1 | 24 031 | 1 | online CDCL(T) LRA driver timeout |
| 1 | 24 136 | 1 | lazy SMT wall-clock |

**74 of 93 (79.6 %) are one route** — the offline dense-matrix LRA engine, 40
aborting on its allocation and 34 exhausting the clock inside it.

Refusals against exhausted clocks (R2): **42 refusals (45.2 %, median 7.0 s of a
24 s budget) and 51 clocks (54.8 %)**. Peak resident set over the undecided:
**median 5.07 GiB, 51 of 93 rows over 4 GiB, max 7.46 GiB.**

## 2. Why it aborts: the harness bounds memory and the solver cannot see it

The board harness runs each file under `ulimit -v 8G`. It never passes
`--memory-limit-mb`. Both admission screens on this route open with

```rust
let budget = crate::memory_budget::current_limit_bytes()?;
```

— a `?` on an `Option`. With no limit installed, `WATCHDOG_LIMIT_BYTES` is 0,
`current_limit_bytes()` returns `None`, and `fm_admission`,
`simplex_admission` and the resident-set watchdog **do not screen at all**. The
process then allocates until `malloc` fails and aborts.

`unknown` is a first-class result and a Hard Rule here; an abort is not a result
at all, and `smtcomp_cli`'s own source already calls it *"strictly worse than
the first-class `unknown`"*.

## 3. Which matrix — measured, because the code's own doc names the wrong one

`lra_online.rs` attributes `_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2`'s bytes
to *"the **offline** Fourier–Motzkin route … `decide_within`'s `n x n` Farkas
multiplier matrix"*, from a 2026-09-08 stack sample. `simplex_first` shipped that
same day and put the simplex ahead of the elimination at
`SIMPLEX_FIRST_AT_CONSTRAINTS = 256`, so the attribution is now stale on the
very file it was written about.

Given 24 GiB of room so it can report rather than die, on that file:

```text
shipped route   cube_simplex_calls=10  cube_simplex_ms=46356  cube_matrices=0   peak 11.50 GiB
fm-first        (pre-2026-09-08 order)                                          peak 23.28 GiB
```

**The dense simplex tableau is the allocator. Fourier–Motzkin builds zero
matrices.** The elimination is worse still when forced to go first, which is why
`simplex_first` was right — but the bytes were never Fourier–Motzkin's.

Two structural facts behind that, both already true in the tree and neither
gated on a memory limit:

- `simplex::feasible_within` calls `Tableau::new` directly, and
  `reset_structure` allocates `vec![Rational::zero(); nvars + m]` **per row** —
  a dense `m × (nvars+m)` matrix. `simplex::MAX_TABLEAU_CELLS = 4_000_000`
  guards `Incremental::new` and **is not consulted on this path**, which the
  `simplex_admission` doc states outright.
- `lra.rs:944` materialises each sparse `LinExpr` (a `BTreeMap`) into
  `vec![Rational::zero(); nvars]`, and `Tableau::new`'s first act is
  `densify_to_sparse` on exactly that vector. The dense form exists **only to be
  re-sparsified**.

## 4. What the solver that succeeds does differently

z3's own `-st` statistics on `QF_LRA/2019-ezsmt/travellingSalesperson/
rand_80_340_1159656267_0.lp.smt2` — 25 273 asserts, 9 081 declarations, a file we
refuse at admission and then spend 24 s on in the dense engine:

```text
sat
 :arith-max-rows          334
 :arith-max-columns      1097
 :arith-make-feasible   77779
 :max-memory            52.92
```

**z3 never materialises the system.** Its tableau holds only the atoms currently
on the CDCL trail — 334 rows — and it re-solves incrementally 77 779 times at
53 MB. We hand the whole constraint set to one dense matrix and reach a 5.07 GiB
median.

That is the structural difference, and it says the remedy is not a bigger budget
for the dense engine. It is that the **incremental** engine should be taking
these queries.

## 5. The lever, its mechanism proof, and the measurement that refutes it

The incremental engine refuses them at an admission screen whose default
(`DEFAULT_ONLINE_LRA_BUDGET_BYTES = 640 MiB`) is calibrated to reproduce the
retired `MAX_ONLINE_LRA_ATOMS = 1_024` **exactly**, and that screen *moves with*
`SolverConfig::memory_limit_mb`. So the whole hypothesis is testable with **one
binary under two environment values and no build**: tell the solver the limit
the harness is already enforcing.

**The flag is live by mechanism, not by verdict count** — a silently-ignored
flag prints the same number. `lra::fm_admission` formats its refusal *from the
value*, so the digits cannot be produced any other way:

```text
UNSET        memory allocation of 626400 bytes failed          (rc=134, no give-up line)
=8192        … needs 10334 MiB …, over memory_limit_mb 8192 …  (clean MemoryLimit decline)
=2048        … needs 10334 MiB …, over memory_limit_mb 2048 …
```

### The A/B

Interleaved per file, arms back to back on the same file on the same pinned
core, order alternating, 6 pinned pairs, 24 s / 8 GiB. Polarity: **base = limit
UNSET (the board's configuration); arm = limit SET.**

```text
rows=200   base=107   arm=107   net=+0   gains=0  losses=0  flips=0
soundness vs declared :status, BOTH arms: comparable=194  disagreements=0
process ABORTS (rc=134): base 41 -> arm 9   (delta -32)
```

**Noise floor, measured and at ROW level** (R5 — a count can be stable while
rows move in both directions; [ADR-2030]'s 21.8 % was 10.2 % at row level): the
census's plain arm and the A/B's base arm are the identical configuration run ten
minutes apart with different neighbours, and they differ on **0 of 200 rows**,
with 0 verdict-identity flips. Three independent same-arm passes — board, census,
A/B base — all read 107. **So +0 is a real null, not two errors cancelling.**

There are **0 movers**, so the 3× mover recheck and the three-authority check
have an **empty subject and a comparable denominator of 0** — printed rather
than reported as a zero disagreement count. The soundness zero above is not
vacuous: its denominator is 194.

### Reached, or never reached? The distinction a verdict count cannot make

[ADR-2030] needed an ordered probe to separate "never reached the site" from
"reached it and came out the other side". Run on the **24** census rows the
screen had refused (`online_probe=admission-screen`):

| n | transition |
|---:|---|
| 19 | `admission-screen` → `model-did-not-replay` |
| 2 | `admission-screen` → `took` |
| 3 | `admission-screen` → died with no report |

**0 still refused. 21 reached the engine. 0 newly decided.**

The bound is **not** the wall. The lever clears the screen completely and buys
nothing, because the engine behind it cannot reconstruct a model that replays —
`"arithmetic outside the incremental engine"`.

### The finding the verdict count hides: the arm CAUSES five aborts

Nine rows still abort in the arm, all `LassoRanker`, and **five of them exited
cleanly in the base**. Mechanism, with 24 GiB of room so both arms can report:

```text
base(UNSET)   online_probe=admission-screen     peak 5.10 - 6.90 GiB   unknown
arm(8192)     online_probe=model-did-not-replay peak 8.02 - 8.05 GiB   unknown
```

(Three of the five probed; `/usr/bin/time`'s figure is KiB, so these are **GiB**
and directly comparable to the ceiling — an earlier draft of this ADR rendered
them as "GB" beside a "GiB" limit, which is the one comparison in the document
that has to be exact.)

The harness ceiling is **8.00 GiB**, so the arm lands 0.02–0.05 GiB *over* it.
See the Decision section for the mechanism and for why this is recorded as a
**loss** rather than as part of the `+0`.

## 6. Re-sizing the prize: the dramatic bucket is not the valuable one

References re-run on the same files at the same budget (R3). `z3 -T:` SECONDS,
`cvc5 --tlimit` MILLISECONDS.

**The first pass was wrong and its own caveat caught it.** It ran six concurrent
shards on s4 and read z3 = **155** against the canonical board's 166. Load can
only make a deadline-bounded solver decide *fewer* files, so that pass
understates addressability — and the rows it understates are exactly the ones it
calls "decided by nobody", which is the most confident sentence in the whole
report. So those 43 rows were re-taken on **idle hosts, one pinned pair each**:
**11 of 43 are decided by z3 after all**, every one of them `LassoRanker`.

That re-take closes the loop exactly: 155 + 11 = **166**, reproducing the
canonical board's z3 figure to the file, and the gap becomes **59** — the number
this lane was briefed with. The merged figures (best verdict per file per
solver, which is the right rule for an addressability question and the wrong one
for a head-to-head score, so they are used only for sizing):

| | decided of 200 |
|---|---:|
| ours | 107 |
| z3 | **166** |
| cvc5 | 126 |
| best-of-two | **166** |
| **gap to best** | **59** |

Reference against declared `:status`: **comparable = 271, disagreements = 0.**

Of our 93 undecided rows, **61 are addressable** and **32 are decided by
nobody**. Crossed against the census cause — this is the number that sizes the
work:

| addressable | nobody | bucket |
|---:|---:|---|
| **30** | 5 | **`Timeout/ResourceLimit`** — 34 dense simplex + 1 lazy-SMT wall-clock |
| **20** | 20 | **process ABORT** |
| 4 | 2 | watchdog |
| 3 | 4 | online LRA model did not replay |
| 3 | 0 | int↔real coercion |
| 1 | 0 | online LRA driver timeout |
| 0 | 1 | silent |

**50 of the 61 addressable rows — 82 % — are the offline dense-matrix engine**
(30 exhausting its clock, 20 aborting on its allocation). Half the abort bucket
is decided by nobody, so it is worth 20 rather than the 40 its size suggests;
but with the re-take folded in it is no longer the cheap half of the story, and
both halves lead to the same engine.

## Decision

**The lever ships `Off`. No code change is made.**

Pre-registered R8 required net **≥ +5** with 0 losses and 0 flips. The measured
net is **+0**, against a measured row-level noise floor of **0 of 200**.

### The lever is not neutral. It is a LOSS.

Stated on its own rather than folded into the `+0`, because a lever that costs
nothing in verdicts and destabilises five files is **worse than doing nothing**,
and the verdict column is exactly where that does not show:

> **Five files that terminate cleanly in the base ABORT under the arm.**
> `Gcd.bpl_Iteration1_Lasso_7`, `collatz.t2.c_Iteration3_Loop_7`,
> `matrixsqrt.t2.c_Iteration12_Loop_7`,
> `NoriSharma-2013FSE-Fig8…_Iteration1_Loop_5`,
> `Lobnya-Boolean-Reordered.bpl_Iteration1_Lasso_7` — all `LassoRanker`.

**Mechanism**, measured with 24 GiB of room so both arms can report rather than
die:

| arm | the screen's own report | peak RSS |
|---|---|---:|
| base (UNSET) | `online_probe=admission-screen` | 5.10 – 6.90 GiB |
| arm (8192) | `online_probe=model-did-not-replay` | **8.02 – 8.05 GiB** |

The harness ceiling is **8.00 GiB**. The arm ends up 0.02–0.05 GiB *over* it, so
these die on allocation. The cause is that **one knob drives two screens that
want opposite settings**: `memory_limit_mb` is what makes the offline screens
bind, which is the intent — but `NormalizationLimits::for_budget` reads the
*same* number, so the online construction's budget jumps 640 MiB → 8 GiB. 640 MiB
was a **fraction** of a process budget; 8 GiB is the **entire** process ceiling,
leaving nothing for the arena, the Boolean skeleton and the CNF the process is
already holding. The construction then grows into the space its own budget told
it was free.

These five are `unknown` in both arms, so R8's `losses=0` is correct as a
verdict count **and** misses this entirely. That is the reason the exit-status
channel is carried through the whole census rather than just the verdict.

R10's second falsifier is the one that fired — *"if the abort rows are ones no
reference solver decides, converting them to `unknown` buys zero board files and
R8 fails by construction"* — and **half of it holds**: 20 of the 40 abort rows
are decided by nobody. The other half is a sharper negative, established by the
**A/B** (not by the reach probe, which ran on the admission-screen rows and not
on these): the remaining 20 abort rows **are** addressable, the lever **does**
convert them from a core dump into a first-class `unknown`, the ladder below
then runs — and since the A/B's net is +0 over all 200 rows, **not one of them
is decided**. Converting the abort is necessary and nowhere near sufficient; the
engine behind the screen is the wall.

R9's correctness claim was pre-registered **separately**, so that a null R8 could
neither be retro-fitted into a win nor used to dismiss a real defect. It stands
on its own and is **reported, not shipped**: on the board's own configuration
this division takes **41 process aborts in 200 files**, each producing no
verdict, no reason and a core dump where the solver could have declined in good
order. That is a defect whether or not it is worth a board file.

It is reported rather than fixed because **the obvious fix is measured here and
is wrong**: auto-installing the process's own limit (readable in safe Rust from
`/proc/self/limits`) clears **37 of the 41** base aborts, leaves 4 standing, and
**creates 5 new ones** — 41 → 9 — because the same number then becomes one
construction's budget. Any future lane doing this must give per-construction
budgets a **fraction** of the process limit, and must re-measure the
`LassoRanker` family specifically: all 9 residual aborts are from it.

The pre-registered **control** (`QF_S`) and **exposure** (`QF_BV`) divisions were
**NOT RUN**. They were conditions on shipping `On`; with the subject division at
+0 the lever ships `Off`, neither can change that decision, and no exposure is
taken. Reported as *did not run* rather than as zeros that were never measured.

## Consequences — what the next lane on this division should do

Ranked by the addressability crosstab, not by bucket size:

1. **The offline dense engine is the whole division.** **50 of the 61
   addressable rows — 82 % — are bound by it.** Two unpriced allocations sit on
   that path independently of any memory limit:
   `simplex::MAX_TABLEAU_CELLS = 4_000_000` is not consulted by
   `feasible_within`, and `lra.rs:944` builds an `n × nvars` dense matrix that
   `Tableau::new` immediately re-sparsifies. Neither needs a config change to
   fix.
2. **The named capability wall is model reconstruction, not admission.** 19 of
   21 rows that reach the online engine die at
   `"online CDCL(T) LRA model did not replay (arithmetic outside the incremental
   engine)"`. That sentence names the work.
3. **Do not size this division off the abort bucket alone.** It is the most
   visible and exactly half of it is decided by nobody — and the half that is
   addressable is still not converted by removing the abort, which the reach
   probe shows directly.
4. **`lra.rs:159`'s give-up string names the wrong engine on every row that
   carries it here**, because `Decision::TimedOut`'s own doc comment does. Any
   future census that reads it as written will attribute simplex cost to
   Fourier–Motzkin, as this one nearly did.

   **Why this lane did not fix it**, stated so the next one does not have to
   re-derive the judgement: it is a *two-part* change, not a string swap — give
   `TimedOut` a detail in `Incomplete(String)`'s style, **and** stop routing
   `ctx.overflow` (`lra.rs:608`) through a timeout variant at all. The second
   half is a correctness-of-diagnosis fix touching a soundness-adjacent path,
   and it deserves its own verification rather than being appended to a lane
   whose entire diff is otherwise **zero Rust files**. Renaming the string
   alone would leave `608` still reporting an `i128` overflow as a clock — a
   half-fix that reads as a whole one, which is the failure mode this ADR is
   about.

## Measurement caveats, stated rather than discovered

- **The A/B arm measures THIS BRANCH**, which is `main` at `cfcae7fa7` plus
  documentation and harness only — no solver code is touched. The post-merge
  value is therefore predicted to be **identical**, and the reason is that the
  lever is an environment variable the shipped binary already reads.
- **The first reference pass was materially wrong, and saying so is the
  point.** It ran on s4 under its own six concurrent shards and read z3 = 155
  where the canonical board reads 166, which would have published **50
  addressable / 43 decided by nobody** and an abort bucket "worth at most 11".
  Re-taken on idle hosts, **11 of those 43 decide**, and the corrected figures
  are 61 / 32 with the abort bucket worth 20. The error was **entirely in the
  direction the caveat predicted** — load cannot make a deadline-bounded solver
  decide more — which is why the re-take was run before publishing rather than
  offered as a hedge. Raw rows:
  `bench-results/qflra-gap-20260914/NOBODY_RECHECK.txt`.
  **A "decided by nobody" claim measured under load is not evidence**, and this
  is the second time this week a sizing number moved by a third for a reason
  that had nothing to do with the subject.
- **The merged reference figures take the best verdict per file per solver.**
  That is the correct rule for "can any reference decide this at this budget?"
  and the **wrong** rule for a head-to-head score, so they size the work here and
  are not a board row.
- `--trace` was shown not to perturb the population (0 of 200 rows), so the
  census's causes and the A/B's counts are on the same footing.
