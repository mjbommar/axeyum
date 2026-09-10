# Roadmap 3.4 measured: the LIA node cap costs us no verdict we can find

Measured 2026-09-10 on `s4`, based on `origin/main` at `474423c8d`. Roadmap item
3.4 ([`11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
proposes replacing our in-theory branch-and-bound with **branching as a lemma to
the SAT solver**, as Yices2, OpenSMT and SMTInterpol all do, and names the gate:

> Count `unknown` verdicts on `QF_LIA` public corpora attributable to the cap.

**The count is 0 of 911 benchmarks across three populations**, including the
full committed regression corpus and a 666-file sample of SMT-LIB 2024's own
`QF_LIA`. Recommendation: **DO NOT BUILD.**

Three things came out of the measurement that are worth more than the zero:

1. **The cap cannot be the thing that stops us, because it is not reachable.**
   Measured node rate on a deliberately cap-forcing *two-variable* instance:
   **686 nodes in 20 s**. At that rate the 50,000-node cap needs ~24 minutes and
   the deadline-relaxed 20,000,000-node cap needs ~6.8 days — and the rate falls
   with depth, so both are lower bounds. Every `unknown` we actually produce
   comes from a wall clock, an admission bound, or an `i128` overflow, long
   before the node counter matters.
2. **A correction.** Two planning documents say three QF_LIA parity losses are
   "branch-and-bound node-cap incompleteness". The census row they cite says, in
   its own `detail` field, `wall-clock deadline passed (node cap 20000000)` — the
   deadline fired and the cap was never approached. Details in §5.
3. **The cap is not distinguishable at the API, and on two of three routes it is
   erased entirely.** This is a real defect and it is cheap to fix; §4.

## 1. What the discriminator actually is

The brief for this item asked for the real discriminator rather than a substring
guess. Reading it out of the source:

`lra.rs:1721` builds every branch-and-bound `unknown`:

```rust
fn lia_bnb_undecided(cause: &'static str, node_cap: u64) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("QF_LIA branch-and-bound undecided: {cause} (node cap {node_cap})"),
    })
}
```

So `UnknownKind` is **always `Incomplete`** and carries no information: the node
cap, the wall-clock deadline, an `i128` overflow and an out-of-range branch
constant are one kind. The four `cause` strings (`lra.rs:2278`, `:2281`, `:2289`,
`:2305`) are the only textual discriminator, and only one of them is the cap:

| `cause` | the stop that fired |
|---|---|
| `node budget exhausted` | **the cap** — `*budget == 0` |
| `wall-clock deadline passed` | the caller's `SolverConfig::timeout` |
| `exact-rational simplex declined (i128 overflow or iteration backstop)` | item 2.3's boundary |
| `branch constant out of i128 range` | a colossal fractional coordinate |

The structural discriminator, independent of prose, is
`LiaCounters::bnb_budget_exhausted`, recorded once per branch-and-bound root at
`lra.rs:1943`:

```rust
lia_counters::record_bnb(node_cap.saturating_sub(budget), budget == 0);
```

and `budget == 0` is exactly the condition of the `node budget exhausted` return.
**Both were used below, and they agree on every population.** The counter is the
load-bearing one, for the reason in §4.

Which cap is in force is decided by `lia_bnb_node_cap` (`lra.rs:1737`) from
`deadline.is_some()` alone: **50,000 without a wall clock, 20,000,000 with one.**
That matters for reading the numbers below, because the committed `:status` sweep
(`corpus_regression.rs:81`–`:109`) uses `SolverConfig::default()`, whose `timeout`
is `None` (`backend.rs:383`) — so the committed gate runs under the **tight**
cap, and the parity runs under the loose one. Both were measured.

## 2. Method

A throwaway probe, `crates/axeyum-bench/examples/lia_cap_probe.rs`, run at
`474423c8d` in a lane worktree. It walks `.smt2` files, decides each on a
256 MB-stack worker under `LiaCountersGuard::enable()`, and reports the verdict,
the `UnknownKind`, the classified `cause`, and the counters — printing
`counters=ABSENT` rather than zeros when the worker never returned, because
`last_lia_counters()` returning `None` means "never read", not "zero"
(`lia_counters.rs:749`). **No solver behaviour was changed and no constant was
touched.** The probe is not left in the tree; §7.

The deadline-free populations are run **one process per file** under
`timeout -k`. This is not tidiness: in that configuration a hard file never
returns, so an in-process worker thread would leak and keep burning a core.

Coverage is reported as *files that entered branch-and-bound*, not just files
examined — an `unknown`-count from a probe that never reached the subject is
indistinguishable from a strong negative.

## 3. The measurement

### 3.1 Committed regression corpus — 218 files, tight (50,000) cap

```
$ ./target/release/examples/lia_cap_probe corpus/regression 0 2000
dir              = corpus/regression
files found      = 218
files examined   = 218
config timeout   = NONE (corpus-sweep config)
harness cap      = 2000 ms   stride=1
--- verdicts ---
  error            12
  harness-timeout  3
  parse-error      50
  sat              60
  unknown          9
  unsat            84
--- unknown attribution (kind | cause) ---
      2  Incomplete | other: integer constant 10000000000 does not fit the bounded width 32; widen the bound
      1  Incomplete | other: integer constant 10000000000000000000000000000 does not fit the bounded width 32; widen th
      6  Incomplete | other: no model within the bounded integer width 32; widen the bound
--- offline branch-and-bound coverage (LiaCounters) ---
  files whose solve entered BnB (bnb_roots>0) : 2
  total bnb_roots                             : 2
  total bnb_nodes                             : 84
  files with bnb_budget_exhausted>0           : 0
  files where counters were absent (None)     : 53
--- files whose FRONT-DOOR unknown is the node cap ---
  (none)
```

**0 of 9 unknowns are the cap.** All nine are the bounded-integer-width stop on
the int-blasting route — a different item entirely.

### 3.2 The QF_LIA parity loss list — 27 files, loose (20,000,000) cap

This is the population the roadmap gate literally names: every SMT-LIB 2024
`QF_LIA` file the reference decides and we do not
(`bench-results/parity-losses-20260905/QF_LIA.census.tsv`, all 27 present on the
NAS mount), at the parity budget of 24 s.

```
$ ./target/release/examples/lia_cap_probe <27-file dir> 24000 30000
files examined   = 27
config timeout   = 24000 ms
--- verdicts ---
  harness-timeout  8
  sat              3
  unknown          16
--- unknown attribution (kind | cause) ---
      1  Incomplete | BNB/exact-rational simplex declined (i128 overflow or iteration backstop)
      1  ResourceLimit | other: lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary (atoms=25667,
     14  Timeout | other: preprocessed dispatch timeout after reduced solve
--- offline branch-and-bound coverage (LiaCounters) ---
  files whose solve entered BnB (bnb_roots>0) : 18
  total bnb_roots                             : 21629
  total bnb_nodes                             : 29134
  files with bnb_budget_exhausted>0           : 0
--- files whose FRONT-DOOR unknown is the node cap ---
  (none)
```

**0 of 16.** Coverage is not in doubt here: **18 of 27 files entered
branch-and-bound**, across 21,629 roots and 29,134 nodes. Against a cap of
20,000,000 that is **0.15% of one file's budget spread over the whole
population**. Three of the 27 are now decided `sat` outright, so the population
has moved since the census.

### 3.3 SMT-LIB 2024 `QF_LIA`, stride-20 sample — 666 files, tight (50,000) cap

The full division is 13,306 files at
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_LIA`.
**The NAS mount was up** (`nas3:/volume1/data on /nas3/data type nfs4`). Sample
is every 20th file of the sorted list — deterministic, and it covers **27 of the
division's 32 families** (missing: `20230321-UltimateAutomizerSvcomp2023`,
`RTCL`, `check`, `fft`, `wisa` — 23 files in total, each family 2-9 files,
so a stride of 20 legitimately misses them).
Deadline-free (tight cap), 10 s external bound per file, 6-way parallel.

```
rows: 666
--- verdicts ---
    283 EXTERNAL-TIMEOUT-OR-CRASH(rc=124)
    263 sat
     97 unsat
     22 unknown
      1 parse-error
--- unknown causes ---
     11 ResourceLimit | other: lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary
     11 Incomplete | BNB/exact-rational simplex declined (i128 overflow or iteration backstop)
cap-exhausted files: 0
BnB-reached files:   111
counters ABSENT:     284
```

**0 of 22.** The two real causes are the `lia-dpll` admission bound (11) and the
`i128` boundary that item 2.3 already measured and deliberately did not open
(11). **111 files entered branch-and-bound and none exhausted its budget.**

The 283 external timeouts are the honest limit of this arm: those workers never
returned inside 10 s, so their counters are `ABSENT` and I cannot claim they are
zero. §6 says what that does and does not leave open.

### 3.4 Why the cap never fires: the Gomory round decides 97.7% of integer calls

The three zeros above are a *that*. This is the *why*, aggregated over the
382 files of §3.3 whose counters were readable (the 284 `ABSENT` rows are
excluded, not counted as zero):

| counter | total | share of offline calls |
|---|---:|---:|
| `offline_calls` (entries to the conjunctive integer decider) | 308,160 | — |
| `gomory_decided` (returned a verdict; branch-and-bound never ran) | **301,122** | **97.716%** |
| `bnb_roots` (entries to branch-and-bound) | 6,889 | 2.236% |
| `bnb_nodes` (summed over every root, every file) | **10,481** | — |

`decide_int_constraints` (`lra.rs:1934`) runs the bounded Gomory fractional-cut
round **first** and falls through to branch-and-bound only when it declines. On
this corpus it declines 2.2% of the time, and when branch-and-bound does run it
closes in a mean of **1.52 nodes per root**.

The scale is the point: **every branch-and-bound node explored across all 382
files put together is 10,481 — 21% of the budget the cap allows a single
call.** For the cap to bind, one root would have to explore about 5,000× the
mean, on a corpus where the deepest thing measured is a few hundred nodes.

One file makes the shape vivid:
`20210219-Dartagnan/ConcurrencySafety-Main/qrcu-2-O0.smt2` records
`offline_calls=70650`, `gomory_decided=70649`, `bnb_roots=1` — seventy thousand
integer decisions, one of which reached branch-and-bound. Its `unknown` is the
`lia-dpll` admission bound at 65,441 atoms, not anything to do with nodes.

### 3.5 Positive controls

An `unknown`-count of zero is worth nothing without evidence the probe can see a
non-zero. Three controls, all fired:

| control | what it had to show | result |
|---|---|---|
| **Coverage** — the four `lia-simplex` census files, deadline-free | branch-and-bound is entered at all | `bnb_roots=2`, `bnb_nodes=410`; one file returned `Incomplete \| BNB/exact-rational simplex declined`, so a *non-cap* BnB `unknown` is reportable |
| **Exhaustion branch** — the committed unit test | `budget == 0`, the exact condition `record_bnb` reports, is reachable | `cargo test -p axeyum-solver --lib --features full bnb_alone_leaves_x_plus_y_half_unknown` → `1 passed` (nonzero), 22.55 s in debug for a budget of **300** |
| **Cap-forcing instance** — see below | a query that must reach BnB and grind | `bnb_roots=1`, `gomory_decided=0`, **686 nodes in 20 s** |

The cap-forcing instance is the `2x + 2y = 1` shape that `lra.rs:3689` pins as
the case branch-and-bound alone cannot close (it keeps finding shifted fractional
vertices), written as two opposite **non-strict** inequalities so neither the
gcd/Diophantine equality refuter nor `tighten_strict_integer_constraints`
(strict-only) short-circuits it — plus one harmless `z <= 2^41`, which makes
`build_gomory_tableau` decline the whole Gomory call (`lra.rs:2465`,
`GOMORY_MAGNITUDE_LIMIT = 1 << 40`) so the query must fall through to
branch-and-bound. The system stays two-variable, which is the cheapest possible
node.

```
ROW  cap_forcing.smt2  unknown  Timeout | other: preprocessed dispatch timeout after reduced solve
     bnb_roots=1  bnb_nodes=686  bnb_exhausted=0  offline_calls=1  gomory_decided=0
```

**686 nodes in 20 s on the cheapest system that can grind.** That is the number
this whole item turns on:

| cap | nodes | time at the measured rate |
|---|---:|---:|
| `MAX_LIA_BNB_NODES` (no clock) | 50,000 | **~24 minutes** |
| `MAX_LIA_BNB_NODES_DEADLINED` (clock set) | 20,000,000 | **~6.8 days** |

Both are lower bounds. `lia_branch_and_bound` recurses depth-first, pushing a
bound constraint per level, so node *k* solves a simplex over roughly *k* rows —
the rate falls as the search deepens. Two independent runs of the same file with
no config timeout were killed at 300 s and 600 s without returning, which is
consistent: the cap had not fired.

## 4. The cap's `unknown` is not distinguishable at the API — and twice it is erased

The brief flagged this as a finding in its own right if true. It is true, in
three places:

1. **`UnknownKind` never distinguishes it.** Every branch-and-bound stop is
   `Incomplete` (`lra.rs:1723`). A caller switching on `kind` cannot tell the cap
   from a deadline, an overflow, or an out-of-range branch constant.
2. **`dpll_lia`'s conflict scan discards the reason.** The lazy loop's integer
   oracle is `check_with_lia_opaque_apps_within_node_cap` (`dpll_lia.rs:1556`),
   which keeps the **tight 50,000 cap even when a deadline is set**. The scan
   then does `if !matches!(oracle(...)?, CheckResult::Unsat) { return
   Ok(Vec::new()) }` (`dpll_lia.rs:1657`): anything not `Unsat` — a node-cap
   `unknown` included — becomes "no conflict found", by documented design
   (`dpll_lia.rs:1534-1544`). A node-cap exhaustion inside the lazy route is
   invisible in the query's verdict. (The *sat*-reconstruction path is the
   exception: `theory_model` at `dpll_lia.rs:2949` does carry the reason through
   as `TheoryModelOutcome::Declined`.)
3. **`lia_online` discards it too.** `Ok(CheckResult::Unknown(_)) | Err(_) =>
   Feasibility::Unknown` at `lia_online.rs:1062` and `:1085` drops the
   `UnknownReason` on the floor on both the cold and warm theory-check paths.

So of the three routes that run branch-and-bound, **only the offline
`lia-simplex` front-door rung can ever surface `node budget exhausted` to the
API.** A measurement built on the detail string alone would have been blind on
the other two — which is why the number above is carried by
`bnb_budget_exhausted`, the one instrument that sees all three. It is opt-in and
off by default (one thread-local read when off), so nothing observes this in a
normal run.

Even §3.5's control shows the erasure: its BnB stop was a wall-clock deadline,
but the verdict that reached the API said `Timeout | preprocessed dispatch
timeout after reduced solve` — the front door's own stop, not the theory's.

**This is worth fixing whether or not 3.4 is ever built**, and it is small: give
`UnknownKind` a variant for a deterministic search-node budget (or reuse
`ResourceLimit`) so `kind` alone separates a cap from a clock, and thread the
`UnknownReason` through the two discard sites rather than collapsing it to a
unit. Without that, the next lane asking this question has to re-derive the
counter route from scratch, exactly as this one did.

## 5. Correction: two planning documents mis-cite their own census

- [`docs/plan/families/smt-quantifier-free/qf-lia.md:29`](../../plan/families/smt-quantifier-free/qf-lia.md)
  — "27 files: … **3 a branch-and-bound node-cap incompleteness**".
- [`docs/plan/smt-parity-plan-2026-09-05.md:634`](../../plan/smt-parity-plan-2026-09-05.md)
  — "3 other (**branch-and-bound node-cap incompleteness**)".

The census row those three files come from reads, verbatim, in
`bench-results/parity-losses-20260905/QF_LIA.census.tsv`:

```
other(incomplete:QF_LIA branch-and-bound undecided: wall-clock deadline passed (node cap 20000000)
```

The stop that fired was the **wall-clock deadline**. `20000000` is the cap that
was *in force and not approached* — it is context in the message, not the cause.
Re-run here at 24 s (§3.2), none of the three even produces a branch-and-bound
`unknown` any more; they time out in dispatch.

One of the three is now decided outright. Run deadline-free (the **tight**
50,000 cap) with no external bound:

```
$ ./target/release/examples/lia_cap_probe <...>/CAV_2009_benchmarks/smt/25-vars/problem_2__034.smt2 0 1200000
ROW  problem_2__034.smt2  sat  -  bnb_roots=1  bnb_nodes=409  bnb_exhausted=0
                                  offline_calls=1  gomory_decided=0
```

**409 nodes — 0.8% of the cap the plan says it was lost to — and the verdict is
`sat`.** Its sibling `v30_problem_2__023.smt2.slack.smt2` was run in the same
configuration for **30 minutes** and neither returned nor tripped the cap
(`bnb_budget_exhausted = 0`), which is the same story from the other side.

This is precisely the failure `LiaBnb::Unknown`'s own doc comment
(`lra.rs:2248-2259`) was written to prevent: *"an `unknown` that misattributes
its own cause is worse than an opaque one, so the cause travels with the
variant."* The cause did travel; the summary dropped it. Note also that QF_LIA
is on the **not-confirmed** list in the census's own correction block, so its
`class` column was never re-derived through the front door — nothing here should
have been inherited, and §3.2 does not inherit it.

Both lines should be reworded to "3 wall-clock deadline inside branch-and-bound".
That is a doc edit outside this note's scope; it is recorded here so whoever owns
those pages can make it.

## 6. What I did not measure

- **The 283 files in §3.3 that overran the 10 s external bound.** Their counters
  are `ABSENT`, not zero. What is *not* open about them: a deadline-free run that
  is still going at 10 s has, by definition, not been stopped by the cap — so
  none of them is a file the cap cost us a *prompt* answer on. What is open: if
  one were left running for the ~24 minutes §3.5 prices, it might eventually trip
  the cap. That would be a file we lose to a 24-minute cap, not to a 50,000-node
  one, and no realistic budget reaches it.
- **A confirmed observation of `bnb_budget_exhausted >= 1` through the front
  door.** The exhaustion *branch* is confirmed reachable by the committed unit
  test (§3.5), but I never saw the counter itself non-zero, because reaching it
  costs the ~24 minutes §3.5 prices. A long-running instance of the cap-forcing control
  was still running when this note was written.
- **The other cap this item's evidence column names**, `MAX_DPLL_ROUNDS = 10_000`
  (`dpll_lia.rs:44`). It is a different stop with a different owner and was out
  of scope.
- **Whether the lemma-based design would be *faster*.** This note measures only
  whether the cap costs verdicts. It does not measure whether emitting the split
  to the SAT solver would decide the 14 dispatch-timeout files in §3.2 sooner —
  it might, and that is a search-speed question, not a completeness one.
- **`solve_smtlib` vs `check_auto`.** The probe calls `check_auto` on the flat
  assertion view. That matches `corpus_regression.rs` for scope-free scripts
  (§3.1) but is not the full text front door used by `smtcomp_cli` (§3.2, §3.3).
  The node cap sits well below dispatch on every route, so this does not affect
  the cap count, but it does mean the verdict tallies here are not the parity
  numbers.
- **Quantified `LIA`, `QF_UFLIA`, `QF_ALIA`, `QF_IDL`.** Only `QF_LIA` was in
  the gate.

## 7. Recommendation

**DO NOT BUILD 3.4 as a completeness fix.** The gate asked for a count and the
count is zero on 911 benchmarks, with 131 of them measured to have entered
branch-and-bound. The binding constraints on this division are, in order: the
`lia-dpll` pre-SAT admission bound, the wall clock, and the `i128` simplex
boundary (item 2.3). The node cap is not among them and is not close.

### What would change the answer

Nothing in a corpus. The cap can only start costing verdicts if node *cost*
drops by orders of magnitude — i.e. if a warm/incremental simplex made a node
cheap enough that 50,000 of them fit in a normal budget. If that ever lands,
re-run §3.3 before re-opening this item, not before.

### Do these two instead

- **Fix the discriminability (§4).** Small, and it is what makes the next
  measurement of this question cheap instead of a day.
- **Correct the two planning lines (§5).**

### On the caution the brief raised — what replaces the cap's guarantee

The brief asked, correctly, what replaces the cap if the lemma design is ever
adopted, since "the references achieve termination differently, not by luck."
Having read them: **on LIA they do not achieve it differently — they achieve it
by not offering the guarantee at all.**
[`05-yices-opensmt-smtinterpol.md:52`](../../solver-comparison-2026-09/05-yices-opensmt-smtinterpol.md)
records that Yices's `simplex_final_check` returns only `FCHECK_SAT` or
`FCHECK_CONTINUE` (`simplex.c:10098-10122`), OpenSMT's `cutFromProof` `UNKNOWN`
means only "no cut found" and falls through to branching, and SMTInterpol's
`checkCompleteness()` returns `INCOMPLETE_THEORY` only for non-linear variables.
Non-termination in all three shows up as **an unbounded CDCL search**, bounded
only by the user's wall clock (or, for SMTInterpol, an optional
`:reproducible-resource-limit` counter).

So a lemma-based redesign here would not need a replacement for the cap's
guarantee — it would need to *decide whether to keep offering one*. Our
`config.timeout` already bounds every route, and this note shows the deadline is
what actually fires. Note also that adopting their posture is not free in the
other direction: a deterministic, clock-free stop is what makes the proof and
interpolant routes reproducible, and those are exactly the deadline-free callers
`MAX_LIA_BNB_NODES`'s own doc comment (`lra.rs:1702-1706`) says it exists for.
Dropping it would make a proof-route `unknown` depend on the machine.

If the item is ever revisited, it should be revisited as **item 3.4-as-speed**
(does branching by lemma decide the 14 dispatch-timeout files?), with a
head-to-head on those files as its gate — not as 3.4-as-completeness, which this
note closes.

## 8. Probe disposition

`crates/axeyum-bench/examples/lia_cap_probe.rs` was written for this measurement
and is **removed** rather than left in the tree, per the Phase 3 brief. Nothing
in it is load-bearing that the repository does not already have: the whole
measurement is `LiaCountersGuard::enable()` plus
`LiaCounters::bnb_budget_exhausted`, which is committed, documented, and was
built for exactly this question. Re-deriving the probe from §2 is a few minutes.

What *is* worth keeping is the cap-forcing instance from §3.5 — it is the only
construction found that reaches branch-and-bound with cheap nodes and a declined
Gomory round, and any future work on this item needs it. Its recipe is written
out in §3.5 in full so it can be rebuilt without the file.
