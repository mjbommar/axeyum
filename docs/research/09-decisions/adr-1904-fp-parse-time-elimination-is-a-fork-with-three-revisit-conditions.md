# ADR-1904: Parse-time FP elimination stays, and the fork has three revisit conditions — only one of which is about size, and the third has already fired once

Status: accepted
Index-summary: Keep FP → BV elimination at parse time (ADR-0023, not ADR-0028 as roadmap 4.4 says) and build no FP theory solver. But roadmap 4.4's single revisit condition — "only if an FP corpus shows parse-time elimination losing on size" — covers one of the fork's three measured costs. The other two are that the rewriter never sees an FP term, and that the ground evaluator replays THE SAME lowered circuit the solver decided, so model replay structurally cannot catch a wrong FP circuit. The third already fired once (the 2026-06-14 `fma` sign-extension defect, caught by the oracle and not by replay), which makes `fp_differential_fuzz` a soundness gate for this route rather than a nicety. Gives the size condition a runnable form against the 75,844-file public FP corpus on NAS, where we commit 31 files.
Date: 2026-09-10

## Context

Roadmap item 4.4 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md:110`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
reads, in full:

> **FP.** We eliminate at parse (ADR-0028, replay checks the same circuit);
> Bitwuzla/STP word-blast lazily via SymFPU. This is a fork, not a gap. |
> Revisit only if an FP corpus shows parse-time elimination losing on size.

The framing is right and the decision it implies is right. Two things about it
are not, and both matter to anyone who later has to act on the revisit
condition.

**First, the ADR citation is wrong.** ADR-0028 is the *software-float validation
oracle* (`rustc_apfloat`, for wide formats). The decision that FP is bit-vector
formula builders with no new solver-side sort is
[ADR-0023](adr-0023-floating-point-bv-lowering.md);
[ADR-0026](adr-0026-first-class-float-sort.md) added the `Float` IR sort that
disambiguates conversions. The tree agrees: `crates/axeyum-solver/src/trust.rs:646`
maps `TrustId::Fpa2Bv => "ADR-0023"`, and `crates/axeyum-smtlib/src/parse.rs:344`
labels the parse-time lowering "ADR-0023 `Fpa2Bv`". Citing 0028 sends a reader
to the oracle rather than to the fork.

**Second, "losing on size" is one of three costs, and it is not the one that has
actually bitten us.** `docs/solver-comparison-2026-09/04-bitwuzla-boolector-stp.md:844-862`
enumerates three things SymFPU-based solving does that parse-time elimination
cannot. Only the first is about size. The third is about *evidence*, and it has
already produced a real defect.

## Decision

**Keep FP → BV elimination at parse time (ADR-0023). Build no FP theory solver
and no lazy word-blaster. Record the fork's three costs separately, with a
separate revisit condition for each — because a single size-shaped condition
cannot fire on the two that are not about size.**

Five commitments.

### 1. No FP theory solver, and "Bitwuzla has one" is not an argument

Restated so it is not relitigated: the roadmap's own "What not to do" says **do
not build an FP theory solver because Bitwuzla has one.** Present-in-a-reference
is not a reason; a measured loss is. Verified in tree at `60fe8bdf2`: there is
no FP theory solver — `axeyum_fp` appears in `crates/axeyum-solver/src/` exactly
twice, both incidental (`lib.rs`, `bv_defined_enum.rs`), and all 37 real call
sites are in `crates/axeyum-smtlib/src/parse.rs`. `crates/axeyum-fp/src/lib.rs`
is 8,257 lines of formula builders.

### 2. Revisit condition A — size. Runnable, with the discriminating step named

The roadmap's condition, made executable. It has three parts and **all three
are required**; the third is what separates "our formula is big" from "our
formula is big *because of FP lowering*", and without it the condition fires on
every hard BV problem that happens to mention a float.

**Corpus.** `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/`,
counted 2026-09-10:

| division | files |
|---|---|
| `QF_FP` | 40,407 |
| `QF_ABVFP` | 18,129 |
| `QF_BVFP` | 17,249 |
| `QF_FPLRA` | 59 |
| **total, quantifier-free** | **75,844** |

plus `QF_ABVFPLRA`, `QF_AUFBVFP`, `QF_BVFPLRA`, `QF_UFFP`, `QF_UFFPDTNIRA` and
the quantified `FP` / `BVFP` / `AUFFPDTNIRA` families, uncounted.

**We commit 31 FP `.smt2` files** — 16 in `corpus/public-curated/…/QF_FP/bitwuzla-regress-clean`,
8 in `…/QF_BVFP/…`, 6 in `corpus/regression/cvc5/qf_fp`, 1 in
`corpus/regression/qf_fp`. That is 0.04% of the quantifier-free public set, and
it is the same shape of blind spot roadmap 3.9 found for QF_BV: whatever the
public corpus would show, the committed corpus structurally cannot.

**Method**, mirroring roadmap 3.8's (which is the closest precedent and worked):

1. Sample every *N*th file per division (3.8 used every 20th and got 752 of
   15,106). Parse with `axeyum_smtlib::parse_script`; record post-parse DAG node
   count, and the `FpUsage` op-set — which the parser already collects, at
   `parse.rs:344-355`, precisely *because* the FP op-set is destroyed by
   lowering (see commitment 3).
2. Solve through `crates/axeyum-bench/examples/smtcomp_cli.rs` — the real
   front door, **not** `explain_corpus`, which disagrees with it on 134 of 397
   benchmarks. Record verdict, wall, peak RSS at a stated budget (3.8 used
   60 s internal / 90 s hard; 23.4 GB RSS was its headline).
3. **The discriminating step.** For each `unknown`, re-parse with the
   `axeyum_fp` arithmetic builders stubbed to fresh unconstrained `BitVec`
   symbols of the same width, and re-measure the DAG. If the DAG collapses, the
   size is FP-lowering-attributable. If it does not, the underlying BV problem
   was large and no word-blasting strategy would have helped.
4. Cross-check against a SymFPU-based solver at the same budget. cvc5 1.3.4 is
   on this host (`/nas3/data/axeyum/harness/bin/cvc5`); Bitwuzla is the closer
   comparison and would need fetching. Note cvc5 is F32/F64-only without
   `--fp-exp` (`docs/plan/gap-analysis-smt-solvers-2026-08-21.md:170`), which
   bounds what it can adjudicate.

**Trigger.** Revisit when the sweep finds **≥ 20 instances** that are
simultaneously (i) `unknown` from the front door at the stated budget,
(ii) decided by a SymFPU-based solver at the same budget, and (iii)
FP-lowering-attributable by step 3. Fewer than 20, or any of the three
conditions missing, is not a trigger — it is a note in the measurement.

### 3. Revisit condition B — the rewriter never sees an FP term

`parse.rs:344-347` states the consequence in the source: FP → BV lowering
"happens eagerly at parse time … so by the time the solver's `QF_BV` evidence
path sees the query it is already bit-vector terms and **the FP op-set is
lost**." The `FpUsage` field exists only to recover it, and it does so by a
deliberately **conservative allow-list scan of the raw s-expressions**
(`scan_fp_usage`) that "can only ever over-report … never miss one" — a re-scan
of text we have already parsed, because the structure was thrown away.

Bitwuzla's FP nodes survive preprocessing and reach `FpSolver`; STP orders FP
lowering *after* `RemoveUnconstrained` specifically so that pass "must see a
float symbol rather than its exposed bits" (`STP.cpp:824-826`, quoted in
`04-bitwuzla-boolector-stp.md:818-823`). We have no such ordering because we
have no such window.

**This is a real cost and it is currently priced at zero, correctly.** Roadmap
3.3 measured word-level rewrite depth generally and returned DO NOT BUILD — of
25 candidate rules, 14 remove zero AND gates. There is no reason to believe
FP-shaped word-level rules would fare better, and no measurement either way.

**Trigger.** Revisit when a word-level rewrite measurement using 3.3's method,
run over FP-bearing instances, shows a rule class that would fire and would
remove nodes — i.e. when the generic finding is shown *not* to transfer to FP.
Until someone measures that, this condition cannot fire, and saying so is more
honest than leaving it implicit.

### 4. Revisit condition C — replay shares the circuit, and this one has fired

This is the cost that matters most and the one roadmap 4.4 mentions only in
parentheses.

ADR-0028 records it in its own words (`:21-26`): **"model replay cannot catch a
wrong FP circuit — the solver and the replay check share the bug and agree."**
It names the instance: a 2026-06-14 `fma` sign-extension defect that would
mis-evaluate `fma(2,3,1) → 0`; native `f64::mul_add` caught it, **replay did
not**.

Every other route in this repository gets its `sat` assurance from replaying the
lifted model through the ground evaluator against the original term — a Hard
Rule. On the FP route that check is structurally vacuous for the *circuit*: the
evaluator evaluates the lowered bit-vector formula, which is the artifact whose
correctness is in question. The FP route's independent assurance comes from
exactly two places: the `rustc_apfloat` / native-float validation of ADR-0028,
and `crates/axeyum-solver/tests/fp_differential_fuzz.rs` against Z3.

**Commitment: `fp_differential_fuzz` is a soundness gate for the FP route, not
a nicety, and may not be weakened.** Until 2026-09-10 it hardcoded
`/usr/bin/z3` and *returned* when the binary was absent — passing, having
adjudicated nothing (roadmap item 0.7). It now routes through
`crates/axeyum-solver/tests/common_z3/mod.rs` (verified: `mod common_z3;` at
`:57`, `z3_available` at `:383`), so `AXEYUM_REQUIRE_Z3=1` makes absence a
failure. That change is what keeps this condition observable at all. Anyone
proposing to relax it should read this commitment first.

**Trigger.** Revisit — and here revisit means *strengthen the evidence route*,
not necessarily adopt SymFPU — when **a second FP defect is found by something
other than replay**. One instance is an anecdote; two is a pattern, and the
second would say the validation oracle plus one differential suite is not
enough. `TrustId::Fpa2Bv` carries `pedantic_level` **5** (`trust.rs:485`) — the
lowest of the reduction trust holes, below `BitBlast` at 8 and the
kernel-checked families at 9–10 — and `parse.rs:357-368` records that **no query
currently qualifies for a certified `Fpa2Bv` trust step**. The ledger already
says this route is our weakest evidence; that is the honest state, not a
surprise.

### 5. What adopting SymFPU would and would not fix

Recorded so a future revisit does not over-claim. Lazy word-blasting fixes
condition A (skip the circuit when the model does not need it) and condition B
(FP nodes survive to later passes). It does **not** fix condition C by itself —
a word-blasted circuit is still a circuit, and if the replay evaluates that
circuit the replay still shares the bug. What fixes C is a first-class FP
evaluation semantics in the ground evaluator, independent of the lowering. That
is a smaller, separable piece of work than an FP theory solver, and it is the
one this ADR would reach for first if condition C fired again.

## Evidence

Verified in this worktree at `60fe8bdf2`.

- `crates/axeyum-smtlib/src/parse.rs` — `grep -c 'axeyum_fp::'` → **37**;
  `:344-355` the "lowering happens eagerly at parse time … the FP op-set is
  lost" comment and the `FpUsage` field; `:357-368` the uncertified-`Fpa2Bv`
  note.
- `crates/axeyum-fp/src/lib.rs` — **8,257** lines.
- `crates/axeyum-solver/src/` — `axeyum_fp` appears in 2 files, incidentally;
  no FP theory solver.
- `crates/axeyum-solver/src/trust.rs:485` (`Fpa2Bv` → pedantic level 5),
  `:646` (`Fpa2Bv` → "ADR-0023").
- `crates/axeyum-solver/tests/fp_differential_fuzz.rs:57`, `:383-397` — routed
  through `common_z3`, so `AXEYUM_REQUIRE_Z3=1` applies.
- ADR-0028 `:21-26` — the shared-circuit consequence and the `fma` instance.
- `docs/solver-comparison-2026-09/04-bitwuzla-boolector-stp.md:844-862` — the
  three-cost enumeration; `:88-92`, `:814-826` — Bitwuzla's and STP's
  SymFPU arrangements; `:1386` — the gap row, sized "Large — this is an
  architectural change to where FP lives, not a feature".
- Corpus counts: `find … -name '*.smt2' | wc -l` per division on
  `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/`;
  committed count by `grep -rl 'QF_FP\|QF_BVFP\|FloatingPoint' corpus/`
  restricted to `.smt2`.
- **Not measured here:** no FP sweep was run. This lane does no heavy compute,
  and the point of commitment 2 is to specify the sweep, not to substitute for
  it. Every number above is a count or a source read.

## Alternatives

- **Adopt SymFPU-style lazy word-blasting now.** Rejected: no measurement says
  we lose verdicts to eager lowering, the comparison doc sizes it "Large — an
  architectural change to where FP lives", and the roadmap's own prohibition
  covers exactly this. Commitment 2 is the measurement that would change it.
- **Leave roadmap 4.4's single revisit condition as written.** Rejected. A
  condition that can only fire on size leaves the two non-size costs with no
  owner, and one of them has already produced a defect. A revisit condition
  nothing can trigger is the same failure shape as a checker that cannot fail.
- **Treat condition C as a reason to adopt SymFPU.** Rejected on commitment 5:
  it would not fix C. Conflating them would buy an architectural change and
  still leave the replay sharing the circuit.
- **Vendor a slice of the public FP corpus now, before deciding.** Deferred,
  not rejected — it is the natural first step of commitment 2's sweep and would
  be a fine lane on its own (compare roadmap 2.5 for strings, and 3.9's finding
  that the committed corpus could not see the gap). It is not a *decision*,
  which is why it is not a commitment here.
- **Defer 4.4 entirely for want of an FP measurement.** Rejected: the
  direction is not in doubt, and the useful output of this item was never the
  keep/change verdict — it was a revisit condition someone could actually run.
  Deferring would have produced neither.

## Consequences

**What this buys.** The fork is written down with three prices instead of one,
each with a named trigger, and the size trigger names a corpus, a method, a
discriminating step and a number. `fp_differential_fuzz` gains a stated status:
it is the FP route's independent check, and weakening it is a soundness
decision, not a CI convenience.

**What is LOST by deciding this way.**

- **The FP route stays our weakest evidence route, deliberately.** `Fpa2Bv` at
  pedantic level 5, no query qualifying for a certified trust step, and a `sat`
  replay that cannot see a wrong circuit. Every other route's Hard Rule replay
  is a real check; here it is not, and we are choosing to keep it that way for
  now.
- **We stay dependent on one external oracle for FP correctness.** Condition C's
  mitigation is `fp_differential_fuzz` against Z3 — a single implementation.
  ADR-1813 names single-oracle blindness as a standing risk and proposes cvc5 as
  an additive second; FP is the route where that would buy the most, and this
  ADR does not implement it.
- **Condition B cannot fire on today's instruments.** It is written as a real
  condition, but nothing currently measures FP-shaped word-level rewrites, so it
  will stay unfired by default rather than by evidence. That is a weaker
  condition than A or C and is marked as such rather than dressed up.
- **The 31-file committed FP corpus keeps every one of these conditions
  invisible to CI.** Against 75,844 public quantifier-free FP files, no gate we
  run today could surface condition A, and that will remain true until someone
  vendors a slice.

## What would falsify this decision

1. **Condition A fires** — ≥ 20 instances `unknown` for us, decided by a
   SymFPU-based solver, FP-lowering-attributable. Then eager lowering is losing
   verdicts and the architecture question is open on measurement.
2. **Condition C fires a second time** — an FP defect found by something other
   than replay. Then the validation oracle plus one differential suite is not
   enough, and commitment 5's first move (independent FP evaluation semantics in
   the ground evaluator) becomes the next work.
3. **The discriminating step in commitment 2.3 turns out not to be
   implementable** — e.g. stubbing the `axeyum_fp` arithmetic builders changes
   satisfiability in a way that makes the DAG comparison meaningless. Then
   condition A needs a different attribution method before it can be run at all,
   and the trigger as stated is unusable.
4. **`references/bitwuzla` is fetched and its lazy word-blasting turns out to
   be cheap to port**, because SymFPU is a library rather than an engine. The
   comparison doc sizes this "Large"; if that is wrong, the cost side of the
   fork changes and conditions A and B should be re-weighed together.
5. **`fp_differential_fuzz` is measured to have been inert on the hosts that
   ran it.** Its `/usr/bin/z3` hardcoding predates `AXEYUM_REQUIRE_Z3` by
   months, and `fleet-hosts.md` now names s2 and s6 as lacking the binary. If
   the FP fuzz has been green-and-empty on the hosts that gated merges, then
   condition C's mitigation was not in place during the period it was assumed
   to be, and the FP route's assurance has to be re-established rather than
   assumed.
