# ADR-2060: the give-up variant could not tell its gates apart, and nothing in the workspace ever asked it to

Status: accepted
Index-summary: `Decision::TimedOut` was a unit variant whose own DOC COMMENT claimed the Fourier–Motzkin elimination had exhausted its budget, and `check_with_lra_within_certified` rendered that sentence faithfully for every producer — [ADR-2045] measured 34 of 34 `QF_LRA` rows wearing it with `cube_matrices=0`, and declined to fix it because it is **two** changes. Both are here. The enumeration was re-done three ways: a name scan gives **six** constructions (ADR-2045's count, and correct at that level), the compiler confirms exactly those six *and* that **exactly one test in the whole workspace** touched the variant, and the transitive closure over the cause-erasing returns BELOW them gives **28 program points** (27 distinct; one is a funnel) carrying **15 distinct causes** — `eliminate` alone returned a bare `None` for **eleven** bail points including **eight `?`-on-`Option` `i128` overflows**, and `simplex_fallback` one `Ok(None)` for five, two of which (**a `sat` model that did not replay** and **an `unsat` certificate that failed its self-check**) are the route's own trust anchors and had no way to be counted at all. Shape: `Decision::GaveUp(GaveUp)`, five gates, two carrying a nested `(FmDecline, SimplexDecline)` pair because reaching the simplex MEANS the elimination already declined; the `ctx.overflow` producer leaves the timeout variant entirely for `Decision::Incomplete`/`UnknownKind::Incomplete`, the **one** `UnknownKind` this moves. Every routing decision is unchanged by construction, and the watchdog keeps its precedence. Measured on the canonical 200-file board, two binaries interleaved per file on four pinned pairs: **0 gains, 0 losses, 0 flips (0/159 comparable), 0 exit-status moves, 0 soundness disagreements (0/185)**, each printed with its denominator, with **107/200 decided in BOTH arms** — reproducing ADR-2045's 107 exactly. Non-vacuity is proved by a channel that MUST move and did: **35 board rows carried the old sentence, 0 still do**, and the gate the solver now names on them is the multiplier-matrix loop (**18**), the entry poll (**13** — the decision never ran at all) or collection (**2**). **None is the elimination**, confirming ADR-2045's counter-based inference through a wholly independent channel. Pinning: four tests of deliberately different kinds, one deriving its population from the file's own source text with a negative control that PANICS rather than returning an empty list; the requested guard deletion goes from **0 tests killed to 2**, and seven mutations kill five different tests between them. Two things found on the way: `rustfmt` rejoins a `\`-continued string literal and leaves the indentation INSIDE it (every new detail shipped briefly with runs of 14 spaces, and all four new tests passed), and `cargo doc -D warnings` is **red on `main`** with 6 errors in `axeyum-ir`/`axeyum-cnf`, measured on the base tree, neither caused nor fixed here.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2045] found that `lra.rs:159` attaches ONE sentence —
`"lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget"` — to
every `Decision::TimedOut` that reaches it, named the six producers inside
`decide_within`, measured that **34 of 34** `QF_LRA` rows wearing that label had
`cube_matrices=0` and `cube_simplex_calls>0` (the elimination had not built a
single matrix on any of them), and then **deliberately did not fix it**, because
it is two changes and not one: give `TimedOut` a detail, *and* stop routing
`ctx.overflow` — an `i128` overflow — through a timeout variant. Renaming alone
leaves the overflow reporting a clock, which is a half-fix that reads as a whole
one.

This is that lane. Branch base: `git merge-base main HEAD` is
`91c721f8eda678e40124e089d6761ce3d3d02f94`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/timeout-diagnosis-20260914/PREREGISTRATION.md)
in their own commit before the binaries were built and before a file was run.

## 1. The enumeration, and why six was the right answer to the wrong question

Three methods, because the first two under-report and saying so is the point.

**A — the name scan** (`Decision::TimedOut` constructions; what ADR-2045 did):
**six**, four in `decide_within` and two in `simplex_after_elimination`.

**B — the compiler**, which is the only method that cannot under-report at that
level. Giving the variant a payload makes every construction site a type error.
It named **exactly those six** in non-test code — so ADR-2045's table is correct
as a count of constructions — and it named **exactly one test in the entire
workspace**, which asserted only *that* the decision gave up. The grep-based
claim that nothing pinned the string is therefore confirmed by a stronger
instrument than the grep.

**C — the transitive closure over the cause-erasing returns that FEED those
six**, which is where the real number is. Four functions below `decide_within`
each collapse several distinct causes into one valueless bail that the caller
then has to guess about:

| function | bail points | what they conflate |
|---:|---:|---|
| `decide_within` | 6 | the six of method A |
| `collect_constraints` | 3 | the deadline, the deadline mid-recursion, the memory watchdog — all one `Ok(None)`, with the caller **re-reading the clock afterwards to guess which** |
| `solve` | 3 | its own per-variable deadline, the back-substitution `i128` overflow, and one arm that is purely a funnel for the row below |
| `eliminate` | 11 | the deadline, the watchdog, the deterministic `MAX_FM_CONSTRAINTS` size guard, and **eight separate `?`-on-`Option` `i128` overflow points** — all one bare `None`, from which `solve` recovered *memory* by asking the sticky watchdog flag and assumed *clock* for everything else |
| `simplex_fallback` | 5 | the row-build deadline, a constant-negation overflow, **a model that did not replay**, **a Farkas certificate that failed its own self-check**, and a strict-delta refutation with no rational certificate — all one `Ok(None)` |

**28 program points**, one of which (`solve`'s funnel arm) is not a bail of its
own, so **27 distinct places whose execution ends in that one sentence**. They
carry **15 distinct causes**, of which **exactly one is the Fourier–Motzkin
elimination running out of wall clock**.

The count is reproducible:
[`enumerate-producers.py`](../../../bench-results/timeout-diagnosis-20260914/scripts/enumerate-producers.py)
run against any tree, and it names the function it failed to find rather than
returning a quiet zero.

Two of those 27 are worth naming on their own, because they are not diagnosis
problems at all. `simplex_fallback` declines when **a `sat` model does not
replay** and when **an `unsat` certificate fails its self-check**. Those are the
two trust anchors of this entire route, and before this change neither had any
way to be counted: both rendered as a Fourier–Motzkin timeout, in a population
where nobody would look for them.

## 2. The misattribution was in the doc comment, and the string was its echo

```rust
/// The Fourier–Motzkin elimination did not finish within the wall-clock /
/// size budget; the query is left undecided (a timely, sound `unknown`).
TimedOut,
```

`check_with_lra_within_certified` rendered that sentence faithfully. Fixing the
string and leaving the doc would have preserved the source of the defect and
left the next reader with a correct-looking comment that is false. The doc is
rewritten as part of the change, and so are `Feasibility::TimedOut`'s,
`eliminate`'s (*"Returns `None` to bail … when the wall-clock `deadline` passes …
or … `MAX_FM_CONSTRAINTS`"*, which already omitted its two overflow families),
`collect_constraints`'s, `simplex_fallback`'s and `Collector::timed_out`'s.

## 3. The shape, and why this shape

`Decision::TimedOut` → `Decision::GaveUp(GaveUp)`, five variants, one per gate:

| variant | what actually happened |
|---|---|
| `DeadlineOnEntry` | the deadline had already passed; nothing ran |
| `DeadlineCollectingConstraints` | the clock expired while linearizing; neither engine ran |
| `DeadlineBuildingFarkasMatrix` | the clock expired in the `32·n²`-byte unit-multiplier loop; **the elimination had not started** |
| `SimplexThenEliminationDeclined { simplex, fm }` | both engines declined, simplex first |
| `EliminationThenSimplexDeclined { fm, simplex }` | both engines declined, elimination first |

`FmDecline` has five values and `SimplexDecline` six; `ElimBail` and
`CollectDecline` type the two chokepoints below them.

**Why two of the five carry a nested pair.** Reaching the simplex *means* the
elimination already declined, so the honest answer is two facts, not one. The
old string asserted the first and was silent about the second, which is exactly
how a dense-simplex cost came to be attributed to an elimination that built zero
matrices. A reader now gets both: *"both engines declined — Fourier–Motzkin hit
its deterministic MAX_FM_CONSTRAINTS size guard (a size bound, not the clock),
then the exact-rational simplex fallback found a point that did not replay
against the original assertions"*.

**Why an enum and not a `String`.** `Incomplete` and `OutOfMemory` carry a
`String` and should: their details interpolate measured numbers. These do not —
the set is closed at compile time — and a closed set is what lets a test assert
that *every* producer has a reason of its own without carrying a literal list to
go stale against.

**Why the overflow is `Incomplete` and not a sixth `GaveUp`.** This is the half
ADR-2045 insisted on. `Decision::Incomplete`'s own doc already names *"an `i128`
overflow"* as its example, and it carries `UnknownKind::Incomplete` — "the
procedure is incomplete for this query", which is precisely what a fixed
rational width being too narrow is. Reusing it rather than inventing a variant
makes the fix idiomatic here instead of novel. **It is the one `UnknownKind`
this change moves** (`ResourceLimit` → `Incomplete`), and that move is measured
rather than asserted; see §5.

**Why `UnknownKind` does NOT move for the other five.** All five are resource
gates, exactly as the sentence they replace claimed. What was wrong was never
the kind; it was the engine and the event.

**What deliberately did not change.** Every routing decision. The watchdog keeps
its precedence over clock/size/overflow bails in `solve`; the collection decline
keeps deadline-outranks-watchdog, which is what the caller's after-the-fact
re-read gave it; `Feasibility::Declined` hands the cube to the simplex exactly
where `Feasibility::TimedOut` did. A diagnosis change that quietly moved a route
would be a capability change wearing a diagnosis change's commit message.

## 4. Pinning, and the guard-deletion result

The string was free to be wrong because nothing asserted it. Four tests now do,
and they are deliberately different in kind, because a suite where every guard
rejects through one shared check is a suite with one guard — six of seven guards
in one suite here were once removable with everything still green.

- `every_declared_give_up_variant_is_listed` derives its population from **this
  file's own source text** (brace-depth parsed, so a struct variant's fields are
  not counted as variants), with a positive control and a **negative control
  that requires a parse which never found its subject to PANIC** rather than
  return an empty list.
- `each_producer_reports_its_own_reason` drives the producers and checks the
  driven set against the declared set minus an explicit exemption list — and the
  exemption list is itself checked against the source. Coverage: **5 of 5**
  `GaveUp`, **5 of 5** `FmDecline`, **4 of 6** `SimplexDecline`. The two not
  driven are named with reasons: `CertificateFailedSelfCheck` is reachable only
  from a procedure bug (constructing it means constructing the bug) and
  `InfeasibleWithoutCertificate` needs a strict-delta refutation no known input
  produces.
- `no_detail_blames_an_engine_that_did_not_run` is the regression as an
  assertion.
- `an_overflow_while_linearizing_is_an_incompleteness_and_not_a_timeout` is
  ADR-2045's singled-out producer, end to end through the public surface.

**The guard deletion.** Deleting `decide_within`'s entry deadline poll killed
**nothing** before this change — the pre-existing test's own doc comment said so
in as many words: *"deleting the entry poll alone leaves all 1,705 unit tests
green, because collection's own poll then produces the same `TimedOut`"*. It now
kills **two**, and both are tests about that poll's identity. Six further
mutations were run, each with its anchor asserted to match exactly once:

| mutation | tests killed |
|---|---:|
| delete `decide_within`'s entry deadline poll | **2** |
| route the `i128` overflow back through a give-up | 1 |
| make two gates render one sentence | 1 |
| map the size guard to a clock in `solve` | 1 |
| drop a variant from the test's own listed set | 1 |
| re-introduce the rejoined-indentation whitespace | 1 |
| make a simplex replay failure report as the engine declining | 1 |

Every mutation kills at least one test, no mutation kills the whole module, and
the five kills spread across **four different tests** — so the guards do not
share a rejection path.

## 5. Verdict neutrality, measured

Rules were registered before the binaries existed. Two binaries (there is no knob
to flip; the change is unconditional code), `--release` from
`lane-snapshot.sh` extractions, interleaved per file back to back on the same
pinned core with the order alternating, on **four pinned pairs** — `s5 0,8`,
`s5 1,9`, `s6 0,8`, `s7 0,8` — over the canonical 200-file `QF_LRA` board at the
board's own 24 s budget and `ulimit -v 8G`. Both arms ran with `--trace`, so the
comparison is between two runs identical in everything but the binary. The runner
**refuses if the two binaries hash the same**, because two identical arms would
make every number below vacuous while looking exactly like agreement.

All four shards completed, 50 rows each, 200 of 200.

| channel | rule | result |
|---|---|---|
| verdict | must not move | **0 gains, 0 losses** out of 200; **0 flips** out of 159 |
| exit status | must not move | **0** rows changed exit class, out of 200 |
| give-up detail | **must** move | **37** of 200 moved; **32** attributable to this change |
| soundness | must not move | **0** disagreements with `:status`, out of 185 annotated rows |

`base decided 107/200, arm decided 107/200` — **reproducing ADR-2045's 107
exactly**, on a re-derived population, which is a second check that the two arms
are looking at the same board.

Every zero above is printed with the denominator it is a zero out of, including
the two that differ from 200: only **159** rows had both arms emit a parseable
verdict line (41 abort in *both* arms, the known allocation-abort population),
and only **185** carry a `:status` annotation. Wilson 95 % upper bounds, since a
zero is a rate too: gains `[0, 0.0189]`, flips `[0, 0.0236]`, soundness
`[0, 0.0203]`.

**Noise floor.** ADR-2045 measured 0 of 200 rows differing over two identical
passes on this board, budget and harness at the merge-base commit one day
earlier; it is cited, not re-measured, and the pre-registration says so. Nothing
moved here, so the condition for re-measuring it did not arise.

### The non-vacuity demonstration, and the finding inside it

A verdict-neutral A/B between two binaries proves nothing unless the binaries
differ. The give-up detail is the channel that **must** move, and it did — but
"it moved" is not "it moved because of this change", since the outer harness
reports a `Watchdog` on one run and a `Timeout` on the next for the same file.
So the movement is attributed rather than counted
([`attribute-detail-moves.py`](../../../bench-results/timeout-diagnosis-20260914/scripts/attribute-detail-moves.py)):

```text
BASE carries the old lra sentence               35/200
ARM  carries the old lra sentence                0/200   <- must be 0
ARM  carries one of the new sentences           33/200

which gate the ARM names, on rows the BASE called a Fourier-Motzkin timeout:
   18  lra: the deadline passed building the Fourier-Motzkin unit-multiplier matrix;
       the elimination itself never started
   13  lra: the deadline had already passed when the conjunctive decider was entered
    2  lra: the deadline passed while linearizing the assertions
```

**Not one of the 33 is the elimination.** Eighteen are the multiplier-matrix
loop, which is Fourier–Motzkin's allocation but not its search; **thirteen are
the entry poll, where the conjunctive decider had not run at all**; two never got
past collection. ADR-2045 inferred this from the engines' own counters
(`cube_matrices=0` on 34 of 34); the solver now says it in its own words, through
a channel that shares nothing with those counters.

A single-file mechanism proof of the same thing, run directly rather than through
the board, on `_standard_init5_ground.i_3_2_2.bpl_7.smt2`:

```text
base: … [ResourceLimit] lra: Fourier–Motzkin elimination exceeded the wall-clock / size budget
arm : … [ResourceLimit] lra: the deadline passed building the Fourier–Motzkin
                             unit-multiplier matrix; the elimination itself never started
```

The five rows that moved for another reason are `Watchdog`↔`Timeout` jitter in
which gate the outer harness saw (4) plus three `Timeout → Timeout` rows whose
inner reason differed; none is a verdict or an exit-status move, and all five are
reported rather than dropped.

## 6. A defect this change shipped, and the guard that now catches it

`rustfmt` takes a `\`-continued string literal, rejoins it onto one line, and
**leaves the continuation's leading indentation inside the string**. Every
detail this lane added shipped, briefly, with runs of fourteen spaces in the
middle of the sentence — and all four new tests passed, because a run of spaces
breaks nothing a `contains` or a `starts_with` looks for. It only corrupts the
sentence a human and a census both read.

Every detail is now built with `concat!`, which rustfmt does not rejoin, and the
rendering test asserts each detail and each `describe()` is one clean line. It
is worth recording because it is the same shape as the defect this whole ADR is
about: **the part of the output no assertion happens to touch is exactly where a
wrong thing survives.**

## 7. What this lane did not do

It attached **no capability lever**. The deliverable is a correct, pinned
diagnosis, and the lane is not measured in files decided.

Left named for whoever wants them, neither needing a decision here:

- `past_deadline` is `stop_requested() || clock_expired`, so every sentence
  above that says "deadline" covers a **portfolio cancellation** as well as an
  exhausted clock. The details say "an expired budget or a portfolio stop" where
  the distinction is visible and do not pretend to separate them; separating
  them would double the enum and needs its own measurement to justify.
- `SimplexDecline::ModelDidNotReplay` and
  `SimplexDecline::CertificateFailedSelfCheck` are now countable for the first
  time. If either shows up on a real board at any rate above zero, that is a
  finding about a trust anchor and not about a budget.
