# ADR-2065: the real collector can hold a term, the `sat` exits close by TYPE, and the simulated +6 was a floor

Status: accepted
Index-summary: [ADR-2050] cause (A) — `lra.rs::linearize` refusing a WHOLE query on meeting a real subterm it cannot linearize — is built, shipped ON, and measured. **The `Sat`-exit enumeration [ADR-2050] asked for and did not run is 9 production sites across two files**, derived by construction site rather than by `?`-scan: the mode is `Refuse` on every `Collector::default`, ONE function can set it, and ONE decision function is reachable with it set. Two sites are reachable from an abstracted system and both close on `has_opaque_vars()`; a third (`try_finish_sat`) closes three ways; and the conflict oracle returns `LraOpaqueOutcome`, **which has no `Sat` variant at all** — so no single-hunk mutant of this design yields a wrong `sat`, and the one that would does not compile. **The integer precedent's soundness argument transfers verbatim** (both are relaxations) but its CONSUMERS do not: the integer side has no Farkas certificate to re-export and no `vars`-indexed interpolant consumer, so the real side additionally refuses to forward the certificate. **A/B on the pinned 200-file `AUFLIRA` parity list, one binary, two env values, interleaved per file, arm order rotating: +14 rows, 0 losses, 0 flips, 0 exit-status regressions**, against a same-arm noise floor of **0 of 200** and a `QF_LRA` control of **0 of 200** shown non-vacuous BY OBSERVATION (93 undecided in base; `lra::decide_within` measured executing on 6 of 20 probed rows) rather than by inference — the control's binding routes turned out to be `nra` and `NONE`, not an `lra` one, so the inference was not available. All 14 are STABLE-GAIN over three passes per arm and all 14 agree with `:status`, z3 AND cvc5 at a comparable denominator of **14/14 on each**, no abstentions. **All SIX of [ADR-2050]'s witnesses convert, plus eight rows the simulation never looked at** — this lane's own P3 predicted fewer than six and was wrong in the conservative direction. The converted rows are decided by `q:mbqi-quick` (8) and `q:bool-skeleton` (6), **not** by `lira-dpll`, the route that was refusing: the refusal sat upstream of several rungs. Cost is honestly split: **0.03x on the converted rows** (73.3 s → 2.2 s) and **1.33x on the 186 that did not move**, 1.13x overall. **A method finding worth more than the lever**: the first `Sat`-exit enumerator excluded test code by cutting each file at its FIRST `#[cfg(test)]` line, which in both files marks a helper in the MIDDLE — it discarded 2,397 and 3,133 lines of production code, including a whole `CheckResult::Sat` construction, and printed a clean, complete-looking enumeration of the accepted subset. And the first guard-deletion run came back **five survivors out of five**, not because the guards are redundant but because they are NESTED and every one of them produces a non-`sat`, so `!matches!(.., Sat)` passes with any single one deleted; the fix was to make each guard NAME itself and to assert the name.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2050] took the 11 quantifier-free queries that z3 and cvc5 both refute and
we do not, and split them into four causes. The largest, **(A) ATOM-REFUSAL**,
was six rows, all `AUFLIRA`, one site:

> `lra.rs::linearize` ends in a bare
> `_ => Err(unsupported("non-linear or non-real subterm in a constraint"))`,
> and `dpll_lia.rs::ArithAbstractor::abstract_term` turns that `Err` into a
> refusal of the **whole query**. The refused subterms are applications of
> *declared* `log` / `divide` and array reads `(select s_values7 i)` — in
> `AUFLIRA` these are plain opaque reals and perfectly good *leaves* of a linear
> constraint. Two to four such atoms discarded a 14-conjunct query whose
> refutation is propositional.

[ADR-2050] deliberately did not build it, and named three obligations. This ADR
discharges them in order.

Branch base: `git merge-base main HEAD` is
`30e2a670720a10e302f53555f12709a92002b9c3`, which **is** local `main`'s HEAD.
Rules were [pre-registered](../../../bench-results/real-opaque-20260914/PREREGISTRATION.md).

## 1. Obligation one: enumerate the `Sat` exits

Pre-registered rule: **if they cannot be closed, this lane ships the enumeration
and no lever.** They can. [Full record.](../../../bench-results/real-opaque-20260914/ref/sat-exits.md)

**Method — by construction site, not by `?`-scan.** [ADR-1966] enumerated 72
refusal-propagation sites and found a `?`-only scan under-reports by half. The
abstraction is a mode on `lra::Collector`; the closure is four steps:

| | question | answer |
|---|---|---|
| E1 | every construction site of `lra::Collector` in the workspace | **2** — `collect_constraints_with_options` (takes the mode) and `check_with_lra_simplex` (`Collector::default` ⇒ `Refuse`) |
| E2 | every caller of the one setter | **3**, of which one discards the verdict (`atom_in_lra_opaque_fragment` is `.map(\|_\| ())`, a membership test) |
| E2b | decision functions reachable with the mode set | **1** — `decide_within_with_options` |
| E3 | `Sat` constructions in the two files, test regions excluded | **9** in production |

Of the nine:

| site | reachable with an abstracted system? | closure |
|---|---|---|
| `lra.rs:868` `replayed_sat` | **yes** | `has_opaque_vars()` **before the model is built** |
| `lra.rs:1057` `simplex_fallback` | **yes** | `has_opaque_vars()` |
| `dpll_lia.rs:3205` `try_finish_sat` | can carry its influence | three closures, §1.1 |
| `lra.rs:153`, `lra.rs:3833` | no — `decide_within` / `Collector::default`, mode `Refuse` | structural |
| `lra.rs:2612` | no — the INTEGER collector, its own shipped downgrade | pre-existing |
| `dpll_lia.rs:371, 668, 1243, 3381` | no — forwarding, a different engine, or the propositional model | structural |

### 1.1 The one exit that matters, closed four ways

1. **Before the call.** `has_opaque_real_apps` at `dpll_lia.rs:1338` and `:1420`,
   the real mirror of `has_opaque_int_apps` one line above each.
2. **Inside it.** Real sat-model reconstruction uses `real_model_oracle` (the
   UNabstracted decider), never `real_theory_oracle`. Mirrors `int_model_oracle`,
   which exists for exactly this reason.
3. **After it.** The combined model is replayed against the **original**
   assertions; an unbound opaque term cannot evaluate.
4. **The type.** `check_with_lra_opaque_apps_within` returns `LraOpaqueOutcome`,
   whose variants are `Unsat` and `Undecided`. **There is no `Sat` to
   construct, forward, or forget to guard.**

Layer 4 is the one a future edit cannot quietly remove, because removing it does
not compile. §3 measures how much work it is actually doing.

### 1.2 The open design question [ADR-2050] left is answered by PLACEMENT

[ADR-2050] §5 observed that its *simulated* abstracted file was decided by
`dl-online`, a route EARLIER than the one that refuses, and concluded that "a
fix confined to `ArithAbstractor` is not obviously the whole of it".

**It is, and the reason is that the simulation rewrote the FILE.** Nothing
rewrites the query here. The abstraction exists only inside one conjunctive
oracle's column space; no other route ever sees an abstracted term, and no
`sat` can be lifted from one. The concern was an artefact of the instrument, not
of the design — which is also why [ADR-2010]'s finding that the front door's
model replay does not cover parser-level rewrites does not apply: there is no
parser-level rewrite.

## 2. Obligation two: how the real collector differs from the integer one

**The soundness argument transfers verbatim.** Both are relaxations. Under any
model of the original, each abstracted subterm denotes *some* value; replacing
it by a fresh unconstrained column only adds solutions; so `abstraction unsat ⟹
original unsat`, and nothing in the other direction. Sharing is by `TermId` on a
hash-consed arena in both, which makes "two occurrences take one column" a fact
about the query rather than an assumption.

**What does not transfer is the CONSUMERS**, and that is the finding:

| | integer side (shipped) | real side (this ADR) |
|---|---|---|
| key | `BTreeMap<TermId, usize>` | same |
| shapes admitted | `Op::Apply` of `Int` sort | `Op::Apply` **and `Op::Select`** of `Real` sort — [ADR-2050] measured both refusing |
| column space | one `next_var` shared with symbol columns | **the real `Collector` had no `next_var` at all**; `index_of` used `vars.len()`, so adding opaque columns required a real refactor, not a flag |
| `sat` downgrade | at the one `CheckResult::Sat` site in `lia_simplex_capped` | at **two** `Decision::Sat` sites, plus a type |
| unsat evidence | none to re-export | a **`FarkasCertificate` whose public `vars` field maps a dense column to a `SymbolId`** — an opaque column has no symbol, so the certificate is deliberately NOT forwarded from the opaque path |

That last row is the part an argument-by-analogy would have missed.
`FarkasCertificate::verify` does not read `vars`, so the self-check inside the
decision is unaffected; what is refused is re-export to a consumer (the Craig
interpolant extractor) that would read an opaque column as a variable.

**Two latent column-space bugs surfaced**, both invisible with the mode off and
both wrong with it on: `nvars` came from `ctx.vars.len()` (symbol columns only),
and `simplex_fallback` keyed its model by POSITION in `vars` rather than through
`var_index`. The `QF_LRA` control (§4) exists to catch exactly these.

## 3. The guard-deletion result, and the round it took to get one

[Full matrix.](../../../bench-results/real-opaque-20260914/ref/guard-deletion.md)

**Round 1 came back FIVE SURVIVORS OUT OF FIVE.** Not because the guards are
redundant. Because every closure on this path produces a non-`sat`, so a
`!matches!(result, Sat)` assertion passes with any single one deleted. The suite
was testing the VERDICT; the guards are about WHICH LAYER produced it. That is
the same defect as "six of seven guards removable with everything still green",
reached from the other direction.

Three fixes, and they are the transferable part:

- **The sat-side tests assert the decline BY NAME.**
- **The simplex guard was made to name itself.** It returned `Ok(None)` — this
  function's "I could not decide, try the elimination" — so deleting it merely
  moved the decline downstream. It now returns `Some(Decision::Incomplete(…))`
  with its own text, which is also **strictly cheaper**: the elimination would
  have decided the same abstracted system feasible and declined again.
- The two `lra.rs` guards are invisible from outside the crate **by design**, so
  they get lib-side unit tests that call `decide_within_with_options` directly.

**Round 2:**

| mutant | tests killed |
|---|---|
| G1 `replayed_sat` | **1** (exactly one) |
| G2 `simplex_fallback` | **1** (exactly one, a different one) |
| G3 support fast path | 3 |
| G4 full path | 3 — *the same 3* |
| G5 `real_model_oracle` | **0 — SURVIVES** |
| C3 = every runtime guard at once | 5 |

**G3 and G4 kill the same three.** They are the two entry gates of one route and
this population reaches both. Said plainly rather than counted as two guards.

**G5 survives and cannot be made not to.** `has_opaque_real_apps` is true on
exactly the atoms the collector abstracts — the detector's arms ARE the
linearizer's arms, deliberately — so no fixture can separate the two oracles
while G3 and G4 stand. G5 is the layer that catches a future *widening* of the
abstraction the detector has not been taught about. Recording that is more
useful than manufacturing a fixture that pretends otherwise.

**What C3 proves.** With every runtime guard deleted the verdict is still
`unknown`: `no interpretation bound for function #0`, from the model replay. Two
closures survive every local edit — the replay (shipped, untouched here) and the
type. The suite is not decorative: it catches the removal of any *nameable*
guard. But **no single-hunk mutant of this design yields a wrong `sat`**, and
that is a property of the design, not a gap in the suite.

The suite is 20 tests, registered at L0 in `hooks/pre-push`
(`scripts/check-suite-gating.py` reports `gated=39` and FAILS naming this suite
when the line is removed — checked, not intended). **All 16 integration tests
fail with `AXEYUM_LRA_OPAQUE_APPS=0`**, so the suite measures this change and
not the ambient solver.

## 4. The A/B — and [ADR-2050]'s +6 was a FLOOR

**[ADR-2050]'s +6 was a SIMULATION outside the solver and is not quoted here as
anything else.** This is the measurement of shipped code that replaces it.

One binary (`edb12ee75` for the stability and control-execution passes,
`6ca42ce09` — differing only by a bool→enum refactor whose diff is one commit —
for the division sweeps), two env values, interleaved per file on the same
pinned core with the arm order rotating, 24 s, `ulimit -v` 8 GiB, four live
pinned slots (`s5` cores 2–3, `s6` cores 2–3), references on an idle `s7`.

**Polarity is INVERTED**, as [ADR-2025]'s is: `AXEYUM_LRA_OPAQUE_APPS` is a KILL
SWITCH, so the BASE arm is `=0` and the shipped arm is `env -u`. Stated in the
runner's header and asserted by a preflight that requires the two arms to differ
by mechanism before any measuring starts.

### `AUFLIRA`, the pinned 200-file full-span parity list

| | |
|---|---|
| **verdict** | **gain 14, loss 0, flip 0** |
| **exit status** | 200/200 identical; **0 regressions** (base `ok` → lever not `ok`) |
| denominators | undecided in base **36/200**; `ok` in base **200/200** |
| stability | **14/14 STABLE-GAIN**, three passes per arm, on the final binary |
| authorities | `:status` **14/14 unsat**, z3 **14/14 unsat**, cvc5 **14/14 unsat**; **0 disagreements at a comparable denominator of 14/14 on each** — fourteen agreements, not fourteen no-opinions |
| noise floor | same arm twice, whole division: **0 of 200** moved, 22 undecided in base |
| control `QF_LRA` | **0 of 200** moved, 0 exit regressions, 1.00x |

14 of 36 undecided rows is **38.9 %**, Wilson 95 % **[24.8 %, 55.1 %]** (plain
Wilson, no continuity correction). 14 of 200 files is 7.0 %, **[4.2 %, 11.4 %]**.
The noise floor and the control are each 0 of 200, **[0.0 %, 1.9 %]**.

For contrast, [ADR-2050]'s simulated 6 of 11 is quoted there as **[31.3 %,
83.2 %]**; a plain Wilson on the same counts gives [28.0 %, 78.7 %]. The
difference is a continuity correction, not a disagreement, and it is noted
rather than silently reconciled.

### Two things the simulation could not have told us

**All SIX of [ADR-2050]'s `AUFLIRA` witnesses convert, and so do eight more.**
Pre-registered **P3 predicted fewer than six would**, reasoning that the
simulation fed the ground checker a rewritten *skeleton* while the shipped path
must reach it through the quantifier rung, and that [ADR-2050] cause (D) is
exactly a case where the rung does not hand the ground checker what the
abstraction describes. **Wrong, and wrong in the conservative direction.**

**The converted rows are not decided by the route that was refusing.**

| | base arm `bound_by` | lever arm `decided_by` |
|---|---|---|
| 8 rows | `q:mbqi` | **`q:mbqi-quick`** |
| 6 rows | `q:egraph` | **`q:bool-skeleton`** |

`lira-dpll` decides none of them. The refusal sat upstream of several rungs, so
removing it hands each query to whichever rung reaches it first. A mechanism
column hard-coded to watch `lira-dpll` — which is what this lane wrote first —
would have printed `absent` in both arms and been dismissed as uninformative.

### The cost, split honestly

| population | base | lever | ratio |
|---|---:|---:|---|
| the 14 converted rows | 73.3 s | 2.2 s | **0.03x** |
| the 186 that did not move | 396.3 s | 528.8 s | **1.33x** |
| whole division | 469.6 s | 531.1 s | 1.13x |

The overall 1.13x is not the interesting number. Admitting an atom stops the
ladder refusing early, so on a query it still cannot decide the ladder now
spends more of its budget before giving up. That is the real trade and it is 33 %
on this division.

### The control's non-vacuity is OBSERVED, not inferred

`QF_LRA` was chosen because the edited functions run there while the abstraction
structurally cannot fire (no real UF application, no array). 93 of 200 rows were
undecided in the base arm, so the zero had room.

**But the inference was not available.** `control-nonvacuity.py` found the
binding routes on those 93 rows are `nra` (45) and `NONE` (41), with only 6 on
`dl-online` — not an `lra` route. So "the changed code runs here" had to be
measured: `control-executes.sh` reads `lra_entries` / `cube_decisions` off the
counter line and finds **`lra::decide_within` executing on 6 of 20 probed rows,
41 cube decisions**. That is what makes the zero a statement about the
column-space refactor rather than about a division the code never touches.

## 5. Decision

**Ship ON**, with `AXEYUM_LRA_OPAQUE_APPS=0` as the kill switch. The
pre-registered **R10** gate is met on every clause: ≥ 4 net (14), 0 losses,
0 flips, 0 exit regressions, 14/14 STABLE-GAIN, 0 authority disagreements at a
full denominator, control 0 and non-vacuous, gain far above a measured noise
floor of 0/200.

**Predicted post-merge value: `AUFLIRA` +14 and every other division unchanged**,
except `QF_UFLRA`, which is a secondary and not a control and whose measurement
is reported in §7 as far as it got. This is a prediction about *this branch's*
arm reproducing after the merge; nothing else in the ladder is touched.

## 6. The rules, against what happened

| rule | pre-registered | outcome |
|---|---|---|
| R1 | pinned pre-existing population, no prefix | §4 — `parity-lists/AUFLIRA.txt`, split into INTERLEAVED halves precisely so a half-finished run is not one family |
| R2 | interleaved, one binary, two env values | §4 |
| R3 | polarity stated, preflight asserts the arms differ | §4 — and the preflight earned its keep, see §4's route table |
| R4 | exit-status channel | §4 — 0 regressions over 200, reported beside the verdict count |
| R5 | 3 passes per arm on every moved row | §4 — 14/14 STABLE-GAIN |
| R6 | noise floor on a whole division | §4 — 0 of 200, 22 undecided in base |
| R7 | control that must not move, shown non-vacuous | §4 — and the non-vacuity argument I had planned was **not available**; it was measured instead |
| R8 | authorities, comparable denominator beside any zero | §4 — 14/14 on each of three |
| R9 | sat-side reference control is vacuous; control on the unsat half | every converted row is `unsat`; §1.2 records why no parser-level rewrite exists to replay |
| R10 | ship gate | §5 — met on every clause |
| R11 | measures THIS BRANCH; post-merge predicted | §5 |
| R12 | freshness by `find -newer` | `build.sh`; both binaries verified |
| R13 | no waiter greps for its own command line | every wait watches a TSV row count. The one `pgrep` run by hand DID self-match and was re-run with a bracketed pattern |
| R14 | unfinished checks reported as "did not run" | §7 |

**The predictions:**

| | predicted | measured |
|---|---|---|
| P1 | `Sat` exits closable, under 10 sites | **right** — 9 |
| P2 | the integer soundness argument transfers; the difference is in the consumers | **right**, §2 |
| P3 | fewer than 6 of the 6 witnesses convert | **WRONG** — 6 of 6, plus 8 more |
| P4 | control 0; `QF_UFLRA` nonzero | control **right**; `QF_UFLRA` see §7 |
| P5 | at least one LOSS in `AUFLIRA` | **WRONG** — 0 losses and 0 exit regressions |

P3 and P5 are the useful ones to have got wrong, and they are wrong the same
way: both assumed that admitting an atom would cost something visible. On this
division it did not. The cost is real and it is in the wall clock (1.33x on the
rows that did not move), which is exactly where a verdict count cannot see it —
so the instrument that caught it is the one R4 exists for.

## 7. Not measured here, and reported as "did not run"

- **`QF_UFLRA` (the secondary) had not finished when this ADR was written.** It
  is 200 pinned files on `s6` cores 2–3 and it is a secondary, not a control:
  real UF applications are its defining feature, so it is expected to MOVE, and
  a move there is a result rather than a regression. Its state is whatever
  `bench-results/real-opaque-20260914/ab/qfuflra-*.tsv` holds; if the files are
  absent or short of 100 rows each, the run did not finish and nothing about
  that division is claimed.
- **`control-executes.sh` over all 100 rows of `QF_LRA.a` had not finished.** The
  20-row probe is what §4 quotes and it is labelled as 20.
- **No division outside `AUFLIRA`, `QF_LRA` and `QF_UFLRA` was measured.** The
  corpus rate of this capability is unknown and [ADR-2050]'s R1 forbids
  transferring a per-division number.
- **The `AUFLIRA` sweep ran on `6ca42ce09`, not on final HEAD.** The only later
  change is one commit, a bool→enum refactor with no behaviour change
  (`git diff 6ca42ce09..HEAD -- crates/`), and the stability pass — 14/14
  STABLE-GAIN, three passes per arm — ran on the FINAL binary, which is the
  re-measurement.
- **Causes (B), (C) and (D) of [ADR-2050] are untouched.**

[ADR-1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-2010]: adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2025]: adr-2025-the-refutation-was-available-before-instantiating-and-we-dropped-the-assertion-carrying-it.md
[ADR-2050]: adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
