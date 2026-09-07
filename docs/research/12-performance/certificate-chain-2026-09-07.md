# certificate-chain lane diary, 2026-09-07

The lane's subject is the one axis no competitor contests: SMT-COMP has had no
proof track since 2024, the fastest checker for the main SMT proof format is
documented as not formally verified, and a kernel-checked pipeline pays a median
6.9% for *checking* while *production* is the real cost. Measured here
yesterday, DRAT recording at the SAT level costs under 1%. So the expensive half
is nearly free for us.

## Where the chain was broken when the lane opened

`with_artifact_recording` had exactly one call site, `evidence.rs:2609`, inside
`dl_decided_report`. Six of the seven one-shot theory routes still built
`crate::cdclt::CdclT`, which emits no proof at all, so their `unsat` reached the
front door as `Evidence::Unsat(None)` with `trusted_steps` EMPTY — the theory
reasoning trusted and *uncounted*.

## Step 1 — three routes onto the native core

`euf_egraph::check_qf_uf_online_cdclt`, `lra_theory::check_qf_lra_online_cdclt`
and `lia_theory::check_qf_lia_online_cdclt` now call
`native_cdclt::solve_native` instead of `CdclT::new(..).solve(..)`. The diff is
the one `dl_online` took in S7b: the outcome enum changes, and the Boolean-leaf
injector takes `&NativeModel` instead of `&CdclT` (both expose
`value(var) -> Option<bool>` with the same "never assigned" contract).

The inline `mod tests` in `lra_theory.rs` and `lia_theory.rs` keep their own
`CdclT` import: those tests pin the *adapter contract* against the driver they
were written for, and they are still worth running.

### The swap moved a give-up reason, and the existing suite caught it

`cdclt_lia_online::default_lia_wrapper_leads_with_generic_cdclt` went red on the
first build. Measured, not guessed — a scratch test printed the probe's actual
return:

```
before: Unknown { kind: Timeout,    detail: "timeout in the online CDCL(T) LIA driver" }
after:  Unknown { kind: Incomplete, detail: "online CDCL(T) LIA model did not replay
                                             (arithmetic outside the incremental engine)" }
```

Cause: `CdclT::solve_inner` tests `timed_out()` at the TOP of its main loop, so
an exhausted budget returns `Outcome::Unknown` having propagated nothing. The
native core checks less eagerly. At a zero budget it propagated both units of
`x > 0 ∧ x < 1`, reached `final_check`, got `Sat` from a theory with no budget
to say otherwise, and returned `Sat`; `lia_theory` then could not build an
integer model and reported `Incomplete`.

No verdict moved — the replay gate turned the vacuous `Sat` into `Unknown`, as
it is there to. But the *kind* moved, and
`dpll_lia::check_with_arith_dpll` branches on it: `budget_unknown_kind(Timeout)`
routes to the legacy loop with the remaining budget, `Incomplete` falls through
to a different arm. A route that silently changes which fallback runs is not a
swap.

Fix is at the engine boundary, in `solve_native`, so every route that moves
inherits it (`dl_online` included): an exhausted deadline returns `Unknown`
before the formula is even built. The test in `native_cdclt/tests.rs` is
discriminating rather than vacuous — its fixture is Boolean-satisfiable and
theory-refuted, so *without* the check the same call returns `Unsat`, and it
carries a no-deadline control proving that.

This is the S7b finding restated in a second currency: that lane found a model
change costing a verdict (MBQI), this one found a deadline-check granularity
change costing a give-up reason. Both are the same shape — the engines differ in
places that are not the Boolean search.

## Step 2 — the string route, and the two routes left behind

`string_theory::check_qf_s_online_cdclt` joins the three above. Its only
non-mechanical part is `SatModelCtx::solver`, a `&CdclT` held purely to read
skeleton-only Bool leaves off the trail; it becomes `&NativeModel`.

`uflra_online` and `uflia_online` are **not** moved, and that is a decision
rather than an omission. Both read `CdclT::theory_propagations()` as a
diagnostic out-param. On the native core that counter lives behind
`TheorySolveOptions::collect_layer_stats`, which turns on per-call clock reads,
so porting it is its own change with its own measurement. `ufbv_online` also
stays: it is the one client of the incremental protocol (S7a step 3), which has
no port yet.

So four of the seven one-shot routes now run the proof-producing core, plus
`dl_online` from S7b. Three do not.

## Step 3 — the trust step reaches the front door

Two halves.

**The dispatcher.** `produce_evidence` resets the artifact channel, wraps its
`auto::solve` call in `with_artifact_recording`, and attaches
`theory_refutation_steps()` on the two BARE `Evidence::Unsat(None)` arms. That
is the empty ledger slot the family page names.

**The ambiguity guard**, which is why it is not two lines. The channel publishes
the LAST refutation, and `auto::check_auto` does not call the engine once: it
enumerates case-split branches (`auto.rs:1298`, `auto.rs:1458`) and reports
`unsat` only when EVERY branch was refuted, discarding each branch's own
`CheckResult::Unsat`. The artifact left behind then refutes the last branch, not
the query. `take_last_theory_refutation` therefore counts refutations since the
last reset and hands one back only when there was exactly one. Relaxing that
`== 1` in a private snapshot killed exactly one test,
`two_refutations_in_one_dispatch_publish_nothing`.

### Small queries do not reach the bare arm, and that shapes the metric

Measured through `produce_evidence` while wiring this:

| fixture | kind |
|---|---|
| QF_UF transitivity `a=b ∧ b=c ∧ ¬(a=c)` | `unsat-alethe` |
| UF pigeonhole (3 elements, 2 constants) | `unsat-bool-euf-exhaustive` |
| Boolean-structured QF_LIA | `unsat-arith-dpll` |

Each is a stronger certificate, and each producer runs ahead of the fallback —
exactly what `dl_decided_report`'s `PRE_SOLVE_ALETHE_MAX_NODES` gate already
assumes. The ADR-1704 step is a LARGE-query metric. Which is why the next piece
had to exist.

## Step 4 — the number, at corpus scale

`smtcomp_cli --evidence` now prints `trusted=<n>[:<label>[+],…]` between
`certified=` and `recheck=`.

**The position is forced, and finding that out was the change's real cost.**
`scripts/execute-autogenesis-operation.py` parsed the line with a regex anchored
at both ends that required `certified=` to be immediately followed by
`recheck=`. Every placement broke it — appending after `ms=` hits the `$` just
the same. That regex is now named-group with `trusted=` optional, so a
transcript recorded before the field still parses, and `parse_observation`'s
returned dict is deliberately unchanged because it is digested into receipts.
The two shell consumers use greedy `.*<key>=\([^ ]*\)` seds and are unaffected
wherever it goes; that was checked, not assumed.

### The measurement

Release binary, `taskset -c 0-7`, `--timeout-ms 8000` inside a
`timeout -k 2 30s` backstop, first 40 files of each committed parity list. The
harness's exit status depends on the finding: a verdict contradicting the file's
declared `:status` is a nonzero exit, so a clean run is a live check.

| division | files | `unsat` | carrying a trust step | of those, ADR-1704 |
|---|---:|---:|---:|---:|
| QF_IDL | 40 | 3 | **3** | **2** |
| QF_LIA | 40 | 4 | 4 | 0 |
| QF_UF | 40 | 16 | 1 | 0 |
| QF_LRA | 40 | 0 | 0 | 0 |

Zero contradictions of `declared` in any division.

Read it honestly, division by division:

- **QF_IDL is the ADR-1704 result.** All three refutations carry a step. Two are
  `sat-refutation-modulo-theory` (uncertified, as ADR-1704 requires) and one is
  `sat-refutation+` — a refutation where the theory contributed no lemma at all,
  so the Boolean DRAT alone refutes the CNF and `check_drat` verified it. The
  grade is a subtraction on the artifact, and here it is visibly doing work in
  both directions.
- **QF_LIA's four steps are `farkas+`, and they are not new.** They come from
  the pre-existing Alethe route. What is new is that a sweep can now SEE them.
- **QF_UF is the finding.** Sixteen refutations, one step. Fifteen of them
  arrive as `unsat-bool-euf-online`, whose evidence producer attaches no trusted
  step at all — so moving `euf_egraph` onto the proof-producing core does not
  surface, because those refutations never reach the arm that reads the channel.
  The route move is necessary and was not sufficient. Wiring
  `check_bool_euf_online_evidence` to the channel is the obvious next slice and
  this lane did not do it.
- **QF_LRA decided nothing at an 8 s budget**, so its row is a budget statement
  and not a certificate statement. Do not read a zero there as a gap.

## Step 5 — the preprocessing witness, and what a straight port missed

`witness_function_abstraction` ports ADR-1721 §7 onto `eliminate_functions`, and
`AckermannUnsatCertificate::recheck` gains it as step 2.

**The straight port did not catch the defect it exists for.** Mutating
`eliminate_functions` so every application of one function shares one fresh
symbol turns the SATISFIABLE `f(a) = 1 ∧ f(b) = 2` into a wrong `unsat`. With
the value comparison in place, `recheck` still returned `Ok(true)`:

```
shipped elimination                    -> no certificate over the SAT query
mutated, value comparison only         -> certificate PRODUCED, recheck = Ok(true)
mutated, value comparison + structural -> certificate PRODUCED, recheck = Ok(false)
```

The reason is that the two sides are compared as **Booleans**. `f(b) = 2` and
`f(a) = 2` are both simply `false` at almost every sample, and agreement on
`false` is not agreement. A sampled value comparison is probabilistic on exactly
the axis that matters, and the array witness's success on its own defect class
was partly luck about which mutation happened to move a Boolean.

So the witness carries a second, **structural** count. Every `Op::Apply` subterm
of the ORIGINAL assertions must have an entry in the interpretation the
abstraction's own application list built, at that sample's argument values. A
merged or dropped application leaves one with no entry, which does not depend on
luck.

Two more shapes worth keeping:

- The first version of the confusion control compared `f(y) = 2` against
  `f(x) = 2` and **passed wrongly**, for the same both-sides-`false` reason. A
  negative control can be vacuous as easily as inverted, and this one was
  vacuous until it was run.
- The two corner samples (all-zero, all-ones) cannot distinguish two
  applications at all: every symbol holds the same value there, so `x` and `y`
  are equal and `f` is asked at one key. A test measures that gap rather than
  asserting the sample count is "enough".

Mutation controls on the witness's own guards, private snapshot, baseline
bracketing green: never incrementing `unnamed_applications` kills **exactly
one** test; never recording a value disagreement kills **three** — the three
value-comparison tests, reported as three rather than trimmed to one, because
they are three distinct fixtures over one guard.

Sampled, so `TrustId::Ackermann` stays uncertified. Evidence, not proof.
