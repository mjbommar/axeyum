# Lane: quant-ground-incremental — the cold ground check and the warm session are alternatives (ADR-2124)

<!-- plan-section: lane-status -->

**Lane QUANT-GROUND-INCREMENTAL (`DONE`, quant-ground-incremental,
2026-09-16).** [ADR-2120] §7 named the ground closure as the quantified
divisions' block. The mechanism turns out to be one `if`.

**What it is.** `prove_quantified_unsat_via_egraph_impl` selects between two
interleaved ground-check sites on `online_clauses.is_none()`, and
`OnlineQuantifierClauseSession::new` builds its encoder with no opaque
abstraction — so `EufEncoder::encode` returns `None` on the first Boolean-sorted
application it has no arm for, an integer comparison is one, and the whole
construction refuses. A `UFLIA` ground set has one in its first round, so the
loop takes the cold branch for its **entire run**, on every file in four
divisions, and nothing in it ever tries again.

**The first version of this block overstated that, and the probe's own numbers
caught it.** It said the two were "alternatives, not companions" and that a live
session never re-solves. 38 of 53 cores ran an IDENTICAL number of cold checks in
both arms, which suppression cannot produce. The true difference is **seven
rounds**: the no-session branch checks on rounds 0–6 and then 7, 15, 31, …; a
live session skips to the exponential schedule alone. On top of that a live
session changes what each round DOES (candidate equalities on a starved round),
so the arms' round sequences diverge and counts can differ by more — the heaviest
core goes 30 → 15 — in either direction.

Neither reference solver does this, verified at `file:line` in the checked-out
clones. z3 internalizes the instance clause into the live `smt::context`
(`qi_queue.cpp:336` → `smt_context.h:1781` → `smt_internalizer.cpp:1460`) and
continues the same search (`smt_context.cpp:4174` `case FC_CONTINUE: break;`);
cvc5 sends it as a lemma into the running prop engine (`instantiate.cpp:339` →
`theory_engine.cpp:1659` → `prop_engine.cpp:296`). **Two guesses in the brief
were wrong**: there is no `context::add_clause` in z3 5.1.0.0, and
`Instantiate::addInstantiation` does not reach `TheoryEngine::lemma` directly.
Both are corrected in the ADR rather than repeated.

**Sizing, measured before any code was written.** On [ADR-2120]'s 53
reference-minimal `UFLIA` cores the interleaved check ran on **45 of 53**, **493
calls**, median 11 and max 29 per core, over sets whose per-core maximum has
median 1,356 and max **8,019** terms; **33 of 53** died on the clock and 32 of
those had run it. Asserting each term once is 71,127 against a linear-growth
estimate of 437,373 re-solved — **6.1x**. On the Tier 1 ledger the quantifier
route's own last decline names the interleaved check on **108 of 1,400**, **101**
of them ending `unknown`: UFNIA 44/200, UFLIA 28/200, AUFDTLIRA 18/200, AUFLIRA
6/200, UF 4/200, UFDTLIRA 1/200, QF_NIA 0/200 (unquantified control).

**One absence is stated, not zeroed.** [ADR-2120] did not commit `cores/raw/`,
so per-core `qf-check` WALL TIME is not recoverable from the ledger. This lane
measures it with `AXEYUM_QTRACE=1`, which the loop's own call site already emits.

**The lever.** `GROUND_SESSION_LEVEL` / `AXEYUM_QINST_GROUND_SESSION`, **shipped
at 0**, which is byte for byte the historical behaviour. At level 1 the encoder
gets `with_opaque_bool_atoms(true)`, the session exists on an arithmetic ground
set, and the loop asserts instances into it instead of re-solving.

**Soundness, twice over and independently.** The abstraction is a WEAKENING:
replacing an atom by a free propositional variable only ADDS models, so `unsat`
of the skeleton transfers back and `sat` says nothing. And the session's `Unsat`
is never the verdict — `scoped_candidate_fixpoint_step` reaches `Refuted` only
through `replay_online_refutation`, the ordinary cold quantifier-free route over
the same ground set. There is no retraction to go stale on either — `ground` is
only appended to and every insertion is `add_permanent_clause` — and **this
lane's own mutation corrected its reading of why**: removing
`add_checked_batch`'s `unwind_to_root()` killed nothing, because
`NativeIncrementalCdcl::add_clause` (`incremental.rs:486`) calls
`between_solves()` itself, unconditionally. What the session's call buys is
LIVENESS (closing the theory epoch so `add_atom_at_root` accepts a
registration), not soundness, and it is measured by its own suite.

**A certificate hole is closed in the same change.** The
`CandidateFixpointStep::Refuted` exit returned `unsat` with **no** instance-set
certificate, while the two cold-check exits beside it both collect one from the
same `(anchor, ground, ground_derivations)` triple. It was nearly invisible while
the session declined every arithmetic file; at level 1 that exit becomes the main
refutation route on `UFLIA`, so a lever shipped without this fix would have
converted certified refutations into bare ones.

**The 53-core probe: the cores move.** OFF 15 decided, ON **16**; one core moved
and it is a GAIN, **0 losses, 0 flips**. The mover's interleaved-check cost drops
from 12.7 s over 27 calls to 0.7 s over one. Across all 53 the check ran on 45 in
both arms; **48.4 s removed of 452.4 s (10.7 %), 3.8 % of the whole budget**, and
the negative half is reported beside it: 20 cores gain (57.3 s), **11 cores lose**
(−9.1 s), 22 unchanged. The session suppresses the cold check on only 13 of 53.
**The regime change is larger than the seconds**: `budget` 29 → **24**,
`incomplete` 9 → **13**, so five cores leave "died on the clock" for an honest
fixpoint, and the detail naming the interleaved ground check drops from 13 rows
to 8. A file reporting a fixpoint has the instance SET as its next blocker rather
than the clock.

**The six-division A/B: −4 over 1,200 rows, 0 verdict disagreements.** AUFDTLIRA
−1, AUFLIRA −1, UFDTLIRA −2, UF/UFLIA/UFNIA +0; nonzero exit statuses 3 on EACH
arm, so the lever created none. Every one of the 8 raw movers re-checked 3× per
arm on one pinned core: **1 STABLE-GAIN, 5 STABLE-LOSS, 2 UNSTABLE.** The single
stable gain is `UFLIA/simplify/javafe.ast.TypeDeclElemPragma.373` — the **same
file the 53-core probe moved**, the only agreement between the two populations.

**Ship decision: OFF.** 0 flips MET; **0 stable losses NOT MET (5)**. The gain and
the losses are the same mechanism from both sides: skipping the first seven
per-round cold checks returns budget to a loop that needs more rounds, and
removes a refutation from a file whose ground set was already refutable in those
rounds. **The held-out draw was not run** — it confirms a lever that passed its
A/B, and drawing a blind population to score one that is not shipping spends the
population for nothing.

**Three red gates, all attributed to the box and not to this diff, with control
distributions on BOTH trees.** Serialized (`--test-threads=1`) this tree is
**1576 / 0**. Main flakes on the same test
(`auto::tests::pathological_overbound_stays_terminal_under_every_policy`, 1 of 4
main runs). And removing this lane's four fixtures made the sweep WORSE, not
better (3 failures against 1) — so it is not this lane's fixtures crowding the
pool either. `quantified_route_trace` is 1-of-3 red on main at load 9–10 and its
assertion is its own non-vacuity guard. `progress_frontier` is green twice, 12
passed, no REGRESSION.

[ADR-2120]: ../../research/09-decisions/adr-2120-quantifier-activation-by-assignment.md

<!-- plan-section: landed-changes -->

| 2026-09-16 | quant-ground-incremental | ADR-2124: the interleaved cold ground check fires behind `online_clauses.is_none()`, so one integer comparison in the ground set puts the whole run in the re-solve regime — the mechanism behind ADR-2120 §7's block, located at `file:line` |
| 2026-09-16 | quant-ground-incremental | sizing before code: 493 cold checks over sets up to 8,019 terms on 53 cores (6.1x more terms re-solved than asserted once); 101 of 1,400 Tier 1 rows end `unknown` with the quantifier route's own last decline naming the check |
| 2026-09-16 | quant-ground-incremental | `AXEYUM_QINST_GROUND_SESSION` (OFF): the retained session hosts an arithmetic ground set by abstracting the unencodable Boolean-position term, with a vacuous-session guard and a no-connective guard |
| 2026-09-16 | quant-ground-incremental | `CandidateFixpointStep::Refuted` shipped `unsat` with no instance-set certificate while the two cold exits beside it collected one — closed on the same facts (that exit is reached only through the cold replay) |
| 2026-09-16 | quant-ground-incremental | 53-core probe: **+1 decided, 0 losses, 0 flips**; 48.4 s of 452.4 s of ground re-solve removed (20 cores gain, **11 lose**), and five cores leave the clock for an honest fixpoint (`budget` 29 → 24) |
| 2026-09-16 | quant-ground-incremental | the mutation that SURVIVED is the finding: `unwind_to_root` is not the stale-clause guard — `NativeIncrementalCdcl::add_clause` unwinds unconditionally — it is the theory-epoch close, and the overclaim is corrected in place |
| 2026-09-16 | quant-ground-incremental | six-division A/B **−4 over 1,200, 0 verdict disagreements**; movers re-checked 3x/arm: **1 STABLE-GAIN, 5 STABLE-LOSS, 2 UNSTABLE** — ship criterion NOT met, lever stays OFF, held-out draw not spent |
| 2026-09-16 | quant-ground-incremental | three red gates attributed to the BOX with control distributions on both trees: serialized this tree is 1576/0, main flakes on the same test, and REMOVING this lane's fixtures made the sweep worse (3 vs 1) |
| 2026-09-16 | quant-ground-incremental | the certificate repair and the `unwind_to_root` call are both measured UNCOVERED (two mutation suites, 9 and 1 tests, both SURVIVED) — recorded rather than assumed |

