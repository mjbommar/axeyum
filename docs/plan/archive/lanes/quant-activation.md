# Lane: quant-activation — the instance clause carries its own activation literal (ADR-2120)

<!-- plan-section: lane-status -->

**Lane QUANT-ACTIVATION (`DONE`, quant-activation, 2026-09-15).** The mechanism
is built, sound, certified and **SHIPS OFF** — and the measurement that matters
is not the A/B, it is what the 53 cores still fail on with activation ON.

**What it is.** [ADR-2113] named a boolean-assignment guard as the fix for
`rej_nocontext`. Read at `file:line` on both references, the artifact z3 and
cvc5 EMIT is a **clause** (`¬q ∨ body[x:=t]`), and this repository already builds
it in `positive_instance_formula` — the residual disjunct IS the activation
literal. What blocked it was `PositiveContext`'s path whitelist, measured at
**3 of 525** undecided files. `AXEYUM_QINST_POSITIVE_PATH` level 1 tracks
polarity instead; the `ite` condition, boolean `=`/`xor`, every crossed binder
and every NEGATIVE arrival stay refused. A second blocker — the driver refusing
outright when every universal is nested — was found by running fixtures, not by
reading. The certificate hole (a replacement entering `ground` but never
`ground_derivations`, so the `unsat` shipped uncertified) is closed in the same
change.

**Ship decision: OFF.** Pinned A/B **−1 over 1,200 rows, 0 verdict
disagreements**; re-check **1 STABLE-GAIN / 1 STABLE-LOSS / 2 UNSTABLE** against
a criterion of 0 stable losses. Held-out **+0 over 948 of 1,200** (still running
at close-out, reported at the denominator reached). Level 0 is verdict-identical
to the pre-Rust binary on **66 DECIDED files, 0 disagreements** — measured
separately, because both A/B arms are the new binary.

**THE HANDOFF, and it is the whole point of the lane.** On [ADR-2113]'s 53
reference-minimal `UFLIA` cores with activation ON: **660,992 tuples handed off
on 16 cores where the shipped arm handed off none**, 41,230 instances admitted,
**87.9 % of z3's own substituted terms already in our ground set**, `qf-check`
running on **45 of 53** over sets up to **8,019 terms** — and **verdict moved on
0 of 53**, with **31 of 53 dying on a clock that names the ground closure** (13
in its own words: *"the interleaved ground check did not decide the set inside
the deadline"*). **The block is neither triggers ([ADR-2113]) nor datatypes
([ADR-2114]) nor activation. It is the GROUND CLOSURE over the instance set.**
Two costs are already located: `quantifier_qf_check` re-solves the WHOLE
accumulated set from scratch every time it is due, and
`OnlineQuantifierClauseSession` **declines to exist** on any ground set carrying
an arithmetic atom, so `UFLIA` structurally cannot reach the warm path.

**Three of this lane's own instruments were wrong first**, and two were caught by
a measurement rather than by re-reading them: a `let`-tree count that printed a
105-digit integer; a `widen_target` column that scored both A/B losses at zero
(corrected ceiling **218 of 525**, discrimination control still flat); and a
level-0 identity check whose first population could not fail. A single
reach-probe observation was published as a conversion and then **refuted by this
lane's own re-check**; it is retracted in place, not deleted.

<!-- plan-section: landed-changes -->

| 2026-09-15 | quant-activation | ADR-2120 §7: on ADR-2113's 53 cores with activation ON, **verdict moves on 0 of 53** while 660,992 tuples are handed off and 87.9 % of z3's substituted terms are ours — **31 of 53 die on a clock naming the GROUND CLOSURE**, which is the next lane's target |
| 2026-09-15 | quant-activation | `AXEYUM_QINST_POSITIVE_PATH` (OFF): polarity-tracked positive positions + the loop running on registrations alone; pinned A/B −1 over 1,200 rows, re-check 1 STABLE-GAIN / 1 STABLE-LOSS, criterion not met |
| 2026-09-15 | quant-activation | `QuantifierPositiveReplacementCertificate`: a positive replacement entered `ground` but never `ground_derivations`, so every `unsat` downstream of one shipped UNCERTIFIED — closed with an owner-chain checker |
| 2026-09-15 | quant-activation | level-0 identity: the new binary with the lever unset is verdict-identical to the pre-Rust binary on 66 DECIDED files, 0 disagreements (the first population was vacuous and is kept, labelled) |

| 2026-09-15 | quant-activation | ADR-2120 §1: the `PositiveContext` whitelist computes a context on **3 of 525** undecided Tier 1 files across six quantified divisions, while **97** hold a split universal it refuses |
| 2026-09-15 | quant-activation | `qshape.py`: a polarity-tracking shape classifier with 7 controls, DAG counts (the first version printed a 105-digit integer), and a `c2`/`c7` pair that separates the shape the engine handles from the shape it drops |
| 2026-09-15 | quant-activation | `exit-agreement.py`: the predicted shape-guard exit joined to ADR-2114's 134 observed rows — 126/129, and 82/85 on the discriminating subset, with all disagreements in the safe direction |
| 2026-09-15 | quant-activation | ADR-2120 §2: the instance clause is `¬q ∨ body[x:=t]` on both references and already exists here as `positive_instance_formula`; z3 DELETES it on backjump (`smt_context.cpp:2560`) while cvc5 keeps it for the whole check-sat — a cost decision, not a soundness one |
