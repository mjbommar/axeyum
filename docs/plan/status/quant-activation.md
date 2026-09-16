# Lane: quant-activation — the instance clause carries its own activation literal (ADR-2120)

<!-- plan-section: lane-status -->

**Lane QUANT-ACTIVATION (`WIP`, quant-activation, 2026-09-15).** The mechanism
is BUILT, SOUND, TESTED and DEMONSTRATED, and it ships **OFF**.

**What it is.** [ADR-2113] named a boolean-assignment guard on quantifier
activation as the fix for `rej_nocontext`. Read at `file:line` on both
references, the artifact z3 and cvc5 actually produce is a **valid clause** —
z3 `¬q ∨ body[x:=t]` (`qi_queue.cpp:274-289`), cvc5 `(=> q body)` turned into
the same clause by its CNF stream (`instantiate.cpp:293`) — and this repository
already builds it in `positive_instance_formula`, where the residual context IS
the activation literal and the ground solver's own search is the assignment.
What blocked it was `PositiveContext`'s path whitelist (`BoolAnd`/`BoolOr`
only). `AXEYUM_QINST_POSITIVE_PATH` level 1 tracks polarity instead: `not`
flips, `=>` flips its antecedent, an `ite` BRANCH keeps; the `ite` CONDITION,
boolean `=`/`xor` and every crossed binder stay refused, and arriving NEGATIVE
is a refusal.

**A second blocker, found by running the fixtures rather than reading the
code:** when every universal is nested, the driver returned "no universal is
asserted; the nested quantifiers present are registered, not instantiated"
BEFORE compiling any registration — so the machinery was unreachable on exactly
the shape it exists for. Level 1 lets the loop run on registrations alone.

**The certificate hole is closed in the same change.** A positive replacement
entered `ground` but never `ground_derivations`, so `collect_ground_derivations`
declined and any `unsat` downstream of one shipped UNCERTIFIED.
`QuantifierPositiveReplacementCertificate` + `check_positive_replacement` now
require the owner to be an assertion or carry its own checked derivation, and
re-derive the conclusion.

**It works, measured twice.** `quantifier_positive_path.rs` 15/15: the
conversion fixture is `unknown` at level 0 and **`unsat` at level 1**, differs
from its SAT twin in ONE polarity, and its refutation is required to carry a
`PositiveReplacement` derivation. On the REAL corpus, `reach-probe.sh` shows arm
B handing off **18,944** and **18,688** tuples where arm A hands off zero, and
on the SPARK shapes `rej_nocontext` 628 → 0 with `rej_handoff` 0 → 592.

**And the corpus does not pay for it.** Interleaved per-file A/B, one binary at
two env values, 24 s / 8 GiB, four pinned s6 physical core pairs, **991 of 1,200
rows**: **−1 total, 0 verdict disagreements, 2 nonzero exit statuses per arm
(the same rows)**. The gain is a `UFLIA` file that IS a widen target; the two
raw losses are timing-shaped (1.5 s arm-A `unsat` against a 22.9 s arm-B
`unknown`). Movers are NOT yet re-checked. **The ship criterion — 0 stable
losses — is not met, so level 0 ships and ADR-2120 stays `proposed`.**

**The sizing column was wrong and the A/B caught it.** The first
`widen_target` scored every universal inside another binder as out of reach; the
engine starts its walk at the MATRIX of a top-level universal, so a universal
there is at a positive position of its owner. Corrected: **218 of 525**
undecided files, not 97 — and the discrimination control still refuses the
reading, 41.5 % undecided against 42.2 % decided. Both columns are kept.

**Open:** the last 209 A/B rows, `recheck-movers.sh` over the movers, and the
held-out draw (1,200 files, already drawn and committed, seed 20260915).

<!-- plan-section: landed-changes -->

| 2026-09-15 | quant-activation | ADR-2120 §1: the `PositiveContext` whitelist computes a context on **3 of 525** undecided Tier 1 files across six quantified divisions, while **97** hold a split universal it refuses |
| 2026-09-15 | quant-activation | `qshape.py`: a polarity-tracking shape classifier with 7 controls, DAG counts (the first version printed a 105-digit integer), and a `c2`/`c7` pair that separates the shape the engine handles from the shape it drops |
| 2026-09-15 | quant-activation | `exit-agreement.py`: the predicted shape-guard exit joined to ADR-2114's 134 observed rows — 126/129, and 82/85 on the discriminating subset, with all disagreements in the safe direction |
| 2026-09-15 | quant-activation | ADR-2120 §2: the instance clause is `¬q ∨ body[x:=t]` on both references and already exists here as `positive_instance_formula`; z3 DELETES it on backjump (`smt_context.cpp:2560`) while cvc5 keeps it for the whole check-sat — a cost decision, not a soundness one |
