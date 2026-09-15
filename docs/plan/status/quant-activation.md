# Lane: quant-activation — the instance clause carries its own activation literal (ADR-2120)

<!-- plan-section: lane-status -->

**Lane QUANT-ACTIVATION (`WIP`, quant-activation, 2026-09-15).** Sizing is
landed before any Rust, and it moved the target. [ADR-2113](../../research/09-decisions/adr-2113-uflia-the-instance-we-never-produce.md) named a
boolean-assignment guard on quantifier activation as the fix for
`rej_nocontext`; read against both references at `file:line`, the artifact z3
and cvc5 actually produce is a **valid clause** — z3 `¬q ∨ body[x:=t]`
(`qi_queue.cpp:274-289`), cvc5 `(=> q body)` which its CNF stream turns into the
same clause (`instantiate.cpp:293`) — and this repository **already builds that
clause** in `positive_instance_formula` (`qinst_egraph.rs:1587`), where the
residual context IS the activation literal. What blocks it is
`PositiveContext`'s path whitelist: `BoolAnd`/`BoolOr` steps only.

**Measured over all 1,200 Tier 1 rows of the six quantified divisions, joined to
the ledger verdict:** the shipped whitelist computes a context on **3 of 525
undecided files**; **97 of 525 (18.5 %)** hold a positively occurring split
universal it refuses — `UFLIA` 52 of 114, `AUFLIRA` 11 of 22, `UFNIA` 23 of 146,
`AUFDTLIRA` 4 of 81, `UF` 6 of 106, `UFDTLIRA` 1 of 56. The broad shape ceiling
(368 of 525, 70.1 %) is reported and then **refused by its own control**: 499 of
675 DECIDED files (73.9 %) hold it too, so shape presence is not a predictor and
only the narrow column is a ceiling. `qshape.py`'s predicted shape-guard exit
agrees with [ADR-2114](../../research/09-decisions/adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md)'s observed one on **126 of 129** files and on **82 of 85**
of the discriminating subset where containment is equality; all three
disagreements run one way.

**Two findings the sources do not record.** (a) A positive replacement enters
`ground` but never `ground_derivations`, so `collect_ground_derivations`
(`qinst_egraph.rs:4957`) declines and any `unsat` downstream of one ships
**uncertified** — sound, but with the evidence path severed, and there is no
`QuantifierGroundDerivation` variant that could describe it. (b) ADR-2113's
claim that `OnlineQuantifierClauseSession` abstracts every arithmetic atom is
refuted: `with_opaque_bool_atoms` is never called, so on an arithmetic atom the
session **declines to exist** — which inverts its follow-on claim that the
session suppresses the interleaved check on `UFLIA`.

**Open:** the lever itself (polarity tracking through `BoolNot`, `BoolImplies`
and the two `Ite` branches, with the `Ite` condition, boolean `=`/`xor` and every
`Forall` step still refused), the certificate variant that closes (a), the
fixtures, the mutation control and the six-division A/B. Nothing ships until the
number exists; ADR-2120 is `proposed`.

<!-- plan-section: landed-changes -->

| 2026-09-15 | quant-activation | ADR-2120 §1: the `PositiveContext` whitelist computes a context on **3 of 525** undecided Tier 1 files across six quantified divisions, while **97** hold a split universal it refuses |
| 2026-09-15 | quant-activation | `qshape.py`: a polarity-tracking shape classifier with 7 controls, DAG counts (the first version printed a 105-digit integer), and a `c2`/`c7` pair that separates the shape the engine handles from the shape it drops |
| 2026-09-15 | quant-activation | `exit-agreement.py`: the predicted shape-guard exit joined to ADR-2114's 134 observed rows — 126/129, and 82/85 on the discriminating subset, with all disagreements in the safe direction |
| 2026-09-15 | quant-activation | ADR-2120 §2: the instance clause is `¬q ∨ body[x:=t]` on both references and already exists here as `positive_instance_formula`; z3 DELETES it on backjump (`smt_context.cpp:2560`) while cvc5 keeps it for the whole check-sat — a cost decision, not a soundness one |
