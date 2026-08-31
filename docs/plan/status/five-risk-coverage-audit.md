# Lane: five-risk-coverage-audit — what the L0 programme bought, per risk

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, five-risk-coverage-audit, 2026-08-31).**
Report-only audit of ADR-0717's five risks (kernel unsoundness, statement
error, vacuity, contamination, false evidence) against every L0 gate. No
gate, census, fact or generator was edited. Full measurements and the
run-versus-read split in
[the audit](../../research/11-design-review/2026-08-31-five-risk-coverage-audit.md);
the seven findings that bind future work in
[ADR-1000](../../research/09-decisions/adr-1000-the-five-risks-are-covered-unevenly-and-vacuity-is-the-thin-one.md).

| risk | covered over | what is missing |
|---|---|---|
| 1 kernel unsoundness | S5: 35 cases, all 8 subsystems, zero Axeyum-accepts/Lean-rejects. S4: pinned Lean's kernel admitted 1,972 declarations | 8/8 mutant kills are a pinned human measurement, not re-derived. Positivity is implemented twice; only the shared predicate's `Const` arm is exercised |
| 2 statement error | 2,167 drift pins; 1,300 identity-bound; **582** hash-bound to pinned Mathlib; 9 type-checked against Lean's own reconstruction | a pin detects drift, not an error present when the pin was made — mutations 1-3 of the S1 mutation gate are caught by the pin alone. 585 of 594 mirrors never have their Axeyum type compared to Mathlib's |
| 3 vacuity | **8 of 2,167**, and all 8 are `Nat.totient`/CRT | 2,159 facts. 92 more name a control never shown to fire. 1,920 evidence rows declare a semantic `kind` while recording an axiom footprint |
| 4 contamination | S2 reaches ~1,956 centrally; 15 guards, each mutation-verified to kill exactly one case | **548 of those subjects (28%) are chosen by the `theorem_of` regex the tree documents as unreliable** — a wrong pick makes all four guards pass on the wrong subject. Per-fact evidence for target self-occurrence is 0 |
| 5 false evidence | every settled fact's checker re-run at gate time; gate-liveness ratchet; census controls run and are honest | replay checks exit 0, not discrimination. 696 facts have no checker naming their own subject. **The census was stale and `gen-safety-matrix.py --check` exited 1 during this audit** |

**Three cross-cutting numbers.** 434 facts (20%) hold exactly one protection
and it is a prelude-wide `--require-axiom-free` sweep; 105 hold none; and no
L0 gate runs in CI or `hooks/pre-push` — all eight are in `just check` /
`scripts/check.sh` only, which is why a red census went unnoticed for seven
hours.

**Two census corrections for whoever owns those columns.**
`independent_replay` at 7 is wrong in **both** directions: it misses all 9
checked-interchange roots (each reads `independent_replay: no`, and they are
the only facts with a published name-and-type real-Lean grade) and it includes
`F:schedule-critical-chain-infeasible`, crediting replay from an
argument-less `check-lean-gate.sh`. And ADR-0795's "only one gate publishes a
per-fact set" is superseded — C2's checked-interchange census publishes
`roots[].fact_id` today, uncredited, and S3's fixture pack publishes half of
one.

**Next.** Vacuity, and its first task is a fixture family outside
`Nat.totient`. It is the only risk whose honest number is under one percent
*and* has no central gate quietly covering the rest.

<!-- plan-section: landed-changes -->

| 2026-08-31 | five-risk-coverage-audit | Per-risk audit of the L0 safety programme: contamination reaches ~1,956 facts but 28% of those subjects are regex-chosen; vacuity reaches 8 of 2,167; `independent_replay` at 7 is mismeasured in both directions; 539 facts hold a prelude-wide sweep or nothing; no L0 gate runs in CI or pre-push (ADR-1000). Report only — nothing repaired. |
