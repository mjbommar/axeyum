# Lane: agent-axreal — the axiomatized reals are renamed before they are retired

<!-- plan-section: lane-status -->

**`Real` -> `AxReal` (ADR-0522 step 1) turned two green assertions red and
rotted six more no validator was looking at (`WIP`, agent-axreal, 2026-08-19).**
Trusted surface unchanged and re-measured: `complex 0 · creal 0 · integer 0 ·
logic 0 · nat 0 · rat 0 · string 0 · real 30`, rows now `AxReal.*`.

**Caught.** `CReal` contains `Real`.
`the_theory_front_door_accepts_the_farkas_route` asserted
`contains("Real.add_le_add")` against a module the shipped route emits over the
CONSTRUCTED carrier — `CReal.add_le_add` satisfied it, so it could not tell the
carriers apart. `infeasibility_farkas_lean`'s "carries ordered-field content"
scan matched `ty.contains("Real.le")`, satisfied by `CReal.le`, and that example
is the checker command of the `proved` fact
`F:schedule-critical-chain-infeasible`, whose notes had transcribed the
collision as a finding. Both now name the carrier in full and stay able to
fail. Third and fourth instances of one collision; only the first was ever
noticed, and it was worked around rather than fixed.

**Broken, and the gap that hid it.** Six evidence rows on three settled facts
are `grep -E` patterns anchored on an example's stdout. `validate-facts.py` said
`340 facts, 0 errors` throughout — it never runs a `checker_command`;
`check-fact-evidence-replay.sh` is the gate that does. One of the six asserts a count of **zero** and so survived the rename by
going vacuous. All 18 rows on the affected facts re-run clean after the fix.

**A rename is not a retirement, so the ledger got a verb for it.**
`--accept-population-change` would have dropped 30 rows to `unclassified` and
filed them as retired — a 30-row reduction that never happened.
`--accept-rename OLD=NEW` re-keys live rows, carries their classification, and
takes type and digest from the measurement: `rows=30`, `retired=35`,
`unclassified=0`. Three guards, each mutation-checked to kill one test.

**Measured.** kernel `--lib` 393; solver `--lib --features full` 1223; the
three carrier examples green with controls non-vacuous (12/17/8 carrier axioms
over `AxReal` against 0 over `CReal`); ledger `--check`, golden pins, clippy on
STABLE (609/609) and rustdoc green. **Next:** ADR-0522 step 2.
[Notes](../notes/71-axreal.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | `c26e492b1` | **The axiomatized reals are renamed `AxReal` (ADR-0522 step 1), and two green assertions were reading the wrong carrier.** `CReal` contains `Real`: a front-door test asserting `contains("Real.add_le_add")` was satisfied by `CReal.add_le_add`, and `infeasibility_farkas_lean`'s ordered-field scan by `CReal.le` — the latter is a `proved` fact's checker command. One string literal moves the whole 30-row package. `--accept-rename OLD=NEW` is new: routing a rename through `--accept-population-change` would have published 30 retirements that never happened. |
