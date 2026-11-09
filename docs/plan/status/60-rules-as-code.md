# Lane: rules-as-code — statutes lifted from the U.S. Code and checked as rule packs

<!-- plan-section: lane-status -->

**Rules-as-code (`WIP`, rules-as-code, 2026-11-09).** 18 U.S.C. § 1030 is lifted
from GovInfo (`scripts/uscode_lift.py`: 104 provisions, 49 resolved reference
targets) and compiled through the provision-keyed rule IR (`scripts/rules_ir.py`:
anchor, literal, dependency, and reference gates). The CFAA pack has 8 checked
obligations in `rules_as_code_examples` (4 certified `unsat-arith-dpll`, 4
replayed `sat` findings) and a 221,184-row three-way validator sweep. Next, in
order: lift the OLRC USLM XML for Title 18 and diff it against the GovInfo lift;
model § 1030(b) and the attempt clauses; model the (g) limitations period as date
arithmetic; lift § 1029 and check a rule spanning both sections. Detail:
[`docs/rules-as-code/ROADMAP.md`](../../rules-as-code/ROADMAP.md).

<!-- plan-section: landed-changes -->

| 2026-11-09 | `d0db9a442` | Real-statute rules-as-code: § 1030 lift, provision-keyed rule IR, CFAA pack with 8 checked obligations. |
