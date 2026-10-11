# Lane: signed-literals — CON-6 parser compatibility and identity

<!-- plan-section: lane-status -->

**Signed integer literals (`WIP`, signed-literals, 2026-10-10).** Implements
optional ASCII minus with unbounded integer construction, declared-symbol
precedence, and preserved quoted numeric identity. Writer stays canonical;
signed decimals require unary subtraction. ADR-2400 records the decision.
Public parser package passed 380 tests including 5 new regressions;
Fresh isolated Python extension passed all 12 selected tests with SAT replay.
Fresh solver front door passed 1/1 and fresh CLI passed 6/6.
Required
required front-door/workspace gates remain pending. `abs`/`distinct` parse and
receive semantic controls. Exact `notes/80` location remains unknown.
