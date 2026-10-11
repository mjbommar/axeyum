# Lane: rules-dates — typed Gregorian source sorts and model lifting

<!-- plan-section: lane-status -->

**Rules Date facade (`WIP`, rules-dates, 2026-10-11).** ADR-3200 proposes
Python Date/Duration terms over integer ordinals, years 1–9999, range obligations
and retained source sorts. Initial facade implemented; eight public Python tests pass, including Date
range, leap/century/year boundaries, source-query replay and type rejection.
Pack loader reads all seven metadata sets; typed benefit evaluator passes
fixture witnesses with SAT replay and missing/applicability statuses. Combined
Python: 13 tests pass; four benefit obligations return native UNSAT (no proof
check claim). Tax/procurement evaluators now replay all 210 generated bounded rows; combined
Python: 18 tests pass. All seven now have typed evaluators; enum/Real lowering passes 251 additional
generated rows. Combined Python: 24 tests pass. Enum guard mutation kills exactly
one targeted test. Real binding limit and explicit as_of are documented. Sourced Minnesota day-period template now computes under explicit applicability
and calendar assumptions: 31 combined tests pass, including 124 reference cases.
Native feasibility/minimality/uniqueness validate all 124 reference cases;
34 Python tests pass. Feasible models replay; UNSAT remains uncertified.
Verdict guard mutation kills exactly one test. Finite-window certificates now replay native ground facts in a separate process;
35 Python tests pass. Least-endpoint guard mutation kills exactly one test.
Certificates remain conditional; native UNSAT/kernel proof routes are open.
Next: validator integration and complete CON-7
validation. No integration/completion claim.
