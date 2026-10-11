# Clause-to-predicate crosswalk

| Source/model premise | Encoding |
|---|---|
| Initial day excluded; positive day period | nominal ordinal = start ordinal + days, days > 0 |
| Weekend endpoint omitted | admitted iff weekday is Monday–Friday |
| Holiday endpoint omitted | admitted iff not in caller's complete holiday set |
| First admitted endpoint after omission | earliest admitted candidate at or after nominal |
| §§645.13/645.14 exceptions | explicit false flags for successive-week and month periods |
| Applicability | explicit true caller fact; not inferred from retrieval/edition |
| Holiday fact authority | source identity plus inclusive complete coverage |
| Representation/resource boundary | Date years 1–9999; bounded day/rollover work |

`computed` includes nominal date, skipped dates and final endpoint. Missing facts,
calendar coverage, unsupported applicability and budget exhaustion carry no
final date. A partial scan never becomes a certified deadline.

Native constraint obligations now cover replayed feasible endpoints, no earlier
admitted candidate, uniqueness, and reference agreement. Weekdays are computed
from ordinal modulo seven in native ground IR, independently of producer weekday
calculation. The current route replays feasibility but has bare UNSAT for the
other two obligations; verification is validated, not checked-native. Their UNSAT
results require a separately identified proof/recheck route before proof credit.
