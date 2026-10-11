# Lane: rules-date-validation — enforce Rules input domains

<!-- plan-section: lane-status -->

**CON-7 R0 integration (`WIP`, rules-date-validation, 2026-10-11).**
Child fddf0d2b2. Validator accepted invalid Gregorian dates, Unicode-digit date
strings and bool as Int. Six input-control tests reproduce these failures;
fix uses ASCII canonical syntax plus datetime.date validation, and excludes
bool from integer inputs. Focused suite passed6/0 failures; existing validator
passed all7 packs. Baseline red: /var/tmp/axeyum-rules-date-before.log.
Metadata now validates both interval dates and a strictly later finite end,
matching the facade half-open interval semantics. Expanded suite passed10/0
failures; all7 packs still validate. Input controls stop at first failure per
method so private guard deletion produces exactly one failure. Private snapshot cb15712ce: calendar/integer guards each kill exactly1 of6
input tests; interval ordering kills exactly1 of4 metadata tests. Originals
restored bytewise. Logs /var/tmp/axeyum-rules-date-v2-{calendar,integer,interval}.log.
Pack loader now rejects invalid/noncanonical/empty/reversed intervals at load
time. Local changed facade plus sealed combined native binary passed35 tests
(metadata/packs/dates),2.33s; native source unchanged by this Python run.
Runtime guard controls passed in private47c91033e snapshot: type/canonical/
order removal each turns2 passing tests into1 failed/1 passed; originals restored.
Logs /var/tmp/axeyum-rules-runtime-control-{type,canonical,order}.log.
Next: broader dated/statute integration and full feedback closure.
Parent targeted gamma tests passed19/0 failed/ignored,3.90s;
/var/tmp/axeyum-feedback-cas-lint-tests.log. Complete lint15399 terminated101 after930/932 targets: four duplicate
doc_markdown diagnostics at CAS expr.rs275 (ValueError/BudgetExceeded).
Corrected both backticks; complete rerun still required.
Parent full CAS3957 passed2147/0 failed/11 ignored,411.14s;
/var/tmp/axeyum-cas-rust-parser-full-cas.log. Workspace81069 and complete
lint13564 confirmed live. Entire objective remains incomplete; no legal claim.
