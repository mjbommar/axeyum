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
Pack intake now rejects duplicate JSON keys, non-object documents and bool
schema versions. Local facade with sealed native passed52 metadata/pack/date/
statute tests,3.81s. Intake controls: duplicate/object/version removals each kill exactly1 of2
paired tests in private405b55811 snapshot with revised otherwise-valid duplicate
fixture; restored originals. /var/tmp/axeyum-rules-intake-control-*.log.
Next: source/calendar authority and applicability evidence, general obligation
proof routes, intake controls and full feedback closure.
Full CAS3957 passed2147/0 failed/11 ignored,411.14s; complete lint13564
passed932/932 targets,27 crates,0 diagnostics,14576 fresh inputs. Workspace81069
remains live. Logs /var/tmp/axeyum-cas-rust-parser-full-cas.log and
/var/tmp/axeyum-rules-runtime-full-clippy.log. Full objective remains incomplete.

Validator now includes statute manifests, required files and fixture populations.
Opt-in --statute-certificates checked1 native-backed conditional fixture; default
reports0 replayed explicitly. Expanded suite17 passed. Private85932e31a snapshot
with new tests:6 manifest guards each kill exactly1 of7 tests; native real replay
rejects changed claim. Originals restored. /var/tmp/axeyum-statute-guard-*.log.
Next: dashboard integration, authority/applicability and general proof routes.
