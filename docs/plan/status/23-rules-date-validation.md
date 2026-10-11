# Lane: rules-date-validation — enforce Rules input domains

<!-- plan-section: lane-status -->

**CON-7 R0 integration (`WIP`, rules-date-validation, 2026-10-11).**
Child fddf0d2b2. Validator accepted invalid Gregorian dates, Unicode-digit date
strings and bool as Int. Six input-control tests reproduce these failures;
fix uses ASCII canonical syntax plus datetime.date validation, and excludes
bool from integer inputs. Focused suite passed6/0 failures; existing validator
passed all7 packs. Baseline red: /var/tmp/axeyum-rules-date-before.log.
Next: private snapshot guard mutations (exactly one test per removed guard),
validator integration into dated/statute packs, broader Rules API closure.
Parent targeted gamma tests passed19/0 failed/ignored,3.90s;
/var/tmp/axeyum-feedback-cas-lint-tests.log. Complete lint15399 remains live.
Entire feedback objective remains incomplete; no legal applicability claim.
