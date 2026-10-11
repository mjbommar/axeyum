# Lane: cas-python-native-parser — shared production grammar

<!-- plan-section: lane-status -->

**LIB-6 X2 (`WIP`, cas-python-native-parser, 2026-10-11).** Child a95216e37.
ADR6900 migrates Python parse to native grammar with character-span translation,
explicit surrogate errors and native byte/final-AST caps. Binding and wrapper
implemented; former Python implementation retained as private reference.
Check4896 passed (1m33s), /var/tmp/axeyum-cas-python-native-check.log.
Native build37851 remains live; stub generation launched, no runtime pass yet. Added native
vs37 reference fixtures, UTF8 byte/character/surrogate controls and final AST
subtraction caps. Fixture generator now uses the independent private reference.
User guide documents tightened native bounds. Next: fresh sealed package/test
runs, stubs and required gates. Source binding frozen during compilation.
Python source length guard now rejects before UTF8 allocation; discriminating
control passed1 test against local wrapper/sealed prior native (no new binding
called). Full native runtime suite still pending. Entire goal remains incomplete.
