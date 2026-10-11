# Lane: cas-python-native-parser — shared production grammar

<!-- plan-section: lane-status -->

**LIB-6 X2 (`WIP`, cas-python-native-parser, 2026-10-11).** Child a95216e37.
ADR6900 migrates Python parse to native grammar with character-span translation,
explicit surrogate errors and native byte/final-AST caps. Binding and wrapper
implemented; former Python implementation retained as private reference.
Check4896 remains live; native build launched, no pass credited. Added native
vs37 reference fixtures, UTF8 byte/character/surrogate controls and final AST
subtraction caps. Fixture generator now uses the independent private reference.
User guide documents tightened native bounds. Next: fresh sealed package/test
runs, stubs and required gates. Source binding frozen during compilation.
Entire feedback goal remains incomplete.
