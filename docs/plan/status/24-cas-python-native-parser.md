# Lane: cas-python-native-parser — shared production grammar

<!-- plan-section: lane-status -->

**LIB-6 X2 (`WIP`, cas-python-native-parser, 2026-10-11).** Child a95216e37.
ADR6900 migrates Python parse to native grammar with character-span translation,
explicit surrogate errors and native byte/final-AST caps. Binding and wrapper
implemented; former Python implementation retained as private reference.
Check4896 passed (1m33s), /var/tmp/axeyum-cas-python-native-check.log.
Native build37851 passed3m04s; stub generation72621 passed3m29s:27 modules/661 items.
Sealed package /data0/axeyum/artifacts/python/cas-python-native-parser-fa_a312k/package,
SHA2567989e34f4deaf1c9982823d3d6e14b74b6fd179317f379cabbc859c2ba689f71.
Initial runtime run46 passed/2 failed: test regexes mismatched actual native
source-byte/shape messages. Corrected assertions; rerun48 passed/0 skipped,
/var/tmp/axeyum-cas-python-native-parser-tests-v2.log. Native/parser source unchanged. Added native
vs37 reference fixtures, UTF8 byte/character/surrogate controls and final AST
subtraction caps. Fixture generator now uses the independent private reference.
User guide documents tightened native bounds. Next: fresh sealed package/test
runs, stubs and required gates. Source binding frozen during compilation.
Python source length guard now rejects before UTF8 allocation; discriminating
control passed1 test against local wrapper/sealed prior native (no new binding
called). Focused native runtime suite passed; broad combined Python suite/stubs pending. Entire goal remains incomplete.

Runtime stub drift passed27 modules/1874 symbols/5 aliases/319 dunders;
type gate1823 params/1738 typed/131 Any all allowlisted/46 Any returns95.3%.
Generated cas stub carries native parser transport. Targeted lint launched.
Combined Python72341 passed1120/0 skipped,67.53s against sealed native;
/var/tmp/axeyum-cas-python-native-combined.log. OMT review confirms unbounded parsing remains
in optimize_smtlib/lex/typed paths, despite search deadline sharing; next lane.
