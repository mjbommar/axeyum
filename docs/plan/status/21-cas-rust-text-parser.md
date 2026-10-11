# Lane: cas-rust-text-parser — native bounded exact expression syntax

<!-- plan-section: lane-status -->

**LIB-6 X2 (`WIP`, cas-rust-text-parser, 2026-10-11).** Child1ac2e66f7.
ADR6800 specifies native grammar matching current Python parser, exact decimals,
Pi distinction, signed powers, byte-span diagnostics and explicit intake caps.
Implemented native tokenizer/Pratt parser, exact BigInt decimal conversion,
Pi/unary/signed powers and byte errors. Final lowered AST also checks64 nodes/
depth32 because subtraction/negative powers add syntax nodes. Initial compiles
caught NthRoot(3) and fallible Rational conversion; corrected, no tests credited.
Compile4076 passed9.82s: `/var/tmp/axeyum-cas-rust-parser-check-v3.log`.
Next: structural/negative/resource
controls, Python differential corpus, canonical wire agreement and broad gates.
Entire feedback goal remains active; parent consolidated build remains separate.

Added5 behavioral tests with constructor/precedence/wide/Pi/wire agreement,
unary heads, malformed UTF8 byte spans and paired resource controls. Test51221
passed5/0 failed/ignored: `/var/tmp/axeyum-cas-rust-parser-tests.log`.
Parent kernel release controls passed3/0 failed/ignored,72.62s.

Differential suite48239 passed6/0 failed/ignored:37 independent Python grammar
fixtures (24 accepted/13 rejected), canonical AST wire comparison. Fixture
generator records sealed native SHA. `/var/tmp/axeyum-cas-rust-parser-differential.log`.
Parser lint passed after one semicolon formatting fix: `/var/tmp/axeyum-cas-rust-parser-clippy.log`, v2 log passed7.90s.
Combined Python run originally failed collection(missing pinned SymPy); installed
SymPy1.14.0/mpmath1.3.0, rerun45817 passed1100/0 skipped,68.95s against sealed combined binary
SHA2560f638f71c1cd68b3e6cf35260f1f10e945938c3137a982ea2c2072fd9dd2cf76.
AddedRust parse_text example exporting canonical wire; example run launched,
`/var/tmp/axeyum-cas-rust-parser-example.log`, uncredited.
