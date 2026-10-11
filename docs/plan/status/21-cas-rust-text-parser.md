# Lane: cas-rust-text-parser — native bounded exact expression syntax

<!-- plan-section: lane-status -->

**LIB-6 X2 (`WIP`, cas-rust-text-parser, 2026-10-11).** Child1ac2e66f7.
ADR6800 specifies native grammar matching current Python parser, exact decimals,
Pi distinction, signed powers, byte-span diagnostics and explicit intake caps.
Implemented native tokenizer/Pratt parser, exact BigInt decimal conversion,
Pi/unary/signed powers and byte errors. Final lowered AST also checks64 nodes/
depth32 because subtraction/negative powers add syntax nodes. Initial compiles
caught NthRoot(3) and fallible Rational conversion; corrected, no tests credited.
Compile4076 live: `/var/tmp/axeyum-cas-rust-parser-check-v3.log`.
Next: structural/negative/resource
controls, Python differential corpus, canonical wire agreement and broad gates.
Entire feedback goal remains active; parent consolidated build remains separate.
