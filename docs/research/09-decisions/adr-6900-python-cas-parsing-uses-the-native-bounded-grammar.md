# ADR-6900: Python CAS parsing uses the native bounded grammar

Status: accepted; bounded surface adopted, final integration gates remain open
Date: 2026-10-11

Route axeyum.cas.parse through the ADR6800 Rust parser via an internal binding
that returns an expression or a structured byte-span diagnostic. Preserve Python
ParseError and its character offsets by translating UTF8 byte spans. Reject
unpaired surrogates explicitly. Native intake limits apply:8192 bytes and final
lowered AST64 nodes/depth32, including subtraction/reciprocal syntax. These can
reject inputs previously admitted by Python's character/builder-only limits.
Document and test those tightened bounds rather than silently maintaining two
production grammars. Parsing still carries no proof or denominator license.

Retain the former Python implementation privately as a differential reference,
not a runtime fallback. Unsupported native syntax must remain a parse error.
Verify grammar fixtures, exact wide amortization, precedence/domains, character
spans and paired source/AST bounds against a freshly built extension.

## Adoption and validation boundary

This bounded surface is adopted on the feedback implementation branch. Current
CAS library tests and the fresh native consumer suites cover exact values,
transport, parser/domain controls and explicit unsupported/resource outcomes;
see the [validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md).
Signed-power fuzzing includes guaranteed zero-base negative-exponent and
undefined-base seed classes. Private Pi/source-binding controls remain recorded
with exact intended failures. Production Python parsing uses ADR-6900; ADR-3100
is historical and superseded. Promoted transport does not widen every arithmetic
operation, and Pi bounds or parsed expressions do not grant kernel admission.
The final workspace/all-target gates and main integration remain open.
