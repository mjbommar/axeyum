# ADR-6900: Python CAS parsing uses the native bounded grammar

Status: proposed
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
