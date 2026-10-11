# ADR-6700: CAS step traces reconstruct through existing Complex ring laws

Status: accepted (bounded reconstruction; final integration gates remain open)
Date: 2026-10-11

ADR0601 requires admission through Kernel::add_declaration. A successful CAS
trace checker is insufficient. Reuse the existing Complex ring-law proof
construction for each complete before/after expression in a checked polynomial
trace, then compose those kernel proofs with Complex.Equiv.trans. The proof
subject is the original expression, not only its normal form or digest.

Translate only an explicitly supported integer-coefficient ring fragment first;
refuse fractions, division, transcendental heads, extra variables and excessive
coefficient magnitudes before constructing unary kernel numerals. Preserve input
syntax during translation: translating both endpoints via their normal form
would erase the claim being reconstructed. Use the CAS checker to validate
trace continuity and rule witnesses before attempting proof generation, but
admission remains an independent kernel check. Verify empty axiom footprint
from the admitted declaration. A corrupted endpoint or assumption must reject.

Initial implementation uses the existing in-tree Complex test bridge to prove
and compose a generated multistep trace, with positive admission and a false
statement negative control. This does not by itself establish a public API,
rational/conditional reconstruction or whole-goal completion; those remain
required extension work. Measure release cost and keep nonzero test counts.

## Adoption evidence — 2026-10-11

Release control run13258 completed:3 passed,0 failed,0 ignored,2655 filtered,
72.62 seconds. It admits a generated multistep identity, measures the admitted
declaration's empty axiom footprint, rejects the altered endpoint and changed
assumption context, and exercises explicit fractional/wide/domain declines.
At adoption, the current bridge file is byte-identical to tested revision
`97e700533`. Receipts and limits are in the [route inventory](../../plan/notes/cas-trace-kernel.md).
The current full workspace run is still uncredited; adoption does not replace
that integration gate or imply rational/conditional/general reconstruction.
