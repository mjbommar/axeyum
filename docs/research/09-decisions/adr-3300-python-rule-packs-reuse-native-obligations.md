# ADR-3300: Python rule packs reuse metadata and native obligations

Status: accepted (bounded contract; final integration gates remain open)
Date: 2026-10-11

Pack loads existing schema-version-1 metadata/expected documents with matching
identity and bounded file sizes, and returns native outcomes for sorted SMT
obligation fixtures. It does not promote bare UNSAT to checked proof status.
Typed evaluators implement existing benefit eligibility, tax-benefit arithmetic
and procurement scoring models,
using source metadata and parameter fixtures, native terms, Date ordinal ranges
and SAT replay before exporting outputs. Missing facts are explicit rather than
false. Unsupported pack evaluators decline with NotImplementedError while their
obligations remain accessible. Source citations accompany every evaluation. Effective intervals are half-open:
from inclusive, to exclusive, with null endpoints unbounded. Complete facts
outside that interval return outside-effective-interval with no rule outputs.
A pack with no SMT fixtures rejects rather than returning an empty check set.

This loader is not a replacement for the repository's full pack validator. It
accepts a caller-selected local directory; sources are data, not executable code.
No statute applicability, complete pack coverage or theorem admission follows.
Tax lowering includes nonnegative income and the stated household-size bounds;
procurement includes the stated quality-score bounds. Ordinal Date comparisons
preserve the fixture calendar order. Authorization, category, grant and workflow evaluators additionally use finite
enum-to-Int maps or exact rational Real bindings. Every output model replays
before lifting; enum ordinals are checked before indexing. Non-temporal packs
require an explicit as_of date for applicability. Real components currently
carry an explicit 127-bit binding limit; floats are rejected. Category evaluation
handles the shipped single equivalence pair and declines a changed pair family.
A sourced statute template and complete integration remain CON-7 work.

## Adoption evidence — 2026-10-11

The implementation and negative controls were reviewed against this contract.
The fresh native consumer population includes the Date, pack metadata, pack
evaluation and deadline tests: 1166 passed, with one unrelated external SAT
checker test skipped. That external route passed separately with its configured
guarded checker. The offline validator controls were rerun at adoption: 20
tests passed; the recorded template validation checks four source snapshots
and replays one conditional certificate. Detailed provenance and private guard
controls remain in the [feedback completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md)
and [lane receipts](../../plan/notes/28-wide-real-smtlib-writer.md).

Acceptance adopts the stated bounded design, not a claim of legal applicability,
native Rust Date support, general theorem admission or completion of the full
feedback goal. The implementation branch still awaits final workspace checks
and integration into main.
