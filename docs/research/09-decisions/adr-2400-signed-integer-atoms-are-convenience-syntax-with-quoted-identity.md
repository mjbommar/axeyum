# ADR-2400: signed integer atoms are convenience syntax with quoted identity

Status: accepted; bounded source/evidence contract adopted, final integration gates remain open
Date: 2026-10-10

## Context

CON-6 requests `-1` at the SMT text front door. Canonical SMT-LIB represents
negative integers with unary subtraction. The parser already accepts unbounded
positive numerals and resolves aliases, declared symbols, and named terms before
numeric parsing. Its lexer strips pipes from quoted simple symbols, including
`|-1|`; extending numeral recognition alone would turn an undeclared quoted
symbol into a literal.

## Decision

Accept an optional single leading ASCII minus followed by one or more ASCII
digits as integer convenience syntax. Apply it only after existing symbol and
alias lookup, preserving existing declared simple-symbol precedence. Reuse
`WideInt` and `int_const_big`; no i128 input ceiling is introduced. Leading
zeros and negative zero have their ordinary integer values.

Preserve pipes for quoted signed numeric-looking symbols, just as for quoted
unsigned numerals. Thus `|-1|` remains a symbol and never captures the unquoted
integer token `-1`. A declared simple symbol named `-1` still wins for unquoted
uses; quoted numeric-looking symbols deliberately retain a distinct key. This
extension reserves an unbound signed digit atom for convenience input while
keeping previous unquoted declaration behavior.

The writer emits canonical unary subtraction, including wide magnitudes and
i128::MIN. Signed decimals and leading plus are outside this extension; use
`(- 1.0)` for negative reals. Existing mixed Int/Real coercion applies to the
resulting integer constants. No new IR operator, solver encoding, or proof rule
is added: these spellings construct the same integer values as canonical input.
Model and proof replay operate on the existing typed terms.

## Validation and consequences

Public parser tests cover exact values, both sides of the i128 boundary, much
wider negatives, zero and leading zeros, writer round trips, quoted symbol
identity, declared-symbol precedence, lets/macros, coercion, abs/distinct and
malformed controls. Solver, Python, and CLI routes must be tested against fresh
builds before CON-6 is marked done. The audit's unidentified `notes/80` remains
unresolved; do not edit an unrelated historical note.

## Adoption and evidence scope

The bounded source/evidence contract is adopted. See the
[current receipts](../../plan/notes/28-wide-real-smtlib-writer.md) and
[completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
The implementation retains unsupported-route declines and source identity;
source-bound replay never substitutes search for checking. Parser/solver gates,
fresh native public-route tests and private source-binding controls supply the
recorded evidence. SAT clausal checking, checked source correspondence, external
proof checking and kernel admission remain separate claims. External reference
checks retain the pinned guard patches documented in
[scripts/patches](../../../scripts/patches/README.md); no unmodified-checker
credit or hole acceptance is inferred. Integer-only `lia_generic` proofs remain
internal-only; scopes/macros and broader portable theory reconstruction remain
explicit open coverage. This adoption does not declare the final workspace or
main integration gates complete.
