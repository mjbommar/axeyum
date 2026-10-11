# ADR-2600: source-bound propositional Alethe reuses the clausal tail

Status: proposed; pending complete validation
Date: 2026-10-10

## Problem

The text proof front door returns no proof for `p` and `not p`. Its BV emitter
rejects non-BV predicates even though its internal propositional tail can already
produce Tseitin clauses and an LRAT-derived closed Alethe refutation. Adding a
second SAT engine or treating a rewritten formula as a source assumption would
introduce unnecessary obligations.

## Decision

Add a private pure-Boolean adapter before the existing theory emitters. Convert
Boolean source trees structurally before IR constant folding and preserve each original assertion as a unit
assumption. Reuse the existing Tseitin clauses, native proof-producing SAT core,
DRAT-to-LRAT elaboration and Alethe resolution tail. No unchecked rewriting or
new artifact format is introduced. Every returned proof must pass the in-tree
checker. Reject non-Boolean operands and unsupported operators explicitly by
returning no proof and continuing to existing routes.

Bound conversion to 128 assertions, 512 visited tree nodes, depth 32 and symbol
bytes 128. Bound SAT search by the caller deadline (ten seconds if absent) and
the native core's existing conflict limit. Decline on expiration or more than
20,000 emitted commands. These limits do not establish preemptibility inside
LRAT elaboration or checking; that remains a validation/implementation obligation.
Supported connectives are not/and/or/Boolean equality/xor/constants, plus binary
implication and Boolean ite using source-form clausification rows checked against
the exact gate and operand polarities. No scope completion is inferred from
this adapter; source reconstruction and arithmetic composition remain open.

## Evidence and trust boundary

Require source-bound positive refutations, SAT controls, missing-premise and
changed-assumption rejection, deterministic bytes, and independent Carcara
checking without holes. Kernel reconstruction/admission is a separate obligation.
Existing BV and quantified-tail callers retain the same default deadline behavior.
Constant pin rules require real checker support before constant cases can ship.
Mutation work must run in a private snapshot and kill exactly one targeted test.
Full solver/workspace and applicable front-door gates remain required.

External replay found that IR-only assumptions change `(not true)` to false.
The adapter therefore reads source assertions from the existing SMT S-expression
reader after typed script validation. The initial source collector declines
push/pop/reset, macros, annotations and query assumptions until their source
reconstruction contract is implemented. It bounds raw input to 64 KiB. Such
declines do not narrow the requested final coverage; they remain open work.
