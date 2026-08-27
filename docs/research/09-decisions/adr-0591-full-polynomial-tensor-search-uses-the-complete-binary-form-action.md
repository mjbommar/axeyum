# ADR-0591: Full-polynomial tensor search uses the complete binary-form action

Status: accepted
Date: 2026-08-26

## Context

ADR-0567 removes only permutation of rank-one summands from the complete tensor-rank SAT
encoding. The sustained `P_6@16` formula remained undecided after more than seven hours. Full
polynomial multiplication is highly structured: homogenizing degree-below-`n` polynomials as
binary forms of degree `n-1` exposes a `PGL(2,F)` action. Over `F_2`, scalar quotienting is
trivial and this is `GL(2,F_2)` of order six. Global interchange of the two multiplicands
doubles the tensor action to twelve.

This is prior symmetry mathematics and prior implementation, not a new technique. Wang's
current public lower-bound source documents and tests the same binary-form representation for
full multiplication, including the six-element `F_2` group and its contragredient action on
input constraints. General lex-leader symmetry breaking goes back at least to Crawford et al.
(KR 1996).

## Decision

Axeyum adds an opt-in complete polynomial-specific encoding. It independently enumerates all
six invertible two-by-two matrices over `F_2`, constructs their homogeneous binary-form
substitution matrices at degrees `n-1` and `2n-2`, applies inverse-transpose to both input
covector factors and direct substitution to the output factor, and composes each with optional
global input swap.

Summands remain lexicographically ordered as in ADR-0567. For every one of the twelve actions
and every summand, the encoding requires slot zero to be lexicographically no larger than that
transformed summand. This is complete: from any decomposition orbit, choose a globally smallest
term among every transformed term, apply its global tensor automorphism, move that term to slot
zero, and sort the remainder. No assumed decomposition symmetry or preferred orbit is imposed.

Known witnesses are canonicalized independently before pinning by transforming and sorting all
twelve images, then choosing the lexicographically smallest sequence. SAT still gains credit
only after the original tensor equation replays; UNSAT still requires checked DRAT.

## Evidence

Three focused controls pass. The twelve actions are distinct and every image of Karatsuba
replays. The enhanced encoding preserves the exact `P_2` boundary: rank three is SAT and lifts,
while rank two emits a DRAT proof accepted by Axeyum. At the target dimensions, all twelve
images of the 36-term schoolbook `P_6` decomposition replay all 396 coefficients. Wang's
published rank-17 `P_6` witness canonicalizes, pins, solves, lifts, and replays in 23 ms.

The new `P_6@16` formula has 26,489 variables / 105,262 clauses, 1,809,746 DIMACS bytes, and
SHA-256 `00e5038f47c1dde3425e03cddd3625151c645ea6ddd1edbc24c3f9dc4291ddb2`.
This is a search reduction, not a rank result. Focused tests, all-target warning-denied Clippy,
and warning-denied Rustdoc pass.

## Alternatives

- Pin one attractive first term: rejected because it assumes an orbit representative without a
  complete argument.
- Encode a full lex leader over sorted transformed decompositions: sound but substantially
  larger; minimum-first already supplies one representative per orbit, with harmless residual
  ties.
- Copy Wang's implementation: rejected. Axeyum independently constructs and coefficient-replays
  the action under its own covector/output convention.

## Consequences

Polynomial tensor searches gain a reusable, family-native symmetry mode rather than a P6-only
clause patch. The formula is roughly twice the ordered-only size, so performance must be measured;
symmetry correctness does not imply a solver speedup. The retained ordered formula and its live
producer remain valid and unchanged until a controlled comparison justifies replacing it.
