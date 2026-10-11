# ADR-2700: real proof scalars use checked closed arithmetic and explicit rewrite bridges

Status: proposed; pending complete validation
Date: 2026-10-10

## Problem

`(* (- 1.0) x)` solves UNSAT in the reported contradictory example but has no
Alethe proof. The LRA proof checker classifies only RealConst leaves as scalar
factors, rejecting unary-minus constants. Existing numeric rendering uses `p/q`
as an atom, which is not portable numeral syntax. Nested negation additionally
requires a source-preserving bridge before Carcara's linear-arithmetic rule.

## Decision

Evaluate a scalar only through a whitelist of RealConst, unary negation, and
binary addition/subtraction/multiplication with checked exact Rational arithmetic.
Bound traversal to 512 visits and depth 32. Variables and applications never
become constants through a model or heuristic evaluation. A closed quotient is
materialized separately only when checked division succeeds; an unknown or
zero denominator retains the existing opaque-term abstraction and cannot be
used as a multiplication coefficient. Nonlinear products decline.

Reuse canonical signed numeral/division rendering, with checked numerator and
denominator access so unsupported promoted values decline instead of panicking.
Preserve original source-term assumptions. Remove double unary negations using
explicit minus_simplify equality steps, lift those steps through surrounding
terms with congruence, and use checked Boolean equality clausification/resolution
to obtain normalized arithmetic assumptions. Farkas/resolution then closes the
refutation. The new checker supports only the double-negation identity of
minus_simplify; other simplifications remain unsupported.

## Required evidence and limits

Require unary, commuted, nested and fractional negative coefficients; zero and
positive SAT models replay; variable/nonlinear/undefined coefficients decline;
changed or omitted rewrite evidence rejects. Independently check exact exports
with pinned Carcara, without holes (Int/Real numeral subtyping is explicit).
Mutation tests run in private snapshots and must kill exactly one targeted test.

Full solver/workspace and arithmetic differential gates remain required before
integration. General source reconstruction, macro/scoped scripts, arithmetic
proof-budget preemption and kernel reconstruction are separate unfinished
obligations. This fixes a reported route without claiming all LRA portability or
all EVD-6 milestones complete.
