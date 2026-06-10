# BV Semantics And Partial Operations

Status: draft
Last updated: 2026-06-10

## Purpose

Pin down one concrete semantics for every bit-vector operation so the
evaluator, rewriter, bit-blaster, and external backends agree. Disagreement on
"undefined" cases is the primary source of false positives in differential
testing and of unsound rewrites.

## Scope

In scope:

- Total semantics for division, remainder, shifts, and width-edge cases.
- The ground evaluator as the executable specification.

Out of scope:

- Floating-point semantics.
- Source-language semantics (C undefined behavior, Rust overflow panics);
  those belong to frontends.

## Core Claims

- Every Axeyum operator must be total over its sort, with one documented
  result for every input. `unknown` is a solver result, never an operator value.
- SMT-LIB 2.6+ already made the hard cases total; Axeyum should adopt the
  SMT-LIB semantics verbatim so external oracles agree by construction.
- The ground evaluator in `axeyum-ir` is the semantic reference. Every rewrite
  rule and every lowering is tested against it on random and exhaustive
  small-width inputs.
- Frontends that need trapping or UB semantics should encode side conditions
  explicitly; the core never guesses.

## Edge-Case Table (SMT-LIB Convention)

| Operation | Edge case | Result |
|---|---|---|
| `bvudiv x 0` | Division by zero | All-ones (`2^n - 1`) |
| `bvurem x 0` | Remainder by zero | `x` |
| `bvsdiv`, `bvsrem`, `bvsmod` | Zero divisor / sign behavior | Defined via `bvudiv`/`bvurem` expansions; `bvsmod` follows divisor sign |
| `bvshl x k`, `k >= n` | Over-shift | Zero |
| `bvlshr x k`, `k >= n` | Over-shift | Zero |
| `bvashr x k`, `k >= n` | Over-shift | All sign bits |
| `extract h l` | `h < l` or `h >= n` | Static sort error at build time, never a runtime value |
| `rotate_left/right k` | `k >= n` | Rotation by `k mod n` |
| `concat` | Width overflow past max width | Static build error |

## Design Implications

- Implement and property-test the evaluator before the rewriter; the rewriter
  is then validated as "evaluator-equivalent on random inputs" from day one.
- For widths <= 8, edge-case operators (`div`, `rem`, shifts, rotates) should be
  tested exhaustively, not just randomly. This is cheap and catches the cases
  random testing misses.
- Signed operators should be defined in the IR as derived forms with explicit
  expansions, mirroring SMT-LIB, so only a small unsigned core needs trusted
  lowering.
- Recent SMT-LIB additions (overflow predicates such as `bvuaddo`/`bvsaddo`)
  are useful for program-analysis clients; track them as optional operators.
- The documented bit-order convention (see bit-blasting note) is part of the
  semantics and must be asserted in evaluator tests.

## Risks

- Backends predating SMT-LIB 2.6 totality, or configured in non-standard
  modes, can disagree on division by zero; differential harnesses must pin
  solver versions and options.
- Frontends may silently assume C semantics (shift UB, truncating division
  toward zero) and misreport Axeyum results as wrong.

## Open Questions

- [ ] Should checked/trapping variants (`div` with explicit nonzero guard) be
      offered as builder conveniences?
- [ ] Should the evaluator be exposed publicly in 0.1 or kept as a test oracle?
- [ ] How are the SMT-LIB overflow predicates prioritized relative to the core subset?

## Source Pointers

- SMT-LIB FixedSizeBitVectors theory: https://smt-lib.org/theories-FixedSizeBitVectors.shtml
- SMT-LIB standard: https://smt-lib.org/
- Bitwuzla documentation: https://bitwuzla.github.io/docs/
