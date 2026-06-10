# Logics And Decidability

Status: draft
Last updated: 2026-06-10

## Purpose

Define the logical fragments Axeyum should prioritize.

## Scope

In scope:

- Boolean logic, bit-vectors, arrays, EUF, and limited combinations.

Out of scope:

- Full quantified first-order logic.
- Higher-order logic.
- Complete nonlinear arithmetic.

## Core Claims

- Boolean SAT is the lowest common denominator and the target of many reductions.
- QF_BV is the first practical SMT fragment for systems and infosec users.
- Arrays are the natural logical model for memory, but practical engines often use
  layered memory models before lowering to array constraints.
- EUF becomes important for abstraction, uninterpreted summaries, and array reasoning.
- Floating-point and quantified formulas should be deferred until the core path is stable.

## Initial Logic Ladder

```text
Bool
  -> BV(n)
  -> QF_BV
  -> QF_ABV / arrays over BV indices and BV values
  -> QF_AUFBV / arrays plus uninterpreted functions
  -> selected extensions
```

## Design Implications

- `Sort` should be explicit and interned.
- `Bool` and `BV(1)` should be distinct in the core, with explicit conversion ops.
- Arrays should not be forced into the first SAT-only milestone.
- Backends should advertise supported logics and feature capabilities.

## Risks

- Treating all formulas as bit-vectors can simplify early work but makes later
  theory extensions awkward.
- Adding arrays too early can hide more tractable memory-overlay strategies.

## Open Questions

- [ ] What is the minimal public logic for `axeyum-ir` 0.1?
- [ ] Should arrays be represented in the IR before the first bit-blaster supports them?
- [ ] Should uninterpreted functions be first-class or delayed until array/EUF work?

## Source Pointers

- SMT-LIB logics: https://smt-lib.org/logics.shtml
- Boolector supported BV/array logics: https://github.com/Boolector/boolector
- Bitwuzla documentation: https://bitwuzla.github.io/docs/

