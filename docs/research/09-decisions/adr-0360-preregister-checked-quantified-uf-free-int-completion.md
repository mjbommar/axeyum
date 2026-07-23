# ADR-0360: Preregister checked quantified-UF free-Int completion

Status: proposed
Date: 2026-07-22

## Context

Accepted ADR-0359 raises the 256-case quantified-UFLIA smoke differential from
111 to 178 checked SAT results. It leaves 39 Z3-SAT cases at the ordinary
satisfiable-instantiation boundary. All 39 contain one or two free integer
symbols in or alongside the universal source. ADR-0359 intentionally preserves
the ground candidate's scalar assignments, so an assignment chosen without the
universal can make every bounded default-only completion fail.

The retained diagnostic first fixed those symbols to values from one complete
Z3 model; 23 of 39 cases then pass the existing Axeyum finite-profile checker.
The original production-shaped probe used the ground Axeyum model, source
integer literals, zero, and checked predecessor/successor values. It reported
33 of 39 checked SAT after 180 candidate queries, but implementation validation
found that the probe truncated oversized pools and fixed generator-declared
symbols absent from the actual assertion sequence. Those are legitimate search
experiments, but they do not measure the stricter policy below. Replaying the
exact assertion symbols and declining rather than truncating closes **28 of
39**. Eleven remain honest Unknowns: seeds 23, 30, 32, 70, 111, 122, 150, 175,
182, 231, and 242.

## Decision

**Add one bounded, deterministic, untrusted candidate search over at most two
free `Int` symbols in the exact assertion sequence of a query with an already
admitted ADR-0357/0358 universal, before the ordinary single-binder MBQI
refinement loop.**

The increment will:

- collect only free `Int` symbols occurring in the exact assertion sequence,
  excluding every universal bound symbol; zero symbols or more than two
  decline;
- build one stable pool from zero, same-sort scalar assignments in the initial
  ground candidate, every exact source `IntConst`, and checked `-1`/`+1`
  neighbors; more than 16 distinct values declines rather than truncates;
- enumerate the complete scalar Cartesian product under a checked 256-tuple
  cap and the existing shared wall-clock deadline;
- obtain each candidate by adding temporary equality fixings only to an
  untrusted quantifier-free candidate query; `Unsat`, `Unknown`, error, or
  timeout under a fixing never transfers to the original query;
- run this search once, before ordinary MBQI instantiation, and leave the
  existing refutation loop in control after any decline; and
- return SAT only when ADR-0357/0358 finite-profile checking, optional
  ADR-0359 default repair, and canonical `check_model` all accept the exact
  original assertion sequence without the temporary fixings.

The scalar choices and temporary equalities are search hints, not evidence.
The returned scalar assignments, complete UF interpretations, source-bound
certificates, and exact original-query replay remain the checkable artifact.
Symbols occurring only in ground assertions remain eligible: the frozen
measurement includes cases where fixing such a symbol changes deterministic QF
model generation enough to expose a certifiable UF model, even though the
fixing itself is absent from the accepted source and evidence.

## Evidence gates

Acceptance requires:

1. Representative one- and two-scalar cases complete to checked SAT while
   their original ground constraints and explicit UF table points replay.
2. The frozen 39-seed remainder produces at least the measured 28 checked SAT
   results under the exact 16-value/256-tuple policy; the eleven declared
   residual seeds remain soundly classified unless a separately explained
   existing route also checks them.
3. Temporary-fixing `Unsat`, `Unknown`, timeout, and error results are ignored;
   no refutation or evidence object may contain a fixing.
4. Zero/more-than-two relevant symbols, non-Int symbols, pool overflow,
   Cartesian overflow, expired deadlines, unsupported universal shapes, and
   tampered returned models decline or fail replay.
5. The 256-case direct-Z3 differential has zero disagreements and every Axeyum
   SAT model replays against the exact source; the ordinary Z3-SAT Unknown
   bucket decreases from the accepted ADR-0359 baseline of 39.
6. Focused model/evidence tests, solver Clippy and rustdoc, workspace tests,
   foundational resources, parity, links, QF_BV profile, and SMT-COMP recovery
   are green.

## Alternatives

- **Trust the fixing or add it to evidence.** Rejected: it is not a source
  premise. Only the final original-query model is evidence.
- **Mutate scalar values in the existing model in place.** Rejected for this
  increment: rerunning the bounded ground candidate query lets explicit UF
  entries and other dependent ground values follow the scalar choice, while
  canonical replay still guards the result.
- **Use Z3 model values.** Rejected: the oracle measurement demonstrates the
  gap but cannot participate in the pure-Rust production solver.
- **Generalize immediately to `Real` or more symbols.** Deferred: the measured
  28-case gain is entirely one/two-symbol `Int`, and the bounded product is
  independently reviewable.

## Consequences

This should close most of the measured post-ADR-0359 SAT remainder without
widening the trusted checker or UNSAT surface. It does not repair the eleven
residual cases, synthesize arbitrary arithmetic defaults, complete free Reals,
search more than two scalars, or claim complete MBQI.

## Implementation evidence

Implemented in `5b4c5b40`. Focused tests cover one- and two-symbol completion,
explicit UF table preservation, exact source/evidence replay, non-Int and
three-symbol declines, complete-pool overflow, and shared-deadline expiry. The
normal 256-case differential reaches 225/225 agreement with 207/207 SAT replay;
the exact eleven-seed Z3-SAT residual matches the corrected preregistration.
The complete solver package gate is green. ADR status remains proposed until
the workspace/static/resource/parity/link/profile/recovery acceptance gate is
also complete.
