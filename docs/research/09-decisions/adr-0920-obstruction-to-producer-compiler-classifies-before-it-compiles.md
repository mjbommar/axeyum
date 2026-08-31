# ADR-0920: The obstruction-to-producer compiler classifies before it compiles, and only the removable class gets a contract

Status: accepted
Date: 2026-08-30
Index-summary: L3 D4's obstruction-to-producer compiler (`scripts/gen-obstruction-producers.py`) sorts every open dispatchable-frontier obstruction into producer / new-construction / not-removable before compiling anything, and only the first class may carry a falsifiable producer contract with a plural, re-verified applicability set — a structural answer to ADR-0602's dispatch-table failure mode.
Index-status: accepted

## Context

ADR-0602 decided that dispatch needs a prospective producer contract
carrying no `proved` field, separate from the retrospective operation
registry, and measured the failure mode a producer layer must not repeat:
an operation registry where every entry named exactly one target (24
operations, 23 facts covered, zero naming more than one, zero of 144
dependency-ready facts covered) — a dispatch table wearing a producer's
name, unable to fail because it only ever describes what already happened.

L3 D4 ("Obstruction-to-producer compiler",
`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`) asks for
exactly the machinery ADR-0602 anticipated needing: normalize a typed
decline into the smallest missing capability, cluster demand across facts,
and compile a producer contract with a shape, budget, candidate inputs,
negative controls, and target population. Its exit criterion restates
ADR-0602's constraint mechanically: "a single-target producer is labeled a
capsule and cannot justify generality."

`scripts/check-dispatchable-frontier.py` already names four registry-backed
construction divergences blocking open `ml430` mirrors (`Nat.testBit`
codomain, `Nat.multichoose` definitional, `Nat.minFac` algorithmic,
`Nat.fastFib` recursion-principle) plus a fifth shape (a genuine proof gap,
`and_or_distrib_left/right`) that sits outside the registry's scope
entirely — the registry only tracks construction-level divergence, not
"no machinery exists for this argument."

## Decision

1. **Classify before compiling.** Every obstruction this compiler finds
   evidence for is sorted into exactly one of three buckets, each with a
   distinct consequence:
   - `producer` — a reusable strategy exists NOW, evaluable against real
     kernel/ledger state, applicable to more than one target. Only this
     class may carry a compiled contract.
   - `new-construction` — removable in principle (the kernel's type system
     already has what is needed) but the construction has not been built,
     so nothing is evaluable today. Compiling a producer here would assert
     a strategy that cannot run — the exact defect being scored against.
   - `not-removable` — the mirror is a different proposition (a
     construction-level divergence the project has already decided must
     stay open) or the statement needs a type this kernel structurally
     lacks.
2. **A producer contract carries no `proved` field, structurally.** The
   checker scans every contract recursively for the key and fails if
   present, so the false-assertion failure mode is unrepresentable, not
   merely avoided by convention (ADR-0602 §2's exact requirement).
3. **Plurality is mechanical.** A contract with `kind: producer` must name
   at least two applicability targets, verified live against the fact
   ledger (existing, `epistemic_status: open`) on every gate run. A
   single-target contract must be labeled `kind: capsule`; the gate fails
   otherwise.
4. **Applicability may not exceed its own obstruction's population.** Each
   contract links to the obstruction record(s) it addresses; the checker
   verifies its applicability set is a subset of that obstruction's
   `blocked_fact_ids`, so a contract cannot claim coverage its own
   classification never established.
5. **Every claim is re-verified on every run, not cached.** The generator's
   `--check` mode recomputes both the classification and every contract
   from primary sources (the fact ledger, the divergence registry,
   `nat_prelude/` source) and fails on drift; the checker's G1 invokes it
   as its own first guard.

## What this run produced

Two producer contracts, both with applicability > 1:

- `extensional-duplicate-close` (3 targets: `and_comm`, `and_assoc`,
  `and_le_left`) — an open `ml430` `Nat.land` mirror is dischargeable by
  evidence pointer alone when an already-proved twin mirror or bare kernel
  declaration under a different name already establishes its content.
  `Nat.minFac`'s coprime mirror initially looked like a fourth candidate
  (same predicate symbols, an already-proved native analogue) and was
  excluded after reading `nat_prelude/min_fac.rs`'s own module doc and the
  native fact's own `notes` field, both of which say explicitly this is
  not a flip — kept as a denylist entry and a negative control.
- `pointwise-bit-extensionality` (2 targets: `and_or_distrib_left/right`)
  — a pure bitwise Nat equality is dischargeable via
  `Nat.eq_of_testbit_eq` plus a finite `{0,1}` case split, composing only
  already-proved lemmas; re-verifies on every run that no cross-operator
  joint-induction machinery exists in the tree.

Mean applicability across the two contracts is 2.5. `Nat.testBit`'s
5-of-6 open mirrors and `Nat.fastFib` are classified `new-construction`
(need, respectively, a Bool-valued `testBitBool` and a well-founded-fix
`binaryRec` reconciled with `Nat.fib`'s own divergence per ADR-0840); one
`Nat.testBit` mirror and all three `Nat.multichoose` mirrors are classified
`not-removable`. No contract was compiled for any of these five, on rule 1.

## Consequences

- A future lane adding an obstruction class must classify it before
  reaching for a contract template; the gate refuses an empty
  classification, an unlinked contract, or a contract whose applicability
  exceeds its own obstruction's stated population.
- The `new-construction` bucket is a to-do list, not a dead end: once
  `Nat.testBitBool` or a reconciled `fastFib`/`fib` pair lands, the same
  compiler should be re-run to check whether a producer becomes evaluable.
- `not-removable` classifications are not appealable by this compiler —
  they cite the project's own mirror-flip criterion and, where available,
  a specific ADR (0840) or module doc; overturning one requires new
  evidence in the tree, not a re-run of this script.
