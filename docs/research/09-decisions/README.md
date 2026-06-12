# Decision Records

Status: draft
Last updated: 2026-06-11

## Purpose

The research-questions register says every open question should resolve into
"an ADR, benchmark, implementation result, or explicit deferral" — this
directory is where those resolutions live. Research notes describe the option
space; decision records close questions.

## Process

- One file per decision: `adr-NNNN-short-slug.md`, numbered sequentially.
- Status is one of: `proposed`, `accepted`, `superseded by adr-NNNN`,
  `deferred`.
- Each ADR links the research-questions entries it closes; the closed
  question in `08-planning/research-questions.md` gets a link back.
- ADRs are immutable once accepted; reversals get a new ADR that supersedes
  the old one.

## Template

```markdown
# ADR-NNNN: Title

Status: proposed | accepted | superseded by adr-NNNN | deferred
Date: YYYY-MM-DD

## Context

What question this closes and why it must be decided now.
Link the research notes and register entries involved.

## Decision

The decision, stated as a single committed sentence, then detail.

## Evidence

Benchmarks, prototypes, references, or reasoning that justified it.

## Alternatives

What was rejected and why.

## Consequences

What becomes easier, what becomes harder, what gets revisited and when.
```

## Index

| ADR | Title | Status |
|---|---|---|
| [0001](adr-0001-vertical-slice-first.md) | Vertical slice before horizontal layers | accepted |
| [0002](adr-0002-ground-up-identity-oracle-bootstrap.md) | Ground-up identity, oracle as bootstrap scaffolding | accepted |
| [0003](adr-0003-m0-ir-representation.md) | M0 IR representation choices | accepted |
| [0004](adr-0004-defer-second-native-backend.md) | Defer the second native backend | accepted |
| [0005](adr-0005-phase3-query-evidence-rewrite-contracts.md) | Phase 3 query, evidence, and rewrite contracts | accepted |
| [0006](adr-0006-phase4-bit-order-and-lowering-entry-contract.md) | Phase 4 bit order and lowering entry contract | accepted |
| [0007](adr-0007-first-pure-rust-sat-adapter.md) | First pure Rust SAT adapter | accepted |
