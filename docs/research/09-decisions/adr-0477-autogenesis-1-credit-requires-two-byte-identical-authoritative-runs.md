# ADR-0477: Autogenesis-1 credit requires two byte-identical authoritative runs

Status: accepted
Date: 2026-08-18
Index-summary: Credit Autogenesis-1 only after two clean B-then-A runs match fixed budgets, semantic identities, and every retained artifact byte

## Context

ADR-0476 supplied the missing event-bound A operation, but implementation and
one successful manual sequence were insufficient for programme credit. The
definition also requires the same A target under the same pre-B and post-B
budget, no proof-affecting intervention, no trusted-base growth, and clean-room
reproduction. Large full-history Git bundles additionally made repeated
retention unnecessarily expensive.

The first automated completion attempt exposed two stale negative controls, an
unreviewed new caller, a Git porcelain parsing bug, and—most importantly—a
pre-B A budget of 20 against an authoritative A budget of 1. Each issue had to
fail before any result could be credited.

## Decision

Autogenesis-1 receives credit only when one exact clean source produces two
separately retained authoritative runs for the preregistered
`F:nat-zero-add -> F:nat-mul-one` chain and a fail-closed comparer establishes:

- the same target and budget fail before B;
- B and A each perform one authoritative write and zero fixture writes;
- B's durable event makes exactly A newly ready;
- A uses the episode-local B and neither result uses a retained answer;
- both axiom footprints and the trusted-base delta are empty;
- no human writes, repairs, selects, or overrides the proof after launch;
- deterministic commits and semantic fields match; and
- every retained artifact byte matches.

The otherwise unreferenced pre-A state is retained in a thin Git bundle whose
prerequisite is the exact source commit. Git stores only a small digested result
index; full receipts remain external and are rehashed when available.

## Evidence

At exact source `cf998788b`, both runs produced run digest
`d6e7b20dfeadd6750cd6080d36425db58565749f2f381b741f17b0534b536102`.
The comparer matched 56 artifact files and produced reproduction digest
`60c6dec66eff79f5dc4192c18f038ed06356a64435129ba0a01b179f612342aa`.
The committed result checker rehashed the external receipts and reported
`external=verified` on the measured host.

## Consequences

- Autogenesis-1 is passed for the exact bootstrap chain, not for a generic
  autonomous proving surface.
- The programme now has a one-command runner, a separate comparer, and a small
  versioned result index instead of vendored receipt trees.
- Same-target evidence without same-budget evidence cannot receive causal
  credit.
- Future changes must preserve this longitudinal result or explain a versioned
  migration; Phase 3 credit requires new held-out composition evidence.
