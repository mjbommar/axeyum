# ADR-0275: Preregister joint triplet reproduction and bounded census

Status: accepted
Date: 2026-07-19

Result state: preregistered; zero ADR-0275 processes

## Context

ADR-0273 rejected an independently tiered calibration and prohibited combining
limits observed on changing authority streams. ADR-0274 corrected that design,
proved one invariant 4,846-check stream, and selected Z3 rlimit 100,000, Axeyum
progress checks 32,768, and Bitwuzla termination polls 512. Those shadow values
qualified on different ADR-0274 tiers, although shadow limits cannot affect the
fixed Z3 authority stream. Before a 338-function row, the exact combined triplet
must nevertheless reproduce jointly under one committed protocol.

No ADR-0275 process was executed while defining this decision.

## Decision

Use the unchanged ADR-0273/0274 Glaurung source, Axeyum measured trees, release
binary and 12 library hashes, `tcpip.sys`, CPU 2, `AnyModel` authority, fixed
environment, memory guard, 60-second per-check wall safety cap, 2,700-second
outer cap, and v4 validation. Freeze the triplet exactly as:

- `GLAURUNG_Z3_RLIMIT=100000`;
- `GLAURUNG_AXEYUM_PROGRESS_CHECK_LIMIT=32768`; and
- `GLAURUNG_BITWUZLA_TERMINATION_POLL_LIMIT=512`.

### Phase A: joint first-20 reproduction

Run N=3 fresh sequential processes with
`IOCTLANCE_MAX_ANALYZED_FUNCTIONS=20`. Require 4,846 checks, authority identity
hash `89d28a2978e4d9fc1bbba78bb1413a80fffc408c0bbc4dcef51b1eb6b5e1e928`,
authority outcome hash
`f0b5580fcc6bba0accd6a91fc76a1373a60835af84c5982394ca9d6b3312fafa`,
byte-identical findings/outer work, all six cells decided and agreeing, direct
warm execution, and zero resource/wall/other/operational/fallback/deadline
rows. A failure rejects ADR-0275 and Phase B must not start.

### Phase B: full bounded census

Only after Phase A passes, run N=3 fresh sequential processes with
`IOCTLANCE_MAX_ANALYZED_FUNCTIONS=338`; keep solve budget 400,000, solve seconds
900, analysis deadline 2,400 seconds, and every other environment value
unchanged. Require all repetitions to analyze exactly 338/338 functions with
identical ordered check identities, outcomes, stop reasons, findings, and outer
work. Every cell must decide at least 95% of occurrences, every nondecision must
be typed resource-limit, all jointly decided verdicts must agree, warm execution
must remain direct, and wall/other/operational/fallback/deadline failures must be
zero. Retain raw/high-confidence/diagnostic findings under cold-Z3 authority.

Any failed process is retained and never rerun. Do not increase limits,
deadlines, budgets, or drop a repetition after observing Phase A or B without a
new ADR. Timing is descriptive only and does not support equal-work or speed
claims.

## Interpretation

Acceptance would establish a deterministic, bounded, cold-Z3-authoritative
six-cell census with shadow verdict agreement. It is not labeled recall,
precision, cross-authority finding parity, exhaustive exploration, or a solver
performance result. High-confidence findings may be reported only as census
output; tcpip remains unlabeled.

## Consequences

ADR-0275 is the only path from the accepted calibration to a census row. A1
remains configuration and measurement; A0 remains reproducibility
infrastructure; symbolic memory stays closed. Failure closes this harder-driver
attempt unless another explicit zero-row decision is justified.
