# ADR-0183: Defer detected-reuse warm default

Status: accepted
Date: 2026-07-16

## Context

ADR-0182 accepts a second-check detected-reuse candidate pending the exact
repeated gate. The candidate deliberately trades eager-lineage speed for lower
retained memory. The existing ADR-0180 time alarm is 3%; a default cannot hide
a larger regression behind a favorable RSS result.

## Decision

Keep detected-reuse `auto` as an explicit memory-optimized option and defer it
as the production default. Fixed lineage remains the faster opt-in policy; the
ordinary default remains off.

## Evidence

The clean Glaurung `5c4ec0f` / Axeyum `0b77ccff` artifact repeats three
processes per family under 4 GiB. All 92,721 checks agree, unknown splits are
zero, and every probe/warm/lifecycle counter is identical.

- SurfacePen: auto 1.141 seconds / 65,404 KiB, +7.37% Axeyum time and -20.66%
  median RSS versus lineage.
- NETwtw10: auto 19.554 seconds / 216,580 KiB, +4.28% time and -15.93% RSS.

Both time regressions exceed 3%. Cross-run Z3 drift is -2.21%/+2.63%, outside
the 2% environment guard, so normalized-ratio deltas are not used causally.
Glaurung `ab3b27b` commits the exact 8,396-byte artifact with SHA-256
`bcc6b5cfce173af23b6ad81b9b412cd96dedc002af94b03a4500f53379c04fdf`.

## Alternatives

Making auto default on memory alone was rejected by the non-regression policy.
Discarding it was rejected because the stable 16--21% RSS reduction is useful
under memory pressure. Relaxing the 3% alarm after observing the result was
rejected as benchmark overfitting.

## Consequences

GQ9 has a measured low-memory option but no default selector yet. The next
admissible selector must preserve eager lineage's speed on these repeat-heavy
streams while avoiding retained state only where topology predicts no future
checks before paying a cold rebuild. GQ4 stays off and GQ8 remains separate.
