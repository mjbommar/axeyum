# ADR-0338: Preregister Tock proof v4 marker parser

Status: proposed
Date: 2026-07-21

## Context

ADR-0337 v3 completes its authenticated Rust test successfully: eight dual-DRAT
certificate/recheck calls, six replayed controls, and the scoreboard assertions
all pass. Its outer producer nevertheless rejects the result because Rust's
`--nocapture` harness writes the first test output after the status prefix
`test authenticated_tock_log2_scoreboard ... ` on the same line. The frozen
parser recognizes only markers at column zero and therefore counts seven proof
rows. Atomic cleanup grants no result credit.

This is a deterministic transport/parser defect after the measured work, not a
proof, target, policy, performance, or acceptance-gate result.

## Decision

Create proof v4 by changing only row-marker extraction. Recognize the first
`TOCK_PROOF|` marker when and only when it follows the exact authenticated test
harness prefix; preserve all column-zero proof/control/scoreboard markers. Pass
the normalized rows through v3's unchanged exact-count, certificate metadata,
trust, replay, and scoreboard validators.

## Frozen v4 gates

1. Commit and push this zero-result ADR before adding v4 producer bytes. V1--v3
   remain closed and are never rerun.
2. Pin and validate v3 registration SHA-256 `a458ce33...7960`, preflight SHA-256
   `1d7505f8...5286`, and negative SHA-256 `31cfa009...e075`. Require v3's
   successful Cargo test, eight completed proof queries, six completed controls,
   parser count 7/8, zero accepted output, and no reported OOM-delta failure.
3. Permit exactly one non-column-zero marker: `TOCK_PROOF|` following exact
   prefix `test authenticated_tock_log2_scoreboard ... `. Reject a missing
   marker, wrong prefix, multiple markers on one line, prefixed control/
   scoreboard markers, or any duplicate/malformed row through existing gates.
4. Preserve byte-for-byte v3 Rust runner, authenticated inputs, goals, dual-DRAT
   API/deadlines/rechecks/hash fields, control `SolverConfig`, native replay,
   expected 8+6 rows, tool/source/archive/cgroup policy, total timeout,
   identity projection, and atomic output.
5. Version registration/result schemas and write only ignored
   `target/tock-log2-20260721/proof-v4`. Commit/push the thin parser wrapper,
   focused mutations, and registration before the same fresh archived-HEAD
   non-authenticated compilation preflight. No target query may run there.
6. After preflight metadata is pushed, require local HEAD/tracking/remote
   equality and absent v4 output, then invoke once. Success still requires two
   functions, eight end-to-end certified proofs, six replayed controls, zero
   `UNKNOWN`, and zero `DISAGREE`.
7. Any official v4 failure closes v4. Never tune a proof/control limit, weaken a
   certificate/recheck condition, or rerun after observation.

## Rejected alternatives

- **Credit v3 from the Rust exit code.** Rejected: the committed artifact gate
  requires the outer parser and stable result to accept all exact rows.
- **Strip arbitrary text before markers.** Rejected: that could admit corrupted
  or injected output. Only the exact known harness prefix is accepted.
- **Change Rust output timing or add a leading newline.** Rejected: the defect is
  in an outer parser that incorrectly assumes test-harness framing.

## Consequences

- V4 isolates one observed orchestration byte-shape without changing science.
- A successful result remains independently auditable through the same dual-
  DRAT hashes, rechecks, controls, and atomic scoreboard.

## References

- [ADR-0337](adr-0337-preregister-tock-end-to-end-proof-v3.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
