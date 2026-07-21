# ADR-0338: Preregister Tock proof v4 marker parser

Status: accepted
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

## Pre-invocation implementation state

The thin v4 wrapper validates exact v3 registration/preflight/negative lineage,
normalizes only one proof marker after the exact authenticated harness prefix,
and delegates to v3's unchanged dual-DRAT metadata/recheck, control replay, exact
count, and scoreboard parser. It rejects wrong prefixes, multiple markers on a
line, prefixed control/scoreboard markers, and absent prefixed proof markers.

Registration SHA-256 is `caa05643...7f1a`; wrapper and focused-test hashes are
`e5439f31...de5a` and `2ed1be93...73a2`. Six focused v4 tests plus v3's dual-
DRAT parser mutation test pass. The Rust runner is byte-identical to v3 and its
ordinary tests/Clippy remain the pushed v3 gate. `proof-v4` is absent. Commit and
push these bytes before archived non-authenticated compilation.

Pushed producer commit `635e7cbd` matches local HEAD, tracking, and remote
`main`. Its fresh archived source compiles locked/offline under the cap in 37.77
seconds and runs exactly the independent-spec test: one pass, zero failures, two
filtered tests, and no authenticated execution. `proof-v4` remains absent.
Exact preflight metadata is committed in
`bench-results/verify-tock-log2-20260721/proof-v4-preflight.json`. Commit/push
this zero-query gate before refs/output verification and one official run.

## Result

Accepted. Runner commit `5267d6a5` was pushed and matched local HEAD, tracking,
and remote `main` before the single official invocation. The exact authenticated
canonicals produce two functions, eight end-to-end certified proof rows, and six
replayed mutation controls with `UNKNOWN=0` and `DISAGREE=0`. Stable result
identity `c4acae04...a37c` independently recomputes.

Each positive row carries and rechecks the independent-reference faithfulness
miter DRAT plus final CNF DRAT/LRAT. The two substantive 64-bit rows are:

- floor-log equivalence: 545 terms, 4.887294 s, 44,705-byte DIMACS,
  13,286-byte DRAT, 69,284-byte LRAT;
- MSB characterization: 991 terms, 6.273062 s, 45,769-byte DIMACS,
  6,081-byte DRAT, 57,481-byte LRAT.

All three controls per width replay the correct reflection against the native
Rust oracle and discriminate at the sign-bit witness: `2^31` yields 31 and
`2^63` yields 63, while wrong-index, inverted-zero, and corrupted-high-partition
mutations differ. Total query time is 12.699759 s; full runner time is 12.713594
s; fresh Cargo wall time is 50.740 s; peak RSS is 1,256,496 KiB. All OOM deltas
are zero.

The ignored full local result SHA-256 is `80e89d0e...8d00`; exact committed
summary metadata and every per-row certificate hash/size are in
`bench-results/verify-tock-log2-20260721/proof-v4-result.json`. The summary was
independently compared field-by-field with the local result. Generated build and
full result bytes remain ignored.

This closes T5.5.3 and supplies the reviewer track's concrete checked-DRAT use
case. It does not establish performance leadership or general whole-kernel
verification. Next is T5.5.4's honest comparison/write-up; no proof rerun or
post-observation policy change is authorized.

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
