# QF linear A5 cross-division census v1 preregistration — 2026-08-07

## Decision boundary

This note preregisters a **measurement-only** census across the complete frozen
QF_LRA, QF_RDL, and QF_IDL parity populations. It authorizes capture tooling,
typed route-provenance validation, immutable retention of the already-published
historical sidecars, and fresh current-Axeyum traces. It does **not** authorize a
solver, timeout, resource-ceiling, route-order, or difference-logic budget
change.

A production change may be proposed only after this census identifies a
lossless repeated mechanism cluster and its controls. A generic `unknown`, a
timing-only difference, or a syntactic family resemblance is not mechanism
evidence.

## Frozen inputs

All three lists contain 200 exact absolute paths. Before any capture, the tool
must reject a missing path, duplicate path, row-count change, ordering change,
or digest change.

| Division | Frozen list SHA-256 | Historical sidecar SHA-256 | Published Axeyum/reference/both/Axeyum-only/reference-only/wrong | Solver commit | UTC timestamp |
|---|---|---|---|---|---|---|
| QF_LRA | `b636239947db1e65f2665a62fca8f852acdcd459c799a9bb326c718a1d1d8da5` | `106913be84886cdb2e83894cdde8d327ea7c3cad75504e397d8a6876a88e9add` | 86/146/86/0/60/0 | `8ea6a7cad` | `2026-08-06T12:44:30Z` |
| QF_RDL | `9dc32e2c5dfbd2d05f79d67ee80683d6941a6dab5e0bc0cc9936dc3ba8e4f149` | `be59cfacc18eab60225d5f0990e6614d1b55299a60f809c77992ca56d034aab1` | 105/155/105/0/50/0 | `b353419e7` | `2026-08-06T13:54:23Z` |
| QF_IDL | `d7c9713a0280a9ec0cb03e7072acd2cc01a089613c05349984cc1a4f4c6a431d` | `2debb3525937eefd6a1b0a62c4aedb406766f80f0a558393ade9df7594a0d862` | 68/124/68/0/56/0 | `198f2dc1b` | `2026-08-06T20:47:11Z` |

The three historical TSVs are initially untrusted inputs. The validator must
require the exact header `file axeyum reference declared`, exactly 200 data
rows, exact list-path order, only `sat`, `unsat`, or `unsolved` outcome cells,
consistency with authoritative declared `sat`/`unsat` statuses, the table above,
and the frozen physical digest. Declared `unknown` is retained but does not
contradict a solver decision.
Only after those checks may their bytes be copied into the tracked A5 evidence
directory. The current census never invokes cvc5: the accepted historical
reference observations are replayed as immutable comparison inputs.

## Fresh Axeyum capture contract

Each division is captured from row 1 with the release `explain_corpus` binary
from one exact clean and pushed topic commit.

- shipped default solver configuration;
- 24,000 ms query timeout and 8 GiB process memory limit;
- 24-core host and one-minute start load no greater than 12;
- one division and one capture process at a time, protected by a nonblocking
  host lock;
- GNU `timeout` outside the complete stream, with enough margin for 200 rows;
- exact executable SHA-256, byte size, Git commit/upstream equality, list
  identity, load, elapsed time, stdout/stderr digests, and exit code retained;
- output and success metadata published atomically only after validation;
- any nonzero exit, stderr, partial stream, malformed JSON, or validation error
  writes non-credited failure metadata and stops the sequence.

Every one of the 200 rows must be a `status=decided` record with a verdict in
`sat`, `unsat`, or `unknown` and a nonempty schema-1 route trace. Linear
arithmetic has no preregistered ingest exception. Generic parse/read/error
records, missing typed decline reasons, empty traces, and row reordering fail
closed.

## Monotonicity and correctness gates

For each division:

1. every historically solved Axeyum row must still be solved with the identical
   verdict; this makes all 259 historical decisions the permanent control for
   the rejected global 12/12 DL split;
2. any newly solved row must agree with the retained reference verdict when it
   is available, and with a declared `sat`/`unsat` status when present;
3. every historically or newly solved row must have a terminal decided trace
   consistent with the top-level verdict;
4. zero Axeyum/reference, Axeyum/declared, and reference/declared disagreements
   are permitted;
5. the repaired LRA high-memory control
   `QF_LRA/sc/sc-39.base.cvc.smt2` must return a typed bounded decline rather
   than crash, OOM, malformed output, or process failure; and
6. `QF_IDL/sal/lpsat/lpsat-goal-18.smt2` must retain UNSAT. The full historical
   solved set, including the compact gate-free and large-equality cases behind
   ADR-0375's adaptive policy, is the stronger budget-allocation control.

A timing-sensitive loss stops the census. It may be investigated in isolation,
but it is not silently waived and no breadth experiment proceeds from a
non-monotone baseline.

## Lossless residual classification

The current reference-only population is derived by joining fresh Axeyum
verdicts with the validated historical reference column. Each residual retains:

- division, exact file, source-family path, declared status, current Axeyum and
  historical reference verdicts;
- the complete route trace;
- first and terminal substantive decline, each preserving route, reason, kind,
  and original detail;
- a separately normalized detail family used only for grouping; and
- one coarse bucket from this closed vocabulary:
  `normalization-resource`, `unsupported-dl-shape`,
  `disequality-boolean-structure`, `explanation-core`, `search-budget`,
  `model-replay`, or `other-unsupported`.

Unsupported/not-applicable attempts are retained in the trace but are not
substantive unless no stronger typed boundary exists. Classification priority
is replay/verifier rejection, deterministic normalization/resource limits,
explicit unsupported difference shape, disequality/Boolean skeleton limits,
explanation/core limits, search budget, then other unsupported. A row that
cannot be placed from typed trace evidence fails the complete-record gate; it
does not receive a guessed bucket.

Groups use the full tuple `(division, source family, bucket, terminal route,
reason, kind, normalized detail, reference verdict)`. A candidate needs at
least three rows with the identical tuple. Smaller clusters remain documented
but selection-ineligible.

## Outputs

The tracked result increment must contain:

- the three exact validated historical TSVs;
- fresh raw Axeyum JSONL and capture metadata, or immutable external-artifact
  pointers if raw size makes direct retention unreasonable;
- a machine-readable joined census and manifest binding every input/output
  digest;
- exact current reference-only lists by division;
- bucket and lossless-group counts, explicit gains/losses/wrongs, and permanent
  control outcomes; and
- a dated result note plus synchronized `PLAN.md` guidance.

The derivation must be reproducible from the retained files without corpus
re-solving.

## Authorization after the census

The first implementation slice, if any, must address one deterministic repeated
mechanism rather than a benchmark name. It must preregister targets, satisfiable
and unsatisfiable controls, original-term replay, exact Farkas/DL evidence
checks, the deep-input non-recursion regression, and nonzero arithmetic fuzz
execution. A/B acceptance is monotone across all three divisions.

Stop without a solver change if no cluster of at least three rows survives the
complete-record and mechanism gates. Do not raise normalization ceilings, the
1,024-atom online-LRA cap, the overall 24-second timeout, or a global DL
fallback reserve; do not retry the rejected global 12/12 split.
