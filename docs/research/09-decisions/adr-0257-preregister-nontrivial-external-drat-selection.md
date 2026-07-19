# ADR-0257: Preregister bounded nontrivial external DRAT selection

Status: accepted
Date: 2026-07-19

Result state: protocol implemented and preregistered; real candidate scan not run

## Context

ADR-0256 accepts one real standard DIMACS/DRAT export consumed by pinned
upstream `drat-trim`, with a separate satisfiable-CNF checker sanity control.
The real CNF is already UNSAT by input unit propagation, however, and the proof
is only `0\n`. That cell demonstrates format interoperability but does not
exercise a nontrivial proof trace.

Selecting a larger proof after inspecting all 508 remaining holdout proofs
would be post hoc. The repository therefore needs a deterministic bounded scan
whose proof-shape-conditioned selection is disclosed and whose rejected rows
remain visible.

## Decision

Add `scripts/select-nontrivial-external-drat.py` and commit it before observing
another real proof. Bind the exact ADR-0251 holdout manifest at SHA-256
`67c7f14f...`, retain only expected-UNSAT rows, exclude ADR-0254's already
observed `0015f5bd...` row, and order the remainder by ascending content hash.
The script SHA-256 at preregistration is `472b96ff...`.

Attempt at most the first 32 rows in that order. Use a clean detached exporter
built from the commit containing this ADR, the unchanged 30-second per-process
diagnostic wall, and pinned checker binary SHA-256 `c0b9bd6a...`. For each row:

1. verify the source bytes against the manifest content hash;
2. export only through the self-rechecked standard proof command;
3. require the real proof to contain more than two bytes and more than one
   textual line;
4. require `drat-trim problem.cnf proof.drat` to exit zero and print
   `s VERIFIED`; and
5. require the same checker on the same CNF with a zero-byte proof not to meet
   that verification condition.

Stop at the first row meeting every gate. Preserve the complete ordered
candidate list and every attempted export/checker result, including failures,
timeouts, trivial proofs, and input-alone verifications. If none of the first
32 rows qualifies, record `no-selection` and do not widen the cap without a new
decision. Keep source, CNF, and proof bytes outside Git; commit hashes, sizes,
exit codes, and normalized checker evidence.

## Evidence before execution

Three focused tests pass. They cover exact hash order after excluding the known
row and SAT rows, fixed-cap enforcement, duplicate rejection, and strict
positive verification classification. Python compilation and diff checks pass.

No remaining holdout proof has been exported through this selector before the
protocol is committed. The prior holdout run established internal proof
rechecking status for every row, not their textual sizes or behavior under an
empty external proof.

## Consequences

A successful scan supports the bounded claim that an independent checker
consumed a nontrivial multi-line Axeyum DRAT whose input did not verify without
the proof. It is still clausal interoperability, not source-to-CNF
certification, proof-population prevalence, or performance evidence.

The deterministic retained-attempt protocol makes the selection bias explicit
and reproducible. Failure to find a qualifying row within the fixed cap is also
a valid result and must remain visible.
