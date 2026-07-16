# ADR-0206: Glaurung shadow unknown-split corpus

Status: accepted
Date: 2026-07-16

## Context

ADR-0205 selects `tcpip` and `dxgkrnl` for GQ10 widening from a 60-second
per-function diagnostic sweep. Running `tcpip` at the established lineage gate's
600-second ceiling changes the distribution materially: the stream grows from
33,501 to 70,639 queries and exposes backend non-decisions that a SAT/UNSAT
disagreement count alone hides.

Axeyum needs the exact formulas where only one backend decides before this can
be classified as solver timeout, translation/error, warm lifecycle reset, or
client resource fallback.

## Decision

Accept Glaurung ADR-015/`a6a5cc0` as the opt-in split-capture boundary.
`GLAURUNG_DUMP_SHADOW_SPLITS` acts only in combined Z3+Axeyum shadow mode and
serializes exactly those queries where one backend returns SAT/UNSAT and the
other returns `Unknown`/`Error`.

Publish exact SMT-LIB bytes atomically as `<sha256>.smt2`. Record only content
hash plus stable Z3/Axeyum result classes in `shadow-splits.tsv`; error text does
not enter identity. Suppress same-process duplicate outcome tuples and fail
closed on byte collisions. Both-nondecided rows are not split rows.

## Evidence

The full-budget source-prefix `tcpip` run records 70,639 same-stream queries,
zero SAT/UNSAT disagreements, 43 Z3 non-decisions, 936 Axeyum non-decisions,
973 unknown splits, 925 warm resets, and 480 assertion-cap fallbacks. Axeyum is
still 1.7x faster (141.388 versus 240.161 seconds) at 440,384 KiB RSS, but this
row fails the correctness gate.

Four combined-feature capture tests pass, including exact split predicates,
stable class labels, atomic byte publication, collision handling inherited from
the query publisher, and the TSV contract. Ordinary solving and ordinary GQ1
capture remain unchanged when the new environment variable is absent.

## Alternatives

- Count unknowns as agreement: rejected because a decided/unknown split is a
  real functionality and exploration divergence.
- Capture every query: rejected because the existing GQ1 route already does so
  and the new artifact should stay focused.
- Store only hashes: rejected because the formulas would not be reproducible.
- Store full error strings: rejected because incidental details make identity
  unstable and can expose local paths.

## Consequences

`tcpip` is not a green GQ10 DriverSpec yet, and the 33,501-query result must be
described as time-truncated. Rebuild the combined release binary, capture the
60-second `tcpip`/`dxgkrnl` split corpora, then use the exact formulas to rank
timeout/lowering/lifecycle/resource work. A 600-second corpus follows only if
the smaller artifact does not explain the dominant failure classes.
