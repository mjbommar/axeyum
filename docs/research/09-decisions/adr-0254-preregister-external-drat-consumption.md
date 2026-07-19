# ADR-0254: Preregister external DRAT consumption on one real query

Status: accepted
Date: 2026-07-19

Result state: exporter implemented; real external-check cell preregistered

## Context

ADR-0253 establishes complete in-tree CNF DRAT rechecking on 509 holdout UNSAT
rows. That supports the clausal-proof claim, but an artifact reviewer should
not have to accept Axeyum's checker and producer as the only executable proof
consumer. `UnsatProof` already stores standard DIMACS and textual DRAT, yet the
repository lacked a file-oriented command that emitted those artifacts from an
SMT-LIB query.

The neutral check must select its real row before proof size, LRAT availability,
external acceptance, or checker timing is observed. The source query is
access-controlled, so preservation must prove identity and outcome without
committing query-derived CNF/proof bytes.

## Decision

Add `qfbv-proof-export`, a standalone `axeyum-bench` binary that accepts one
flat, single-check `QF_BV` script and a new output directory. It emits standard
`problem.cnf`, `proof.drat`, optional `proof.lrat`, and a SHA-256-bound
`manifest.json` only after `UnsatProof::recheck()` accepts. It refuses existing
output, satisfiable/inconclusive queries, non-QF_BV logic, multiple checks, and
scoped/reset/assumption command streams.

For the first external real-query cell, select the lexicographically lowest
content hash among ADR-0251's exact 509 expected-UNSAT rows:

`0015f5bd8a50e7d1859888c308e0621fede3e8fb322ffaf1222c4e6aad28000e`
(`register-slice`). This selection uses no proof or checker observation.

Pin upstream `drat-trim` revision
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985` and source SHA-256
`d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee`.
The pinned Makefile's strict C99 command fails on GCC 15.2.0 because it does not
declare `getc_unlocked`; compile the unchanged source with the preregistered
`-D_GNU_SOURCE` command. The resulting checker binary SHA-256 is
`c0b9bd6a2369918f171a42d024aa2993d5eff4f597e019850c073d0aa08bd9db`.

Acceptance requires:

1. a clean detached exporter build from the commit containing this decision;
2. exact source hash agreement with the preregistered row;
3. exporter exit zero and `self_rechecked: true`;
4. `drat-trim problem.cnf proof.drat` exit zero with `s VERIFIED`; and
5. a teeth control made only by deleting the final textual DRAT line, for which
   the same checker must not print `s VERIFIED`.

Record byte counts, hashes, commands, exit codes, and exact checker streams.
Do not commit the access-controlled source, CNF, DRAT, or LRAT bytes.

## Evidence before the real cell

Two process tests cover standard export plus independent in-tree parsing/check,
manifest construction, overwrite refusal, satisfiable no-output behavior, and
scoped-query rejection. They pass under clippy `-D warnings`; documentation
links pass. The exporter source SHA-256 is
`8736e8f2a46185aee002b5578ba4a38e54b6a3711d1dc7aaa77234b37942cc87`.

The external checker was fetched and built before row execution, but it has not
seen this row's proof. No real query has been passed to the new exporter before
this selection and protocol are committed.

## Consequences

Consumers gain a concrete standard proof-bundle workflow without adding a C
dependency to Axeyum's default or runtime graph. A successful cell establishes
format interoperability with a neutral checker on one preregistered real
proof; it does not estimate proof coverage or certify SMT-LIB lowering. The
stronger end-to-end route remains separately reported.
