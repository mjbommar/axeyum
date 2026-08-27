# ADR-0599: Palette-orbit refutations may compose complete labelled proof sets

Status: accepted
Date: 2026-08-27

## Context

ADR-0597 encodes palette-orbit Hamming distance with one existential bijection. On the live
five-colour Rado radius-22 instance, its no-cutoff CaDiCaL producer exceeded two hours and 20 GB
of incomplete DRAT. The previously checked labelled ball cannot simply be promoted: the canonical
colouring CNF contains least-first-occurrence symmetry clauses, so arbitrary relabelling does not
preserve the encoded formula.

The orbit is nevertheless finite. For five colours it is exactly the union of 120 ordinary
labelled Hamming balls, one for each complete palette permutation. A swap-of-colours diagnostic
closed UNSAT in 6.07 seconds; its 38,821,222-byte DRAT independently checked in 1.763 seconds.

## Decision

Axeyum adds a bounded lexicographic palette-permutation enumerator, an explicit fail-closed witness
permutation, and a proof-set checker that regenerates and checks one labelled Hamming formula for
every permutation. The checker derives completeness from its own enumerator rather than trusting a
producer manifest. A missing, oversized, malformed, incomplete, or invalid proof fails the command.
The limits are 8! permutations, 64 GiB per proof, and 1 TiB total proof bytes.

The single existential encoding remains available. The proof-set route is an alternative
certificate decomposition, not a claim that all palette-orbit formulas should be factorially
expanded.

## Evidence

Focused controls enumerate all six three-colour permutations in lexicographic order, reject a
five-row ceiling without returning a prefix, and reject malformed witness permutations. The first
real nonidentity five-colour proof checked with Axeyum's file-backed backward DRAT route. All-target/
all-feature Clippy for `axeyum-search` passes. The complete 120-proof production remains live and
earns no orbit result until the new checker accepts every member.

## Consequences

Small palette orbits can trade one symmetry-entangled SAT instance for independent, resumable proof
obligations with an exact completeness boundary. Partial proof sets remain valueless. Factorial
growth is explicit and bounded; larger palettes should retain the existential encoding or use a
different checked symmetry argument.
