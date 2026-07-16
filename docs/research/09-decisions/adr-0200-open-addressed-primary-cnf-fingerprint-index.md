# ADR-0200: Open-addressed primary CNF fingerprint index

Status: deferred
Date: 2026-07-16

## Context

The latest Glaurung feedback keeps cold one-shot lowering as the remaining
pure-solver gap: bit blast plus CNF consume about 84% and SAT about 15%.
ADR-0175's deterministic open-addressed AIG table materially reduced bit-blast
cost. CNF is now the leading cold stage at about 46%.

ADR-0144/0150 made clause dedup collision-safe and removed a heap vector from
the common one-clause fingerprint bucket. The accepted full corpus still makes
53,748,044 clause attempts. Its primary `fingerprint -> clause index` owner is
a `std::HashMap` with a pass-through deterministic hasher, even though keys are
already mixed 64-bit fingerprints, entries are never deleted, and table
iteration never affects output. Genuine equal-fingerprint/distinct-clause
collisions remain in a separate exact side bucket.

## Proposed decision

Replace only the primary fingerprint map with an in-tree deterministic
open-addressed table.

- Store `(fingerprint, primary formula index)` inline in power-of-two slots.
- Use the already mixed complete fingerprint directly for initial placement;
  fold high/low halves on 32-bit targets.
- Resolve table collisions by exact fingerprint equality and linear probing.
  No deletion means the first empty slot proves absence.
- Grow at the same fixed 70% load ceiling used by the accepted AIG table.
- Return an owned occupied/vacant slot decision so a new canonical clause is
  appended to the authoritative formula before its index is installed, without
  a second table probe.
- Preserve canonicalization, fingerprints, formula/literal order, exact
  full-clause comparison, collision-only side buckets, duplicate counters,
  DIMACS, SAT submission, lift maps, proofs, and replay byte for byte.
- Keep the collision side table unchanged until real collisions or attribution
  justify a second experiment.

## Required evidence

Focused tests must cover empty lookup, repeated fingerprint lookup, different
keys with the same initial slot, growth/rehash, deterministic slot behavior,
and the existing forced equal-fingerprint/distinct-clause regression. All CNF,
SAT-BV, proof, formatting, strict Clippy, and documentation gates must pass
under the 4 GiB wrapper.

Acceptance then requires five clean representative cold processes with
identical clause attempts, tautology/duplicate counts, emitted clauses,
decisions, and replay, and improvements in both CNF and total medians. The full
30,628-query 4 GiB tier must confirm the win with identical AIG/CNF structure.
Otherwise restore the `HashMap` primary and defer this ADR; do not combine a
clause encoding or side-bucket change to rescue it.

## Rejection conditions

Reject on any changed clause order/content, collision suppression, proof/model
replay difference, memory regression beyond the established process alarm, or
end-to-end loss. A microbenchmark-only lookup win is insufficient.

## Experiment

The isolated candidate used power-of-two slots, linear probing, a fixed 70%
growth threshold, and an occupied/vacant lookup result that avoided a second
probe. The collision side table and every exact clause comparison remained
unchanged. Focused collision/probe/growth/layout tests passed, as did all
`axeyum-cnf` unit, interpolant, mathematical-route, vivification, proof, format,
and strict-Clippy gates under the 4 GiB wrapper.

Five independent baseline processes at revision `881be6db` and five candidate
processes at revision `98e7fe7a` ran the corrected 162-query representative
corpus. Every process decided 162/162 queries (88 SAT, 74 UNSAT) with zero
errors, disagreements, or model-replay failures. Structure was identical in
every run: 81,040 AIG nodes, 175,502 clause attempts, 5,019 tautologies,
95,898 duplicate clauses, and 74,585 emitted clauses.

## Result

The candidate fails both required performance conditions. Relative to the
five-process baseline, mean/p50 total Axeyum time regress 3.67%/3.87%, while
mean/p50 CNF encoding time regress 8.55%/7.52%. The normalized ratio regresses
1.16%; Z3's +2.49% control drift does not explain the isolated 8.55% CNF loss,
and every candidate CNF run is slower than every baseline CNF run. The
representative gate is decisive, so the full tier was not run.

## Decision

Restore the accepted `std::HashMap` primary index and defer this design. The
implementation was reverted in `90e298f2`. Do not retry direct linear probing
or alter the collision side table without new per-probe evidence that explains
why the AIG table result does not transfer to clause fingerprints. Continue
GQ5 from a separately attributed CNF subphase or an encoding change with a
larger structural hypothesis.
