# ADR-0548: Stop extrapolating the level-three connected trace bound

Status: accepted
Date: 2026-08-20
Index-summary: Record the exact GF(16) level-three counterexample to the ell^4 connected Adams trace allowance and retain the one-extra-q cutoff only as an unproved stopping hypothesis

## Context

ADR-0547 made the extension-field connected Adams trace deterministically
shardable.  For `(ell,n)=(3,7)`, the first three field rows had minimum
normalized coefficients

```text
q=2: 1,  q=4: 10,  q=8: 58.
```

All three obeyed the proposed coefficient `ell^4=81` in

```text
abs(T_r) <= ell^4 q^(2ell+2n).
```

That survival was finite evidence only.  The next row has `16^7=268435456`
monic polynomials and was the first intended use of the checked shard merge.

## Decision

Run the exact `(q,ell,n)=(16,3,7)` population as 100 deterministic contiguous
shards from commit `3e49485b0f6f6c5d808c54a6e69e25c6d81af149`.  The release binary had
SHA-256

```text
d8894fcc2887c935c774b20e360abacd71ad1b44da80cc0f7ffcaf5c47891141.
```

Hosts `s1,s4,s5,s6,s7` each received one residue class of 20 shard indices
under a user transient unit with `MemoryHigh=1G`, `MemoryMax=2G`, two worker
processes, and `CPUWeight=25`.  Every unit exited successfully and emitted an
empty error log.  The merge rejected neither coverage nor population:

```text
candidate count       = 268435456
class count           = 4096
sum of populations    = 268435456
M_2                    = 267386880
M_4                    = 4433642394746880
fourth cumulant num.  = 17945712018094817280
connected trace       = 301079086801372657987092480
geometric scale       = 1208925819614629174706176
minimum coefficient  = 250
```

An independent integer recomputation from all 100 JSON class vectors checked
the partition endpoints, common metadata, 4096-vector lengths, population
conservation, both moments, the Wick subtraction, the trace, and the ceiling.
The SHA-256 of the 100 ordered shard SHA-256 values is

```text
8b5cf5dab29188f63318458c36c49e7159580e985f9f9ddcb5014daa64a5d7aa.
```

Because `250>81`, the level-three row refutes the coefficient-`ell^4`
allowance by a factor of approximately `3.07465`.  It does **not** refute a
cohomological cutoff by itself: the weaker one-extra-`q` allowance has
coefficient `ell^4 q=1296` and survives this row.  Nor does this extension-field
trace test the separate binary Witt off-diagonal inequality or the signed
cross-order endpoint sum.

Add `scripts/run-gf2-connected-trace-shards.sh` as the reusable fleet driver.
It partitions indices by stride, limits local process parallelism, refuses to
overwrite completed shards, writes through a process-unique temporary path,
and atomically renames only successful output.  Resource caps remain an
explicit responsibility of the transient-unit caller.

## Consequences

- The `q<=8` level-three pattern is closed as a source of the original bound;
  no proof may extrapolate it.
- The one-extra-`q` allowance remains a finite stopping hypothesis, not a
  theorem or endpoint input.
- Another larger row is lower value than deriving the exact level-three
  extension trace or its virtual zeta recurrence: the coefficients
  `1,10,58,250` already show substantial field-size growth.
- This negative result does not move the binary endpoint proof frontier.  It
  prevents a false geometric lemma from entering the paper or fact ledger.
