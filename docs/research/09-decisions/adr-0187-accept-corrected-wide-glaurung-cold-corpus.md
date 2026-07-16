# ADR-0187: Accept the corrected wide Glaurung cold corpus

Status: accepted
Date: 2026-07-16

## Context

ADR-0184 proved that Glaurung's old SMT-LIB producer encoded every assertion
root as a BV1 equality even though the native backends use arbitrary-width
truthiness. Axeyum's strict sort errors were correct, and the old 128/13,462
cold tiers became historical byte identities. GQ1 and GQ10 therefore required
a new zero-exclusion capture before another cold performance or rewrite claim.

The corrected three-driver recapture contains 5,102 distinct scripts. All
218,434 assertion roots in that recapture are width one, so the 2,225 old
malformed hashes cannot be mapped to current corrected byte identities. The
claim that those exact hashes were recoverable is not supportable. Widening the
same corrected capture to SurfacePen and NETwtw10 instead produces the current
workload evidence that matters: 30,628 distinct scripts, including 7,953
scripts with at least one wide root and 13,015 width-64 assertion roots.

A monolithic full-tier v31 process exceeded the hard 4 GiB limit through
cumulative process residency. The largest individual script is only about
1.07 MiB, so raising the memory limit or excluding large formulas would hide a
harness/process-lifetime problem rather than validate the corpus.

## Decision

Accept
`2026-07-16-corrected-wide-v3` as the GQ1/GQ10 cold corpus for the five
available query-producing drivers. Pin its 162-query representative tier in
the availability-aware regular semantic gate. Preserve the 30,628-query full
tier as four physical, deterministic process shards using
`u64::from_be_bytes(sha256[0:8]) modulo 4`.

The shard boundary is only a memory/process envelope. A publishable full result
must pass `summarize-glaurung-shards.py`, which validates the byte-pinned parent
and child capture indexes, exact disjoint path union, manifest bytes,
configuration/source identity, every per-instance trusted and Z3 verdict,
original-model replay, rewrite decision invariance, and each successful 4 GiB
time record before summing timings. Glaurung/Z3 remain untrusted downstream
differential evidence; they do not replace Axeyum's replay/proof boundaries.

## Evidence

Glaurung producer `1b32cb9` and strict builder `3b64aaf` captured 30,678
observations, 30,628 distinct hashes, 50 duplicate observations, zero verdict
conflicts, and zero exclusions across `win10-vwififlt`, Dptf, IntcSST,
SurfacePen, and NETwtw10. The representative tier has 162 scripts (88 SAT / 74
UNSAT); the full tier has 30,628 (21,333 SAT / 9,295 UNSAT).

Pinned identities are:

- representative capture index / manifest:
  `6e97e653a01bde899050be08b9a3920f7f4f8472cf98d265f6f45131be5987be` /
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- full capture index / manifest:
  `b9cf0083cbe6d2f7a274f7d7886ea1e03e50629f3211cc561611ae84883cfacf` /
  `c3cad70caff90d7f1528196e306cbb45808c14f839f07e742aac6ad2f0ade75c`;
- four-shard set:
  `c0d7b54fe6b784655e57e198693a01df5998179f5a6d1003387b6c570f683a36`.

Eight clean Axeyum `f7f174c5` processes use one solver worker, eight manifest
hash workers, deterministic resource limits, in-process Z3, original-model
replay, and `--require-reproducible-run`. Both policies decide and agree on all
30,628 scripts with zero unknowns, errors, disagreements, oracle gaps, replay
failures, or rewrite decision changes.

- Raw: Axeyum 30.802801 seconds, Z3 69.126627 seconds, ratio 0.445600;
  68,161,077 AIG nodes and 72,701,196 emitted clauses; 1,445,304 KiB maximum
  child RSS.
- Canonical v4: Axeyum 18.470722 seconds, Z3 68.556019 seconds, ratio 0.269425;
  32,350,460 AIG nodes and 32,119,981 emitted clauses; 1,424,500 KiB maximum
  child RSS. It changes 30,627 DAGs through 4,790,690 applications while all
  30,628 decisions match raw/trusted/Z3 outcomes.

The fail-closed raw/canonical summary SHA-256 values are
`ae345d18f37abbb5357c20e6860386172809865f54d784410df304f3cf802b59`
and
`a942cf05add547746c37ffbf2eff0f6a80e9b26076dacb30985c63e2c4ffc451`.
This is a clean composite baseline, not yet run-to-run variance evidence.

## Consequences

GQ1's corrected cold truth and GQ10's five-driver widening are complete for
available families. The regular gate now detects regressions on the corrected
162-query distribution, and the sharded full contract prevents decided-rate,
exclusion, dirty-source, or OOM artifacts from masquerading as speedups.

Canonical v4 is strongly productive on the widened distribution, but the
0.269x ratio must not be compared causally with the stale 2026-07-14 ratio:
query bytes, family mix, and process envelope changed. Repeat the exact clean
four-shard composite before setting variance alarms or comparing commits.
Then use the new post-canonical stage totals (CNF 4.440 s, bit blast 3.673 s,
SAT 3.406 s, word rewriting 4.336 s) to select any next cold optimization.
GQ4 remains off, and GQ8 cache work still requires explicit content/config/
scope identity plus mandatory model or proof replay.

## Alternatives

Keeping the stale capture was rejected because it tests producer-invalid byte
identity. Excluding wide roots was rejected because they are a first-class
Glaurung requirement. Raising the monolithic memory limit was rejected because
it weakens the established deployment envelope. Treating shard timings as
independent repetitions was rejected because they partition one corpus run;
only repeated complete shard sets can establish variance.
