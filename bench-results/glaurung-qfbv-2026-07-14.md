# Glaurung QF_BV capture and artifact-v26 baseline

Date: 2026-07-14  
Axeyum measurement revision: `f1e02094d2e150db4f46e5725868f55d6a5f4d65`  
Glaurung capture revision: `286f7445142347f6beb46ca18f2ebbd48b9c21d1`  
Data location: access-controlled; query bytes are not committed here.

## Capture audit

The three driver captures were run sequentially to avoid the producer's
cross-process `SEEN` race. The raw result contains 15,710 index rows, 15,687
unique hash-named files, 23 duplicate rows, and zero hashes with conflicting
verdicts. The source drivers are pinned by SHA-256:

| Driver | SHA-256 |
|---|---|
| `win10-vwififlt.sys` | `13c3b69a5d0179ed3cc2c999ff97edbaedd63da55ddb74427251c360706a3820` |
| `sqfs-intel-DptfDevGen.sys` | `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b` |
| `windows-update-intel-audio-IntcSST.sys` | `f7c8e4f106baa5b2a1a18e60731ad42a6f734aee1d049576eaf6d123d5629750` |

The producer's 17-row exclusion file contains 11 unique hashes, but a strict
full ingestion found 2,214 additional malformed dumps. All 2,225 rejected
scripts are genuinely ill-sorted: 1,429 contain a 120-vs-64 operation, 795 a
96-vs-64 operation, and one a 160-vs-128 operation. Z3's CLI also emits a sort
error for these scripts before continuing with later commands, so the captured
internal-Z3 verdict is not a trusted verdict for the dumped SMT-LIB text.
Axeyum's strict sort checking is therefore retained.

Two hash-free capture indexes were regenerated through Axeyum's strict
manifest generator:

| Tier | Files | Verdicts | Manifest SHA-256 |
|---|---:|---|---|
| representative | 128 | 64 SAT / 64 UNSAT | `1e7725089147a20a778342db55323503c4bd4c6d126bf3c4d13865b57f096a45` |
| full well-typed | 13,462 | 1,774 SAT / 11,688 UNSAT | `5d2f74c2977f734c477a1a7835b03e17bd96a6b13a1ef17293bf1e6e6775ee9b` |

The deterministic representative archive digest is
`216a7b3d2eb4c2d1730f26cc9c633bef624246704cb9ceb306ffec09886a006a`.

## Representative repeated result

Each policy ran in five fresh processes. Every trial decided all 128 queries,
matched the manifest and in-process Z3, and had zero operational errors,
SAT/UNSAT disagreements, or model-replay failures. Separate raw and canonical
proof companions rechecked all 64 UNSAT results.

| Policy | Axeyum total p50 | Z3 total p50 | ratio p50 | word policy p50 | bit-blast p50 | CNF p50 | SAT p50 |
|---|---:|---:|---:|---:|---:|---:|---:|
| raw | 0.982 s | 0.151 s | 6.53x | 0 | 0.827 s | 0.106 s | 0.0419 s |
| canonical v2 | 0.506 s | 0.148 s | 3.42x | 0.0120 s | 0.360 s | 0.0911 s | 0.0377 s |
| configured | 0.512 s | 0.145 s | 3.54x | 0.0122 s | 0.358 s | 0.0996 s | 0.0385 s |

Canonical v2 reduces median Axeyum time by 48.5% versus raw and is the best
cold candidate. One canonical trial had an anomalously fast Z3 control
(0.102 s versus about 0.148--0.150 s in the other four), so ratio CV is 18.4%
while Axeyum-total CV is only 0.54%. The ratio target remains open at 3.42x.

Canonical rewrites 127/128 queries with 13,156 applications. It removes 1,315
of 1,435 measured slice/coercion opportunities, reduces reachable term bits
materialized from 556,330 to 236,606, and preserves every verdict and replay.

## Full well-typed single-run result

The raw and canonical artifact-v26 runs share the same source revision and
environment. Both decide all 13,462 queries with zero errors, disagreements,
or model-replay failures. These are single scheduled-tier trials, not a
run-to-run variance claim.

| Policy | Axeyum total | Z3 total | ratio | word policy | bit-blast | CNF | SAT |
|---|---:|---:|---:|---:|---:|---:|---:|
| raw | 118.17 s | 7.78 s | 15.19x | 0 | 104.42 s | 9.81 s | 3.67 s |
| canonical v2 | 50.75 s | 8.04 s | 6.32x | 2.10 s | 35.63 s | 9.20 s | 3.64 s |

Canonical reduces full-tier Axeyum time by 57.1% and materialized term bits by
72.0% (82.36M to 23.03M). It does not reduce final circuit size: AIG nodes rise
3.0% and CNF clauses rise 1.2%. The speedup is primarily less word-DAG traversal.

## Measurement finding and next order

Artifact v25's conservative bit-demand diagnostic currently runs inside every
production lowering. On the canonical full tier it costs 29.57 s, 83.0% of
reported bit-blast time and 58.3% of total Axeyum time. It is observational—it
does not yet drive lowering—and therefore must become an opt-in diagnostic (or
be fused into actual partial lowering) before another client ratio is accepted.
The current ratios measure this real regression faithfully, but do not describe
the intended production path.

After canonicalization, structural demand says 98.16% of term bits and 91.51%
of symbol bits are live on the full tier. That moves broad GQ4 partial-bit
lowering behind the measurement repair and targeted word/CNF work unless a
family-specific profile shows a larger cone reduction.

The next implementation order is:

1. make demand profiling opt-in and rerun representative/full raw and canonical
   v2 at one clean revision;
2. keep canonical v2 as the cheap cold candidate only if corrected end-to-end
   repetitions remain non-worse;
3. add exact bounded affine BV add/sub constant-chain normalization (and cheap
   duplicate-root handling) for the remaining `slice-partial` hotspot;
4. re-attribute the post-repair pipeline; CNF construction is the likely GQ5
   target, while SAT tuning remains gated;
5. fix Glaurung's width-coercion/dump validation and cross-process capture
   deduplication; and
6. capture an ordered path/scope trace before warm integration or caching.

