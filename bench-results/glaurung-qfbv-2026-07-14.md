# Glaurung QF_BV capture and artifact-v26/v27 baseline

Date: 2026-07-14  
Axeyum measurement revision: `f1e02094d2e150db4f46e5725868f55d6a5f4d65`  
Axeyum production rerun revision: `5bd9b9658034fc123af57656d8c030c84071da1e`
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

## Artifact-v26 measurement finding (superseded by v27 below)

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

The implementation order inferred before the production correction was:

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

## Artifact-v27 production correction

ADR-0143 makes the structural demand walk opt-in. Normal lowering still
materializes the complete circuit and retains actual term/symbol-bit counts,
but does not pay for observational request/availability analysis. Artifact v27
marks structural demand fields unavailable rather than encoding “not measured”
as zero. All raw artifacts are retained beside the access-controlled capture at
`axeyum-results/5bd9b965-v27/`; the two full artifacts have SHA-256 digests
`7339841054356719ca0d22fa8c66eb382e707231c55b3055c1c7a0c3f68970b5`
(raw) and
`b6f462958d9dcfb2a1bf528ae85b12c0ade24a661b4fbc3f26963cddcbb61cdd`
(canonical).

Every v27 trial is 100% decided and manifest/Z3 agreed with zero operational
errors or model-replay failures.

| Tier/policy | Axeyum | Z3 | ratio | word | bit-blast | CNF | SAT |
|---|---:|---:|---:|---:|---:|---:|---:|
| representative raw, p50 of 5 | 0.2505 s | 0.1517 s | 1.65x | 0 | 0.0950 s | 0.1075 s | 0.0424 s |
| representative canonical, p50 of 5 | 0.2069 s | 0.1505 s | 1.37x | 0.0119 s | 0.0595 s | 0.0922 s | 0.0383 s |
| full raw, one trial | 24.30 s | 7.66 s | 3.17x | 0 | 10.52 s | 9.83 s | 3.68 s |
| full canonical, one trial | 21.07 s | 7.76 s | 2.71x | 1.84 s | 5.85 s | 9.40 s | 3.78 s |

The representative Axeyum totals are stable (raw/canonical CV 0.55%/0.51%).
One canonical Z3 control trial ran in 0.103 seconds rather than roughly
0.146--0.151 seconds, inflating ratio CV; the reported ratio is therefore the
five-trial median.

Removing the diagnostic cuts the comparable full raw/canonical totals by
79.4%/58.5% relative to v26. On the corrected production path, canonical v2
reduces full Axeyum time by 13.3% and bit-blast time by 44.4%; the earlier 57.1%
total reduction was dominated by avoiding work in the observational profiler.
CNF size remains roughly flat and CNF encoding is now the largest canonical
stage: 9.40 seconds (44.6%), versus 5.85 seconds bit blast (27.8%), 3.78 seconds
SAT (18.0%), and 1.84 seconds rewriting (8.7%).

Family aggregation makes the next target precise. `register-slice` contributes
12.08 seconds and `slice-partial` 8.78 seconds of the 21.07-second canonical
total. Their CNF costs are 4.94 and 4.36 seconds respectively. Across the full
tier, CNF gate emission costs 4.79 seconds, root emission 1.91 seconds,
reachability/planning 1.22 seconds, and variable allocation 0.069 seconds;
53.75 million clause attempts emit 49.20 million clauses and discard 4.25
million duplicates. GQ5 gate/root emission and duplicate handling therefore
precede SAT tuning. The bounded affine-word hypothesis remains secondary until
it demonstrates a circuit/CNF reduction on `slice-partial` rather than only a
word-DAG reduction.

## ADR-0144 CNF deduplication ownership win

Revision `f6c4b5755a75129ec1c7a31be69eaac8d34ea5da` replaces the
`BTreeSet<Vec<CnfLit>>` dedup copy with a deterministic fingerprint table that
references formula-owned clauses and requires exact equality before suppressing
a duplicate. A scalar ordered-index prototype regressed representative CNF by
39.4% and was rejected. The accepted deterministic hash table improves the
five-process representative canonical median from 0.2069 to 0.1938 seconds
(-6.31%) and CNF from 0.0922 to 0.0781 seconds (-15.29%).

The full confirmation decides and replays all 13,462 queries with zero errors
or disagreements. Axeyum falls 21.070 → 19.217 seconds (-8.79%), CNF falls
9.397 → 7.659 seconds (-18.49%), and the ratio falls 2.715x → 2.470x while Z3
remains 7.76/7.78 seconds. Both versions emit exactly 49,199,541 clauses with
identical CNF-variable distributions. The accepted full artifact digest is
`0b1a956a5d92171fa9b822a93006517f2f251aafb46e2c5663d12adfa7087523`.

Post-change CNF subphases are 3.56 seconds gate emission, 1.40 seconds root
emission, 1.21 seconds planning, and 0.067 seconds allocation. CNF remains the
largest stage (39.9%), followed by bit blast (31.0%), SAT (18.6%), and word
rewrite (9.5%). The next GQ5 slice should target clause-emission allocation or
duplicate generation inside gate/root encoding, then planning; SAT tuning and
broad GQ4 remain gated.

## ADR-0145 stack-emitted not-AND clauses

Revision `c139d73bfe8e08c0db5beba0ea302bd1afec499f` replaces the
encoder-local forward `Vec` and reverse `Vec<Vec<EncodedLit>>` Cartesian
expansion for the bounded two-factor not-AND family with fixed stack arrays and
four exact shape matches. Every clause still crosses the ordinary normalization
and collision-safe exact-dedup boundary.

Five clean representative canonical processes improve median total from
0.19380 to 0.18985 seconds (-2.04%) and median CNF from 0.07813 to 0.07298
seconds (-6.60%). The full confirmation decides all 13,462 queries (1,774 SAT /
11,688 UNSAT) with zero errors, disagreements, or replay failures. Against
ADR-0144, Axeyum total falls 19.2172 → 18.6909 seconds (-2.74%), CNF falls
7.6588 → 7.2313 seconds (-5.58%), gate emission falls 3.5579 → 3.1861
seconds (-10.45%), and the ratio falls 2.470x → 2.399x while Z3 remains
7.78/7.79 seconds.

The before/after artifacts both emit exactly 49,199,541 clauses and retain the
same variable and gate counts, including 2,232,632 recognized not-AND gates.
The accepted full artifact digest is
`d2920cbf660564333d2b0b2bb7fcb5128f2d6c3416491b9ec220752417285a63`.
Post-change CNF subphases are 3.19 seconds gate emission, 1.39 seconds root
emission, 1.21 seconds planning, and 0.067 seconds allocation. CNF remains the
largest stage (38.7%), followed by bit blast (31.6%), SAT (19.1%), and word
rewrite (9.7%). The next bounded GQ5 investigation is root-emission allocation
and planning; SAT tuning remains attribution-gated.

## ADR-0146 direct-root scratch rejection

Per-instance artifact-v27 attribution after ADR-0145 correlates root-emission
time with direct-root count at 0.920 and reachable AIG nodes at 0.953. The
`register-slice` and `slice-partial` families account for 1.379 of 1.391 root
seconds and 169,758 direct roots. Source inspection identifies one exact waste:
emission retraverses a planned private OR tree and allocates fresh leaf/helper
vectors even though it never consumes the helper list. Proposed ADR-0146 reuses
one cleared encoder-local leaf buffer for that second traversal.

The hypothesis fails the five-process representative gate. Against accepted
ADR-0145, median total regresses 0.18985 → 0.19187 seconds (+1.06%), mean
total regresses 0.18970 → 0.19242 seconds (+1.43%), median CNF regresses
0.07298 → 0.07656 seconds (+4.91%), and the matched third run's root subphase
regresses 0.01427 → 0.01456 seconds (+2.05%). Every run is still 128/128
decided with zero errors, disagreements, or replay failures, and emits the same
507,195 clauses with 1,911 direct roots. Revision `6ccc8984` is therefore
reverted without a full-tier run and ADR-0146 is deferred. Planning attribution,
not another root scratch, is next.

## ADR-0147 zero-copy reverse-node rejection

Private AND-tree planning visits nodes in descending dense-ID order so a parent
claims eligible helpers first. The backing `Aig::nodes()` slice iterator is
already exact-size and double-ended, but its opaque return type exposed only
`Iterator`; planning therefore copied every `(id,node)` into a temporary vector
solely to reverse it. The tested ADR-0147 exposes the existing standard iterator
traits and iterates directly in the same order.

The five-process gate shows the local optimization but rejects the whole-pipeline
result. Median planning improves 0.01207 → 0.01177 seconds (-2.49%), while
median total regresses 0.18985 → 0.19083 seconds (+0.51%), mean total
regresses 0.18970 → 0.19122 seconds (+0.80%), and median CNF regresses
0.07298 → 0.07557 seconds (+3.55%). All runs remain 128/128 decided with
identical CNF/verdict/replay shape. The projected full planning saving is only
about 0.03 seconds, so revision `99e93a08` is reverted without a full run and
ADR-0147 is deferred. Shared gate/root clause normalization and allocation,
not another planning micro-slice, is next.

## ADR-0148 bounded CNF capacity rejection

Both the outer formula clause vector and collision-safe fingerprint index start
empty and grow during 53.75 million clause attempts. Existing variable/root
counts support a no-pass hint:
`min(5 * cnf_variables + min(roots, 1,024), 65,536)`, with zero reserved for a
zero-variable encoding. On the full tier it covers all 13,462 final clause
counts, reserves 69,225,859 aggregate slots for 49,199,541 emitted (1.407x),
and stays below the approximately 71,566,146 final slots (1.455x) implied by
ordinary power-of-two vector growth. Proposed ADR-0148 applies the private hint
to both containers without changing clause content.

The five-process representative gate rejects the combined hint. Median total
regresses 0.18985 → 0.19465 seconds (+2.53%), mean total regresses 0.18970
→ 0.19442 seconds (+2.49%), median CNF regresses 0.07298 → 0.08030
seconds (+10.04%), median gate emission regresses 0.03211 → 0.03965 seconds
(+23.49%), and median allocation regresses about 12.2%. Root emission improves
about 4.9%, but the sparse pre-sized fingerprint table makes common lookups
costlier. All runs remain 128/128 decided with the same 507,195 clauses and zero
errors, disagreements, or replay failures. Revision `2527741b` is reverted
without a full run and ADR-0148 is deferred. A formula-header-only experiment,
with ordinary index growth retained, is the only admissible capacity follow-up.

## ADR-0149 formula-header-only capacity rejection

ADR-0149 isolates the unresolved half of ADR-0148: the same capped no-pass hint
pre-sizes only contiguous `CnfClause` headers, while the collision-safe
fingerprint table starts empty and grows exactly as in accepted ADR-0145. This
preserves lookup locality and tests only avoided header moves. Revision
`84b39844` passes 284 CNF tests, 30 SAT-BV tests, strict Clippy, and five clean
representative processes under the 4 GiB cap. All runs remain 128/128 decided,
emit 507,195 clauses, identify 1,911 direct roots, and have zero errors,
disagreements, or replay failures.

Against accepted `c139d73b`, total p50 changes 0.189851 → 0.189539 s (-0.16%)
but mean changes 0.189702 → 0.189841 s (+0.07%) and CV rises 0.570% → 0.852%.
CNF p50 changes 0.072978 → 0.073583 s (+0.83%) and mean changes 0.073648 →
0.074138 s (+0.67%). Matched allocation/gate/root/planning medians change
+0.94%/+0.68%/+2.09%/-0.45%. The candidate fails the predeclared CNF-and-total
gate, so ordinary vector growth is restored, no full run is spent, and
ADR-0149 is deferred. Capacity-hint micro-work is exhausted; the next GQ5 step
must re-attribute shared clause normalization/ownership.

## ADR-0150 inline primary fingerprint-index acceptance

The ownership audit finds that accepted ADR-0144's
`HashMap<u64, Vec<usize>>` performs separate membership/insertion probes and
allocates on the first index push for each distinct fingerprint. The full tier
emits 49,199,541 clauses; `register-slice` plus `slice-partial` contribute
53,247,640/53,748,044 attempts (99.1%) and 48,702,009/49,199,541 emitted clauses
(99.0%). ADR-0150 retains the first formula index inline and uses a
secondary vector only for genuine fingerprint collisions. Exact equality,
formula ownership, clause order, decisions, and replay remain acceptance
invariants. The implementation passes 283 CNF tests, 31 SAT-BV tests, strict
Clippy, and forced-collision coverage.

Against accepted `c139d73b`, five representative processes improve total
p50/mean 0.189851/0.189702 → 0.165169/0.165105 s (-13.00%/-12.97%) and CNF
p50/mean 0.072978/0.073648 → 0.051845/0.051885 s (-28.96%/-29.55%). Gate/root
medians improve 24.94%/23.07%, and total CV falls 0.570% → 0.212%. All trials
remain 128/128 decided with identical 507,195 clauses and zero errors,
disagreements, or replay failures.

The full 13,462-query run improves total 18.6909 → 16.5397 s (-11.51%), CNF
7.2313 → 5.1768 s (-28.41%), gate/root emission 3.1861/1.3910 →
2.3999/1.0835 s (-24.68%/-22.11%), and ratio 2.399x → 2.136x. Both revisions
make 53,748,044 attempts, skip 4,248,964 duplicates, and emit exactly
49,199,541 clauses; every decision/oracle/replay gate passes. Artifact SHA-256:
`43ff5944eacd8e511a0c4656b3cdd99f0794ba376f6580a9883527684618075e`.
ADR-0150 is accepted. Bit blast is now the largest stage at 5.88 s, ahead of
CNF at 5.18 s, so the next slice must re-attribute residual lowering/AIG work.

## ADR-0151 dense term-bit lift-index acceptance

The accepted full artifact materializes 23,029,676 term-bit bindings, including
22,797,529 (99.0%) in `register-slice` and `slice-partial`, and inserts every
binding into an ordered `(TermId, bit) -> AigLit` map. Term IDs are dense, each
term's bindings are already contiguous in the authoritative vector, and the
map's only read surface is point lookup; interpolation iterates the vector and
model replay uses symbol inputs. Proposed ADR-0151 replaces the redundant map
with per-term ranges while preserving public lookup, binding order, incremental
growth, and replay. All 20 BV, 10 BV interpolant, and 31 SAT-BV tests plus
strict Clippy pass.

Against accepted `4d66fc0e`, five representative processes improve total
p50/mean 0.165169/0.165105 → 0.155940/0.155751 s (-5.59%/-5.67%) and bit-blast
p50/mean 0.060683/0.060721 → 0.051270/0.051258 s (-15.51%/-15.58%). All runs
retain identical 746,716 AIG requests, 410,719 created nodes, and 507,195
clauses, with every decision/replay gate green.

The full 13,462-query run improves total 16.5397 → 15.5961 s (-5.71%), bit
blast 5.8839 → 4.9393 s (-16.05%), and ratio 2.136x → 1.992x. CNF/SAT remain
flat, while both artifacts retain 76,493,904 AIG requests, 40,063,239 created
nodes, and 49,199,541 clauses. Artifact SHA-256:
`b346394c5a727da6c58ae15b013f837f703ad7dd03268cedf3f98a6989712c3c`.
ADR-0151 is accepted; CNF and bit blast now cost 5.18/4.94 s, so the next audit
compares remaining dense-ID memo work with shared normalization.
