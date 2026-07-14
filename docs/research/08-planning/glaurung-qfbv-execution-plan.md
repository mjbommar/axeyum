# Glaurung QF_BV execution plan

Status: active measured execution plan
Last updated: 2026-07-14

## Outcome

The shortest evidence-backed path to useful Glaurung functionality is:

1. repair and ingest the real capture through Axeyum's artifact-v26 contract;
2. reproduce the current **raw one-shot** integration before comparing any
   preprocessing policy (complete for the representative and well-typed full
   tiers);
3. remove the always-on observational bit-demand pass from production timing;
4. retain exact extract/coercion cancellation as the cheap cold candidate and
   extend word simplification only from the measured residual;
5. optimize AIG/CNF construction only where corrected counters attribute cost;
6. capture an ordered extending-path trace and validate warm push/pop reuse in
   the Glaurung explorer; and
7. derive caching and an automatic preprocessing policy from the cold corpus
   and warm trace rather than from synthetic formulas.

The byte-complete 2026-07-14 capture and artifact-v27 results now supersede the
producer's artifact-v17 estimate and the profiler-confounded v26 timing. Five
representative production trials put raw at 1.65x Z3 and canonical v2 at 1.37x;
both earlier proof companions recheck all 64 UNSAT rows. The well-typed
13,462-query full tier is 3.17x raw and 2.71x canonical in one scheduled trial.
ADR-0143 removes the artifact-v25 structural demand diagnostic from production
and proves CNF construction, not SAT, is now the dominant measured stage.
ADR-0144's first GQ5 slice then reduces full canonical CNF 18.5% and total time
8.8%, reaching 19.22 seconds / 2.47x Z3 without changing CNF content.
ADR-0145's bounded not-AND emitter removes temporary-vector expansion for 2.23
million recognized gates and further reduces full CNF 5.6%, gate emission
10.5%, and total 2.7%, reaching 18.69 seconds / 2.40x Z3 with the same clauses.
ADR-0150 then removes the common per-fingerprint index-vector allocation and
second map probe: full CNF falls 28.4%, total falls 11.5% to 16.54 seconds, and
the ratio reaches 2.14x with the same 49,199,541 clauses.

This note expands `PLAN.md` items GQ1--GQ10 into an executable sequence. It does
not authorize changes to the Glaurung repository; producer-side and explorer
tasks below identify the required cross-project handoff.

## Evidence inspected

### Producer capture

The captured Glaurung source is commit `286f7445142347f6beb46ca18f2ebbd48b9c21d1`
on `sec/axeyum-backend`. Its committed capture directory contains the procedure,
builder, exclusion list, and a 128-entry representative manifest, but no SMT-LIB
payload. The representative distribution is:

| Family | Queries |
|---|---:|
| `register-slice` | 42 |
| `slice-partial` | 48 |
| `arithmetic` | 23 |
| `comparison` | 12 |
| `mixed` | 2 |
| `trivial` | 1 |
| **Total** | **128 (64 SAT / 64 UNSAT)** |

The capture audit resolves the four original handoff questions:

- 15,710 index rows correspond to 15,687 unique hash-named files: exactly 23
  cross-process duplicate rows, with zero conflicting verdicts.
- `excluded-hashes.txt` has 17 rows and 11 unique hashes, but strict ingestion
  finds 2,225 ill-sorted dumps in total (1,429 120-vs-64, 795 96-vs-64, and
  one 160-vs-128). Z3's CLI also diagnoses these scripts as ill-sorted.
- separate self-contained 128-query representative and 13,462-query well-typed
  full roots now pass exact membership and Axeyum-generated SHA-256 manifests;
  the malformed 2,225 remain a Glaurung producer bug, not an Axeyum corpus tier.
- both roots use strict hash-free `capture-index-v1.json` input and Axeyum owns
  byte hashing and ordinary manifest re-ingestion.

The producer still needs to make cross-process deduplication/conflict detection
atomic and validate every dumped script with a strict SMT-LIB parser before
indexing it. An exclusion list must not hide width-coercion defects.

### Current integration mode

Glaurung's one-shot Axeyum backend creates a fresh `IncrementalBvSolver` for
each check and calls raw `assert`. Its own measurements say
`assert_configured` is about 1.3--2x slower in that cold mode. The producer's
artifact-v17 command likewise used neither `--rewrite default` nor
`--preprocess`.

Axeyum's current `bench-glaurung-qfbv` recipe does pass `--preprocess`.
Consequently, that recipe does **not** reproduce either the reported 2.10x
profile or Glaurung's current API behavior. The initial baseline must preserve
three separately named policies:

| Policy | Harness flags | Purpose |
|---|---|---|
| `raw` | rewrite off, preprocess off | Current Glaurung one-shot and artifact-v17 reproduction; primary cold control |
| `canonical` | `--rewrite default`, preprocess off | Cheap exact rewrite candidate |
| `configured` | `--preprocess` | Full warm-oriented preprocessing diagnostic; not the cold default |

The proof companion must use the same term policy as the performance artifact
whose assurance it accompanies. No policy may be renamed or silently changed
under an existing regression series.

### Current Axeyum implementation

The implementation audit narrows the first optimization slices:

- ADR-0142 completes GQ3's exact implementation tranche: `axeyum-rewrite`
  composes nested extracts, selects same-side or straddling concat ranges with
  direct whole-side returns, handles low/high/straddling zero/sign-extension
  regions, distributes extracts over bitwise operators and BV `ite`, and
  reassembles adjacent extracts. Stable per-class IDs preserve attribution.
- The bottom-up canonicalizer now reconsiders a replacement root for at most
  eight exact applications. A public report counter records actual remaining
  opportunities at exhaustion, and every expansion has a fixed per-rule fresh-
  node bound. This completes the semantic/fuel boundary; only the real-corpus
  AIG/CNF/time exit remains open.
- `axeyum-bv` currently lowers every child to a full `Vec<AigLit>` before an
  extract slices it. Raw `extract` therefore does not avoid constructing the
  discarded source bits. GQ4 must change the lowering demand contract, not just
  add another post-hoc slice.
- `axeyum-aig` already has deterministic structural hashing plus substantial
  constant, identity, XOR, and mux simplification. Artifact v24 now partitions
  primitive AND requests into trivial simplification, absorption, unique-table
  hit, and new-node outcomes; its `BTreeMap` is not an optimization target until
  the real capture shows that construction dominates.
- `axeyum-cnf` is already reachable-only and polarity-aware, with direct roots,
  XOR/mux/not-AND/private-tree recognition, and clause deduplication. Artifact
  v24 times its planning, allocation, gate-emission, and root-emission
  subphases and counts recognized gates and filtered clauses; GQ5 must consume
  that evidence before replacing encodings or data structures.
- The producer attribution assigns only 15% to SAT. GQ6 stays gated until the
  artifact-v25 reproduction or a later optimization makes SAT dominant.

These conclusions are consistent with the official [Z3 BV rewriter], which
collapses nested extracts and distributes general slices over concatenations,
and the official [Bitwuzla BV rewrites], which use exact extract rules with
growth guards. Bitwuzla's [AIG manager] uses an average-constant-time unique
table, while its [AIG-to-CNF path] preserves sharing and recognizes selected
gate shapes. Those are design references, not evidence that the same changes
will improve Axeyum.

[Z3 BV rewriter]: https://github.com/Z3Prover/z3/blob/master/src/ast/rewriter/bv_rewriter.cpp
[Bitwuzla BV rewrites]: https://github.com/bitwuzla/bitwuzla/blob/main/src/rewrite/rewrites_bv.cpp
[AIG manager]: https://github.com/bitwuzla/bitwuzla/blob/main/src/lib/bitblast/aig/aig_manager.cpp
[AIG-to-CNF path]: https://github.com/bitwuzla/bitwuzla/blob/main/src/lib/bitblast/aig/aig_cnf.cpp

## Functional requirements from Glaurung

Performance is not the only acceptance boundary. The integrated route must
retain all of the following:

- strict Bool/BV sort checking and explicit unsigned width coercion;
- complete scalar QF_BV translation for Glaurung's emitted formulas;
- SAT model values through width 128 in Glaurung's current `u128` slot, with a
  deliberate policy if wider values enter the workload;
- `Unknown`, timeout, and operational error counted separately, never folded
  into agreement or speedup;
- original-query model replay for every SAT result and independent proof
  recheck for the UNSAT assurance companion;
- deterministic resource bounds and the explorer's per-thread solve budget;
- one arena/solver per worker with no shared native context requirement;
- the native-free `qfbv` feature profile; and
- end-to-end finding behavior, not only per-query verdicts.

The last point needs special treatment. Different satisfying models can choose
different concrete addresses and steer exploration even when every SAT/UNSAT
verdict agrees. Glaurung already records model divergence. Functional parity
therefore requires either a solver-independent deterministic concretization
policy or an exploration comparison that accounts for equivalent choices; raw
finding equality cannot be attributed to solver correctness without controlling
this variable.

## Dependency-ordered work

### G0 — repair the capture contract

Owner split: Glaurung produces bytes and semantic index facts; Axeyum validates,
hashes, and benchmarks them.

1. Recover or regenerate the 128 representative `.smt2` files and retain the
   full raw directory in an access-controlled stable location.
2. Produce strict `capture-index-v1.json` with ordered relative path, trusted
   expected verdict, family, and tier membership only. The producer must not
   supply content hashes.
3. Make cross-process capture deduplication explicit. Reject duplicate hashes
   with conflicting verdicts; report index rows, unique hashes, SAT, UNSAT,
   undecided omissions, and exclusions separately.
4. Deduplicate the exclusions and explain or fix all 11 unique rejected
   formulas rather than allowing the list to hide a parser/producer regression.
5. Make representative and full roots self-contained, or give them separate
   roots and manifests. Exact directory membership must pass.
6. Run `--generate-corpus-manifest`, then ordinary manifest ingestion, before
   timing. Record source driver hashes, Glaurung revision, toolchain, capture
   command, and an archive digest for an access-controlled pack.

Checkpoint: the 128-query tier and a 13,462-query well-typed full tier have
byte-complete validated manifests; row/unique arithmetic and verdict conflicts
are audited; no query shape is normalized during handoff. G0 remains open on
the producer side until capture deduplication is atomic and all 2,225 malformed
dumps are prevented by explicit width coercion plus strict pre-index validation.

### G1 — establish the cold truth (GQ1 + GQ10)

Preparation landed 2026-07-14: explicit raw, canonical-only, and configured
recipes now cover single, repeated, and proof-companion runs. Raw is the
unsuffixed current-integration control; policy-specific output defaults and
dry-run regression tests prevent accidental series mixing.

1. Use the landed policy recipes without editing their flags.
2. Run raw first for five fresh-process repetitions on the representative tier,
   plus its separate proof-check companion.
3. Run the same repetition matrix for canonical-only and configured policies.
4. Report aggregate and per-family ratios, p50/p95, run-to-run CV, formula/AIG/
   CNF sizes, stage shares, and raw Z3 control drift.
5. Schedule the full tier using the access-controlled payload. Put the 128
   representative tier in the regular regression lane only after its runtime
   and licensing/data boundary are acceptable.

Every row requires 100% decided, zero errors, zero SAT/UNSAT disagreement, and
zero replay/proof failures. Regression thresholds are set only after stable
same-environment variance exists. This closes the measurement part of GQ1 and
the corpus-adoption foundation of GQ10.

Measured checkpoint (artifact v27): five representative raw/canonical trials
all pass the validity gates. Median aggregate ratios are 1.65x and 1.37x;
canonical's Axeyum total is 17.4% below raw. Raw and canonical proof companions
from the same semantic tranche each check all 64 UNSAT proofs. One scheduled
full trial per raw/canonical policy decides all 13,462 well-typed rows and
records 3.17x versus 2.71x; canonical is 13.3% faster. The full tier still needs
repeated trials before setting a regression threshold.

### G2 — add attribution needed for the first optimization

Extend the artifact without changing solver behavior:

- **Landed in artifact v23:** before/after/residual counts per GQ3 rule class,
  including same-side versus straddling concat slices, whole operands, extension
  regions, exact low cancellation, and nested-extract depth;
- **Landed in artifact v25:** request, unique-demanded, available, and actually
  lowered bit counts for terms and symbols. Structural propagation is exact for
  extract/concat/extensions/pointwise BV/ITE/rotations/FP reinterpretation and
  conservative-full for other operators; its nested analysis cost and coverage
  invariants are recorded;
- **Landed in artifact v24:** AIG unique-table hits/new nodes and primitive AND
  simplification counts; CNF planning/allocation/gate/root timing; reachable,
  skipped-helper, direct-root, and recognized/fused gate-family counts; and
  attempted, tautological, duplicate, and emitted clause counts. Explicit
  partition invariants catch incomplete instrumentation, and the CNF timers are
  marked as nested in total encode time;
- still needed: emitted and skipped literal counts, plus any finer
  subphase split justified by the real run; and
- metrics partitioned by Glaurung family and verdict.

Artifact v26 fixes a separate omission: canonical rewrite elapsed time is now
charged to word preprocessing, PAR-2, cold total, and the Axeyum/Z3 comparison.
The real run then exposed a more serious issue: structural demand analysis is
an always-on observational pass inside `lower_terms`, costing 29.57 s of the
canonical full tier's 50.75 s. Make it opt-in (or fuse it into actual partial
lowering), mark profile completeness explicitly, and keep production
performance artifacts free of observational overhead. Diagnostic artifacts
remain separate and must not be cited as client ratios. ADR-0143/artifact v27
now enforce that boundary: production reports structural demand as unavailable
while retaining actual lowered counts; explicit demand recipes run the complete
diagnostic. Corrected full raw/canonical totals are 24.30/21.07 s versus Z3
7.66/7.76 s, and CNF encoding is the largest canonical stage at 9.40 s.

Exit: the counters explain where the measured bit-blast and CNF time goes, and
their diagnostic overhead is absent from production timing or measured in a
separately named diagnostic artifact. This exit is currently open.

### G3 — exact cheap rewrite tranche (GQ2 + GQ3)

Create or extend an ADR before changing the public rewrite manifest. The first
tranche is exact-denotation only:

1. collapse `extract(extract(x))`;
2. handle general `extract(concat(...))`, including a boundary straddle and
   direct return of a complete high/low operand;
3. handle low, high, and straddling regions of zero/sign extension;
4. cancel the common low-slice coercion shape directly; and
5. reprocess replacements under deterministic bounded fuel, with a growth
   guard that rejects expansions whose cost is not justified.

Only after corpus telemetry warrants it should the tranche add guarded
low-prefix propagation through add/multiply or more expansive ITE/bitwise
rules. Tests must include exhaustive small widths, evaluator equivalence,
randomized and Z3 differential checks, rewrite-manifest IDs, deterministic
fuel termination, AIG/CNF size deltas, and original-model replay.

Exit: residual targeted opportunities and total AIG/CNF construction fall on
the real tier; total cold time is non-worse in aggregate; all validity gates
remain green. The measured bounded subset becomes GQ2's cheap tier rather than
making full preprocessing always-on.

Implementation checkpoint (2026-07-14): ADR-0142 and
`axeyum-rewrite-default-v2` land items 1--5 with stable rule IDs, fixed
fresh-node bounds, eight-step local replacement fuel, exhaustive small-width
evaluation, seeded wider evaluation, and Z3 SAT/UNSAT differential replay.
Real-corpus checkpoint: canonical v2 removes 1,315/1,435 representative GQ3
opportunities, lowers term-bit materialization by 57% on that tier and 72% on
the full tier, and cuts measured Axeyum total by 48.5%/57.1% with every validity
gate green. It does not reduce full-tier AIG/CNF size (nodes +3.0%, clauses
+1.2%), and the ratio still includes the always-on demand diagnostic. GQ3 is a
validated client time/term-DAG win but remains WIP on its circuit-size and
corrected-production-timing exit.

### G4 — demand-driven cold bit lowering (GQ4)

Record the lowering and model-projection contract in an ADR. Implement the
narrowest exact demand system first:

- memoize partial term bits (for example, one optional literal per bit) and
  union repeated/disjoint demands deterministically;
- map extract demands into source ranges;
- split concat demands across operands;
- map extension demands to source bits, constants, or the sign bit;
- propagate identical bit ranges through pointwise bitwise operations and BV
  ITE, always demanding the ITE condition; and
- conservatively request all inputs for unsupported demand-aware operators.

Then, only when measured, add low-prefix add/subtract, constant shift/rotate,
and low-prefix multiply demand rules. Comparisons and variable shifts may remain
conservative initially.

Omitted symbol bits need an explicit deterministic model-projection/defaulting
rule, and the lifted model must still replay every untouched source assertion.
Tests include exhaustive full-vs-demand lowering equivalence, SAT/UNSAT
differential checks, AIG evaluation, disjoint shared-subterm demands, wide
8-of-64 structural gates, and SAT model replay.

Exit: demanded/available and actually-lowered bit ratios, AIG nodes, CNF
variables/clauses, bit-blast time, CNF time, and end-to-end ratio all improve on
the real tier without a validity regression.

Current ranking: after canonicalization the full tier demands 98.16% of term
bits and 91.51% of symbol bits under the conservative analysis. Broad partial
lowering therefore follows measured GQ5 CNF work unless family-specific
evidence identifies a substantially narrower cone.

### G5 — measured AIG/CNF engineering (GQ5)

Use the G2 counters to choose one isolated change at a time:

- if unique-table lookup dominates, replace the `BTreeMap` with a deterministic
  fixed-hash/open-addressing table while preserving stable construction and
  output order;
- if allocation dominates, pre-size measured vectors/maps and eliminate
  repeated temporary allocations;
- if clause sorting/dedup dominates, adopt a deterministic cheaper dedup path;
- if a gate family dominates, improve only that recognizer/encoding and preserve
  sharing guards; and
- consider word-operator provenance or direct encodings only as a larger ADR-led
  change after the AIG-level options are measured.

Each commit must preserve AIG evaluation, CNF assignment replay, model lift, and
the proof-check route. A smaller CNF is insufficient without an end-to-end real
corpus win.

Corrected artifact-v27 production attribution after ADR-0150 is 1.80 seconds
word policy, 5.88 seconds bit blast, 5.18 seconds CNF, and 3.50 seconds SAT.
Within CNF, gate/root/planning/allocation cost 2.40/1.08/1.20/0.066 seconds.
Bit blast is now the largest measured stage; re-attribute residual operator
lowering and AIG request/hash/allocation work by family before selecting the
next exact GQ3/GQ5 slice. The first audit result is proposed ADR-0151: replace
23,029,676 ordered term-bit lookup insertions with dense per-term ranges into
the existing authoritative binding vector. Its BV, interpolation, and SAT-BV
suites plus strict Clippy pass. ADR-0151 is accepted after representative
total/bit blast improve 5.59%/15.51% and full total/bit blast improve
5.71%/16.05%, reaching 15.60 seconds / 1.99x Z3 with identical structure and
replay. CNF and bit blast are now 5.18/4.94 seconds; audit the remaining dense-ID
memo and shared normalization before another bounded slice. That audit selects
proposed ADR-0152: use ADR-0151 range presence as the completion memo and remove
the ordered map's duplicate ownership of 23,029,676 literals across 982,044
terms, while leaving operand cloning unchanged. Its 21 BV, 10 interpolation,
and 31 SAT-BV tests plus strict Clippy pass; representative/full timing gates
remain. SAT and broad GQ4 remain gated by measured opportunity.

### G6 — SAT work remains conditional (GQ6)

Do not tune the SAT core while construction owns most wall time. Re-evaluate
after G3--G5. If SAT becomes dominant, run the exact same emitted CNF through
BatSat, the proof-producing core, and pinned reference solvers; partition clause
ingestion from search; then select restart, phase, activity, inprocessing, or
XOR work from that evidence. Deterministic resource limits, assignment replay,
and UNSAT proof recheck remain mandatory.

### G7 — capture and implement the real warm shape (GQ7)

The deduplicated cold corpus cannot validate incremental reuse because it loses
query frequency, order, path-prefix relationships, push/pop scopes, and model
choice. Add an access-controlled ordered trace format carrying stable query or
constraint IDs, path/worker identity, scope operations, occurrence order,
expected verdict, and timing metadata without duplicating all term bytes.

On the Glaurung side, introduce a path-aware incremental solver seam with a
persistent arena/translator and one `IncrementalBvSolver` per worker/path state.
Map explorer fork/merge behavior to push/assert/check/pop, assert only the
delta, and preserve retained AIG/CNF/learned state. On the Axeyum side, make
configured assertion process only newly added terms and affected summaries.

Exit: same-stream real-driver shadow diff reports verdict, unknown/error,
model-divergence, p50/p95 per-check time, total solver time, memory, and warm
break-even depth. Finding comparison uses the controlled concretization policy.
The synthetic 7.5x warm result is only a hypothesis until this gate passes.

### G8 — reuse only what the trace justifies (GQ8)

Measure exact duplicates, prefix extensions, and repeated subformulas in the
ordered trace. Prefer retained warm state for prefixes. Add an exact-verdict
cache only if duplicate frequency justifies it, keyed by canonical formula,
solver/config semantics, scope identity, and artifact/version identity.
Cached SAT and UNSAT artifacts must still replay; cache bounds and invalidation
are deterministic and explicit. A prefix is never treated as an identical
query.

### G9 — publish the policy (GQ9)

After raw/canonical/configured/warm data exists, expose a telemetry-visible
policy that selects among them using formula shape, cold/warm context, retained
state, and measured cost. Fit on the representative corpus, validate on a held
out/full tier and ordered traces, and retain explicit fixed-policy overrides.
Document that full `assert_configured` preprocessing is currently a cold loss
and a warm candidate. Do not change the default until auto is non-worse at all
validity gates.

## Milestones and stop/go gates

| Milestone | Roadmap coverage | Stop/go decision |
|---|---|---|
| M0 byte-complete capture | GQ1, GQ10 | **Axeyum side done:** representative and well-typed full manifests validate; producer still must prevent 2,225 malformed dumps and atomically deduplicate |
| M1 raw v27 baseline | GQ1, GQ10 | **Done:** five representative raw/canonical production trials plus one full trial each pass every gate; repeat full for accepted changes |
| M2 diagnostic attribution | GQ1, GQ3--GQ5 | **Done for current boundary:** ADR-0143 removes the 29.57 s observational pass from production and marks diagnostic completeness explicitly |
| M3 cheap exact rewriting | GQ2, GQ3 | **Measured production win:** canonical cuts Axeyum total 17.4% representative median / 13.3% full and bit blast 37.3% / 44.4%; circuit-size exit remains |
| M4 demand lowering | GQ4 | Continue only with replay-safe real AIG/CNF and wall-time reductions |
| M5 AIG/CNF optimization | GQ5 | **Two wins accepted:** ADR-0144 cuts full canonical CNF 18.5% / total 8.8%; ADR-0145 then cuts CNF 5.6% / gate emission 10.5% / total 2.7%, all with identical content; continue only measured root/planning slices |
| M6 SAT re-attribution | GQ6 | Start SAT work only if search becomes material/dominant |
| M7 ordered warm trace | GQ7, GQ8 | Decide incremental API shape and whether a cache is worthwhile |
| M8 Glaurung warm integration | GQ7 | Require real same-stream functionality and performance, not the synthetic result |
| M9 auto policy and regression lane | GQ8--GQ10 | Change defaults only after representative/full/trace validation |

## Immediate next actions

1. Profile the residual root-emission allocation/copy path and CNF planning on
   `register-slice` and `slice-partial`. After ADR-0145, gate emission is 3.19
   s, root emission 1.39 s, and planning 1.21 s; gate work is no longer the
   automatic first target. ADR-0146's reusable root scratch regresses
   representative total/CNF 1.1%/4.9% and is restored/deferred without a full
   run.
2. Attribute the 1.21-second planning path by reachability/use-count, gate
   detection, private-tree collection, and direct-root work without repeating
   the always-on observational-profiler mistake. ADR-0147 removes private-tree
   planning's full-node reverse-iteration copy and improves planning 2.5%, but
   regresses total/CNF 0.5%/3.6%; it is restored/deferred without a full run.
   Deprioritize planning micro-work and re-attribute shared gate/root clause
   normalization, formula growth, and index rehash next. ADR-0148 is the first
   candidate: a capped no-pass variable/root hint pre-sizes formula headers and
   the exact-dedup index, but regresses representative total/CNF 2.5%/10.0%
   because gate lookup rises 23.5%. It is restored/deferred. Any capacity
   follow-up must isolate formula-header storage and leave index growth intact.
   ADR-0149 performs that isolation, but still regresses representative CNF
   median/mean 0.83%/0.67%; its 0.16% total-median improvement is contradicted
   by a 0.07% mean regression and higher variance. It is restored/deferred
   without a full run. Close capacity micro-work and attribute shared clause
   normalization, fingerprinting, exact duplicate checks, and insertion before
   choosing a larger GQ5 slice. That audit selects ADR-0150: the accepted
   fingerprint map stores a heap-backed index vector and performs separate
   lookup/insertion probes for the common unique-clause case. Retain one inline
   primary formula index and allocate a secondary bucket only for genuine
   fingerprint collisions; preserve exact equality, formula ownership, clause
   order, and replay. Forced-collision tests and the usual representative/full
   gates remain mandatory. The candidate implementation passes all 283 CNF
   tests, 31 SAT-BV tests, strict Clippy, and forced-collision coverage. It is
   accepted after representative total/CNF improve 13.0%/29.0% and full
   total/CNF improve 11.5%/28.4%, with identical content and replay. Re-attribute
   the now-largest bit-blast stage before selecting another exact slice.
3. Keep the next exact word tranche around affine BV add/sub constant-chain
   normalization and cheap duplicate-root handling behind evidence that it
   reduces downstream AIG/CNF for the
   `slice-partial` hotspot; require proof/model replay and real total-time wins.
4. Re-attribute CNF after steps 1--3, then choose only the measured GQ5
   subphase. Keep SAT-core work gated and broad GQ4 behind its small measured
   post-canonical demand residual unless family data reverses the ranking.
   After ADR-0150 makes bit blast largest, ADR-0151 is the next isolated
   ownership candidate: dense `TermId` plus contiguous bit bindings can replace
   the redundant ordered term-bit lookup map without changing lookup, order,
   incremental growth, or replay. It is accepted after the full client gate
   cuts total 5.71% and bit blast 16.05% with identical AIG/CNF structure.
   ADR-0152 then isolates the remaining memo ownership: range presence replaces
   ordered completion lookup, and child bits are reconstructed from the same
   authoritative bindings without changing operand cloning or AIG algorithms.
5. On the Glaurung side, fix explicit width coercion plus strict dump validation
   and cross-process dedup/conflict handling. Define the ordered warm-trace and
   controlled-concretization schema before GQ7/GQ8 cache or auto-policy work.

All heavy Rust validation and benchmark commands remain subject to the local
4 GiB virtual-memory cap and should use serial execution where parallel test
residency would exceed it.
