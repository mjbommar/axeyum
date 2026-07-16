# Glaurung QF_BV execution plan

Status: active measured execution plan
Last updated: 2026-07-16

## Outcome

The shortest evidence-backed path to useful Glaurung functionality is:

1. retain ADR-0187's corrected, zero-exclusion five-driver artifact-v31
   capture and exact sharded full gate;
2. reproduce the current **raw one-shot** integration before comparing any
   preprocessing policy (complete for the representative and well-typed full
   tiers);
3. remove the always-on observational bit-demand pass from production timing;
4. retain accepted exact extract/coercion/additive cancellation as the cheap
   cold policy, expose it to embedders, and extend it only from a new measured
   residual;
5. optimize AIG/CNF construction only where corrected counters attribute cost;
6. capture an ordered extending-path trace and validate warm push/pop reuse in
   the Glaurung explorer; and
7. derive caching and an automatic preprocessing policy from the cold corpus
   and warm trace rather than from synthetic formulas.

The byte-complete 2026-07-14 capture and artifact-v27 results superseded the
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
ADR-0153's modular add-chain folding reaches 14.11 seconds / 1.85x Z3.
ADR-0155 then cancels the remaining constant across equality: five clean full
processes improve mean time 59.7% to 5.625 seconds and ratio 60.1% to 0.730x
Z3, while new AIG nodes and clauses fall 76.7%/75.4%. The cold real-lifter gap
is closed at the one-shot canonical-v4 benchmark boundary. The native driver
still needs an exact entry-path attribution, and the newest client profile
re-prioritizes production GQ4 demand slicing plus rewrite-impact telemetry.
ADR-0156 adds the missing matching solver surface: one batch admission
shares the canonicalizer memo across all roots while retaining originals for
replay. Its representative fresh-incremental gate is replay-clean but 18.8%
slower than one-shot and emits 80.9% more clauses with the same AIG, so the API
remains explicit plumbing and its cold Glaurung recommendation is deferred.
ADR-0187 now supersedes that old corpus identity. Glaurung `1b32cb9` plus the
strict builder `3b64aaf` produce a zero-exclusion five-driver tier with 30,628
distinct scripts, including 7,953 scripts with wide roots. Eight clean
Axeyum `f7f174c5` shard processes decide and agree on every script: raw is
30.803 seconds / 0.446x Z3 and canonical v4 is 18.471 seconds / 0.269x Z3.
The four shards are one exact full-corpus process envelope, not repetitions.
ADR-0188 repeats the complete composite and installs guarded variance alarms.

This note expands `PLAN.md` items GQ1--GQ10 into an executable sequence. It does
not authorize changes to the Glaurung repository; producer-side and explorer
tasks below identify the required cross-project handoff.

## Evidence inspected

### Producer capture

The accepted corrected source is Glaurung producer `1b32cb9` plus strict
builder `3b64aaf` on `sec/axeyum-backend`. Its access-controlled five-driver
pack contains 30,678 observations, 30,628 unique hash-named scripts, 50 exact
duplicate observations, zero verdict conflicts, and zero exclusions. The
representative distribution is:

| Family | Queries |
|---|---:|
| `register-slice` | 52 |
| `slice-partial` | 54 |
| `arithmetic` | 36 |
| `comparison` | 12 |
| `mixed` | 7 |
| `trivial` | 1 |
| **Total** | **162 (88 SAT / 74 UNSAT)** |

The corrected capture audit resolves the original handoff questions:

- the original three-driver corrected recapture has 5,102 distinct scripts and
  all 218,434 current roots are width one, so the 2,225 stale malformed hashes
  cannot be mapped to corrected current byte identities;
- widening to SurfacePen and NETwtw10 adds 25,526 scripts, including 7,953
  scripts with wide roots and 13,015 width-64 assertions;
- separate self-contained 162-query representative and 30,628-query full roots
  pass strict exact membership and ordinary Axeyum manifest ingestion; and
- the full tier is a byte-pinned exact union of four deterministic physical
  process shards because the monolithic process exceeds 4 GiB cumulatively.

Glaurung now publishes query bytes atomically, detects cross-process verdict
conflicts, and validates exact file inventory/content before emitting either
tier. An exclusion list is not part of the accepted corrected contract.

### Current integration mode

Glaurung's one-shot Axeyum backend creates a fresh `IncrementalBvSolver` for
each check and calls raw `assert`. Its own measurements say
`assert_configured` is about 1.3--2x slower in that cold mode. The producer's
artifact-v17 command likewise used neither `--rewrite default` nor
`--preprocess`.

Axeyum's original `bench-glaurung-qfbv` recipe passed `--preprocess` and did
not reproduce either the reported profile or Glaurung's current API behavior.
That mismatch is repaired: current recipes preserve three separately named
policies, and the unsuffixed compatibility route remains the raw control:

| Policy | Harness flags | Purpose |
|---|---|---|
| `raw` | rewrite off, preprocess off | Current Glaurung one-shot and artifact-v17 reproduction; primary cold control |
| `canonical` | `--rewrite default`, preprocess off | Accepted cheap exact v4 policy; not yet wired into Glaurung's raw one-shot path |
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

1. Retain the corrected representative/full `.smt2` roots in their
   access-controlled stable location.
2. Preserve strict `capture-index-v1.json` with ordered relative path, trusted
   expected verdict, family, and tier membership only. The producer must not
   supply content hashes.
3. Keep cross-process capture deduplication explicit. Reject duplicate hashes
   with conflicting verdicts; report index rows, unique hashes, SAT, UNSAT,
   undecided omissions, and exclusions separately.
4. Require zero exclusions; an ill-sorted or missing indexed script fails the
   corpus build rather than entering a side list.
5. Keep representative, full, and physical shard roots self-contained with
   exact directory membership and a byte-pinned shard union.
6. Run `--generate-corpus-manifest`, then ordinary manifest ingestion, before
   timing. Record source driver hashes, Glaurung revision, toolchain, capture
   command, and an archive digest for an access-controlled pack.

Checkpoint: **complete in ADR-0187.** The 162-query representative and
30,628-query full tier have byte-complete manifests, exact row/unique/conflict
arithmetic, zero exclusions, and no query normalization during handoff. The
old 2,225 hashes remain historical producer-invalid identities rather than a
recovery denominator.

### G1 — establish the cold truth (GQ1 + GQ10)

Preparation landed 2026-07-14: explicit raw, canonical-only, and configured
recipes now cover single, repeated, and proof-companion runs. Raw is the
unsuffixed current-integration control; policy-specific output defaults and
dry-run regression tests prevent accidental series mixing.

1. Use the landed policy recipes without editing their flags.
2. Run raw first in a fresh process on every deterministic full shard, plus its
   separate proof-check companion when UNSAT proof assurance is under test.
3. Run the same complete shard set for canonical-only and configured policies;
   repeat complete sets rather than treating child shards as repetitions.
4. Report aggregate and per-family ratios, p50/p95, run-to-run CV, formula/AIG/
   CNF sizes, stage shares, and raw Z3 control drift.
5. Keep the access-controlled full tier scheduled through the exact shard
   aggregator and the 162-query representative in the regular semantic lane.

ADR-0187 closes the corrected single-composite checkpoint: clean raw and
canonical v4 shard sets cover 30,628/30,628 with zero semantic/replay failures
at 0.446x and 0.269x Z3. The corrected 162-query tier is now the pinned regular
semantic gate. ADR-0187 left a second complete clean shard set as the required
boundary before run-to-run variance or cross-commit timing alarms.
ADR-0188 supplies that second set. Raw Axeyum/Z3/ratio CV is
0.458%/0.558%/0.100%; canonical is 0.787%/0.150%/0.937%. Corrected-corpus
cross-commit comparison now applies explicit 3% Axeyum, 3% ratio, 5% RSS, and
2% Z3-drift alarms after exact identity validation.

Every row requires 100% decided, zero errors, zero SAT/UNSAT disagreement, and
zero replay/proof failures. Regression thresholds are set only after stable
same-environment variance exists. This closes the measurement part of GQ1 and
the corpus-adoption foundation of GQ10.

Measured checkpoint (artifact v27): five representative raw/canonical trials
all pass the validity gates. Median aggregate ratios are 1.65x and 1.37x;
canonical's Axeyum total is 17.4% below raw. Raw and canonical proof companions
from the same semantic tranche each check all 64 UNSAT proofs. One scheduled
full trial per raw/canonical policy decides all 13,462 well-typed rows and
records 3.17x versus 2.71x; canonical is 13.3% faster.

Regular-lane checkpoint (2026-07-14): `just check` now invokes an
availability-aware real-capture gate. It uses an explicit representative path
or the pinned NAS pack, reports a visible skip only when neither exists, and
fails if explicitly configured data is incomplete. It runs both the raw
current-integration and canonical candidate under manifest, in-process Z3,
deterministic-resource, 100%-decided, zero-error/disagreement/replay gates.
Artifacts stay under ignored `target/` state because the regular lane permits a
dirty worktree and makes no release-performance claim. The first real run
decides and agrees on all 128 rows for both policies; its diagnostic totals are
0.184/0.149 seconds (1.23x) raw and 0.157/0.150 seconds (1.04x) canonical.

Scheduled variance checkpoint (2026-07-14): five independent clean-revision
canonical full-tier processes all decide and agree on 13,462/13,462 rows. Mean
Axeyum/Z3/ratio are 15.644/7.738 seconds/2.0217x with CV
0.514%/0.310%/0.510%; every attributed stage is below 1% CV. The provisional
same-environment comparator alarms are 3% maximum ratio regression, 3% maximum
Axeyum-total regression, and 2% maximum absolute Z3 drift. The guarded recipe
applies them, while retaining exact corpus/config/environment/backend identity
and distinct clean source revisions.

Native-entry checkpoint (ADR-0160, 2026-07-15): Axeyum now exposes an opt-in
incremental phase snapshot with no clock/counter overhead in ordinary
constructors. Glaurung records the unchanged raw fresh-arena/fresh-solver path
as exact-query, process-ordered JSONL and separately times arena creation,
translation/interning, solver creation, lower/encode, SAT, model lift/replay,
and client model extraction. The fail-closed summarizer preserves duplicate
occurrences and can reconcile overlapping hashes/outcomes/families with the
capture manifest.

The first exploratory Z3-authoritative release stream executes 13,126 identical
queries with 100% decisions and zero disagreements/unknowns. Its 17.429 seconds
of native phase time is 42.81% bit blast, 37.58% incremental CNF, 7.23% SAT,
and 4.53% translation. There are 7,065 unique hashes and 6,061 duplicate
occurrences; 52 unique hashes overlap the pinned representative manifest with
no verdict conflict. An unprofiled same-stream shadow control measures ordinary
Axeyum/Z3 wrapper time at 18.826/6.478 seconds (2.906x). This is a
single-driver exploratory checkpoint, not the clean multi-driver publication
gate. It selects incremental gate-fusion attribution ahead of SAT tuning and
makes ordered GQ7/GQ8 capture urgent.

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
separately named diagnostic artifact. This exit is complete for the current
boundary; add finer counters only when a fresh post-v4 residual justifies them.

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

Accepted completion checkpoint: ADR-0153 adds exact scalar/wide modular
constant-chain folding. ADR-0155 then adds only exact constant cancellation
across equality and advances the default identity to v4. Five clean full v4
processes decide and replay every query, improve mean total 13.946 → 5.625
seconds, and improve ratio 1.829x → 0.730x Z3. Output DAG nodes fall 45.4%,
new AIG nodes 76.7%, and clauses 75.4%; both excess-owning families become
faster than Z3. GQ3 is complete for the measured workload. Broader affine
normalization remains deferred unless a fresh v4 residual reopens it.

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

Historical aggregate ranking: before canonical v4, the conservative full-tier
diagnostic demanded 98.16% of term bits and 91.51% of symbol bits. That result
does not veto the production pass: it mixes families, counts narrow
intermediates alongside wide discarded register inputs, and predates the new
client profile reporting bit blast at about 45% and register-slice shapes at
about 88% of the real stream. GQ4 is now the first implementation priority.

Implement it as an additive cold lowering route first. Roots demand their full
Boolean result. A deterministic worklist unions per-term bit ranges and exact
rules propagate through extract, concat, extensions, pointwise operators, and
ITE; unsupported operators request the conservative full operand. Store
partial results as per-term optional literals so disjoint later demands extend
the memo without rebuilding already-materialized bits. Omitted symbol bits use
a documented deterministic value during lift, and a candidate is accepted only
after the resulting full-width model evaluates every original assertion.

Gate the first slice on `register-slice` separately: demanded/lowered source
bits, AIG requests/new nodes, clauses, bit-blast/CNF/SAT/end-to-end time, and Z3
ratio must all be reported for that family and the full corpus. The existing
observational `structural_bit_demand` pass is scaffolding and an oracle for
counters; calling its `BTreeSet` walk before ordinary full lowering is not the
production implementation.

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
and 31 SAT-BV tests plus strict Clippy pass. Five representative processes
preserve structure, but bit blast improves only 0.57% while total mean/CNF p50
regress 0.38%/0.88%. It is restored/deferred without a full run. Close memo
micro-work and advance the data-availability-aware GQ10 representative gate.
The subsequent family attribution selects ADR-0153: `slice-partial`
is only 1,584/13,462 queries but owns 39.7% of Axeyum time, runs 3.82x behind
Z3, and creates 16.91 million AIG nodes plus 22.87 million clauses. Its source
scripts contain 377,320 `bvadd` occurrences, while the current AC canonicalizer
sorts mixed symbol/constant chains without combining their constant leaves.
Exact modular add-chain folding is accepted: full total improves 9.80% to
14.11 seconds / 1.85x Z3, clauses fall 17.23%, and `slice-partial` improves
24.4% with every semantic gate green. SAT and broad GQ4 remain gated by fresh
post-v3 opportunity. Accepted ADR-0155 supplies that next attribution and
eliminates the remaining constant adder across equality. Full mean total falls
to 5.625 seconds / 0.730x Z3, CNF to 1.396 seconds, bit blast to 1.310 seconds,
and SAT to 0.929 seconds. Direct construction and SAT work are no longer the
Glaurung cold blocker; the bounded word pass at 1.832 seconds is now the largest
stage, and any further cold change requires a fresh post-v4 profile.

The fresh-client experiment adds a distinct GQ5 boundary. ADR-0156's batch API
is semantically clean but misses its cold performance gate. In five interleaved
representative comparisons, fresh incremental canonical assertion takes
0.060969 seconds versus one-shot canonical `sat-bv` at 0.051301 seconds
(+18.8%; `register-slice` +26.4%). Both paths construct exactly the same AIG,
but incremental CNF emits 170,102 clauses per trial versus 94,043 (+80.9%).
The incremental encoder already performs lazy polarity propagation; its
documented missing one-shot gate fusion is the measured delta to investigate.
Keep ADR-0156's API as plumbing, but do not recommend it for cold Glaurung
until this gap closes or a purpose-built one-shot client API supplies the same
original-root replay contract.

ADR-0160 closes the missing native attribution boundary. All 52 exact hashes
shared by the ordered Glaurung stream and the current standalone raw artifact
preserve AIG size. Weighted across 154 occurrences, both build 494,150 AIG
nodes while incremental Glaurung emits 875,083 clauses versus one-shot's
506,480 (+72.78%). Glaurung's hash-consed `ExprId` sharing therefore survives
translation and lowering. Full native
attribution places SAT at only 7.23%. The next GQ5 implementation slice is
therefore one measured incremental gate-fusion pattern with unchanged retained
selector/scope semantics, AIG, model replay, and end-to-end native outcome. Do
not reopen broad sharing work or GQ6 from aggregate intuition.

### G6 — SAT work remains conditional (GQ6)

Do not tune the SAT core while construction owns most wall time. Re-evaluate
after G3--G5. If SAT becomes dominant, run the exact same emitted CNF through
BatSat, the proof-producing core, and pinned reference solvers; partition clause
ingestion from search; then select restart, phase, activity, inprocessing, or
XOR work from that evidence. Deterministic resource limits, assignment replay,
and UNSAT proof recheck remain mandatory.

### G7 — capture and implement the real warm shape (GQ7)

The concrete producer/consumer event contract is
[Glaurung ordered warm-trace v1](glaurung-ordered-trace-v1.md). It is derived
from the reviewed `GLAURUNG_DUMP_QUERIES` capture seam and keeps content-addressed
query bytes while restoring occurrences, scopes, path/worker lineage,
unknown/error events, and model choices.

ADR-0166--0170 implement and validate this boundary across a clean three-driver
tier. ADR-0171 then carries explicit per-path ownership through Glaurung's live
translation seam: three repeated rounds reach 0.746x same-stream Z3 versus
snapshot's 2.093x with every check agreed, but lineage raises RSS. Glaurung
`49f1fe2` adds atomic live-path/assertion ceilings and visible one-shot fallback.
ADR-0172 adds opt-in exact-query/path phase records without taxing ordinary
solvers; 6,986 decided records attribute live lineage to CNF 43.78%, bit blast
22.86%, and SAT 17.45%. ADR-0173 adds exact gate/root deltas: definitions own
71.75% of clauses and AND-tree shapes own 53.89% of halves, while existing root
fusion is saturated and duplicate/tautology opportunities are zero. Profiled
time remains diagnostic, not a performance bar. ADR-0174 then defers the
selected internal AND candidate: later helper reuse grows retained Dptf clauses
17.62% and regresses unprofiled Axeyum time 3.65% despite 83,544 clauses avoided
at application time. ADR-0175 then accepts exact v4 AIG/lowering attribution
and a deterministic open-addressed unique table. Three repeated pairs per
driver preserve all 20,958 decisions per policy and improve weighted Axeyum
time 7.66% / actual-client ratio 0.742x→0.680x with flat memory. The accepted
v4 profile moves bit blast to 18.21% behind CNF's 46.55%. ADR-0176 calibrates
the existing atomic fallback on that baseline: 9 live paths and 128 assertions
preserve weighted Axeyum time while reducing RSS on both 11-path drivers.
Glaurung `1f24d5d` makes those limits visible bounded defaults only when lineage
reuse is explicitly selected. ADR-0177 then supersedes only the assertion
ceiling after held-out SurfacePen reaches 479 roots: 512 matches unbounded warm
traffic and improves Axeyum 34.9% over 128 without an RSS increase. A bounded
23,797-check NETwtw10 run has zero assertion fallback at 512 and retains nine
live sessions as the measured memory/time tradeoff. Glaurung `90df708` now uses
9/512 inside explicit lineage mode. ADR-0178 accepts the repeated held-out gate:
SurfacePen runs identical 2,551-check streams at 0.243x Z3 and 0.34% Axeyum CV;
fixed-budget NETwtw10 runs identical 28,356-check streams at 0.360x Z3 and
0.44% Axeyum CV, with exact structural/fallback identity and 257,736 KiB median
RSS. Glaurung `eb938ae` records wall-cutoff runs as diagnostic only.
ADR-0179 makes that tier executable in Glaurung `89aea59`: source/environment/
driver/policy/work/finding/resource identity, hard memory limiting, atomic
publication, exact validation, and homogeneous artifact comparison are
fail-closed. Focused tests and a real SurfacePen artifact smoke pass.
ADR-0180 adds explicit post-identity alarms in Glaurung `a0e5f9f`: 3% Axeyum,
3% normalized ratio, 5% median RSS, and 2% absolute Z3 drift. Four focused tests
and artifact self-comparison pass; a clean full baseline remains to publish.

The deduplicated cold corpus cannot validate incremental reuse because it loses
query frequency, order, path-prefix relationships, push/pop scopes, and model
choice. Add an access-controlled ordered trace format carrying stable query or
constraint IDs, path/worker identity, scope operations, occurrence order,
expected verdict, and timing metadata without duplicating all term bytes.

On the Glaurung side, the path-aware incremental solver seam now retains a
persistent arena/translator and one `IncrementalBvSolver` per worker/path state.
Explorer fork/terminal/restart behavior maps to isolated ownership; later
checks assert only the delta and preserve retained AIG/CNF/learned state. The
first GQ7 memory-limit calibration, held-out assertion correction, repeated
variance, and executable gate are complete. The remaining admission work is a
clean baseline with alarms, newly available driver families, and a topology/
cost policy, not basic ownership plumbing or another threshold sweep.

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

## Post-capture ten-item work order

The latest Glaurung feedback is integrated as the following concrete order.
Consumer-reported percentages and ratios remain reproduction targets until a
clean artifact pins the exact Glaurung/Axeyum revisions and policy.

| Priority | Requirement | Next executable gate |
|---|---|---|
| 1 | Land GQ4 demand-driven slicing | **Deferred after both real gates failed.** V1 regresses about 3x; v2 admits little useful gate work and is also slower. Reopen only with a gate-cone estimator or a qualitatively different specialization. |
| 2 | Make rewrite effort fire-rate driven | **Done for the current structural tranche (ADR-0159).** Clean repeated ablations show `extract_extend` saves lowering materialization/time, but the four measured rules remove zero AIG nodes and zero clauses. |
| 3 | Close native-driver versus bench delta | **Done for bounded native lineage timing/phase/gate/AIG/admission identity (ADR-0171--0179).** Original lineage is 0.680x Z3; held-out 9/512 is 0.243x/0.360x with exact work identity and a fail-closed runner. Profiled/unprofiled/cold bars remain separately named. |
| 4 | Strengthen AIG sharing | **First construction-cost tranche accepted (ADR-0175).** Client sharing already survived; exact v4 telemetry selected low-hit ordered unique-table probes. Deterministic open addressing preserves structure and cuts three-driver Axeyum time 7.66%. Reopen literal ownership/two-level rewriting only from a fresh causal gate. |
| 5 | Reduce CNF for measured gates | **Current tranche closed/deferred (ADR-0172--0175).** Root fusion/dedup are exhausted; internal AND flattening grows retained Dptf clauses/time. CNF is again dominant after the AIG win, but reopen only with future-use evidence or clause replacement. |
| 6 | Make warm entry delta-only | **Bounded admission repeated, executable, and alarmed (ADR-0171--0180).** Nine paths preserve the RSS/time tradeoff and 512 assertions cover every stream. Exact identity and alarms are enforced. Publish clean baseline before automatic selection. |
| 7 | Reuse duplicates and prefixes soundly | Measure exact duplicates/prefixes first; cache exact queries with replay, but reuse retained state rather than verdicts for strict prefixes. |
| 8 | Add the register-slice fast path | Treat this as the first specialized GQ4 policy only if the generic exact range propagation leaves measurable avoidable work. |
| 9 | Queue SAT tuning | **Material but behind CNF:** accepted-table lineage SAT is 18.48% versus CNF's 46.55%. Compare identical CNF only after the next measured CNF tranche. |
| 10 | Expand and trend real capture | **Corrected widening accepted (ADR-0187).** Five drivers, 30,628 distinct scripts, 7,953 wide-root scripts, zero exclusions, and an exact clean sharded baseline are complete. Repeat the whole composite for variance; retain cold/ordered/profile tiers separately. |

## Milestones and stop/go gates

| Milestone | Roadmap coverage | Stop/go decision |
|---|---|---|
| M0 byte-complete capture | GQ1, GQ10 | **Done in ADR-0187:** corrected atomic five-driver capture has 162 representative / 30,628 full scripts, 50 duplicate observations, zero conflicts, zero exclusions, and exact manifests/shard union |
| M1 corrected cold baseline | GQ1, GQ10 | **Done in ADR-0187/0188:** repeated full composites keep all 30,628 decisions/replays green, measure raw/canonical ratio CV at 0.100%/0.937%, and enable guarded 3%/3%/5% + 2% comparisons |
| M2 diagnostic attribution | GQ1, GQ3--GQ5 | **Done for bounded cold/native phase/gate/AIG bars:** ADR-0160 covers one-shot; ADR-0172/0173 validate phase/CNF records; ADR-0174 separates immediate from retained CNF effects; ADR-0175 validates all 6,986 v4 AIG/memo/copy records |
| M3 cheap exact rewriting | GQ2, GQ3 | **Done for the measured current shapes:** canonical v2 cuts corrected full total 13.3%, ADR-0153 cuts another 9.80%, accepted ADR-0155 reaches 5.625 s / 0.730x Z3, and ADR-0159 causally closes the current extract tranche without finding another AIG/CNF lever |
| M4 demand lowering | GQ4 | **Deferred:** both v1 and admission-controlled v2 fail the representative performance gate while preserving correctness; keep explicit/off and reopen only from a different gate-cone hypothesis |
| M5 AIG/CNF optimization | GQ5 | **First native AIG tranche accepted:** ADR-0175 replaces the ordered unique table and improves the repeated actual-client ratio 0.742x→0.680x with unchanged structure. CNF candidate remains deferred; reopen only from new causal evidence |
| M6 SAT re-attribution | GQ6 | **Done for bounded accepted-table lineage:** SAT is 18.48% weighted and remains behind CNF at 46.55% |
| M7 ordered warm trace | GQ7, GQ8 | **Done for clean three-driver controls (ADR-0166--0170):** assertions, lineage/scopes/choices, backend timing, cold/snapshot/lineage controls, and memory validate |
| M8 Glaurung warm integration | GQ7 | **Bounded admission repeated/executable/alarmed (ADR-0171--0180):** original lineage is 0.680x Z3; held-out 9/512 identity and alarms are accepted. Publish clean baseline before auto policy |
| M9 auto policy and regression lane | GQ8--GQ10 | **GQ9/GQ10 done for current families:** adaptive warm admission is the downstream default; the corrected regular pin plus repeated full composites have executable identity and timing alarms. GQ8 cache semantics remain separate |

## Immediate next actions

1. Specify GQ8's deterministic bounded content/config/scope/lineage identity,
   eviction, invalidation, and mandatory model/proof replay contract before
   implementing verdict reuse.
2. Keep the corrected 162-query regular semantic gate and exact full shard
   union pinned; reject exclusions, dirty source, incomplete manifests, or a
   raised memory envelope as substitutes for coverage.
3. Keep ADR-0157/0158 explicit and off. ADR-0159 closes the current structural
   rewrite tranche: `extract_extend` is a real lowering win, but none of the
   four ablated rules changes AIG/CNF. Reopen GQ3/GQ4 only for a specific new
   downstream gate-cone hypothesis.
4. Reopen GQ5 literal-copy ownership only with a fresh isolated design and
   native gate. CNF is again dominant; internal flattening still requires
   future-use evidence or clause replacement.
5. Keep complete assertion/symbol capture and separate backend timing mandatory
   in every new ordered artifact; merge per-process traces atomically before
   GQ7/GQ8 cache or auto-policy work.
6. Run every accepted cold candidate through ADR-0188's guarded repeated sharded full
   comparisons. A threshold violation is a regression alarm to investigate,
   not permission to ignore raw controls or semantic gates.

All heavy Rust validation and benchmark commands remain subject to the local
4 GiB virtual-memory cap and should use serial execution where parallel test
residency would exceed it.
