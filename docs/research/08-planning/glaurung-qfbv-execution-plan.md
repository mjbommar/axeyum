# Glaurung QF_BV execution plan

Status: active planning baseline
Last updated: 2026-07-14

## Outcome

The shortest evidence-backed path to useful Glaurung functionality is:

1. repair and ingest the real capture through Axeyum's artifact-v22 contract;
2. reproduce the current **raw one-shot** integration before comparing any
   preprocessing policy;
3. add observability at the two measured dominant stages;
4. land exact extract/coercion cancellation, then demand-driven bit lowering;
5. optimize AIG/CNF data structures only where the new counters attribute cost;
6. capture an ordered extending-path trace and validate warm push/pop reuse in
   the Glaurung explorer; and
7. derive caching and an automatic preprocessing policy from the cold corpus
   and warm trace rather than from synthetic formulas.

The producer's artifact-v17 result is already useful for ranking work: on its
128-query representative tier, Axeyum decided and agreed on all queries, ran
2.10x slower than Z3, and spent 84% of its cold time in bit lowering plus CNF
encoding. It is not yet the publishable Axeyum baseline because the query bytes
are not present in either checkout and the run predates artifact v22's
identity, deterministic-resource, repetition, and proof-companion gates.

This note expands `PLAN.md` items GQ1--GQ10 into an executable sequence. It does
not authorize changes to the Glaurung repository; producer-side and explorer
tasks below identify the required cross-project handoff.

## Evidence inspected

### Producer capture

The inspected Glaurung source is commit `7cab030bec857c177cd36e60c7164d3ed60d89ff`
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

The handoff has four issues to close before the full corpus is authoritative:

- The README reports 15,687 distinct queries, but 1,797 SAT plus 13,913 UNSAT
  is 15,710.
- `excluded-hashes.txt` has 17 rows but only 11 unique hashes.
- `build_corpus.py` emits a manifest naming every full-tier query while copying
  only representative files, so the advertised full pack is not self-contained.
- The exporter writes `index.tsv` and the builder authors a hash-bearing
  manifest directly, bypassing Axeyum's stricter artifact-v22
  `capture-index-v1.json` to manifest handshake.

The count discrepancy is plausibly explained by cross-process duplicates, but
this remains an inference until the raw directory is inspected. The capture's
`SEEN` set is process-local, while the documented command runs three separate
processes into one directory. A repeated formula can therefore append another
TSV row while overwriting the same hash-named `.smt2` file. The builder then
silently collapses TSV rows through `verdict[h] = v` and does not reject a
conflicting duplicate verdict.

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

- `axeyum-rewrite` already simplifies whole extracts, same-side extracts over
  concat, low-region extracts over zero/sign extension, extracts over bitwise
  operators and BV `ite`, and adjacent extract reassembly. GQ3 is therefore a
  **partial foundation**, not a blank TODO. Missing high-value cases include
  nested extract collapse, concat-boundary straddles, extension high/straddle
  regions, direct full-side returns, and bounded reprocessing of newly created
  terms.
- The canonicalizer is bottom-up but applies one local rule to the rebuilt
  parent; a replacement term is not recursively canonicalized in the same
  pass. A bounded fixpoint/fuel policy is necessary for composed lifter shapes.
- `axeyum-bv` currently lowers every child to a full `Vec<AigLit>` before an
  extract slices it. Raw `extract` therefore does not avoid constructing the
  discarded source bits. GQ4 must change the lowering demand contract, not just
  add another post-hoc slice.
- `axeyum-aig` already has deterministic structural hashing plus substantial
  constant, identity, XOR, and mux simplification. Its unique table is a
  `BTreeMap`, but no hit/miss/rule counters yet show that lookup is the cost.
- `axeyum-cnf` is already reachable-only and polarity-aware, with direct roots,
  XOR/mux/not-AND/private-tree recognition, and clause deduplication. GQ5 must
  profile its planning, allocation, and emission subphases before replacing
  encodings or data structures.
- The producer attribution assigns only 15% to SAT. GQ6 stays gated until the
  artifact-v22 reproduction or a later optimization makes SAT dominant.

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

Exit: the 128-query tier and full tier both have byte-complete validated
manifests; count arithmetic is reconciled; duplicate/conflict checks are
machine-enforced; no query shape is normalized during handoff.

### G1 — establish the cold truth (GQ1 + GQ10)

1. Add explicit raw, canonical-only, and configured recipes. Make raw the
   current-integration control and remove the ambiguous meaning of the existing
   recipe.
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

### G2 — add attribution needed for the first optimization

Extend the artifact without changing solver behavior:

- before/after/residual counts per GQ3 rule class, including same-side versus
  straddling concat slices, extension regions, and nested-extract depth;
- requested, unique-demanded, and actually lowered bits per term and symbol;
- AIG unique-table hits/misses, new nodes, and simplification counts by rule;
- CNF timing for reachability/use counts, gate recognition, variable allocation,
  clause construction, and deduplication;
- emitted variables, clauses, literals, direct roots, and each recognized/fused
  gate family; and
- metrics partitioned by Glaurung family and verdict.

Exit: the counters explain where the measured bit-blast and CNF time goes, and
their diagnostic overhead is either bounded or measured separately.

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
| M0 byte-complete capture | GQ1, GQ10 | No performance implementation without the representative bytes and strict manifest |
| M1 raw v22 baseline | GQ1, GQ10 | Confirm or revise the 84% construction attribution and per-family ranking |
| M2 diagnostic attribution | GQ1, GQ3--GQ5 | Choose rewrites, demand lowering, or data-structure work from counters |
| M3 cheap exact rewriting | GQ2, GQ3 | Continue only if real total time is non-worse and structure falls |
| M4 demand lowering | GQ4 | Continue only with replay-safe real AIG/CNF and wall-time reductions |
| M5 AIG/CNF optimization | GQ5 | Take only measured subphase wins; otherwise move to warm integration |
| M6 SAT re-attribution | GQ6 | Start SAT work only if search becomes material/dominant |
| M7 ordered warm trace | GQ7, GQ8 | Decide incremental API shape and whether a cache is worthwhile |
| M8 Glaurung warm integration | GQ7 | Require real same-stream functionality and performance, not the synthetic result |
| M9 auto policy and regression lane | GQ8--GQ10 | Change defaults only after representative/full/trace validation |

## Immediate next actions

1. Obtain or regenerate the 128 query bytes and strict capture index; run the
   Axeyum manifest generator and document the count reconciliation.
2. Split the Glaurung recipes into raw, canonical-only, and configured modes;
   reproduce raw artifact v22 first with five fresh processes and a proof
   companion.
3. Add the G2 AIG/CNF and residual-rewrite counters while byte transfer is
   pending; this is behavior-preserving and will make the first real run
   actionable.
4. Draft the exact-extract rewrite ADR and tests, but do not promote the rules
   based only on synthetic timing.
5. Define the ordered warm-trace schema with Glaurung before implementing cache
   or auto-policy behavior.

All heavy Rust validation and benchmark commands remain subject to the local
4 GiB virtual-memory cap and should use serial execution where parallel test
residency would exceed it.
