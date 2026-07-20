# ADR-0300: Preregister a dense bit-lowering term memo

Status: proposed
Date: 2026-07-20

## Context

The accepted Glaurung evidence no longer supports a blanket performance
headline: warm Bitwuzla wins all four neutral drivers, and the bounded harder
driver protocol drops work. Axeyum's defensible publication spine is strict
correctness, checkable evidence, deployability, reproducibility, and a precisely
characterized performance regime. Cold engineering remains useful, but it must
be reported as bounded implementation work rather than a paper thesis.

The cold client profile gives this experiment a legitimate target. On the
accepted Glaurung population, bit lowering plus CNF encoding account for about
84% of Axeyum's cold pipeline while SAT search accounts for about 15%. The
strict IR errors that exposed Glaurung's concat, extension, and empty-model bugs
must remain untouched.

ADR-0285 closes the retained-clause-layout candidate before timing. A follow-up
code audit finds a separate mechanism in `axeyum-bv`: ordinary batch and
incremental full bit lowering use a `BTreeMap<TermId, Vec<AigLit>>` even though
`TermId` is a dense insertion-order `u32` index. The map is never iterated for
semantic output. Every lookup is by exact `TermId`; ordering contributes no
behavior.

The candidate note reports a 3.89x isolated scratch result for a combined dense
index plus `Rc` representation. Its named scratchpad directories are absent
from the current checkout, so that number is neither reproducible nor accepted
evidence. It also conflates lookup representation with literal-vector sharing.
Only the isolated in-tree experiment below can select a production change.

## Decision

Test exactly one representation change: replace the private full-lowering memo
with a dense `Vec<Option<Vec<AigLit>>>` indexed by `TermId::index()`.

The experiment deliberately retains owned `Vec<AigLit>` values and all current
clones. It does not add `Rc`, borrow operand slices across mutable AIG work,
reuse `term_bit_ranges` as the lowering cache, or change `lower_app`. This
isolates dense indexing from allocation/copy changes and keeps the lift map
authoritative and independent.

The dense memo must obey these rules:

1. resize lazily to the source arena length immediately before ordinary full
   lowering; demanded/range-demanded routes that do not use the memo must not
   pay for dense slots;
2. incremental lowering grows slots monotonically when the same arena grows,
   preserving every completed term across calls, deadline expiry, and ordinary
   lowering errors exactly as today;
3. lookup and insertion use checked dense indices internally; a completed term
   is stored once and no sparse or cross-arena identity is invented;
4. the ordered `term_bits`, `term_bit_ranges`, symbol-input map, root bits, AIG
   construction order, model lifting, replay, and every public type remain
   unchanged; and
5. no IR builder, sort rule, coercion, rewrite, AIG hash rule, CNF encoding
   rule, SAT policy, proof route, or Glaurung integration policy changes.

Before observing the fixed corpus, add representation-neutral memo telemetry in
a separate commit while the `BTreeMap` baseline is still production. Artifact
version 39 (version 38 remains reserved for ADR-0285's reverted flat-arena
experiment) records, for each admitted full-lowering instance:

- representation (`btree-v1` or `dense-v1`), source arena terms, occupied memo
  entries, memo lookup/hit/write counts, and payload literal length/capacity;
- exact logical header/payload bytes using native `size_of` values, with the
  formula and invariants stated in the artifact rather than relabeled as RSS;
- slot/occupancy, payload, term-bit binding, and root-width invariants; and
- the existing AIG, CNF, verdict, oracle, and replay identities.

The profile switch is diagnostic only. Unprofiled timing uses separately built
baseline and candidate commits and does not execute profile counters or retain
both memo representations.

## Pre-observation gates

Implementation is admitted to measurement only after all of these pass:

1. a private dense-memo unit gate covers empty storage, exact dense insertion,
   hit/miss behavior, growth with holes, replacement rejection, and deterministic
   occupied/payload accounting;
2. batch lowering remains byte-for-byte identical in root bits, AIG nodes,
   `term_bits`, `term_bit_ranges`, symbol inputs, evaluation, and reconstructed
   models across constants, all supported scalar operators, wide BV, shared
   DAGs, multiple roots, and unreachable arena terms;
3. incremental lowering matches batch lowering, reuses old roots without new
   nodes, grows with the arena, preserves completed children after timeout, and
   retains the exact existing profiled lookup/hit/write/copy counters;
4. ordinary, demanded, and range-demanded lowering remain semantically equal
   on their accepted slices, and the latter two show zero memo allocation in
   the new diagnostic;
5. deterministic fuzz and Z3-oracle QF_BV tests retain zero disagreement, every
   SAT model replays against the original terms, and UNSAT proof/checker routes
   remain unchanged;
6. artifact-v39 baseline and candidate profile records fail closed on missing
   fields, unknown representation, slot/occupancy drift, payload mismatch,
   non-finite numbers, or any changed AIG/CNF/verdict/replay row;
7. the complete workspace tests, strict Clippy, warning-denied rustdoc,
   formatting, docs links, no-default/QF_BV builds, and ordinary plus
   `+simd128` wasm32 QF_BV builds pass; and
8. every Rust build/test command uses one build job inside the 4 GiB cgroup;
   full tests use `CARGO_PROFILE_TEST_DEBUG=0`. A capped OOM is a failed gate.

The telemetry commit and its tests must be committed before the baseline
profile. The candidate commit and its tests must be committed before the
candidate profile. No corrected-wide-v3 result may be used to alter these
gates.

## Fixed structural observation

Run one clean detached baseline profile and one clean detached candidate profile
over ADR-0285's accepted corrected-wide-v3 representative population:

- manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- 162 queries: 88 SAT and 74 UNSAT, with exact family counts 36 arithmetic, 12
  comparison, 7 mixed, 52 register-slice, 54 slice-partial, and 1 trivial;
- raw/rewrite-off `sat-bv`, in-process Z3, one job;
- 10,000 ms wall, 2,000,000 BatSat progress checks, 300,000 term nodes,
  3,000,000 CNF variables, and 8,000,000 CNF clauses; and
- 100% decided, manifest/Z3 agreement, and all SAT original-model replays.

The candidate advances to timing only if every per-query outcome, original
model replay, AIG node/input/request/hash statistic, root literal, CNF variable,
clause/construction statistic, term-bit binding, memo occupancy, memo payload
length, and exact family/population count matches the baseline. Dense slots must
equal source arena terms on every full-lowering row; occupied entries must equal
completed full-lowering terms; payload literal length must equal retained
full-lowering term-bit bindings.

Report logical bytes per instance and in aggregate. The candidate's aggregate
logical memo bytes may not exceed 110% of the baseline's conservative logical
memo bytes. This is a deterministic guard, not a memory claim. Any structural,
soundness, accounting, or logical-storage failure rejects the candidate before
timing.

## Conditional unprofiled timing protocol

Only after the structural gate passes, compare distinct prebuilt release
executables for the preregistration baseline and dense candidate. Run six
order-balanced pairs in the fixed sequence `B,C,C,B,B,C,C,B,B,C,C,B` over the
same 162-query population with profiling disabled and every other corpus,
backend, oracle, worker, timeout, and deterministic-resource setting unchanged.

Every process must decide 162/162, replay 88/88 SAT models, agree with the
manifest and in-process Z3, and preserve every per-query AIG/CNF structure.
Source/binary identities are the only permitted environment differences.

For each pair, sum per-query `bit_blast_ms` and `cold_total_ms`. Accept only if:

- the six candidate/baseline bit-blast ratios have geometric mean at most
  `0.97` and deterministic paired-bootstrap 95% upper bound below `1.0`;
- neither baseline nor candidate bit-blast run-total CV exceeds 3%;
- no family with at least 5 ms aggregate baseline bit-blast time has a paired
  geometric mean above `1.02`; smaller families remain reported;
- cold-total geometric mean is at most `1.0` with paired-bootstrap 95% upper
  bound at most `1.02`; and
- candidate process peak RSS is no more than 5% above paired baseline.

The bit-blast gate is the selection criterion. The absent scratch result,
fewer comparisons, lower logical bytes, or a favorable point estimate cannot
rescue failed correctness, identity, variance, family, total-time, or RSS
gates. Do not rerun to select a quieter sample or combine another optimization.
On rejection, restore the `BTreeMap` representation and retain the ADR and
measurements as negative evidence.

## Consequences

If every gate passes, dense indexing becomes the private full-lowering memo and
the result is reported as a bounded cold-path implementation improvement. It
does not establish solver leadership, change the neutral Bitwuzla result,
expand decided coverage, or support the missing scratch number.

If any gate fails, production remains on `BTreeMap`; the exact failure and
artifact remain useful negative evidence. `Rc` sharing, lift-map unification,
term-interning changes, packed CNF literals, and other data-structure candidates
require separate ADRs.

## Rejected alternatives

- **Adopt the reported dense-plus-`Rc` prototype directly:** rejected because
  the reproduction is absent and it conflates two mechanisms.
- **Use `term_bit_ranges` as the memo:** rejected for this experiment because
  lift/replay metadata must remain explicit and sparse-demand ranges are not a
  full literal-vector cache.
- **Allocate dense slots in every lowering mode:** rejected because demanded
  routes do not consume the full memo and should not inherit unrelated cost.
- **Keep a runtime BTree/dense switch:** rejected because it contaminates the
  hot path and memory layout; distinct commits provide the control.
- **Select on comparison counts or microbenchmarks:** rejected by the project
  methodology and the ADR-0259/0285 lessons.

## References

- ADR-0009, ADR-0200, ADR-0259 through ADR-0277, and ADR-0285.
- `docs/research/08-planning/cold-path-datastructure-candidates.md`.
- `docs/research/08-planning/benchmarking-and-performance-methodology.md`.
- `crates/axeyum-bv/src/lib.rs`, `IncrementalLowering` and `LoweringBuilder`.
