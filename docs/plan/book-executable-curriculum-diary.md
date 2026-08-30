# Executable textbook curriculum diary

This is the chronological engineering record for the Axeyum machinery behind
*Instruction Sets, Programs, and Proofs*. It records what was attempted, what
failed, what the controls established, and what remains unavailable. The
capability claims in `PLAN.md` and the book must stay narrower than this diary:
an entry records work; only replayable gates establish support.

## 2026-08-30 — repository audit and semantic boundary

The book inventory contained definitions and open obligations, but no active
machine-proof evidence rows. The four `CandidateLanguage`, `EvidenceManifest`,
and lesson-interface listings were explicitly illustrative. Axeyum provided
IR, solver, evidence, and Python foundations but no instruction-set semantic
authority. Starting with Python or a solver formula would therefore create a
second, ungrounded meaning for the machine examples.

Decision ADR-0811 creates `axeyum-machine` as a dependency-light Rust boundary:
concrete machine behavior first, formulas and certificates second, faithful
Python projection last. This also preserves ADR-0545's rule that Python may
project implemented Rust operations but may not invent them.

## 2026-08-30 — A0 concrete execution, first complete pass

Implemented the canonical A0 contract from the companion book:

- modular words at widths 8, 16, ..., 64, with signed and unsigned readings;
- little-endian split/join and finite byte-addressed data memory;
- eight general registers, Z/N/C/V conditions, modular PC, and explicit
  running, halted, and trapped outcomes;
- immutable code, four-byte fetch, strict decode, and every specified opcode;
- addition carry/overflow and subtraction no-borrow/overflow;
- logical and arithmetic shifts, compare, all eight branch predicates, jump,
  halt, precise fetch/data/encoding traps, and bounded state traces.

The first Clippy pass found 24 conversion, documentation, and expression-shape
problems. They were repaired without relaxing `-D warnings`. Nine initial
semantic tests passed, but that was too shallow to call the model complete.

The expanded suite found three bad test encodings/expectations, not semantic
implementation faults: the test's `rs1` field selected r2 instead of r1, its
left-shift expected value was wrong, and its subtraction carry expected borrow
rather than A0's declared no-borrow convention. Each control was corrected.

The expansion also found a real implementation omission. Code fetch subtracted
base addresses in host `u64` arithmetic, so a valid code image crossing the top
of an 8-bit address space could not fetch after PC wrap. Fetch now reduces the
offset at the architectural word width. A regression executes a jump at 252,
wraps to 0, fetches the following halt, and stops normally.

Current focused evidence:

```text
AXEYUM_AGENT=book-executable scripts/cargo-serialized.sh clippy \
  -p axeyum-machine --all-targets -- -D warnings
PASS

AXEYUM_AGENT=book-executable scripts/cargo-serialized.sh test \
  -p axeyum-machine
PASS: 17 integration tests, including exhaustive 8-bit add/sub flags
```

The suite covers every opcode family, every branch predicate with a taken and
untaken control, all supported immediate widths, zero and nonzero shifts,
unaligned 16-bit little-endian memory, incomplete/misaligned fetch, modular
code wrap, illegal/reserved encodings, finite-range stores without partial
writes, and terminal-state stuttering.

## Next boundary

A0 concrete execution alone does **not** establish a machine proof. The next
slice must add an independently checkable A0 observation/relation layer and a
derived QF_BV proof route with a mutation control. Only after that route emits
and replays evidence should the book mark its A0 proof obligations implemented.
RV64 and x86-64 remain unavailable until their authoritative source revisions,
supported instruction forms, decode constraints, and differential controls are
pinned and implemented.

## 2026-08-30 — first content-bound computation route

Added `axeyum-machine-evidence` as a consumer of the semantic crate. Keeping it
separate prevents serialization, hashing, and future solver dependencies from
becoming part of the machine's concrete semantic authority.

The first route emits an A0 semantic package whose digest binds the exact
compiled `a0.rs`, then exhaustively enumerates byte split/join for all 256
8-bit words and all 65,536 16-bit words. The report carries the package digest,
exact domain and count, pass bit, and a digest over every checked input, byte
sequence, and reconstruction. The checker validates the source-bound package
and recomputes the whole report; it does not trust the producer's pass bit.

The load-bearing negative control reverses the byte sequence before
reconstruction. It changes the recomputed result digest from
`2a1cb64d420914df46de45836be160f4aba2a49025556174c4ec9b35c3cb47d1`
to `70c1dacac9208e633a1a435302fc0c944426cc0f524ffe60bbcd7be16dd32fb2`
and exits nonzero with `semantic-mismatch`. A second control mutates the bound
semantic-source digest and is rejected as `semantic-package-mismatch`.

Focused evidence:

```text
AXEYUM_AGENT=book-executable scripts/cargo-serialized.sh clippy \
  -p axeyum-machine-evidence --all-targets -- -D warnings
PASS

AXEYUM_AGENT=book-executable scripts/cargo-serialized.sh test \
  -p axeyum-machine-evidence
PASS: 2 route/control tests

axeyum-machine-evidence check-word-roundtrip PACKAGE REPORT
PASS: values=65792

axeyum-machine-evidence control-word-roundtrip-reversed PACKAGE REPORT
EXPECTED NONZERO: semantic-mismatch
```

This earns only the `computation` trust class over the printed 8- and 16-bit
domain. It is not a general-width theorem, certificate, or kernel result.

## 2026-08-30 — observations, footprints, and a halt-PC defect

The next audit compared the executable step to A0's opcode effect table rather
than relying on terminal-state stuttering alone. It found a real defect: the
executor assigned the sequential PC before dispatch, so `halt` changed PC by
four even though the contract says it writes only the outcome. The original
test established that an already halted state had no successor but did not
inspect the transition that entered the halted state. `halt` now preserves PC,
and the regression asserts that value directly.

Added canonical observations over selected registers, nonoverlapping finite
memory spans, PC, conditions, and outcome. Construction sorts the selection
while rejecting duplicate registers, empty or overlapping spans, arithmetic
overflow, invalid register indices, and ranges outside the observed state's
memory. Applying an observation is pure and returns a canonical visible state.

Added dynamic read/write footprints for every decoded instruction. They expose
implicit PC and running-outcome reads, condition reads and writes, possible
trap-outcome writes, wrapped effective memory addresses, and word-sized byte
counts. Components are deduplicated when operands alias. `halt` is explicitly
`reads={outcome}, writes={outcome}`.

Focused evidence is now 19 passing A0 integration tests under both `cargo test`
and strict all-target Clippy. The new tests cover narrow versus broad
observations, purity, canonical ordering, malformed selectors, every
instruction footprint, operand aliasing, and the halt-PC regression.

## 2026-08-30 — source-bound observation separation route

Promoted the semantic package to schema/version 2 after observations and
dynamic effects became part of the bound source. Its metadata now declares the
implemented surfaces rather than making consumers infer them from a file hash.

Added a replayable observation report over two complete states. Both retain
`r0=7`, but `r3` is 19 on the left and 20 on the right. The narrow observation
of r0 and outcome agrees. The broad observation includes r0, r3, a memory span,
PC, conditions, and outcome; it separates the states at r3. The report binds a
canonical digest of both full input states and the exact semantic package.

The negative control removes requested r3 from the broad observation. Its
recomputation changes `broad_equal=false` to `broad_equal=true`, so the checker
exits nonzero with `semantic-mismatch`. The CLI producer, positive checker, and
control all ran directly, and the evidence crate now has three passing route
tests under strict all-target Clippy.

This route earns only the `trace` class for the printed pair of states. It does
not prove that one observation factors through another for every state, nor
does it yet serialize arbitrary states for a public Python API.
